# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: rapids_cxs_tile_straps_tb
# Purpose: rapids_cxs_top with TILE_CREDITS = 1: the straps toward RAPIDS --
#          landing space per cell, the descriptor intake queue, credit returns,
#          resync and quiescent gating (TILE_SPEC 11.9-11.11, rapids TASK-027)
#
# Documentation: projects/components/compute-eng-ip/tile/docs/TILE_SPEC.md (Section 11)
# Subsystem: rapids
# Author: sean galloway
# Created: 2026-10-19
"""RAPIDS as the tile I/O, from the senders' side.

The testbench plays the cells and the tetrads' control cores sending INTO
RAPIDS. Each starts from its strap -- a cell TILE_LAND_FLITS flits (header
included), a core TILE_DESC_PER_CORE descriptor entries -- sends only while
its strap covers a whole packet, and gets credits back as `add` packets on
RAPIDS's own credit interface (m_tile_credit_*). RAPIDS must
  * land every cell's data in its landing space and deliver it to its sink
    channel, returning every flit (header included) as it is consumed;
  * keep a cell whose channel cannot take its data from holding anyone
    else's: the sink port never waits on a landing space;
  * consume and return what it discards (a disabled channel, an unsupported
    packet), so no path swallows a credit;
  * pass core descriptors through the intake queue and return an entry as each
    one moves into the descriptor queue, never dropping one under the strap;
  * on a resync, while the tile is quiescent, send every legal cell and core
    one `set` restoring its strap; and act on a channel reset only while
    the tile is quiescent.
"""
from typing import Any, Dict, List, Tuple
import os

import cocotb
from cocotb.triggers import RisingEdge

from projects.components.dma_ip.rapids.dv.tbclasses.rapids_cxs_tile_tb import (
    PTYPE_CREDIT, PTYPE_DESC, PTYPE_MEM, RAPIDS_COORD, TileHeader, coord)
from projects.components.dma_ip.rapids.dv.tbclasses.rapids_cxs_tile_credits_tb import (
    CLASS_DESC, CLASS_SPACE, LEVEL_TETRAD, OP_ADD, OP_SET, RapidsCxsTileCreditsTB, cell)
from TBClasses.monbus import parse_stream
from TBClasses.monbus.monbus_types import ProtocolType, PktType

PTYPE_RESERVED = 5
RAPIDS_EVENT_STALL = 0x8
SNK_STALL_AGENT, SRC_STALL_AGENT = 0x0B, 0x0C


def core(x: int, y: int) -> int:
    """A tetrad's control core: the external ID of its tetrad node."""
    return coord(LEVEL_TETRAD, x, y, 0, ext=1)


class RapidsCxsTileStrapsTB(RapidsCxsTileCreditsTB):
    """rapids_cxs_top with TILE_HDR = 1, TILE_CREDITS = 1, seen from the senders."""

    def __init__(self, dut):
        super().__init__(dut)
        self.LAND = int(os.environ.get('TEST_TILE_LAND_FLITS', '16'))
        self.DESC_PER_CORE = int(os.environ.get('TEST_TILE_DESC_PER_CORE', '2'))
        self.returns: List[Tuple[int, TileHeader]] = []   # (cycle, header) of each credit packet
        self.sent_flits: Dict[int, int] = {}              # per cell: flits sent against the strap
        self.sent_desc: Dict[int, int] = {}               # per core: entries sent against the strap
        self._cycle = 0

    async def initialize_test(self):
        await super().initialize_test()
        cocotb.start_soon(self._watch_credit_port())

    async def _watch_credit_port(self):
        d = self.dut
        while True:
            await RisingEdge(self.clk)
            self._cycle += 1
            if int(d.m_tile_credit_valid.value) and int(d.m_tile_credit_ready.value):
                self.returns.append((self._cycle, TileHeader.unpack(int(d.m_tile_credit_data.value))))

    # ---- what RAPIDS has returned ----------------------------------------
    def returned(self, sender: int, cls: int) -> int:
        """Credits RAPIDS has given back to `sender` in class `cls` (adds only)."""
        return sum(h.length for _c, h in self.returns
                   if h.dst == sender and (h.target & 3) == cls and h.op == OP_ADD)

    def return_errors(self) -> List[str]:
        """Every credit packet must be a well-formed header from RAPIDS."""
        errs = []
        for c, h in self.returns:
            if h.src != RAPIDS_COORD or h.ptype != PTYPE_CREDIT or h.tag != 0 or h.target >> 2:
                errs.append(f"credit packet at cycle {c} malformed: {h}")
        return errs

    def strap_free(self, sender: int) -> int:
        return self.LAND - self.sent_flits.get(sender, 0) + self.returned(sender, CLASS_SPACE)

    def desc_free(self, sender: int) -> int:
        return self.DESC_PER_CORE - self.sent_desc.get(sender, 0) + self.returned(sender, CLASS_DESC)

    async def wait_for(self, cond, timeout_cycles: int = 20000) -> bool:
        for _ in range(timeout_cycles):
            if cond():
                return True
            await self.wait_clocks(self.clk_name, 1)
        return cond()

    # ---- what a cell or core sends ---------------------------------------
    async def cell_write(self, sender: int, channel: int, payload: List[int],
                         ptype: int = PTYPE_MEM, op: int = 0, honour_strap: bool = True) -> bool:
        """A write-format packet from `sender` into sink channel `channel`,
        sent only once its strap covers every flit (header included)."""
        flits = 1 + len(payload)
        if honour_strap and not await self.wait_for(lambda: self.strap_free(sender) >= flits):
            return False
        self.sent_flits[sender] = self.sent_flits.get(sender, 0) + flits
        hdr = TileHeader(RAPIDS_COORD, sender, ptype, op, len(payload) * self.STRB_WIDTH, 0, channel)
        await self.cell_send(channel, hdr, payload)
        return True

    async def core_descriptor(self, sender: int, src_channel: int, desc: int,
                              honour_strap: bool = True) -> bool:
        """A desc packet from a control core, against its intake strap."""
        if honour_strap and not await self.wait_for(lambda: self.desc_free(sender) >= 1):
            return False
        self.sent_desc[sender] = self.sent_desc.get(sender, 0) + 1
        hdr = TileHeader(dst=RAPIDS_COORD, src=sender, ptype=PTYPE_DESC, op=0,
                         length=32, target=0, tag=src_channel)
        await self.cell_send(src_channel, hdr, [desc], payload_strbs=[(1 << 32) - 1])
        return True

    # ---- the sink side ---------------------------------------------------
    def sink_slot(self, channel: int, k: int) -> int:
        return self.DST_BASE + channel * self.CHANNEL_OFFSET + k * 0x1000

    async def sink_descriptor(self, channel: int, k: int, beats: int) -> int:
        """Kick sink channel `channel` with a descriptor for `beats` beats at its slot k."""
        desc_addr = self.DESC_BASE + channel * 0x1000 + k * 0x40
        dst = self.sink_slot(channel, k)
        self.register_descriptor(self.desc_snk_mem, desc_addr,
                                 self.create_descriptor(0, dst, beats, channel_id=channel))
        await self.kick_off_channel('snk', channel, desc_addr)
        return dst

    async def wait_sink(self, dst: int, pattern: List[int], timeout_cycles: int = 20000) -> bool:
        return await self.wait_for(lambda: self.read_sink(dst, len(pattern)) == pattern, timeout_cycles)

    async def strap_status(self) -> Dict[str, int]:
        v = await self.read_reg('src', 'TILE_CREDIT_STATUS')
        return {'resync_busy': (v >> 1) & 1, 'land_overrun': (v >> 2) & 1,
                'intake_overrun': (v >> 3) & 1, 'ret_count': v >> 16}

    async def finish_straps(self, errors: List[str], what: str, want_land_overrun: int = 0,
                            want_intake_overrun: int = 0) -> Tuple[bool, Dict[str, Any]]:
        st = await self.strap_status()
        if st['land_overrun'] != want_land_overrun:
            errors.append(f"TILE_CREDIT_STATUS.LAND_OVERRUN = {st['land_overrun']}, expected {want_land_overrun}")
        if st['intake_overrun'] != want_intake_overrun:
            errors.append(f"TILE_CREDIT_STATUS.INTAKE_OVERRUN = {st['intake_overrun']}, "
                          f"expected {want_intake_overrun}")
        if st['ret_count'] != len(self.returns) & 0xFFFF:
            errors.append(f"TILE_CREDIT_STATUS.RET_COUNT = {st['ret_count']}, "
                          f"{len(self.returns)} credit packets seen")
        errors += self.return_errors()
        return self._finish(errors, what)

    def _strap_back(self, sender: int, what: str) -> List[str]:
        """Everything a cell sent has come back: its strap is whole again."""
        got = self.returned(sender, CLASS_SPACE)
        sent = self.sent_flits.get(sender, 0)
        return [] if got == sent else [f"{what}: {sent} flits sent, {got} returned"]

    # =====================================================================
    # Scenarios
    # =====================================================================
    async def test_land(self, channel: int = 2, packets: int = 6, beats: int = 7) -> Tuple[bool, Dict[str, Any]]:
        """A cell streams more than its strap into one sink channel: every
        packet lands where its descriptor says, the cell can only keep going
        because RAPIDS returns each flit, header included, and at the end every
        flit is back. Returns come promptly: the first header flit back within
        a few cycles of the header."""
        self.log.info(f"=== TILE straps: landing space, {packets} x {beats} beats > strap {self.LAND} ===")
        a = cell(1, 2)
        errors = await self.open_window({a: 64})
        for k in range(packets):
            pat = self._pattern(0x40 + k, channel, beats)
            dst = await self.sink_descriptor(channel, k, beats)
            t0 = self._cycle
            if not await self.cell_write(a, channel, pat):
                errors.append(f"packet {k}: the strap never covered {1 + beats} flits "
                              f"({self.strap_free(a)} free): credits were not returned")
                break
            if not await self.wait_sink(dst, pat):
                errors.append(f"packet {k}: the payload did not land at 0x{dst:X}")
            if k == 0:
                first = next((c for c, h in self.returns if h.dst == a), None)
                if first is None or first - t0 > 200:
                    errors.append(f"the first return came {None if first is None else first - t0} "
                                  f"cycles after the first packet, expected promptly")
        await self.settle(300)
        errors += self._strap_back(a, "cell")
        if self.read_sched_error('snk') not in (0, -1):
            errors.append(f"snk_sched_error=0x{self.read_sched_error('snk'):X}")
        return await self.finish_straps(errors, "landing space")

    async def test_land_isolation(self, beats: int = 0) -> Tuple[bool, Dict[str, Any]]:
        """Cell A's channel has no descriptor yet: A's two packets wait in A's
        landing space (only their header flits come back). Cell B, on another
        channel, is not held up behind them: its packets land meanwhile. Once
        A's channel gets its descriptors, A's data drains and every flit
        returns. Two packets of `beats` (default LAND/2 - 1) fill A's strap."""
        beats = beats or self.LAND // 2 - 1
        self.log.info("=== TILE straps: a waiting cell holds only its own landing space ===")
        a, b = cell(0, 0), cell(3, 3)
        ch_a, ch_b = 3, 4
        errors = await self.open_window({a: 64, b: 64})
        pat_a = [self._pattern(0xA0 + k, ch_a, beats) for k in range(2)]
        for k in range(2):
            if not await self.cell_write(a, ch_a, pat_a[k]):
                errors.append(f"A packet {k}: no strap to send it")
        await self.settle(200)
        if self.returned(a, CLASS_SPACE) != 2:
            errors.append(f"A: {self.returned(a, CLASS_SPACE)} flits back while its data waits, "
                          f"expected 2 (the headers)")
        for k in range(3):
            pat = self._pattern(0xB0 + k, ch_b, beats)
            dst = await self.sink_descriptor(ch_b, k, beats)
            if not await self.cell_write(b, ch_b, pat):
                errors.append(f"B packet {k}: no strap to send it")
            if not await self.wait_sink(dst, pat, 5000):
                errors.append(f"B packet {k}: did not land while A waited -- A's landing space held B")
        if self.read_sink(self.sink_slot(ch_a, 0), beats) == pat_a[0]:
            errors.append("A's data landed before its channel had a descriptor")
        for k in range(2):
            dst = await self.sink_descriptor(ch_a, k, beats)
            if not await self.wait_sink(dst, pat_a[k]):
                errors.append(f"A packet {k}: did not drain once its channel had a descriptor")
        await self.settle(300)
        errors += self._strap_back(a, "cell A") + self._strap_back(b, "cell B")
        return await self.finish_straps(errors, "landing isolation")

    async def test_land_discard(self, beats: int = 3) -> Tuple[bool, Dict[str, Any]]:
        """What RAPIDS throws away still returns its credit: data for a
        disabled sink channel (drained from the landing space, nothing
        written), a read request into RAPIDS and a reserved ptype (dropped at
        the header, flagged unsupported). A core's data packet has no landing
        space: it is dropped and returns no flit credit. The channel stays
        usable."""
        self.log.info("=== TILE straps: discarded packets return their credits ===")
        a, k_core = cell(2, 0), core(0, 1)
        ch_off = 5
        errors = await self.open_window({a: 64})
        all_ch = (1 << self.NUM_CHANNELS) - 1
        await self.write_fields('snk', 'CHANNEL_ENABLE', CH_EN=all_ch & ~(1 << ch_off))
        before = self.read_sink(self.sink_slot(ch_off, 0), beats)
        await self.cell_write(a, ch_off, self._pattern(0xD0, ch_off, beats))
        await self.cell_write(a, ch_off, [], op=1)                         # read request into RAPIDS
        await self.cell_write(a, ch_off, self._pattern(0xD1, ch_off, beats), ptype=PTYPE_RESERVED)
        await self.cell_write(k_core, ch_off, self._pattern(0xD2, ch_off, beats), honour_strap=False)
        await self.settle(500)
        errors += self._strap_back(a, "cell")
        if self.returned(k_core, CLASS_SPACE):
            errors.append(f"a core got {self.returned(k_core, CLASS_SPACE)} flit credits for a dropped data packet")
        if self.read_sink(self.sink_slot(ch_off, 0), beats) != before:
            errors.append("data for a disabled channel was written to memory")
        if not self.tile_status()['unsupported']:
            errors.append("sts_tile_unsupported not set by the read request / reserved ptype")
        await self.write_fields('snk', 'CHANNEL_ENABLE', CH_EN=all_ch)
        pat = self._pattern(0xD3, ch_off, beats)
        dst = await self.sink_descriptor(ch_off, 1, beats)
        await self.cell_write(a, ch_off, pat)
        if not await self.wait_sink(dst, pat):
            errors.append("the channel did not carry data after its discards")
        await self.settle(200)
        errors += self._strap_back(a, "cell after re-enable")
        return await self.finish_straps(errors, "discards return credits")

    async def test_coalesce(self, beats: int = 3) -> Tuple[bool, Dict[str, Any]]:
        """While the credit port is held, returns build up; when it opens they
        leave as one add per sender, the whole count, never split."""
        self.log.info("=== TILE straps: returns coalesce while the credit port waits ===")
        a = cell(1, 1)
        ch = 1
        errors = await self.open_window({a: 64})
        self.dut.m_tile_credit_ready.value = 0
        for k in range(2):
            pat = self._pattern(0xC0 + k, ch, beats)
            dst = await self.sink_descriptor(ch, k, beats)
            await self.cell_write(a, ch, pat)
            if not await self.wait_sink(dst, pat):
                errors.append(f"packet {k} did not land")
        await self.settle(100)
        n_before = len(self.returns)
        self.dut.m_tile_credit_ready.value = 1
        await self.settle(100)
        new = [h for _c, h in self.returns[n_before:] if h.dst == a]
        # the output register already held the first return when the port closed
        if not (1 <= len(new) <= 2):
            errors.append(f"{len(new)} credit packets after the port opened, expected the held one "
                          f"and one coalesced return")
        errors += self._strap_back(a, "cell")
        return await self.finish_straps(errors, "coalesced returns")

    def _src_pattern_desc(self, channel: int, k: int, dst: int, beats: int = 1):
        desc, hdr, pat = self._src_desc(channel, k, beats, dst, 0x200 + k * 0x10)
        return desc, hdr, pat

    async def test_intake(self, n: int = 6) -> Tuple[bool, Dict[str, Any]]:
        """A control core issues descriptors against its intake strap
        (TILE_DESC_PER_CORE entries), waiting for each entry to come back.
        Every descriptor runs, in order per channel, none is dropped, and
        every entry returns (class 1)."""
        self.log.info(f"=== TILE straps: descriptor intake, {n} descriptors, strap {self.DESC_PER_CORE} ===")
        k_core, dst = core(1, 1), cell(2, 2)
        errors = await self.open_window({dst: 1000, k_core: 4})
        expect: Dict[int, List] = {}
        for i in range(n):
            ch = i % 2
            desc, hdr, pat = self._src_pattern_desc(ch, i, dst, beats=2)
            expect.setdefault(ch, []).append((hdr, pat))
            if not await self.core_descriptor(k_core, ch, desc):
                errors.append(f"descriptor {i}: the intake strap never came back")
                break
        for ch, want in expect.items():
            if not await self.wait_egress_packets(ch, len(want)):
                errors.append(f"ch{ch}: {len(self.egress_packets(ch))} of {len(want)} packets went out")
            for j, (hdr, pat) in enumerate(want):
                pkts = self.egress_packets(ch)
                if j < len(pkts):
                    errors += self.check_packet(pkts[j], hdr, pat, f"ch{ch} packet {j}")
        await self.settle(200)
        if self.returned(k_core, CLASS_DESC) != n:
            errors.append(f"{self.returned(k_core, CLASS_DESC)} intake entries returned for {n} descriptors")
        if int(self.dut.sts_tile_desc_dropped.value):
            errors.append(f"sts_tile_desc_dropped=0x{int(self.dut.sts_tile_desc_dropped.value):X}")
        return await self.finish_straps(errors, "descriptor intake")

    async def test_intake_overrun(self, n: int = 40) -> Tuple[bool, Dict[str, Any]]:
        """A core ignores its strap and floods descriptors at a channel whose
        destination is out of credits, so the channel holds them. What does
        not fit the intake queue is dropped, flagged, and still returned; the
        descriptor queue itself never drops one (it waits instead). Once the
        destination returns credits the held descriptors run in order: the
        ones that survived are an in-order subsequence of those sent (the
        queue keeps draining into the descriptor queue during the flood, so
        drops land wherever it happened to be full)."""
        self.log.info(f"=== TILE straps: intake overrun, {n} descriptors ===")
        k_core, dst = core(0, 0), cell(3, 1)
        ch = 6
        per = self.flits(1 * self.STRB_WIDTH)
        errors = await self.open_window({dst: per, k_core: 4})
        want = []
        for i in range(n):
            desc, hdr, pat = self._src_pattern_desc(ch, i, dst, beats=1)
            want.append((hdr, pat))
            await self.core_descriptor(k_core, ch, desc, honour_strap=False)
        await self.settle(300)
        st = await self.strap_status()
        if not st['intake_overrun']:
            errors.append("INTAKE_OVERRUN not set by a flood past the intake queue")
        if int(self.dut.sts_tile_desc_dropped.value):
            errors.append("the descriptor queue dropped a descriptor (it must wait for the slot)")
        await self.send_credit(dst, per * n)
        if not await self.wait_for(lambda: self.returned(k_core, CLASS_DESC) == n, 40000):
            errors.append(f"{self.returned(k_core, CLASS_DESC)} entries returned for {n} sent")
        await self.settle(2000)
        pkts = self.egress_packets(ch)
        if not 1 < len(pkts) < n:
            errors.append(f"{len(pkts)} packets went out of {n}: expected some, not all")
        # match each packet to the next sent descriptor it can be: in order, none twice
        nxt = 0
        for j, pkt in enumerate(pkts):
            k = next((i for i in range(nxt, n) if not self.check_packet(pkt, want[i][0], want[i][1], "")), None)
            if k is None:
                errors.append(f"packet {j} matches no descriptor sent after the previous one "
                              f"(out of order, duplicated or corrupt)")
                break
            nxt = k + 1
        return await self.finish_straps(errors, "intake overrun", want_intake_overrun=1)

    async def test_resync(self) -> Tuple[bool, Dict[str, Any]]:
        """A resync waits for the quiescent signal, then restores exactly the
        legal senders' straps: a set of TILE_LAND_FLITS to each cell that
        advertised, a set of TILE_DESC_PER_CORE to each core, nothing to a
        sender that never advertised."""
        self.log.info("=== TILE straps: resync after failover ===")
        a, b, k_core, absent = cell(0, 1), cell(2, 3), core(1, 0), cell(3, 3)
        errors = await self.open_window({a: 32, b: 32, k_core: 4})
        d = self.dut
        d.tile_quiescent.value = 0
        n0 = len(self.returns)
        await self.write_fields('src', 'TILE_RESYNC', GO=1)
        await self.settle(200)
        st = await self.strap_status()
        if not st['resync_busy']:
            errors.append("RESYNC_BUSY not set while the resync waits for quiescent")
        if len(self.returns) != n0:
            errors.append("credit packets went out before the tile was quiescent")
        d.tile_quiescent.value = 1
        await self.settle(200)
        sets = {(h.dst, h.target & 3): h.length for _c, h in self.returns[n0:] if h.op == OP_SET}
        want = {(a, CLASS_SPACE): self.LAND, (b, CLASS_SPACE): self.LAND, (k_core, CLASS_DESC): self.DESC_PER_CORE}
        if sets != want:
            errors.append(f"resync sets {sets}, expected {want}")
        if any(h.dst == absent for _c, h in self.returns):
            errors.append("a resync set went to a cell that never advertised")
        st = await self.strap_status()
        if st['resync_busy']:
            errors.append("RESYNC_BUSY still set after the sets went out")
        return await self.finish_straps(errors, "resync")

    async def test_quiescent_reset(self, channel: int = 1, beats: int = 2) -> Tuple[bool, Dict[str, Any]]:
        """A channel reset acts only while the tile is quiescent: a sink
        channel errored by a length mismatch stays errored through a reset
        written while not quiescent, and clears on one written while it is."""
        self.log.info("=== TILE straps: channel reset gated by quiescent ===")
        a = cell(1, 0)
        errors = await self.open_window({a: 64})
        await self.sink_descriptor(channel, 0, beats)
        await self.cell_write(a, channel, self._pattern(0xE0, channel, beats + 1))   # one beat too many
        if not await self.wait_for(lambda: (self.read_sched_error('snk') >> channel) & 1, 5000):
            return self._finish(["the length mismatch did not error the channel"], "quiescent reset")
        d = self.dut
        d.tile_quiescent.value = 0
        await self.write_fields('snk', 'CHANNEL_RESET', CH_RST=1 << channel)
        await self.settle(50)
        await self.write_fields('snk', 'CHANNEL_RESET', CH_RST=0)
        await self.settle(50)
        if not (self.read_sched_error('snk') >> channel) & 1:
            errors.append("a channel reset acted while the tile was not quiescent")
        d.tile_quiescent.value = 1
        await self.write_fields('snk', 'CHANNEL_RESET', CH_RST=1 << channel)
        await self.settle(50)
        await self.write_fields('snk', 'CHANNEL_RESET', CH_RST=0)
        await self.settle(50)
        if (self.read_sched_error('snk') >> channel) & 1:
            errors.append("a channel reset while quiescent did not clear the error")
        pat = self._pattern(0xE1, channel, beats)
        dst = await self.sink_descriptor(channel, 1, beats)
        await self.cell_write(a, channel, pat)
        if not await self.wait_sink(dst, pat):
            errors.append("the channel did not carry data after its reset")
        await self.settle(200)
        errors += self._strap_back(a, "cell")
        return await self.finish_straps(errors, "quiescent-gated reset")

    # ---- stalled-data checks (TILE_SPEC 11.9 hazard rules) ---------------
    def _stall_records(self, n0: int) -> List[Any]:
        ws = self.mon_w_beats[n0:]
        ws = ws[:len(ws) - len(ws) % 3]
        return [r.packet for r in parse_stream(ws, stride_bytes=24, ts_mode=1)
                if r.packet.protocol == ProtocolType.PROTOCOL_CORE
                and r.packet.packet_type == PktType.PktTypeError
                and r.packet.agent_id in (SNK_STALL_AGENT, SRC_STALL_AGENT)]

    async def _wait_stall_records(self, n0: int, n: int) -> List[Any]:
        """The capture master lags by thousands of cycles: wait for n records."""
        for _ in range(400):
            if len(self._stall_records(n0)) >= n:
                break
            await self.wait_clocks(self.clk_name, 50)
        await self.wait_clocks(self.clk_name, 500)
        return self._stall_records(n0)

    def _check_stall_record(self, recs: List[Any], agent: int, channel: int, kind: int,
                            cycles: int, what: str) -> List[str]:
        mine = [p for p in recs if p.agent_id == agent]
        if len(mine) != 1:
            got = [(p.channel_id, hex(p.event_data)) for p in mine]
            return [f"{what}: {len(mine)} stall records from agent 0x{agent:02X} {got}, expected 1"]
        p = mine[0]
        errs = []
        if p.channel_id != channel:
            errs.append(f"{what}: stall record on channel {p.channel_id}, expected {channel}")
        if p.event_code != RAPIDS_EVENT_STALL:
            errs.append(f"{what}: event code 0x{p.event_code:X}, expected 0x{RAPIDS_EVENT_STALL:X}")
        if (p.event_data >> 32) & 1 != kind or p.event_data & 0xFFFF_FFFF != cycles:
            errs.append(f"{what}: event data 0x{p.event_data:X}, expected kind {kind}, threshold {cycles}")
        return errs

    async def test_stall_sink(self, channel: int = 2, beats: int = 4, cycles: int = 300) -> Tuple[bool, Dict[str, Any]]:
        """Sink SRAM data that cannot be written out (the memory holds WREADY
        low) raises one stall error on MonBus past the threshold, and the
        channel's TILE_STALLED bit; when the memory takes the data again the
        bit clears and the data lands. A transfer that moves raises nothing."""
        self.log.info(f"=== TILE straps: sink stalled-data check, threshold {cycles} ===")
        a = cell(0, 2)
        errors = await self.open_window({a: 64})
        await self.write_reg('src', 'TILE_STALL_CYCLES', cycles)
        await self.write_fields('src', 'WRMON_PKT_MASK', PKT_MASK=0)   # CORE packets to the capture
        n0 = len(self.mon_w_beats)
        pat0 = self._pattern(0x70, channel, beats)                       # moves: no record
        dst0 = await self.sink_descriptor(channel, 0, beats)
        await self.cell_write(a, channel, pat0)
        if not await self.wait_sink(dst0, pat0):
            errors.append("the unstalled transfer did not land")
        self.wr_slave['W'].set_ready_policy('stall')
        pat = self._pattern(0x71, channel, beats)
        dst = await self.sink_descriptor(channel, 1, beats)
        await self.cell_write(a, channel, pat)
        await self.settle(3 * cycles)
        if not (await self.read_reg('snk', 'TILE_STALLED') >> channel) & 1:
            errors.append("SNK.TILE_STALLED not set while the channel's data could not move")
        self.wr_slave['W'].set_ready_policy('always')
        if not await self.wait_sink(dst, pat):
            errors.append("the data did not land once the memory took it again")
        await self.settle(100)
        if await self.read_reg('snk', 'TILE_STALLED'):
            errors.append("SNK.TILE_STALLED still set after the data moved")
        recs = await self._wait_stall_records(n0, 1)
        errors += self._check_stall_record(recs, SNK_STALL_AGENT, channel, 0, cycles, "sink")
        return await self.finish_straps(errors, "sink stalled-data check")

    async def test_stall_source(self, channel: int = 3, beats: int = 4, cycles: int = 300) -> Tuple[bool, Dict[str, Any]]:
        """A source channel whose reads are outstanding with no R beat (the
        memory answers late) raises one stall error on MonBus and its
        TILE_STALLED bit; the packet still goes out correctly once the data
        arrives."""
        self.log.info(f"=== TILE straps: source stalled-data check, threshold {cycles} ===")
        dst = cell(1, 3)
        errors = await self.open_window({dst: 1000})
        await self.write_reg('src', 'TILE_STALL_CYCLES', cycles)
        await self.write_fields('src', 'WRMON_PKT_MASK', PKT_MASK=0)
        n0 = len(self.mon_w_beats)
        rd = self.rd_slave['interface']
        rd.response_delay_cycles = 4 * cycles
        desc, hdr, pat = self._src_desc(channel, 0, beats, dst, 0x80)
        await self.kick(channel, desc)
        await self.settle(3 * cycles)
        if not (await self.read_reg('src', 'TILE_STALLED') >> channel) & 1:
            errors.append("SRC.TILE_STALLED not set while the channel's reads went unanswered")
        rd.response_delay_cycles = 1
        if not await self.wait_egress_packets(channel, 1):
            errors.append("the packet never went out once the reads were answered")
        else:
            errors += self.check_packet(self.egress_packets(channel)[0], hdr, pat, "late-read packet")
        await self.settle(100)
        if await self.read_reg('src', 'TILE_STALLED'):
            errors.append("SRC.TILE_STALLED still set after the data arrived")
        recs = await self._wait_stall_records(n0, 1)
        errors += self._check_stall_record(recs, SRC_STALL_AGENT, channel, 1, cycles, "source")
        return await self.finish_straps(errors, "source stalled-data check")
