# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: rapids_cxs_tile_tb
# Purpose: rapids_cxs_top built with TILE_HDR = 1: the tile packet header on
#          both CXS ports and cell-issued descriptors (TILE_SPEC 11.5 / 11.11)
#
# Documentation: projects/components/compute-eng-ip/tile/docs/TILE_SPEC.md (Section 11)
# Subsystem: rapids
# Author: sean galloway
# Created: 2026-10-17
"""RAPIDS as the tile I/O.

With TILE_HDR = 1 every packet on the source and sink ports starts with one
header beat (bits [127:0]); the layout is rapids_pkg::tile_hdr_pack, i.e.
TILE_SPEC Section 11.5's packing. This testbench is the CXS top testbench
(network BFMs, memory models, APB by name) plus a cell's view of the header:
it builds the packets a cell would send into the sink port and reads the
packets RAPIDS sends out of the source port as {header, payload}.
"""

from dataclasses import dataclass
from typing import Any, Dict, List, Tuple

from projects.components.dma_ip.rapids.dv.tbclasses.rapids_cxs_top_tb import RapidsCxsTopTB

# rapids_pkg tile header layout (TILE_SPEC 11.5)
PTYPE_CFG, PTYPE_PROG, PTYPE_MEM, PTYPE_CREDIT, PTYPE_DESC = 0, 1, 2, 3, 4
COORD_W, TARGET_W = 15, 49       # coordinate {ext, level, X, Y, Z}; dst_addr = {coord, target}
HDR_BYTES = 16
RAPIDS_COORD = 0x3000            # {ext 0, level 3 = tile I/O, X 0, Y 0, Z 0}: the top's default


def coord(level: int, x: int, y: int, z: int, ext: int = 0) -> int:
    """A tile coordinate (TILE_SPEC 11.3). ext = 0 names the node itself,
    ext = 1 what is attached at its local port (a cell, a control core)."""
    return ((ext & 1) << 14) | ((level & 3) << 12) | ((x & 0xF) << 8) | ((y & 0xF) << 4) | (z & 0xF)


@dataclass(frozen=True)
class TileHeader:
    dst: int
    src: int
    ptype: int
    op: int
    length: int
    target: int
    tag: int

    def pack(self) -> int:
        return ((self.dst & ((1 << COORD_W) - 1))
                | (self.src & ((1 << COORD_W) - 1)) << 15
                | (self.ptype & 7) << 30
                | (self.op & 1) << 33
                | (self.length & 0xFFFF_FFFF) << 34
                | (self.target & ((1 << TARGET_W) - 1)) << 66
                | (self.tag & 0xF) << 115)

    @classmethod
    def unpack(cls, word: int) -> 'TileHeader':
        m = (1 << COORD_W) - 1
        return cls(dst=word & m, src=(word >> 15) & m, ptype=(word >> 30) & 7,
                   op=(word >> 33) & 1, length=(word >> 34) & 0xFFFF_FFFF,
                   target=(word >> 66) & ((1 << TARGET_W) - 1), tag=(word >> 115) & 0xF)


class RapidsCxsTileTB(RapidsCxsTopTB):
    """rapids_cxs_top with TILE_HDR = 1."""

    # ---- descriptors carrying the tile fields ---------------------------
    def create_tile_descriptor(self, src_addr: int, nbytes: int, dst_coord: int, target: int,
                               ptype: int = PTYPE_MEM, op: int = 0, channel_id: int = 0,
                               next_ptr: int = 0, last: bool = True) -> int:
        """A SOURCE descriptor: dst_addr = {coordinate, target address},
        ptype at [215:213], op at [216] (RAPIDS HAS, Descriptor Format)."""
        dst_addr = ((dst_coord & ((1 << COORD_W) - 1)) << TARGET_W) | (target & ((1 << TARGET_W) - 1))
        desc = self.create_descriptor(src_addr, dst_addr, 0, channel_id=channel_id,
                                      length_bytes=nbytes, last=last)
        desc |= (next_ptr & 0xFFFF_FFFF) << 160
        desc |= (ptype & 7) << 213
        desc |= (op & 1) << 216
        return desc

    # ---- the source port, read as packets -------------------------------
    def egress_packets(self, channel: int) -> List[List[Tuple[int, int]]]:
        """The channel's egress as packets of (data, strb) beats, split at TLAST."""
        pkts, cur = [], []
        for data, strb, last in self.captured_axis_beats.get(channel, []):
            cur.append((data, strb))
            if last:
                pkts.append(cur)
                cur = []
        if cur:
            pkts.append(cur)
        return pkts

    async def wait_egress_packets(self, channel: int, n: int, timeout_cycles: int = 20000) -> bool:
        for _ in range(timeout_cycles):
            if len([p for p in self.egress_packets(channel)]) >= n and \
                    self.captured_axis_beats.get(channel, [(0, 0, 1)])[-1][2]:
                return True
            await self.wait_clocks(self.clk_name, 1)
        return False

    def check_packet(self, pkt: List[Tuple[int, int]], want_hdr: TileHeader,
                     payload: List[int], what: str) -> List[str]:
        errs = []
        if not pkt:
            return [f"{what}: no packet"]
        hdr_word, hdr_strb = pkt[0]
        got = TileHeader.unpack(hdr_word)
        if got != want_hdr:
            errs.append(f"{what}: header {got} != expected {want_hdr}")
        if hdr_word >> 119:
            errs.append(f"{what}: header beat has data above bit 118: 0x{hdr_word >> 119:X}")
        if hdr_strb != (1 << HDR_BYTES) - 1:
            errs.append(f"{what}: header strobe 0x{hdr_strb:X}, expected 0x{(1 << HDR_BYTES) - 1:X}")
        data = [d for d, _s in pkt[1:]]
        if data != payload:
            errs.append(f"{what}: payload {len(data)} beats, expected {len(payload)}; "
                        f"{sum(1 for a, b in zip(data, payload) if a != b)} mismatches")
        return errs

    # ---- the sink port: what a cell sends -------------------------------
    async def cell_send(self, stream: int, hdr: TileHeader, payload: List[int] = (),
                        payload_strbs: List[int] = None):
        """One packet into the sink port on CXS stream (TID) `stream`: header
        beat, then the payload beats."""
        bpb = self.STRB_WIDTH
        beats = [hdr.pack()] + list(payload)
        strbs = [(1 << HDR_BYTES) - 1] + (list(payload_strbs) if payload_strbs
                                          else [(1 << bpb) - 1] * len(payload))
        await self._drive_axis_packet(stream, beats, strbs)

    async def cell_send_descriptor(self, src_channel: int, desc: int, stream: int = None):
        """A cell-issued descriptor (TILE_SPEC 11.11): a desc packet to RAPIDS
        (level 3), tag = the source channel, one 256-bit descriptor payload."""
        hdr = TileHeader(dst=RAPIDS_COORD, src=coord(0, 1, 1, 0), ptype=PTYPE_DESC, op=0,
                         length=32, target=0, tag=src_channel)
        await self.cell_send(src_channel if stream is None else stream, hdr, [desc],
                             payload_strbs=[(1 << 32) - 1])

    def tile_status(self) -> Dict[str, int]:
        d = self.dut
        return {n: int(getattr(d, f'sts_tile_{n}').value)
                for n in ('unsupported', 'tag_mismatch', 'desc_count', 'credit_count')}

    def _status_errors(self, want_desc: int = None, want_credit: int = 0,
                       want_unsupported: int = 0) -> List[str]:
        st = self.tile_status()
        errs = []
        if st['unsupported'] != want_unsupported:
            errs.append(f"sts_tile_unsupported={st['unsupported']}, expected {want_unsupported}")
        if st['tag_mismatch']:
            errs.append("sts_tile_tag_mismatch set")
        if want_desc is not None and st['desc_count'] != want_desc:
            errs.append(f"sts_tile_desc_count={st['desc_count']}, expected {want_desc}")
        if st['credit_count'] != want_credit:
            errs.append(f"sts_tile_credit_count={st['credit_count']}, expected {want_credit}")
        return errs

    async def check_w1c(self, half: str, reg: str, bit: int, port: str, port_bit: int = 0) -> List[str]:
        """A tile status CSR bit reads 1, a write of 1 clears it in the CSR
        AND in the RTL sticky it mirrors (the top-level port drops too), and
        it stays clear afterwards."""
        errs = []
        v = await self.read_reg(half, reg)
        if not (v >> bit) & 1:
            errs.append(f"{half}.{reg} = 0x{v:X}: bit {bit} not set")
        await self.write_reg(half, reg, 1 << bit)
        await self.wait_clocks(self.clk_name, 10)
        v = await self.read_reg(half, reg)
        if (v >> bit) & 1:
            errs.append(f"{half}.{reg} = 0x{v:X}: bit {bit} still set after a write-1 clear")
        p = int(getattr(self.dut, port).value)
        if (p >> port_bit) & 1:
            errs.append(f"{port} still set after {half}.{reg} was cleared (the RTL sticky did not clear)")
        return errs

    def _finish(self, errors: List[str], what: str) -> Tuple[bool, Dict[str, Any]]:
        errors = list(self.test_errors) + errors + self.cxs_link_errors()
        for e in errors:
            self.log.error(f"  SCOREBOARD: {e}")
        if not errors:
            self.log.info(f"  SCOREBOARD: {what} verified")
        return not errors, {'errors': errors}

    def _pattern(self, tag: int, channel: int, beats: int) -> List[int]:
        return [((tag << 56) | (channel << 40) | i) for i in range(beats)]

    # =====================================================================
    # Scenarios
    # =====================================================================
    async def test_source_write(self, channel=0, beats=4) -> Tuple[bool, Dict[str, Any]]:
        """A source descriptor's ptype / op / coordinate / target become the
        header of its packet, ahead of the payload."""
        self.log.info(f"=== TILE source write: ch{channel}, {beats} beats ===")
        desc_addr = self.DESC_BASE + channel * 0x1000
        src_addr = self.SRC_BASE + channel * self.CHANNEL_OFFSET
        pattern = self._pattern(0x71, channel, beats)
        self.preload_source(src_addr, pattern)
        dst, target = coord(0, 2, 3, 0), 0x2_0040
        nbytes = beats * self.STRB_WIDTH
        self.register_descriptor(self.desc_src_mem, desc_addr, self.create_tile_descriptor(
            src_addr, nbytes, dst, target, ptype=PTYPE_MEM, channel_id=channel))
        await self.kick_off_channel('src', channel, desc_addr)
        errors = []
        if not await self.wait_half_idle('src'):
            errors.append('src half did not return to idle')
        if not await self.wait_egress_packets(channel, 1):
            errors.append('no packet on the source port')
        await self.wait_clocks(self.clk_name, 100)
        pkts = self.egress_packets(channel)
        if len(pkts) != 1:
            errors.append(f"{len(pkts)} packets on ch{channel}, expected 1")
        if pkts:
            errors += self.check_packet(pkts[0], TileHeader(dst, RAPIDS_COORD, PTYPE_MEM, 0, nbytes,
                                                            target, channel), pattern, "source write")
        if self.read_sched_error('src') not in (0, -1):
            errors.append(f"src_sched_error=0x{self.read_sched_error('src'):X}")
        return self._finish(errors, "tile source write")

    async def test_source_read(self, channel=3, nbytes=200) -> Tuple[bool, Dict[str, Any]]:
        """op = 1 (read request): the packet is the header alone, carrying the
        requested length, and no source memory is read."""
        self.log.info(f"=== TILE source read request: ch{channel}, {nbytes} bytes ===")
        ar_seen = []
        self.rd_slave['AR'].add_callback(lambda t: ar_seen.append(t))
        desc_addr = self.DESC_BASE + channel * 0x1000
        dst, target = coord(0, 1, 0, 0), 0x400
        self.register_descriptor(self.desc_src_mem, desc_addr, self.create_tile_descriptor(
            self.SRC_BASE, nbytes, dst, target, ptype=PTYPE_MEM, op=1, channel_id=channel))
        await self.kick_off_channel('src', channel, desc_addr)
        errors = []
        if not await self.wait_half_idle('src'):
            errors.append('src half did not return to idle')
        if not await self.wait_egress_packets(channel, 1):
            errors.append('no packet on the source port')
        await self.wait_clocks(self.clk_name, 100)
        pkts = self.egress_packets(channel)
        if len(pkts) != 1:
            errors.append(f"{len(pkts)} packets, expected 1")
        if pkts:
            errors += self.check_packet(pkts[0], TileHeader(dst, RAPIDS_COORD, PTYPE_MEM, 1, nbytes,
                                                            target, channel), [], "read request")
        if ar_seen:
            errors.append(f"read request issued {len(ar_seen)} source-memory reads, expected 0")
        if self.read_sched_error('src') not in (0, -1):
            errors.append(f"src_sched_error=0x{self.read_sched_error('src'):X}")
        return self._finish(errors, "tile read request")

    async def test_sink_write(self, channel=2, beats=4, want_desc=0, want_credit=0,
                              want_unsupported=0) -> Tuple[bool, Dict[str, Any]]:
        """A cell's mem write into a sink channel: the header is stripped, the
        payload lands at the sink descriptor's address. The want_* are the
        tile status counters expected afterwards (a scenario that ran first
        leaves its own)."""
        self.log.info(f"=== TILE sink write: ch{channel}, {beats} beats ===")
        desc_addr = self.DESC_BASE + channel * 0x1000
        dst_addr = self.DST_BASE + channel * self.CHANNEL_OFFSET
        pattern = self._pattern(0x5C, channel, beats)
        nbytes = beats * self.STRB_WIDTH
        self.register_descriptor(self.desc_snk_mem, desc_addr,
                                 self.create_descriptor(0, dst_addr, beats, channel_id=channel))
        await self.kick_off_channel('snk', channel, desc_addr)
        await self.cell_send(channel, TileHeader(RAPIDS_COORD, coord(0, 0, 1, 0), PTYPE_MEM, 0,
                                                 nbytes, 0, channel), pattern)
        errors = []
        if not await self.wait_half_idle('snk', start_cycles=50):
            errors.append('snk half did not return to idle')
        await self.wait_clocks(self.clk_name, 200)
        got = self.read_sink(dst_addr, beats)
        if got != pattern:
            errors.append(f"sink ch{channel}: {sum(1 for a, b in zip(got, pattern) if a != b)}/{beats} "
                          f"beats mismatch")
        if self.read_sched_error('snk') not in (0, -1):
            errors.append(f"snk_sched_error=0x{self.read_sched_error('snk'):X}")
        errors += self._status_errors(want_desc=want_desc, want_credit=want_credit,
                                      want_unsupported=want_unsupported)
        return self._finish(errors, "tile sink write")

    async def test_cell_descriptors(self, beats=4, base_channel=0) -> Tuple[bool, Dict[str, Any]]:
        """Cell-issued descriptors (TILE_SPEC 11.11) on several source channels:
          b+0, b+1  idle channels, injected together
          b+2       busy: a host-kicked descriptor runs first, the injected one after it
          b+3       the injected descriptor chains on into a memory-resident one
        (b = base_channel). Each packet must reach the coordinate its
        descriptor names, in order."""
        c0, c1, c2, c3 = (base_channel + i for i in range(4))
        self.log.info("=== TILE cell-issued descriptors ===")
        bpb = self.STRB_WIDTH
        nbytes = beats * bpb
        expect: Dict[int, List[Tuple[TileHeader, List[int]]]] = {}

        def src(ch, k):
            return self.SRC_BASE + ch * self.CHANNEL_OFFSET + k * 0x1_0000

        def inj(ch, k, dst, target, next_ptr=0, last=True):
            pat = self._pattern(0x40 + k, ch, beats)
            self.preload_source(src(ch, k), pat)
            expect.setdefault(ch, []).append((TileHeader(dst, RAPIDS_COORD, PTYPE_MEM, 0, nbytes,
                                                         target, ch), pat))
            return self.create_tile_descriptor(src(ch, k), nbytes, dst, target, channel_id=ch,
                                               next_ptr=next_ptr, last=last)

        # ch2 busy: a long host-kicked transfer first
        host_beats = 8 * beats
        host_pat = self._pattern(0x99, c2, host_beats)
        self.preload_source(src(c2, 9), host_pat)
        host_dst = coord(0, 3, 3, 0)
        expect[c2] = [(TileHeader(host_dst, RAPIDS_COORD, PTYPE_MEM, 0, host_beats * bpb, 0x10, c2),
                       host_pat)]
        self.register_descriptor(self.desc_src_mem, self.DESC_BASE + c2 * 0x1000,
                                 self.create_tile_descriptor(src(c2, 9), host_beats * bpb, host_dst,
                                                             0x10, channel_id=c2))
        await self.kick_off_channel('src', c2, self.DESC_BASE + c2 * 0x1000)
        await self.wait_clocks(self.clk_name, 30)

        # ch3 chain target: a memory-resident descriptor the injected one points at
        chain_addr = self.DESC_BASE + c3 * 0x1000
        d_ch3a = inj(c3, 0, coord(0, 0, 2, 0), 0x80, next_ptr=chain_addr, last=False)
        d_ch3b = inj(c3, 1, coord(0, 1, 2, 0), 0x90)
        self.register_descriptor(self.desc_src_mem, chain_addr, d_ch3b)

        for d_ch, d in ((c0, inj(c0, 0, coord(0, 1, 1, 0), 0x100)),
                        (c1, inj(c1, 0, coord(0, 2, 1, 0), 0x200)),
                        (c2, inj(c2, 0, coord(0, 3, 1, 0), 0x300)),
                        (c3, d_ch3a)):
            await self.cell_send_descriptor(d_ch, d)

        errors = []
        for ch, pkts_want in sorted(expect.items()):
            if not await self.wait_egress_packets(ch, len(pkts_want), timeout_cycles=40000):
                errors.append(f"ch{ch}: {len(self.egress_packets(ch))} of {len(pkts_want)} packets")
        await self.wait_clocks(self.clk_name, 300)
        for ch, pkts_want in sorted(expect.items()):
            got = self.egress_packets(ch)
            if len(got) != len(pkts_want):
                errors.append(f"ch{ch}: {len(got)} packets, expected {len(pkts_want)}")
            for k, ((hdr, pat), pkt) in enumerate(zip(pkts_want, got)):
                errors += self.check_packet(pkt, hdr, pat, f"ch{ch} packet {k}")
        if self.read_sched_error('src') not in (0, -1):
            errors.append(f"src_sched_error=0x{self.read_sched_error('src'):X}")
        errors += self._status_errors(want_desc=4)
        return self._finish(errors, "cell-issued descriptors")

    async def test_cell_descriptor_overflow(self, channel=5) -> Tuple[bool, Dict[str, Any]]:
        """A desc packet with no free slot is dropped: the channel's sticky
        sts_tile_desc_dropped bit is set, and nothing else changes. The channel
        is kept busy by a long host-kicked transfer, so its scheduler takes
        nothing from its queue (8) and slot (1) while the cell sends 10
        descriptors: the 10th has no slot. The running transfer, and the nine
        that were taken, must all complete; no channel is errored; the sink
        port keeps taking packets."""
        self.log.info(f"=== TILE cell descriptor overflow: ch{channel} ===")
        bpb = self.STRB_WIDTH
        host_beats = 256
        src = self.SRC_BASE + channel * self.CHANNEL_OFFSET
        host_pat = self._pattern(0x33, channel, host_beats)
        self.preload_source(src, host_pat)
        host_dst = coord(0, 0, 0, 1)
        desc_addr = self.DESC_BASE + channel * 0x1000
        self.register_descriptor(self.desc_src_mem, desc_addr, self.create_tile_descriptor(
            src, host_beats * bpb, host_dst, 0, channel_id=channel))
        await self.kick_off_channel('src', channel, desc_addr)
        busy = False
        for _ in range(500):                         # wait until the scheduler is running it
            await self.wait_clocks(self.clk_name, 1)
            if self.captured_axis_beats.get(channel):
                busy = True
                break
        inj_src = src + 0x8_0000
        inj_pat = self._pattern(0x34, channel, 1)
        self.preload_source(inj_src, inj_pat)
        inj_dst = coord(0, 2, 2, 0)
        d = self.create_tile_descriptor(inj_src, bpb, inj_dst, 0x20, channel_id=channel)
        n = 8 + 1 + 1                      # queue + slot + the one with no slot
        for _ in range(n):
            await self.cell_send_descriptor(channel, d)
        await self.wait_clocks(self.clk_name, 50)
        errors = [] if busy else [f"ch{channel} never started its host transfer"]
        dropped = int(self.dut.sts_tile_desc_dropped.value)
        if dropped != (1 << channel):
            errors.append(f"sts_tile_desc_dropped=0x{dropped:X}, expected 0x{1 << channel:X}")
        want = 1 + (n - 1)                 # the host packet, then the nine taken
        if not await self.wait_egress_packets(channel, want, timeout_cycles=40000):
            errors.append(f"ch{channel}: {len(self.egress_packets(channel))} of {want} packets")
        await self.wait_clocks(self.clk_name, 200)
        pkts = self.egress_packets(channel)
        if len(pkts) != want:
            errors.append(f"ch{channel}: {len(pkts)} packets, expected {want}")
        if pkts:
            errors += self.check_packet(pkts[0], TileHeader(host_dst, RAPIDS_COORD, PTYPE_MEM, 0,
                                                            host_beats * bpb, 0, channel),
                                        host_pat, "running transfer")
        for k, pkt in enumerate(pkts[1:want]):
            errors += self.check_packet(pkt, TileHeader(inj_dst, RAPIDS_COORD, PTYPE_MEM, 0, bpb,
                                                        0x20, channel), inj_pat, f"taken desc {k}")
        se = self.read_sched_error('src')
        if se not in (0, -1):
            errors.append(f"src_sched_error=0x{se:X}: a dropped descriptor must not error a channel")
        errors += self._status_errors(want_desc=n)
        counts = await self.read_reg('snk', 'TILE_COUNTS')
        if counts & 0xFFFF != n:
            errors.append(f"SNK.TILE_COUNTS.DESC_COUNT = {counts & 0xFFFF}, expected {n}")
        errors += await self.check_w1c('src', 'TILE_DESC_DROPPED', channel, 'sts_tile_desc_dropped', channel)
        # The link is still live: a sink write on another channel completes
        ok, st = await self.test_sink_write(channel=1, beats=2, want_desc=n)
        errors += [] if ok else [f"after overflow: {e}" for e in st['errors']]
        return self._finish(errors, "descriptor overflow")

    async def test_source_bad_ptype(self, channel=6) -> Tuple[bool, Dict[str, Any]]:
        """A source descriptor may carry cfg / prog / mem only. One with ptype
        credit is refused like an invalid descriptor: the channel errors and
        sends nothing, and the other channels are untouched."""
        self.log.info(f"=== TILE source descriptor with ptype credit: ch{channel} ===")
        desc_addr = self.DESC_BASE + channel * 0x1000
        src = self.SRC_BASE + channel * self.CHANNEL_OFFSET
        self.preload_source(src, self._pattern(0x66, channel, 2))
        self.register_descriptor(self.desc_src_mem, desc_addr, self.create_tile_descriptor(
            src, 2 * self.STRB_WIDTH, coord(0, 1, 0, 0), 0, ptype=PTYPE_CREDIT, channel_id=channel))
        await self.kick_off_channel('src', channel, desc_addr)
        await self.wait_clocks(self.clk_name, 500)
        errors = []
        se = self.read_sched_error('src')
        if se != (1 << channel):
            errors.append(f"src_sched_error=0x{se:X}, expected 0x{1 << channel:X}")
        if self.egress_packets(channel):
            errors.append(f"ch{channel} sent {len(self.egress_packets(channel))} packets for a refused descriptor")
        return self._finish(errors, "source ptype refusal")

    async def test_unsupported(self, channel=4) -> Tuple[bool, Dict[str, Any]]:
        """The sink port never stalls on what it cannot act on: a credit packet
        is consumed and counted; a read request addressed to RAPIDS is consumed
        and sets the sticky flag. A data write on the same stream still lands."""
        self.log.info(f"=== TILE credit / unsupported packets on stream {channel} ===")
        await self.cell_send(channel, TileHeader(RAPIDS_COORD, coord(0, 1, 1, 0), PTYPE_CREDIT, 0,
                                                 16, 0, channel))
        await self.wait_clocks(self.clk_name, 20)
        errors = self._status_errors(want_desc=0, want_credit=1)
        await self.cell_send(channel, TileHeader(RAPIDS_COORD, coord(0, 1, 1, 0), PTYPE_MEM, 1,
                                                 64, 0x40, channel))
        await self.wait_clocks(self.clk_name, 20)
        if not self.tile_status()['unsupported']:
            errors.append("a read request to RAPIDS did not set sts_tile_unsupported")
        ok, st = await self.test_sink_write(channel=channel, beats=2, want_credit=1,
                                            want_unsupported=1)
        errors += [] if ok else [f"after unsupported: {e}" for e in st['errors']]
        # The same status through the CSRs, and the write-1 clear
        counts = await self.read_reg('snk', 'TILE_COUNTS')
        if (counts >> 16) & 0xFFFF != 1:
            errors.append(f"SNK.TILE_COUNTS.CREDIT_COUNT = {(counts >> 16) & 0xFFFF}, expected 1")
        errors += await self.check_w1c('snk', 'TILE_STATUS', 0, 'sts_tile_unsupported')
        return self._finish(errors, "credit / unsupported")
