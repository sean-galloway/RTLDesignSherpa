# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: rapids_cxs_top_tb
# Purpose: Testbenches for rapids_cxs_top / rapids_beats_cxs_top: the AXIS top
#          testbenches with the network BFMs swapped for CXS
#
# Documentation: projects/components/dma-ip/rapids/docs/rapids_planes.md
# Subsystem: rapids
# Author: sean galloway
# Created: 2026-10-15
"""RAPIDS with the CXS network planes.

Everything RAPIDS-specific -- APB configuration, descriptors, memory models,
the scoreboards of every scenario -- is the AXIS top testbench, unchanged.
Only the network BFMs differ (the `_create_network_bfms` hook):

  sink ingress   CXSTransmitter on s_cxs_* (the plane is a CXS receiver)
  source egress  CXSReceiver    on m_cxs_* (the plane is a CXS transmitter)
  both links     CXSMonitor     -- credit model, link handshake, placement

The AXIS beats a scenario sends become CXS flits by the planes' own mapping
(projects/components/utility-ip/converters/rtl/axis_to_cxs.sv): one packet per TLAST run, START at pointer 0 on
the first beat, END on the last with END0PTR = the last strobed 4-byte word,
TID -> CXSSRCID, TDEST -> CXSTGTID, {TUSER, TSTRB} -> CXSUSER. Received flits
are turned back into (data, strb, last) beats and filed under CXSSRCID, so the
AXIS scenarios' egress scoreboards judge them as they would an AXIS beat.
"""

import os

from CocoTBFramework.components.cxs import (CXSCntl, CXSConfig, CXSFlit, create_cxs_monitor,
                                            create_cxs_receiver, create_cxs_transmitter)
from CocoTBFramework.components.shared.flex_randomizer import FlexRandomizer
from cocotb.triggers import RisingEdge
from TBClasses.monbus import parse_stream
from TBClasses.monbus.monbus_types import CXSErrorCode, PktType, ProtocolType

CXS_ERR_EVENT_DROPPED = int(CXSErrorCode.CXS_ERR_EVENT_DROPPED)

from projects.components.dma_ip.rapids.dv.tbclasses.rapids_beats_top_tb import RapidsBeatsTopTB
from projects.components.dma_ip.rapids.dv.tbclasses.rapids_top_tb import RapidsTopTB

AXIS_ID_WIDTH, AXIS_DEST_WIDTH, AXIS_USER_WIDTH = 8, 4, 1


class _CXSNetworkMixin:
    """Replaces the AXIS network BFMs with CXS ones; everything else inherited."""

    def cxs_config(self):
        sw = self.DATA_WIDTH // 8
        carry_tuser = sw + AXIS_USER_WIDTH <= 128
        # The tops default CXS_MAX_CREDIT to SRAM_DEPTH (one channel's SRAM);
        # past the spec's 63 the link is built beyond spec at both ends.
        credits = int(os.environ.get('TEST_CXS_MAX_CREDIT', '512'))   # the runner sets it from SRAM_DEPTH
        return CXSConfig(issue='D', data_width=self.DATA_WIDTH, max_pkt_per_flit=2, start_align=16,
                         srcid_width=AXIS_ID_WIDTH, tgtid_width=AXIS_DEST_WIDTH,
                         user_width=sw + (AXIS_USER_WIDTH if carry_tuser else 0),
                         max_credit=credits, credit_beyond_spec=credits > 63,
                         link_control=True, check=False).validate()

    def _idle_network_inputs(self):
        d = self.dut
        d.s_cxs_valid.value = 0
        d.s_cxs_crdrtn.value = 0
        d.s_cxs_activereq.value = 0
        d.m_cxs_crdgnt.value = 0
        d.m_cxs_activeack.value = 0
        d.m_cxs_deacthint.value = 0

    def _create_network_bfms(self):
        d = self.dut
        self.cxs_cfg = cfg = self.cxs_config()
        self._egress_srcids = []
        # The beats testbench files egress by data only; the CXS egress also
        # keeps (data, strb, last) for both trees (TLAST-run counting).
        if not hasattr(self, 'captured_axis_beats'):
            self.captured_axis_beats = {ch: [] for ch in range(self.NUM_CHANNELS)}
        self.cxs_tx = create_cxs_transmitter(
            d, 'CXS TX (sink ingress)', 's_cxs_', self.clk, cfg, reset=self.rst_n, log=self.log,
            randomizer=FlexRandomizer({'valid_gap': ([(0, 0)], [1])}), idle_deactivate=64)
        self.cxs_rx = create_cxs_receiver(
            d, 'CXS RX (source egress)', 'm_cxs_', self.clk, cfg, reset=self.rst_n, log=self.log,
            randomizer=FlexRandomizer({'grant_gap': ([(0, 0)], [1]), 'drain_gap': ([(0, 0)], [1]),
                                       'ack_delay': ([(0, 2)], [1])}))
        self.cxs_rx.add_callback(self._on_cxs_egress)
        self.cxs_mon_in = create_cxs_monitor(d, 'CXS Mon (ingress)', 's_cxs_', self.clk, cfg,
                                             reset=self.rst_n, log=self.log)
        self.cxs_mon_out = create_cxs_monitor(d, 'CXS Mon (egress)', 'm_cxs_', self.clk, cfg,
                                              reset=self.rst_n, log=self.log)
        # The base's AXIS objects do not exist on a CXS top
        self.axis_master = self.cxs_tx
        self.axis_slave = None

    # ---- AXIS beats <-> CXS flits (the planes' mapping) ----------------
    def beats_to_flits(self, channel, beats, strbs):
        cfg = self.cxs_cfg
        sw = self.DATA_WIDTH // 8
        full = (1 << sw) - 1
        n = len(beats)
        flits = []
        for i, data in enumerate(beats):
            strb = strbs[i] if strbs else full
            last = i == n - 1
            words = [k for k in range(self.DATA_WIDTH // 32) if (strb >> (4 * k)) & 0xF]
            cntl = CXSCntl(starts=(0,) if i == 0 else (),
                           ends=((words[-1] if words else 0),) if last else ()).encode(cfg)
            flits.append(CXSFlit(cfg, data=data, cntl=cntl, srcid=channel, tgtid=0, user=strb))
        return flits

    async def _drive_axis_packet(self, channel, beats, strbs):
        """Send the packet as CXS flits; return once the transmitter has sent
        all of them (the sink holds its FIFO -- and so its credits -- until the
        channel's descriptor is fetched, exactly as the AXIS plane holds tready)."""
        flits = self.beats_to_flits(channel, list(beats), strbs)
        target = self.cxs_tx.stats['flits'] + len(flits)
        for f in flits:
            self.cxs_tx.send_flit(f)
        while self.cxs_tx.stats['flits'] < target:
            await RisingEdge(self.clk)

    def _on_cxs_egress(self, flit):
        sw = self.DATA_WIDTH // 8
        strb = flit.get('user') & ((1 << sw) - 1)
        last = int(len(flit.control.ends) > 0)
        tid = flit.get('srcid') & (self.NUM_CHANNELS - 1)
        data = flit.get('data')
        ctl = flit.control
        self._egress_srcids.append((tid, bool(ctl.starts), bool(ctl.ends)))
        self.captured_axis.setdefault(tid, []).append(data)
        self.captured_axis_beats.setdefault(tid, []).append((data, strb, last))

    async def kick_channels_together(self, half, channels):
        """Stage every channel's descriptor address, then launch them all in
        ONE KICK_ENABLE write (a singlepulse per bit), so their transfers
        overlap instead of each finishing before the next kick lands."""
        for ch in channels:
            a = self.DESC_BASE + ch * 0x1000
            await self.write_reg(half, f'CH{ch}_DESC_ADDR_LOW', a & 0xFFFF_FFFF)
            await self.write_reg(half, f'CH{ch}_DESC_ADDR_HIGH', (a >> 32) & 0xFFFF_FFFF)
        await self.write_fields(half, 'KICK_ENABLE', **{f'KICK{ch}': 1 for ch in channels})
        for ch in channels:
            self.kicked_desc_addrs[half].setdefault(ch, []).append(self.DESC_BASE + ch * 0x1000)
        self.log.info(f"Staged + kicked {half} ch{list(channels)} in one write")

    # ---- concurrent channels: streams interleaved on the one link -------
    async def test_source_concurrent(self, channels=(0, 1, 2, 3), beats=64):
        """Several source channels at once. The egress arbitrates per drain
        block, so channel packets interleave mid-packet on the single CXS
        link and only per-stream framing keeps that legal (IHI 0079D 2.5.2).
        Requires the interleave to have actually happened: a run where every
        packet went out whole would pass without testing anything."""
        self.log.info(f"=== SOURCE concurrent: ch{list(channels)}, {beats} beats each ===")
        self._egress_srcids = []
        patterns = {}
        for ch in channels:
            desc_addr = self.DESC_BASE + ch * 0x1000
            src_addr = self.SRC_BASE + ch * self.CHANNEL_OFFSET
            patterns[ch] = [(0x6000_0000_0000_0000 + (ch << 40) + i) for i in range(beats)]
            self.preload_source(src_addr, patterns[ch])
            self.register_descriptor(self.desc_src_mem, desc_addr,
                                     self.create_descriptor(src_addr, 0, beats, channel_id=ch))
        await self.kick_channels_together('src', channels)
        errors = []
        if not await self.wait_half_idle('src', timeout_cycles=50000):
            errors.append('src half did not return to idle')
        for _ in range(20000):
            await self.wait_clocks(self.clk_name, 1)
            if all(len(self.captured_axis.get(ch, [])) >= beats for ch in channels):
                break
        await self.wait_clocks(self.clk_name, 200)
        for ch in channels:
            got = self.captured_axis.get(ch, [])
            if got != patterns[ch]:
                errors.append(f"source ch{ch}: captured {len(got)}/{beats} beats, "
                              f"{sum(1 for a, b in zip(got, patterns[ch]) if a != b)} mismatches")
        switches = self._mid_packet_switches()
        multi = any(not end for _s, _st, end in self._egress_srcids)   # some packet spans flits
        self.log.info(f"  egress: {len(self._egress_srcids)} flits, {switches} mid-packet stream "
                      f"switches, multi-flit packets: {multi}")
        # The beats tree frames one packet per drain block (one flit at drain
        # size 1), so its packets cannot interleave; the byte tree's must.
        if multi and switches == 0:
            errors.append("no channel switched mid-packet on the link: the interleave was not exercised")
        errors += self.cxs_link_errors()
        for e in errors:
            self.log.error(f"  SCOREBOARD: {e}")
        return not errors, {'errors': errors, 'switches': switches}

    async def test_sink_concurrent(self, channels=(0, 1, 2, 3), beats=64):
        """Several sink channels at once: their flits interleave beat by beat
        on the single CXS link, one packet open per stream."""
        self.log.info(f"=== SINK concurrent: ch{list(channels)}, {beats} beats each ===")
        patterns, per_ch = {}, {}
        for ch in channels:
            desc_addr = self.DESC_BASE + ch * 0x1000
            dst_addr = self.DST_BASE + ch * self.CHANNEL_OFFSET
            patterns[ch] = [(0xB000_0000_0000_0000 + (ch << 40) + i) for i in range(beats)]
            self.register_descriptor(self.desc_snk_mem, desc_addr,
                                     self.create_descriptor(0, dst_addr, beats, channel_id=ch))
            per_ch[ch] = self.beats_to_flits(ch, patterns[ch], None)
        await self.kick_channels_together('snk', channels)
        order = [per_ch[ch][i] for i in range(beats) for ch in channels]
        target = self.cxs_tx.stats['flits'] + len(order)
        for f in order:
            self.cxs_tx.send_flit(f)
        errors = []
        for _ in range(50000):
            await self.wait_clocks(self.clk_name, 1)
            if self.cxs_tx.stats['flits'] >= target:
                break
        else:
            errors.append(f"transmitter sent {self.cxs_tx.stats['flits']} of {target} flits")
        if not await self.wait_half_idle('snk', timeout_cycles=50000):
            errors.append('snk half did not return to idle')
        await self.wait_clocks(self.clk_name, 200)
        for ch in channels:
            got = self.read_sink(self.DST_BASE + ch * self.CHANNEL_OFFSET, beats)
            if got != patterns[ch]:
                errors.append(f"sink ch{ch}: {sum(1 for a, b in zip(got, patterns[ch]) if a != b)}"
                              f"/{beats} beats mismatch")
        se = self.read_sched_error('snk')
        if se not in (0, -1):
            errors.append(f"snk_sched_error=0x{se:X}")
        errors += self.cxs_link_errors()
        for e in errors:
            self.log.error(f"  SCOREBOARD: {e}")
        return not errors, {'errors': errors}

    def _mid_packet_switches(self):
        """Flits whose stream differs from the previous flit's while that
        previous stream still had a packet open."""
        open_s, prev, n = set(), None, 0
        for srcid, start, end in self._egress_srcids:
            if prev is not None and srcid != prev and prev in open_s:
                n += 1
            if start:
                open_s.add(srcid)
            if end:
                open_s.discard(srcid)
            prev = srcid
        return n

    # ---- the CXS monitor-lites through the monbus group ----------------
    async def test_cxs_monitors(self, beats=4):
        """The CXS counterpart of test_axis_monitors: program both planes'
        monitors (the same SRC.RDMON_* / SNK.WRMON_* CSRs the AXIS plane
        uses) for completions, move one packet each way, and require one
        PROTOCOL_CXS Completion/PACKET_END per CXS packet, on the right
        channel, from the right agent, in the capture master's trace."""
        self.log.info(f"=== CXS monitor-lites: {beats} beats each way ===")
        for half, reg in (('src', 'RDMON'), ('snk', 'WRMON')):
            await self.write_fields(half, f'{reg}_ENABLE', MON_EN=1, ERR_EN=1, COMPL_EN=1)
            await self.write_fields(half, f'{reg}_PKT_MASK', PKT_MASK=0)
        n0 = len(self.mon_w_beats)
        src_ch, snk_ch = 1, 2
        ok_src, st_src = await self.test_source_path(channel=src_ch, beats=beats)
        ok_snk, st_snk = await self.test_sink_path(channel=snk_ch, beats=beats)
        errors = list(st_src['errors']) + list(st_snk['errors'])

        # One CXS packet per AXIS TLAST run (axis_to_cxs): the source count is
        # what the egress actually framed -- one per descriptor on the byte
        # tree, drain-size packets on the beats tree.
        n_src = sum(1 for _d, _s, last in self.captured_axis_beats.get(src_ch, []) if last)
        want = {self.SRC_AXIS_MON_AGENT_ID: (src_ch, 'source-egress', n_src),
                self.SNK_AXIS_MON_AGENT_ID: (snk_ch, 'sink-ingress', 1)}

        def _records():
            ws = self.mon_w_beats[n0:]
            ws = ws[:len(ws) - len(ws) % 3]
            return [r.packet for r in parse_stream(ws, stride_bytes=24, ts_mode=1)]

        def _compl(pkts, agent):
            return [p for p in pkts if p.agent_id == agent
                    and p.protocol == ProtocolType.PROTOCOL_CXS
                    and p.packet_type == PktType.PktTypeCompletion]

        # The capture master lags the traffic by thousands of cycles: wait for
        # the expected completions AND a quiet stream, under a cap.
        quiet, last = 0, len(self.mon_w_beats)
        for _ in range(400):
            await self.wait_clocks(self.clk_name, 50)
            cur = len(self.mon_w_beats)
            quiet, last = (quiet + 50 if cur == last else 0), cur
            pkts = _records()
            if quiet >= 200 and all(len(_compl(pkts, a)) >= n for a, (_c, _n, n) in want.items()):
                break
        pkts = _records()
        for agent, (ch, name, n) in want.items():
            compl = _compl(pkts, agent)
            # PACKET_END event_data = {PRCLTYPE, SRCID, TGTID, ends, pkts[31:0]}
            # (channel_id is {PRCLTYPE[2:0], TGTID[5:0]}); the RAPIDS channel
            # rides CXSSRCID (TID), so read it from event_data[55:48].
            chans = [(p.event_data >> 48) & 0xFF for p in compl]
            # The lite drops-and-counts when events outrun its 4-entry queue
            # (one-beat packets back to back on the beats tree): lost events
            # come back as Error/EVENT_DROPPED with the count in event_data.
            # The contract is delivered + reported-dropped == issued, with at
            # least one delivered.
            dropped = sum(p.event_data & 0xFFFF for p in pkts
                          if p.agent_id == agent and p.protocol == ProtocolType.PROTOCOL_CXS
                          and p.packet_type == PktType.PktTypeError
                          and p.event_code == CXS_ERR_EVENT_DROPPED)
            if not compl or len(compl) + dropped != n:
                errors.append(f"{name} CXS monitor (agent 0x{agent:02X}): {len(compl)} PACKET_END "
                              f"completions + {dropped} reported dropped, expected {n}")
            if any(c != ch for c in chans):
                errors.append(f"{name} CXS monitor: completion channels {chans}, expected all {ch}")
            self.log.info(f"  {name} agent 0x{agent:02X}: {len(compl)} CXS completion(s) on {chans}, "
                          f"{dropped} reported dropped")
        if not n_src:
            errors.append("source egress framed no packet (no TLAST beat captured)")
        errors += self.cxs_link_errors()
        for e in errors:
            self.log.error(f"  SCOREBOARD: {e}")
        return not errors, {'records': len(pkts), 'errors': errors}

    # ---- link-level verdict --------------------------------------------
    def cxs_link_errors(self):
        """Wire-level monitors clean, BFM credit checks clean, DUT link flags low."""
        errs = []
        for b in (self.cxs_tx, self.cxs_rx, self.cxs_mon_in, self.cxs_mon_out):
            if b.total_violations():
                errs.append(f"{b.title}: {b.violations}")
        d = self.dut
        for name in ('src_cxs_protocol_error', 'snk_cxs_protocol_error', 'snk_cxs_unsupported'):
            if int(getattr(d, name).value):
                errs.append(f"DUT {name} set")
        return errs


class RapidsCxsTopTB(_CXSNetworkMixin, RapidsTopTB):
    """rapids_cxs_top (byte-granular RAPIDS, CXS planes)."""


class RapidsBeatsCxsTopTB(_CXSNetworkMixin, RapidsBeatsTopTB):
    """rapids_beats_cxs_top (beat-granular RAPIDS, CXS planes)."""

    async def send_axis_packet(self, channel, beats):
        """The beats sink accepts as soon as it has SRAM space, so the AXIS
        testbench sends blocking; keep that contract with full strobes."""
        await self._drive_axis_packet(channel, beats, None)
