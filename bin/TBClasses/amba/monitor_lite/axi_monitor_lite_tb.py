# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""axi_monitor_lite through its wrapper (amba/monitor-lite TASK-001).

The DUT is axi4_slave_rd_monlite or axi4_slave_wr_monlite: an
AXI4 master BFM drives the s_axi side, a memory-backed AXI4 slave BFM answers
on the fub side, and a MonbusSlave collects every packet. Each phase asserts
exact packets -- type, event code, channel (the ID), event data (the address,
and for completions the latency in the top 16 bits) -- and exact counts, not
"some packets arrived".

Phases (every level; the counts scale): completions for singles and bursts,
a SLVERR read/write that yields one error and no completion, a stalled slave
that yields one timeout naming the phase, a pile of outstanding transactions
that trips the active-count threshold, and a held monbus that drops events
and then reports the count.
"""
import os
import cocotb
from cocotb.triggers import ClockCycles

from TBClasses.axi4.axi4_slave_read_tb import AXI4SlaveReadTB
from TBClasses.axi4.axi4_slave_write_tb import AXI4SlaveWriteTB
from TBClasses.monbus.monbus_slave import MonbusSlave
from TBClasses.monbus.monbus_types import PktType, AXIErrorCode, AXITimeoutCode, AXIThresholdCode, AXIAddrMatchCode
from TBClasses.monbus.monbus_validators import find_packets_by_criteria
from CocoTBFramework.components.shared.flex_randomizer import FlexRandomizer

# Packet vocabulary comes from the shared monbus types (mirrors monitor_pkg.sv);
# nothing is redefined here. Completion payload layout is the lite's, matching
# the full monitor's compl reporter: event_data[AW-1:0] = address,
# event_data[63:48] = latency in cycles (docs/markdown/rtl-amba/monitor/axi_monitor_lite.md).
PKT_ERROR   = PktType.PktTypeError
PKT_COMPL   = PktType.PktTypeCompletion
PKT_THRESH  = PktType.PktTypeThreshold
PKT_TIMEOUT = PktType.PktTypeTimeout
ERR_SLVERR        = AXIErrorCode.AXI_ERR_RESP_SLVERR
ERR_EVENT_DROPPED = AXIErrorCode.AXI_ERR_EVENT_DROPPED
TMO_DATA = AXITimeoutCode.AXI_TIMEOUT_DATA
TMO_RESP = AXITimeoutCode.AXI_TIMEOUT_RESP
THRESH_ACTIVE_COUNT = AXIThresholdCode.AXI_THRESH_ACTIVE_COUNT
THRESH_LATENCY = AXIThresholdCode.AXI_THRESH_LATENCY
PKT_ADDRMATCH = PktType.PktTypeAddrMatch
ERR_ADDR_RANGE = AXIErrorCode.AXI_ERR_ADDR_RANGE
CHAN_ID_BITS = 6      # channel_id = {3'b0, 6'(id)} in create_monitor_packet()


def compl_addr(p):
    """Address carried in a completion/error/timeout payload (low 32 bits)."""
    return p.data & 0xFFFF_FFFF


def compl_latency(p):
    """Latency in cycles carried in a completion payload (bits 63:48)."""
    return p.data >> 48

PROFILE = {
    'gate': dict(singles=4,  bursts=(2, 4),        pile=6,  held=8),
    'func': dict(singles=16, bursts=(2, 4, 8, 16), pile=6,  held=12),
    'full': dict(singles=48, bursts=(2, 4, 8, 16), pile=7,  held=24),
}


class AxiMonitorLiteTB:
    """Thin layer over the existing slave TBs: they own the BFMs and the memory."""

    OOR_ADDR = 0x0010_0000          # beyond the 256 KB memory model: SLVERR by contract

    def __init__(self, dut, is_write: bool):
        self.dut = dut
        self.is_write = is_write
        self.base = (AXI4SlaveWriteTB if is_write else AXI4SlaveReadTB)(dut, aclk=dut.aclk, aresetn=dut.aresetn)
        self.log = self.base.log
        self.level = os.environ.get('TEST_LEVEL', 'gate').lower()
        if self.level not in PROFILE:
            self.level = 'gate'
        self.cfg = PROFILE[self.level]
        self.max_trans = int(os.environ.get('MAX_TRANSACTIONS', '8'))
        self.id_width = self.base.TEST_ID_WIDTH
        self.errors = []
        self.mon = None

    # ---- mandatory ------------------------------------------------------

    async def setup_clocks_and_reset(self):
        await self.base.start_clock('aclk', self.base.TEST_CLK_PERIOD, 'ns')
        d = self.dut
        if hasattr(d, 'cfg_monitor_enable'): d.cfg_monitor_enable.value = 1
        if hasattr(d, 'cfg_error_enable'): d.cfg_error_enable.value = 1
        if hasattr(d, 'cfg_timeout_enable'): d.cfg_timeout_enable.value = 1
        if hasattr(d, 'cfg_perf_enable'): d.cfg_perf_enable.value = 0
        if hasattr(d, 'cfg_compl_enable'): d.cfg_compl_enable.value = 1
        if hasattr(d, 'cfg_threshold_enable'): d.cfg_threshold_enable.value = 1
        if hasattr(d, 'cfg_debug_enable'): d.cfg_debug_enable.value = 0
        if hasattr(d, 'cfg_timeout_cycles'): d.cfg_timeout_cycles.value = 0          # 0 = never (wrapper maps to 0xFFFF)
        if hasattr(d, 'cfg_latency_threshold'): d.cfg_latency_threshold.value = 0x0FFF_FFFF   # clocks: high -> latency threshold quiet
        if hasattr(d, 'cfg_freq_sel'): d.cfg_freq_sel.value = 0                # LUT entry 0 = the slowest clock = the shortest tick
        for name in ('cfg_axi_pkt_mask', 'cfg_axi_err_select', 'cfg_axi_error_mask', 'cfg_axi_timeout_mask',
                     'cfg_axi_compl_mask', 'cfg_axi_thresh_mask', 'cfg_axi_perf_mask', 'cfg_axi_addr_mask',
                     'cfg_axi_debug_mask'):
            if hasattr(d, name): getattr(d, name).value = 0
        for name in ('cfg_id_filter_enable', 'cfg_id_match_base', 'cfg_id_match_count', 'cfg_addr_filter_enable',
                     'cfg_addr_filter_low', 'cfg_addr_filter_high', 'cfg_addr_check_enable',
                     'cfg_addr_range_enable', 'cfg_addr_range_low', 'cfg_addr_range_high',
                     'cfg_start_event_sel', 'cfg_end_event_sel', 'cfg_start_trigger', 'cfg_end_trigger',
                     'cfg_window_force_close', 'i_mon_time'):
            if hasattr(d, name):
                getattr(d, name).value = 0
        await self.assert_reset()
        await self.base.wait_clocks('aclk', 10)
        await self.deassert_reset()
        await self.base.wait_clocks('aclk', 10)
        self.mon = MonbusSlave(dut=self.dut, title="MonBus", prefix="", clock=self.dut.aclk,
                               bus_name="monbus", pkt_prefix="", log=self.log)
        # Every phase but `drop` wants exact packet counts, so the consumer
        # takes each packet the cycle it is offered; `drop` holds it on purpose.
        self.mon.set_ready_randomizer(FlexRandomizer({'ready_delay': ([(0, 0)], [1])}))
        self.base.set_timing_profile('normal')

    async def assert_reset(self):
        await self.base.assert_reset()

    async def deassert_reset(self):
        await self.base.deassert_reset()

    # ---- helpers --------------------------------------------------------

    def _slave_bfm(self):
        """The memory-backed slave BFM: the read TB calls it axi4_slave, the write TB interface."""
        return getattr(self.base, 'axi4_slave', None) or self.base.interface

    def _fail(self, msg):
        self.log.error(msg)
        self.errors.append(msg)

    def pkts(self, ptype=None, code=None):
        crit = {}
        if ptype is not None: crit['pkt_type'] = int(ptype)
        if code is not None: crit['event_code'] = int(code)
        return find_packets_by_criteria(self.mon.received_packets, **crit)

    def take(self):
        """Snapshot and clear the received list."""
        got = list(self.mon.received_packets)
        self.mon.clear_received_packets()
        return got

    async def settle(self, cycles=60):
        await ClockCycles(self.dut.aclk, cycles)

    async def xfer(self, addr, beats=1, txn_id=0):
        """One transaction through the master BFM; returns (ok, exception)."""
        m = self.base.test_master
        try:
            if self.is_write:
                data = [(0xA5000000 | (addr & 0xFFFFFF) | k) for k in range(beats)]
                r = await m.write_transaction(addr, data if beats > 1 else data[0], id=txn_id, size=2)
                ok = bool(r.get('success', True)) if isinstance(r, dict) else True
                return ok, None
            await m.read_transaction(addr, burst_len=beats, id=txn_id, size=2)
            return True, None
        except Exception as e:      # the BFM raises on SLVERR/DECERR for reads
            return False, e

    def _check_compl(self, pkt, addr, txn_id, where):
        if compl_addr(pkt) != addr:
            self._fail(f"{where}: completion address 0x{compl_addr(pkt):08X} != 0x{addr:08X}")
        if pkt.channel_id != (txn_id & ((1 << CHAN_ID_BITS) - 1)):
            self._fail(f"{where}: completion channel {pkt.channel_id} != id {txn_id & ((1 << CHAN_ID_BITS) - 1)}")
        if compl_latency(pkt) == 0:
            self._fail(f"{where}: completion latency is 0 cycles")

    # ---- phases ---------------------------------------------------------

    async def phase_singles(self):
        n = self.cfg['singles']
        self.take()
        issued = []
        for i in range(n):
            addr = 0x1000 + i * 0x40
            tid = i % (1 << self.id_width)
            ok, e = await self.xfer(addr, 1, tid)
            if not ok:
                self._fail(f"singles: transaction {i} failed: {e}")
            issued.append((addr, tid))
        await self.settle()
        got = self.take()
        compl = find_packets_by_criteria(got, pkt_type=int(PKT_COMPL))
        others = [p for p in got if not p.is_completion_packet()]
        if len(compl) != n:
            self._fail(f"singles: {len(compl)} completion packets for {n} transactions")
        if others:
            self._fail(f"singles: {len(others)} unexpected packets: {[ (p.pkt_type, p.event_code) for p in others[:4]]}")
        seen = {(compl_addr(p), p.channel_id) for p in compl}
        for addr, tid in issued:
            if (addr, tid & ((1 << CHAN_ID_BITS) - 1)) not in seen:
                self._fail(f"singles: no completion for 0x{addr:08X} id {tid}")
        for p in compl:
            if compl_latency(p) == 0:
                self._fail("singles: a completion carries zero latency")
        self.log.info(f"phase singles: {n} transactions, {len(compl)} completions, addresses and ids all matched")

    async def phase_bursts(self):
        self.take()
        for k, beats in enumerate(self.cfg['bursts']):
            addr = 0x8000 + k * 0x100
            ok, e = await self.xfer(addr, beats, k + 1)
            if not ok:
                self._fail(f"bursts: {beats}-beat transaction failed: {e}")
            await self.settle(80)
            got = self.take()
            compl = find_packets_by_criteria(got, pkt_type=int(PKT_COMPL))
            if len(compl) != 1:
                self._fail(f"bursts: {len(compl)} completions for one {beats}-beat burst")
            else:
                self._check_compl(compl[0], addr, k + 1, f"bursts[{beats}]")
            if find_packets_by_criteria(got, pkt_type=int(PKT_ERROR)):
                self._fail(f"bursts[{beats}]: error packet on a clean burst")
        self.log.info(f"phase bursts: {self.cfg['bursts']} beats, one completion each")

    async def phase_slverr(self):
        self.take()
        ok, e = await self.xfer(self.OOR_ADDR, 1, 3)
        await self.settle()
        got = self.take()
        errs = find_packets_by_criteria(got, pkt_type=int(PKT_ERROR))
        compl = find_packets_by_criteria(got, pkt_type=int(PKT_COMPL))
        if len(errs) != 1:
            self._fail(f"slverr: {len(errs)} error packets for one out-of-range access")
        else:
            p = errs[0]
            if p.event_code != ERR_SLVERR:
                self._fail(f"slverr: error code {p.event_code}, expected RESP_SLVERR")
            if compl_addr(p) != self.OOR_ADDR or p.channel_id != 3:
                self._fail(f"slverr: packet names 0x{compl_addr(p):08X}/id {p.channel_id}, expected 0x{self.OOR_ADDR:08X}/3")
        if compl:
            self._fail(f"slverr: {len(compl)} completion packets for an errored transaction")
        self.log.info("phase slverr: one Error/RESP_SLVERR with the address and id, no completion")

    async def phase_timeout(self):
        slave = self._slave_bfm()
        saved = slave.response_delay_cycles
        slave.response_delay_cycles = 400
        if hasattr(self.dut, 'cfg_timeout_cycles'): self.dut.cfg_timeout_cycles.value = 2          # 2 ticks of the LUT-0 tick
        self.take()
        ok, e = await self.xfer(0x2000, 1, 5)
        await self.settle()
        got = self.take()
        tmo = find_packets_by_criteria(got, pkt_type=int(PKT_TIMEOUT))
        want = TMO_RESP if self.is_write else TMO_DATA
        if len(tmo) != 1:
            self._fail(f"timeout: {len(tmo)} timeout packets for one stalled transaction")
        else:
            p = tmo[0]
            if p.event_code != want:
                self._fail(f"timeout: code {p.event_code}, expected {want} ({'RESP' if self.is_write else 'DATA'})")
            if compl_addr(p) != 0x2000 or p.channel_id != 5:
                self._fail(f"timeout: packet names 0x{compl_addr(p):08X}/id {p.channel_id}")
        if len(find_packets_by_criteria(got, pkt_type=int(PKT_COMPL))) != 1:
            self._fail("timeout: the stalled transaction should still complete once")
        slave.response_delay_cycles = saved
        if hasattr(self.dut, 'cfg_timeout_cycles'): self.dut.cfg_timeout_cycles.value = 0
        self.log.info(f"phase timeout: one Timeout/{'RESP' if self.is_write else 'DATA'} packet, then the completion")

    async def phase_threshold(self):
        slave = self._slave_bfm()
        saved = slave.response_delay_cycles
        slave.response_delay_cycles = 150
        self.take()
        # enough outstanding to cross the wrapper's threshold (MAX_TRANSACTIONS / 2)
        n = min(self.max_trans, self.max_trans // 2 + self.cfg['pile'] - 4)
        done = []

        async def _one(i):
            await self.xfer(0x3000 + i * 0x40, 1, i % (1 << self.id_width))
            done.append(1)

        for i in range(n):
            cocotb.start_soon(_one(i))
        for _ in range(400):
            if len(done) == n:
                break
            await ClockCycles(self.dut.aclk, 10)
        await self.settle()
        got = self.take()
        thr = find_packets_by_criteria(got, pkt_type=int(PKT_THRESH))
        if not thr:
            self._fail(f"threshold: no threshold packet with {n} transactions outstanding (threshold {self.max_trans // 2})")
        else:
            if thr[0].event_code != THRESH_ACTIVE_COUNT or thr[0].data < self.max_trans // 2:
                self._fail(f"threshold: code {thr[0].event_code} data {thr[0].data}, expected ACTIVE_COUNT >= {self.max_trans // 2}")
        if len(find_packets_by_criteria(got, pkt_type=int(PKT_COMPL))) != n:
            self._fail(f"threshold: {len(find_packets_by_criteria(got, pkt_type=int(PKT_COMPL)))} completions for {n} transactions")
        slave.response_delay_cycles = saved
        self.log.info(f"phase threshold: {n} outstanding, {len(thr)} threshold packet(s), count {thr[0].data if thr else '-'}")

    async def phase_drop(self):
        n = self.cfg['held']
        self.take()
        # hold the monbus for longer than the whole burst of transactions takes:
        # the first events fill the output skid, the rest must be dropped
        self.mon.set_ready_randomizer(FlexRandomizer({'ready_delay': ([(400, 400)], [1])}))
        self.base.set_timing_profile('fast')
        for i in range(n):
            ok, e = await self.xfer(0x4000 + i * 0x40, 1, i % (1 << self.id_width))
        # release: the randomizer is consulted per packet, so the held one
        # still finishes its 400 cycles before the rest stream out
        self.mon.set_ready_randomizer(FlexRandomizer({'ready_delay': ([(0, 0)], [1])}))
        await self.settle(900)
        self.base.set_timing_profile('normal')
        got = self.take()
        compl = find_packets_by_criteria(got, pkt_type=int(PKT_COMPL))
        drops = find_packets_by_criteria(got, pkt_type=int(PKT_ERROR), event_code=int(ERR_EVENT_DROPPED))
        # One report per stretch of loss: the bus may stall again while the
        # first report waits, so more than one is legal -- the counts must sum.
        reported = sum(p.data for p in drops)
        if not drops:
            self._fail("drop: no EVENT_DROPPED packet after the bus freed")
        elif reported + len(compl) != n:
            self._fail(f"drop: {len(compl)} delivered + {reported} reported dropped (in {len(drops)} report(s)) != {n} issued")
        elif reported == 0:
            self._fail("drop: the held bus lost nothing?")
        if len(compl) < 4:
            self._fail(f"drop: only {len(compl)} delivered -- the output skid should hold four events through a stall")
        others = [p for p in got if not (p.is_completion_packet() or p.is_error_packet())]
        if others:
            self._fail(f"drop: unexpected packets {[ (p.pkt_type, p.event_code) for p in others[:4]]}")
        self.log.info(f"phase drop: {n} issued, {len(compl)} delivered, {reported} reported dropped in {len(drops)} report(s)")

    async def phase_latency(self):
        """Threshold/LATENCY: a low latency threshold against a slow slave yields one
        threshold packet per completion, coded LATENCY, naming the address and id
        and carrying the latency; the completion itself still arrives."""
        d = self.dut
        if not hasattr(d, 'cfg_latency_threshold'):
            return
        slave = self._slave_bfm()
        saved = slave.response_delay_cycles
        slave.response_delay_cycles = 40
        d.cfg_latency_threshold.value = 10
        self.take()
        ok, e = await self.xfer(0x6000, 1, 6)
        await self.settle()
        got = self.take()
        lat = find_packets_by_criteria(got, pkt_type=int(PKT_THRESH), event_code=int(THRESH_LATENCY))
        if len(lat) != 1:
            self._fail(f"latency: {len(lat)} Threshold/LATENCY packets for one slow completion ({[(p.pkt_type, p.event_code) for p in got]})")
        else:
            p = lat[0]
            if compl_addr(p) != 0x6000 or p.channel_id != 6 or compl_latency(p) <= 10:
                self._fail(f"latency: packet names 0x{compl_addr(p):08X}/id {p.channel_id}, latency {compl_latency(p)}")
        if len(find_packets_by_criteria(got, pkt_type=int(PKT_COMPL))) != 1:
            self._fail("latency: the slow transaction should still complete once")
        # A held event going out is not a fired event: the drop counter must not
        # move (the pre-2026-09-28 accounting subtracted the held take from the
        # fired total and underflowed by 15, which surfaced as a bogus
        # EVENT_DROPPED report after every latency packet).
        bogus = find_packets_by_criteria(got, pkt_type=int(PKT_ERROR), event_code=int(ERR_EVENT_DROPPED))
        if bogus:
            self._fail(f"latency: {len(bogus)} EVENT_DROPPED report(s) ({[p.data for p in bogus]}) after a latency packet with the bus free")
        d.cfg_latency_threshold.value = 0x0FFF_FFFF
        slave.response_delay_cycles = saved
        self.log.info("phase latency: one Threshold/LATENCY with address, id and latency, plus the completion")

    async def phase_addr_range(self):
        """Optional address-range checker (N_ADDR_RANGES > 0): range 0 is an
        ERROR range (ADDR_RANGE_IS_ERROR[0]=1) -- a read outside it is one
        Error/ADDR_RANGE packet; range 1 is a MATCH range -- a read inside it is
        one AddrMatch packet. Both name the address and id. Skipped when the
        wrapper was built without the checker."""
        d = self.dut
        n_ranges = int(os.environ.get('N_ADDR_RANGES', '0'))
        if n_ranges < 2 or not hasattr(d, 'cfg_addr_check_enable'):
            self.log.info("phase addr_range: skipped (N_ADDR_RANGES < 2)")
            return
        self.take()
        # range 0 (error flavour): 0x1000..0x1FFF allowed; range 1 (match): 0x8000..0x80FF
        d.cfg_addr_range_low.value  = (0x8000 << 32) | 0x1000
        d.cfg_addr_range_high.value = (0x80FF << 32) | 0x1FFF
        d.cfg_addr_range_enable.value = 0b11
        d.cfg_addr_check_enable.value = 1
        d.cfg_addr_match_enable.value = 1
        await self.settle(4)
        # in the error range: nothing but the completion
        ok, e = await self.xfer(0x1200, 1, 2)
        await self.settle()
        got = self.take()
        if find_packets_by_criteria(got, pkt_type=int(PKT_ERROR)) or find_packets_by_criteria(got, pkt_type=int(PKT_ADDRMATCH)):
            self._fail(f"addr_range: in-range access raised {[(p.pkt_type, p.event_code) for p in got]}")
        # outside every range: one Error/ADDR_RANGE naming the address and id
        ok, e = await self.xfer(0x3000, 1, 3)
        await self.settle()
        got = self.take()
        errs = find_packets_by_criteria(got, pkt_type=int(PKT_ERROR), event_code=int(ERR_ADDR_RANGE))
        if len(errs) != 1:
            self._fail(f"addr_range: {len(errs)} ADDR_RANGE errors for one out-of-range access ({[(p.pkt_type, p.event_code) for p in got]})")
        elif compl_addr(errs[0]) != 0x3000 or errs[0].channel_id != 3:
            self._fail(f"addr_range: error names 0x{compl_addr(errs[0]):08X}/id {errs[0].channel_id}")
        # inside the match range: one AddrMatch (and, being outside the error range, one ADDR_RANGE error)
        ok, e = await self.xfer(0x8040, 1, 4)
        await self.settle()
        got = self.take()
        hits = find_packets_by_criteria(got, pkt_type=int(PKT_ADDRMATCH))
        if len(hits) != 1:
            self._fail(f"addr_range: {len(hits)} AddrMatch packets for one in-range access ({[(p.pkt_type, p.event_code) for p in got]})")
        elif compl_addr(hits[0]) != 0x8040 or hits[0].channel_id != 4:
            self._fail(f"addr_range: match names 0x{compl_addr(hits[0]):08X}/id {hits[0].channel_id}")
        d.cfg_addr_check_enable.value = 0
        d.cfg_addr_match_enable.value = 0
        d.cfg_addr_range_enable.value = 0
        self.log.info("phase addr_range: one ADDR_RANGE error on a miss, one AddrMatch on a hit, silence in range")

    async def phase_after(self):
        """The monitor is healthy after all of that: a clean single still completes."""
        self.take()
        ok, e = await self.xfer(0x5000, 1, 1)
        await self.settle()
        got = self.take()
        if len(find_packets_by_criteria(got, pkt_type=int(PKT_COMPL))) != 1 or [p for p in got if not p.is_completion_packet()]:
            self._fail(f"after: expected exactly one completion, got {[(p.pkt_type, p.event_code) for p in got]}")

    async def run_suite(self):
        await self.phase_singles()
        await self.phase_bursts()
        await self.phase_slverr()
        await self.phase_timeout()
        await self.phase_threshold()
        await self.phase_drop()
        await self.phase_latency()
        await self.phase_addr_range()
        await self.phase_after()
        self.log.info(f"axi_monitor_lite {'write' if self.is_write else 'read'} {self.level}: {len(self.errors)} error(s)")
        return not self.errors
