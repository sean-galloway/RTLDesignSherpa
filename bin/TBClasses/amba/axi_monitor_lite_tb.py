# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""axi_monitor_lite through its wrapper (TASK-098).

The DUT is axi4_slave_rd_mon or axi4_slave_wr_mon with MONITOR_LITE=1: an
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
from CocoTBFramework.components.shared.flex_randomizer import FlexRandomizer

PKT_ERROR, PKT_COMPL, PKT_THRESH, PKT_TIMEOUT = 0, 1, 2, 3
ERR_SLVERR, ERR_DECERR, ERR_DATA_ORPHAN, ERR_RESP_ORPHAN = 0, 1, 2, 3
ERR_EVENT_DROPPED = 0xE
TMO_CMD, TMO_DATA, TMO_RESP = 0, 1, 2
THRESH_ACTIVE_COUNT = 0

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
        d.cfg_monitor_enable.value = 1
        d.cfg_error_enable.value = 1
        d.cfg_timeout_enable.value = 1
        d.cfg_perf_enable.value = 0
        d.cfg_compl_enable.value = 1
        d.cfg_threshold_enable.value = 1
        d.cfg_debug_enable.value = 0
        d.cfg_timeout_cycles.value = 0          # 0 = never (wrapper maps to 0xFFFF)
        d.cfg_freq_sel.value = 0                # LUT entry 0 = the slowest clock = the shortest tick
        d.cfg_latency_threshold.value = 0
        for name in ('cfg_axi_pkt_mask', 'cfg_axi_err_select', 'cfg_axi_error_mask', 'cfg_axi_timeout_mask',
                     'cfg_axi_compl_mask', 'cfg_axi_thresh_mask', 'cfg_axi_perf_mask', 'cfg_axi_addr_mask',
                     'cfg_axi_debug_mask'):
            getattr(d, name).value = 0
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
        out = []
        for p in self.mon.received_packets:
            if ptype is not None and p.pkt_type != ptype:
                continue
            if code is not None and p.event_code != code:
                continue
            out.append(p)
        return out

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
        if (pkt.data & 0xFFFFFFFF) != addr:
            self._fail(f"{where}: completion address 0x{pkt.data & 0xFFFFFFFF:08X} != 0x{addr:08X}")
        if pkt.channel_id != (txn_id & 0x3F):
            self._fail(f"{where}: completion channel {pkt.channel_id} != id {txn_id & 0x3F}")
        if (pkt.data >> 48) == 0:
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
        compl = [p for p in got if p.pkt_type == PKT_COMPL]
        others = [p for p in got if p.pkt_type != PKT_COMPL]
        if len(compl) != n:
            self._fail(f"singles: {len(compl)} completion packets for {n} transactions")
        if others:
            self._fail(f"singles: {len(others)} unexpected packets: {[ (p.pkt_type, p.event_code) for p in others[:4]]}")
        seen = {(p.data & 0xFFFFFFFF, p.channel_id) for p in compl}
        for addr, tid in issued:
            if (addr, tid & 0x3F) not in seen:
                self._fail(f"singles: no completion for 0x{addr:08X} id {tid}")
        for p in compl:
            if (p.data >> 48) == 0:
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
            compl = [p for p in got if p.pkt_type == PKT_COMPL]
            if len(compl) != 1:
                self._fail(f"bursts: {len(compl)} completions for one {beats}-beat burst")
            else:
                self._check_compl(compl[0], addr, k + 1, f"bursts[{beats}]")
            if [p for p in got if p.pkt_type == PKT_ERROR]:
                self._fail(f"bursts[{beats}]: error packet on a clean burst")
        self.log.info(f"phase bursts: {self.cfg['bursts']} beats, one completion each")

    async def phase_slverr(self):
        self.take()
        ok, e = await self.xfer(self.OOR_ADDR, 1, 3)
        await self.settle()
        got = self.take()
        errs = [p for p in got if p.pkt_type == PKT_ERROR]
        compl = [p for p in got if p.pkt_type == PKT_COMPL]
        if len(errs) != 1:
            self._fail(f"slverr: {len(errs)} error packets for one out-of-range access")
        else:
            p = errs[0]
            if p.event_code != ERR_SLVERR:
                self._fail(f"slverr: error code {p.event_code}, expected RESP_SLVERR")
            if (p.data & 0xFFFFFFFF) != self.OOR_ADDR or p.channel_id != 3:
                self._fail(f"slverr: packet names 0x{p.data & 0xFFFFFFFF:08X}/id {p.channel_id}, expected 0x{self.OOR_ADDR:08X}/3")
        if compl:
            self._fail(f"slverr: {len(compl)} completion packets for an errored transaction")
        self.log.info("phase slverr: one Error/RESP_SLVERR with the address and id, no completion")

    async def phase_timeout(self):
        slave = self._slave_bfm()
        saved = slave.response_delay_cycles
        slave.response_delay_cycles = 400
        self.dut.cfg_timeout_cycles.value = 2          # 2 ticks of the LUT-0 tick
        self.take()
        ok, e = await self.xfer(0x2000, 1, 5)
        await self.settle()
        got = self.take()
        tmo = [p for p in got if p.pkt_type == PKT_TIMEOUT]
        want = TMO_RESP if self.is_write else TMO_DATA
        if len(tmo) != 1:
            self._fail(f"timeout: {len(tmo)} timeout packets for one stalled transaction")
        else:
            p = tmo[0]
            if p.event_code != want:
                self._fail(f"timeout: code {p.event_code}, expected {want} ({'RESP' if self.is_write else 'DATA'})")
            if (p.data & 0xFFFFFFFF) != 0x2000 or p.channel_id != 5:
                self._fail(f"timeout: packet names 0x{p.data & 0xFFFFFFFF:08X}/id {p.channel_id}")
        if len([p for p in got if p.pkt_type == PKT_COMPL]) != 1:
            self._fail("timeout: the stalled transaction should still complete once")
        slave.response_delay_cycles = saved
        self.dut.cfg_timeout_cycles.value = 0
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
        thr = [p for p in got if p.pkt_type == PKT_THRESH]
        if not thr:
            self._fail(f"threshold: no threshold packet with {n} transactions outstanding (threshold {self.max_trans // 2})")
        else:
            if thr[0].event_code != THRESH_ACTIVE_COUNT or thr[0].data < self.max_trans // 2:
                self._fail(f"threshold: code {thr[0].event_code} data {thr[0].data}, expected ACTIVE_COUNT >= {self.max_trans // 2}")
        if len([p for p in got if p.pkt_type == PKT_COMPL]) != n:
            self._fail(f"threshold: {len([p for p in got if p.pkt_type == PKT_COMPL])} completions for {n} transactions")
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
        compl = [p for p in got if p.pkt_type == PKT_COMPL]
        drops = [p for p in got if p.pkt_type == PKT_ERROR and p.event_code == ERR_EVENT_DROPPED]
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
        others = [p for p in got if p.pkt_type not in (PKT_COMPL, PKT_ERROR)]
        if others:
            self._fail(f"drop: unexpected packets {[ (p.pkt_type, p.event_code) for p in others[:4]]}")
        self.log.info(f"phase drop: {n} issued, {len(compl)} delivered, {reported} reported dropped in {len(drops)} report(s)")

    async def phase_after(self):
        """The monitor is healthy after all of that: a clean single still completes."""
        self.take()
        ok, e = await self.xfer(0x5000, 1, 1)
        await self.settle()
        got = self.take()
        if len([p for p in got if p.pkt_type == PKT_COMPL]) != 1 or [p for p in got if p.pkt_type != PKT_COMPL]:
            self._fail(f"after: expected exactly one completion, got {[(p.pkt_type, p.event_code) for p in got]}")

    async def run_suite(self):
        await self.phase_singles()
        await self.phase_bursts()
        await self.phase_slverr()
        await self.phase_timeout()
        await self.phase_threshold()
        await self.phase_drop()
        await self.phase_after()
        self.log.info(f"axi_monitor_lite {'write' if self.is_write else 'read'} {self.level}: {len(self.errors)} error(s)")
        return not self.errors
