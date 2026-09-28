# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# Module: axis_monitor_lite_tb
# Purpose: Exact-packet testbench for axis_monitor_lite (amba/monitor-lite TASK-003).
"""axis_monitor_lite, driven through the framework AXIS master and slave BFMs.

The DUT is val/amba/monitor-lite/tb_axis_monitor_lite.sv: the core tapping a
stream whose payload side the AXIS master BFM drives and whose tready the AXIS
slave BFM drives. A MonbusSlave collects every packet. Each phase asserts the
class, code AND payload of what the core emitted, and that nothing else came
out -- a checker verdict here is a count, never a bare "no violations".

Stimulus is the BFMs' own: stalls come from the slave's ready policy, bubbles
inside a packet from the master's valid-delay randomizer, TSTRB from the
master's strb argument. The one protocol violation (TVALID withdrawn before
the handshake) is driven on the pins while both BFMs are idle, because a
compliant BFM cannot produce it -- the same precedent as the AXIS observer's
test, and the only place a pin is touched.
"""
import os
import cocotb
from cocotb.triggers import ClockCycles, RisingEdge

from TBClasses.shared.tbbase import TBBase
from TBClasses.monbus.monbus_slave import MonbusSlave
from TBClasses.monbus.monbus_types import (PktType, AXISErrorCode, AXISTimeoutCode, AXISCompletionCode,
                                            AXISCreditCode, AXISChannelCode, AXISStreamCode)
from TBClasses.monbus.monbus_validators import find_packets_by_criteria
from CocoTBFramework.components.shared.flex_randomizer import FlexRandomizer
from CocoTBFramework.components.axis4.axis_factories import create_axis_master, create_axis_slave

# Packet vocabulary from the shared monbus types; nothing is redefined here.
PKT_ERROR   = PktType.PktTypeError
PKT_TIMEOUT = PktType.PktTypeTimeout
PKT_COMPL   = PktType.PktTypeCompletion
PKT_CREDIT  = PktType.PktTypeCredit
PKT_CHANNEL = PktType.PktTypeChannel
PKT_STREAM  = PktType.PktTypeStream
ERR_VALID_TIMING  = AXISErrorCode.AXIS_ERR_VALID_TIMING
ERR_STRB_INVALID  = AXISErrorCode.AXIS_ERR_STRB_INVALID
ERR_EVENT_DROPPED = AXISErrorCode.AXIS_ERR_EVENT_DROPPED
TMO_HANDSHAKE = AXISTimeoutCode.AXIS_TIMEOUT_HANDSHAKE
TMO_PACKET    = AXISTimeoutCode.AXIS_TIMEOUT_PACKET
COMPL_STREAM_END = AXISCompletionCode.AXIS_COMPL_STREAM_END
CREDIT_BACKPRESSURE = AXISCreditCode.AXIS_CREDIT_BACKPRESSURE
CHAN_ID_CHANGE   = AXISChannelCode.AXIS_CHAN_ID_CHANGE
CHAN_DEST_CHANGE = AXISChannelCode.AXIS_CHAN_DEST_CHANGE
STREAM_START  = AXISStreamCode.AXIS_STREAM_START
STREAM_PAUSE  = AXISStreamCode.AXIS_STREAM_PAUSE
STREAM_RESUME = AXISStreamCode.AXIS_STREAM_RESUME

# Payload layouts (axis_monitor_lite.sv, lifted from the observer's tap):
#   STREAM_END / START / *_CHANGE : {16'(a), 16'(b), 32'(count)}  -- START only for packets of 2+ beats
#   PAUSE / RESUME / VALID_TIMING / STRB_INVALID : {32'(hi), 32'(lo)}
#   HANDSHAKE / PACKET timeout    : {32'(cycles or beats), 16'(age_us), 16'(cfg)}
#   BACKPRESSURE                  : {32'(stall_cycles), 32'(cfg_stall_threshold)}
def d_hi16(p):  return (p.data >> 48) & 0xFFFF
def d_mid16(p): return (p.data >> 32) & 0xFFFF
def d_hi32(p):  return (p.data >> 32) & 0xFFFF_FFFF
def d_lo32(p):  return p.data & 0xFFFF_FFFF
def d_lo16(p):  return p.data & 0xFFFF
def d_age16(p): return (p.data >> 16) & 0xFFFF     # the {32, 16 age, 16 cfg} layout's middle field

# US_TICK: LUT entry 0 of counter_freq_invariant at CFI_MIN=CFI_MAX=ACLK_MHZ is one
# microsecond of the configured clock -- 100 cycles at 100 MHz (the fixture's ACLK_MHZ).
US_TICK_CYCLES = 100

PROFILE = {
    'gate': dict(packets=4,  beats=(1, 2, 4),        gap=3, held=6),
    'func': dict(packets=16, beats=(1, 2, 4, 8),     gap=5, held=10),
    'full': dict(packets=48, beats=(1, 2, 4, 8, 16), gap=7, held=20),
}


class AxisMonitorLiteTB(TBBase):
    """The BFMs own the stream; this class owns the expectations."""

    def __init__(self, dut):
        super().__init__(dut)
        self.level = os.environ.get('TEST_LEVEL', 'gate').lower()
        if self.level not in PROFILE:
            self.level = 'gate'
        self.cfg = PROFILE[self.level]
        self.data_width = int(os.environ.get('TEST_DATA_WIDTH', '32'))
        self.id_width   = int(os.environ.get('TEST_ID_WIDTH', '8'))
        self.dest_width = int(os.environ.get('TEST_DEST_WIDTH', '4'))
        self.user_width = int(os.environ.get('TEST_USER_WIDTH', '1'))
        self.clk_period = int(os.environ.get('TEST_CLK_PERIOD', '10'))
        self.strb_all = (1 << (self.data_width // 8)) - 1
        self.id_mask = (1 << self.id_width) - 1
        self.dest_mask = (1 << self.dest_width) - 1
        self.errors = []
        self.master = None
        self.slave = None
        self.mon = None

    # ---- mandatory ------------------------------------------------------

    async def setup_clocks_and_reset(self):
        await self.start_clock('aclk', self.clk_period, 'ns')
        d = self.dut
        d.clear.value = 0
        d.i_mon_time.value = 0
        d.cfg_freq_sel.value = 0                 # LUT entry 0: the configured clock's microsecond
        d.cfg_timeout_cnt.value = 0xFFFF         # never
        d.cfg_error_enable.value = 1
        d.cfg_timeout_enable.value = 1
        d.cfg_compl_enable.value = 1
        d.cfg_credit_enable.value = 1
        d.cfg_channel_enable.value = 1
        d.cfg_stream_enable.value = 1
        d.cfg_strb_check_enable.value = 0
        d.cfg_stall_threshold.value = 0          # off
        d.cfg_axis_pkt_mask.value = 0
        await self.assert_reset()
        await self.wait_clocks('aclk', 10)
        await self.deassert_reset()
        await self.wait_clocks('aclk', 10)
        # The BFMs: master drives the payload side, slave drives tready. Both
        # start deterministic (no delays) so every phase's count is exact.
        self.master = create_axis_master(
            d, d.aclk, prefix='axis_', data_width=self.data_width, id_width=self.id_width,
            dest_width=self.dest_width, user_width=self.user_width, log=self.log,
            randomizer=FlexRandomizer({'valid_delay': ([(0, 0)], [1])}))['master']
        self.slave = create_axis_slave(
            d, d.aclk, prefix='axis_', data_width=self.data_width, id_width=self.id_width,
            dest_width=self.dest_width, user_width=self.user_width, log=self.log,
            randomizer=FlexRandomizer({'ready_delay': ([(0, 0)], [1])}))['slave']
        self.mon = MonbusSlave(dut=d, title="MonBus", prefix="", clock=d.aclk,
                               bus_name="monbus", pkt_prefix="", log=self.log)
        self.mon.set_ready_randomizer(FlexRandomizer({'ready_delay': ([(0, 0)], [1])}))
        await self.wait_clocks('aclk', 5)

    async def assert_reset(self):
        self.dut.aresetn.value = 0

    async def deassert_reset(self):
        self.dut.aresetn.value = 1

    # ---- helpers --------------------------------------------------------

    def _fail(self, msg):
        self.log.error(msg)
        self.errors.append(msg)

    def take(self):
        got = list(self.mon.received_packets)
        self.mon.clear_received_packets()
        return got

    async def settle(self, cycles=40):
        await ClockCycles(self.dut.aclk, cycles)

    def master_gap(self, cycles):
        """Cycles of TVALID-low the master inserts before EVERY beat."""
        self.master.set_randomizer(FlexRandomizer({'valid_delay': ([(cycles, cycles)], [1])}))

    async def send(self, beats, tid=0, tdest=0):
        data = [(0xA5000000 | (tid << 16) | k) & ((1 << self.data_width) - 1) for k in range(beats)]
        await self.master.send_stream_data(data, id=tid, dest=tdest)

    async def beat(self, last, tid=0, tdest=0, strb=None, data=0x1234):
        await self.master.send_single_beat(
            data=data & ((1 << self.data_width) - 1), last=last, id=tid, dest=tdest, user=0,
            strb=self.strb_all if strb is None else strb)

    @staticmethod
    def sel(got, ptype, code=None):
        crit = {'pkt_type': int(ptype)}
        if code is not None:
            crit['event_code'] = int(code)
        return find_packets_by_criteria(got, **crit)

    def expect_only(self, got, allowed, where):
        """Every packet in `got` is one of the (type, code) pairs in `allowed`."""
        bad = [(p.pkt_type, p.event_code) for p in got if (p.pkt_type, p.event_code) not in allowed]
        if bad:
            self._fail(f"{where}: unexpected packets {bad[:6]}")

    # ---- phases ---------------------------------------------------------

    async def phase_packets(self):
        """One START and one STREAM_END per packet, payload naming tid/tdest/beats; nothing else."""
        n = self.cfg['packets']
        self.take()
        plan = [(self.cfg['beats'][i % len(self.cfg['beats'])], (i * 3) & self.id_mask, (i * 5) & self.dest_mask)
                for i in range(n)]
        for beats, tid, tdest in plan:
            await self.send(beats, tid, tdest)
        await self.settle()
        got = self.take()
        starts = self.sel(got, PKT_STREAM, STREAM_START)
        ends = self.sel(got, PKT_COMPL, COMPL_STREAM_END)
        multi = [(i, b, t, e) for i, (b, t, e) in enumerate(plan) if b > 1]   # a one-beat packet's START is implied
        if len(starts) != len(multi) or len(ends) != n:
            self._fail(f"packets: {len(starts)} START / {len(ends)} STREAM_END for {n} packets ({len(multi)} multi-beat)")
        for i, (beats, tid, tdest) in enumerate(plan):
            if i < len(ends):
                p = ends[i]
                if (d_hi16(p), d_mid16(p), d_lo32(p)) != (tid, tdest, beats):
                    self._fail(f"packets: STREAM_END #{i} payload tid/tdest/beats = "
                               f"{d_hi16(p)}/{d_mid16(p)}/{d_lo32(p)}, expected {tid}/{tdest}/{beats}")
                if p.channel_id != tid:
                    self._fail(f"packets: STREAM_END #{i} channel_id {p.channel_id} != tid {tid}")
        for k, (i, beats, tid, tdest) in enumerate(multi):
            if k < len(starts):
                p = starts[k]
                if (d_hi16(p), d_mid16(p), d_lo32(p)) != (tid, tdest, i):
                    self._fail(f"packets: START for packet #{i} payload tid/tdest/count = "
                               f"{d_hi16(p)}/{d_mid16(p)}/{d_lo32(p)}, expected {tid}/{tdest}/{i}")
        self.expect_only(got, {(int(PKT_STREAM), int(STREAM_START)), (int(PKT_COMPL), int(COMPL_STREAM_END))}, "packets")
        if int(self.dut.packet_count.value) != n:
            self._fail(f"packets: packet_count {int(self.dut.packet_count.value)} != {n}")
        self.log.info(f"phase packets: {n} packets, {len(starts)} START + {len(ends)} STREAM_END, payloads exact")

    async def phase_channel(self):
        """TID/TDEST changing under one packet: one Channel packet per change, against the previous beat."""
        if self.id_width < 2:
            self.log.info("phase channel: skipped, id_width < 2")
            return
        self.take()
        t0, t1 = 1 & self.id_mask, 2 & self.id_mask
        e0, e1 = 0 & self.dest_mask, 1 & self.dest_mask
        await self.beat(0, tid=t0, tdest=e0)          # beat 1
        await self.beat(0, tid=t1, tdest=e0)          # beat 2: ID change
        await self.beat(0, tid=t1, tdest=e1)          # beat 3: DEST change
        await self.beat(1, tid=t1, tdest=e1)          # beat 4: last, no change
        await self.settle()
        got = self.take()
        idc = self.sel(got, PKT_CHANNEL, CHAN_ID_CHANGE)
        dsc = self.sel(got, PKT_CHANNEL, CHAN_DEST_CHANGE)
        if len(idc) != 1 or len(dsc) != 1:
            self._fail(f"channel: {len(idc)} ID_CHANGE / {len(dsc)} DEST_CHANGE, expected 1 / 1")
        if idc and (d_hi16(idc[0]), d_mid16(idc[0]), d_lo32(idc[0])) != (t0, t1, 2):
            self._fail(f"channel: ID_CHANGE payload old/new/beat = {d_hi16(idc[0])}/{d_mid16(idc[0])}/{d_lo32(idc[0])}, expected {t0}/{t1}/2")
        if dsc and (d_hi16(dsc[0]), d_mid16(dsc[0]), d_lo32(dsc[0])) != (e0, e1, 3):
            self._fail(f"channel: DEST_CHANGE payload old/new/beat = {d_hi16(dsc[0])}/{d_mid16(dsc[0])}/{d_lo32(dsc[0])}, expected {e0}/{e1}/3")
        ends = self.sel(got, PKT_COMPL, COMPL_STREAM_END)
        if len(ends) != 1 or d_lo32(ends[0]) != 4:
            self._fail(f"channel: expected one STREAM_END of 4 beats, got {[(d_lo32(p)) for p in ends]}")
        # beat-by-beat sends leave TVALID low between beats: legal bubbles, reported as PAUSE/RESUME
        self.expect_only(got, {(int(PKT_STREAM), int(STREAM_START)), (int(PKT_COMPL), int(COMPL_STREAM_END)),
                               (int(PKT_STREAM), int(STREAM_PAUSE)), (int(PKT_STREAM), int(STREAM_RESUME)),
                               (int(PKT_CHANNEL), int(CHAN_ID_CHANGE)), (int(PKT_CHANNEL), int(CHAN_DEST_CHANGE))}, "channel")
        self.log.info("phase channel: one ID_CHANGE at beat 2, one DEST_CHANGE at beat 3, payloads exact")

    async def phase_pause(self):
        """Master bubbles inside a packet: PAUSE and RESUME once per gap, never at packet boundaries."""
        beats = max(self.cfg['beats'])
        gap = self.cfg['gap']
        self.take()
        self.master_gap(gap)
        await self.send(beats, tid=3 & self.id_mask, tdest=0)
        self.master_gap(0)
        await self.settle()
        got = self.take()
        pauses = self.sel(got, PKT_STREAM, STREAM_PAUSE)
        resumes = self.sel(got, PKT_STREAM, STREAM_RESUME)
        if len(pauses) != beats - 1 or len(resumes) != beats - 1:
            self._fail(f"pause: {len(pauses)} PAUSE / {len(resumes)} RESUME for a {beats}-beat packet with a gap before every beat; expected {beats-1} each")
        for k, p in enumerate(pauses):
            if d_hi32(p) != k + 1:
                self._fail(f"pause: PAUSE #{k} reports {d_hi32(p)} beats accepted, expected {k+1}")
        self.expect_only(got, {(int(PKT_STREAM), int(STREAM_START)), (int(PKT_STREAM), int(STREAM_PAUSE)),
                               (int(PKT_STREAM), int(STREAM_RESUME)), (int(PKT_COMPL), int(COMPL_STREAM_END))}, "pause")
        self.log.info(f"phase pause: {beats-1} PAUSE + {beats-1} RESUME for {beats-1} gaps of {gap} cycles")

    async def phase_stall(self):
        """Slave holds tready for a long stall: one Credit/BACKPRESSURE at the cycle threshold, one Timeout/HANDSHAKE at the microsecond timeout, then the beat completes."""
        stall = 3 * US_TICK_CYCLES          # 300 cycles
        self.dut.cfg_stall_threshold.value = 50
        self.dut.cfg_timeout_cnt.value = 2   # 2 microseconds; the stall spans it once
        self.take()
        self.slave.set_randomizer(FlexRandomizer({'ready_delay': ([(stall, stall)], [1])}))
        await self.beat(1, tid=4 & self.id_mask)
        await self.settle()
        self.slave.set_randomizer(FlexRandomizer({'ready_delay': ([(0, 0)], [1])}))
        self.dut.cfg_stall_threshold.value = 0
        self.dut.cfg_timeout_cnt.value = 0xFFFF
        got = self.take()
        cred = self.sel(got, PKT_CREDIT, CREDIT_BACKPRESSURE)
        tmo = self.sel(got, PKT_TIMEOUT, TMO_HANDSHAKE)
        if len(cred) != 1:
            self._fail(f"stall: {len(cred)} BACKPRESSURE packets for one stall, expected exactly 1")
        elif d_hi32(cred[0]) != 50 or d_lo32(cred[0]) != 50:
            self._fail(f"stall: BACKPRESSURE payload stall_cycles/threshold = {d_hi32(cred[0])}/{d_lo32(cred[0])}, expected 50/50")
        if len(tmo) != 1:
            self._fail(f"stall: {len(tmo)} HANDSHAKE timeouts for one stall, expected exactly 1")
        else:
            p = tmo[0]
            # age counts microsecond tick EDGES since the stall began, so age >= 2 is
            # reached after between one and two tick periods of stall
            if d_lo16(p) != 2 or d_age16(p) != 2 or d_hi32(p) < US_TICK_CYCLES or d_hi32(p) > 2 * US_TICK_CYCLES:
                self._fail(f"stall: HANDSHAKE payload cycles/age/cfg = {d_hi32(p)}/{d_age16(p)}/{d_lo16(p)}, expected {US_TICK_CYCLES}..{2*US_TICK_CYCLES}/2/2")
        if len(self.sel(got, PKT_COMPL, COMPL_STREAM_END)) != 1:
            self._fail("stall: the stalled beat should still complete once")
        self.expect_only(got, {(int(PKT_STREAM), int(STREAM_START)), (int(PKT_COMPL), int(COMPL_STREAM_END)),
                               (int(PKT_CREDIT), int(CREDIT_BACKPRESSURE)), (int(PKT_TIMEOUT), int(TMO_HANDSHAKE))}, "stall")
        self.log.info(f"phase stall: {stall}-cycle stall -> one BACKPRESSURE at 50 cycles, one HANDSHAKE timeout at 2 us, then the completion")

    async def phase_gap_timeout(self):
        """Master goes quiet inside a packet for longer than the timeout: one Timeout/PACKET, plus the PAUSE/RESUME pair."""
        gap = 3 * US_TICK_CYCLES
        self.dut.cfg_timeout_cnt.value = 2
        self.take()
        await self.beat(0, tid=5 & self.id_mask)
        self.master_gap(gap)
        await self.beat(1, tid=5 & self.id_mask)
        self.master_gap(0)
        await self.settle()
        self.dut.cfg_timeout_cnt.value = 0xFFFF
        got = self.take()
        tmo = self.sel(got, PKT_TIMEOUT, TMO_PACKET)
        if len(tmo) != 1:
            self._fail(f"gap: {len(tmo)} PACKET timeouts for one long gap, expected exactly 1")
        else:
            p = tmo[0]
            if d_hi32(p) != 1 or d_lo16(p) != 2 or d_age16(p) != 2:
                self._fail(f"gap: PACKET timeout payload beats/age/cfg = {d_hi32(p)}/{d_age16(p)}/{d_lo16(p)}, expected 1/2/2")
        if len(self.sel(got, PKT_STREAM, STREAM_PAUSE)) != 1 or len(self.sel(got, PKT_STREAM, STREAM_RESUME)) != 1:
            self._fail("gap: expected exactly one PAUSE and one RESUME around the gap")
        if len(self.sel(got, PKT_TIMEOUT, TMO_HANDSHAKE)) != 0:
            self._fail("gap: a source-side gap is not a handshake stall; HANDSHAKE timeout must not fire")
        self.expect_only(got, {(int(PKT_STREAM), int(STREAM_START)), (int(PKT_STREAM), int(STREAM_PAUSE)),
                               (int(PKT_STREAM), int(STREAM_RESUME)), (int(PKT_COMPL), int(COMPL_STREAM_END)),
                               (int(PKT_TIMEOUT), int(TMO_PACKET))}, "gap")
        self.log.info(f"phase gap: {gap}-cycle bubble inside a packet -> one PACKET timeout, one PAUSE/RESUME pair")

    async def phase_strb(self):
        """An all-zero TSTRB beat is an Error/STRB_INVALID only when the check is armed."""
        self.take()
        await self.beat(1, tid=6 & self.id_mask, strb=0)              # unarmed: silent
        await self.settle()
        got = self.take()
        if self.sel(got, PKT_ERROR, ERR_STRB_INVALID):
            self._fail("strb: STRB_INVALID reported with cfg_strb_check_enable=0")
        self.dut.cfg_strb_check_enable.value = 1
        await self.beat(0, tid=6 & self.id_mask)
        await self.beat(1, tid=6 & self.id_mask, strb=0)              # armed: beat 2 of the packet
        await self.settle()
        self.dut.cfg_strb_check_enable.value = 0
        got = self.take()
        err = self.sel(got, PKT_ERROR, ERR_STRB_INVALID)
        if len(err) != 1:
            self._fail(f"strb: {len(err)} STRB_INVALID packets for one zero-strobe beat, expected 1")
        elif d_hi32(err[0]) != 2:
            self._fail(f"strb: STRB_INVALID names beat {d_hi32(err[0])}, expected 2")
        if int(self.dut.error_count.value) < 1:
            self._fail("strb: error_count did not count the error packet")
        self.log.info("phase strb: silent unarmed, one STRB_INVALID at beat 2 armed")

    async def phase_valid_drop(self):
        """PROTOCOL VIOLATION, pins driven on purpose while both BFMs are idle (the observer test's precedent):
        TVALID asserted, no TREADY, TVALID withdrawn -> one Error/VALID_TIMING."""
        d = self.dut
        self.take()
        # park the slave so it will not take the beat: 'stall' holds tready low
        self.slave.set_ready_policy('stall')
        await self.settle(4)
        d.axis_tvalid.value = 1
        d.axis_tlast.value = 0
        for _ in range(3):
            await RisingEdge(d.aclk)
        d.axis_tvalid.value = 0
        await RisingEdge(d.aclk)
        self.slave.set_ready_policy('always')
        await self.settle(10)
        got = self.take()
        err = self.sel(got, PKT_ERROR, ERR_VALID_TIMING)
        if len(err) != 1:
            self._fail(f"valid_drop: {len(err)} VALID_TIMING packets for one withdrawn TVALID, expected 1")
        elif d_hi32(err[0]) < 2:
            self._fail(f"valid_drop: VALID_TIMING reports {d_hi32(err[0])} stall cycles before the drop, expected >= 2")
        self.expect_only(got, {(int(PKT_ERROR), int(ERR_VALID_TIMING))}, "valid_drop")
        self.log.info("phase valid_drop: one VALID_TIMING error for a withdrawn TVALID")

    async def phase_mask(self):
        """The type mask drops a class at the source: Stream masked, completions still flow."""
        self.take()
        d = self.dut
        d.cfg_axis_pkt_mask.value = 1 << int(PKT_STREAM)
        await self.send(2, tid=7 & self.id_mask)
        await self.settle()
        d.cfg_axis_pkt_mask.value = 0
        got = self.take()
        if self.sel(got, PKT_STREAM):
            self._fail("mask: Stream packets emitted with the Stream bit masked")
        if len(self.sel(got, PKT_COMPL, COMPL_STREAM_END)) != 1:
            self._fail("mask: the completion must still flow with only Stream masked")
        self.log.info("phase mask: Stream masked -> no Stream packets, the completion flows")

    async def phase_drop(self):
        """The monbus is held: the 4-deep queue fills, the rest is dropped and COUNTED, and the count is reported."""
        n = self.cfg['held']
        d = self.dut
        # only the two per-packet classes, so every issued event is accounted for
        d.cfg_stream_enable.value = 1
        d.cfg_channel_enable.value = 0
        d.cfg_credit_enable.value = 0
        self.take()
        self.mon.set_ready_randomizer(FlexRandomizer({'ready_delay': ([(400, 400)], [1])}))
        for i in range(n):
            await self.send(1, tid=i & self.id_mask)
        self.mon.set_ready_randomizer(FlexRandomizer({'ready_delay': ([(0, 0)], [1])}))
        await self.settle(900)
        d.cfg_channel_enable.value = 1
        d.cfg_credit_enable.value = 1
        got = self.take()
        issued = n                           # one-beat packets: STREAM_END only (START implied)
        delivered = len(self.sel(got, PKT_COMPL, COMPL_STREAM_END))
        drops = self.sel(got, PKT_ERROR, ERR_EVENT_DROPPED)
        reported = sum(p.data & 0xFFFF for p in drops)
        if not drops:
            self._fail("drop: no EVENT_DROPPED packet after the bus freed")
        elif delivered + reported != issued:
            self._fail(f"drop: {delivered} delivered + {reported} reported dropped (in {len(drops)} report(s)) != {issued} issued")
        elif reported == 0:
            self._fail("drop: the held bus lost nothing?")
        if delivered < 4:
            self._fail(f"drop: only {delivered} delivered -- the 4-deep queue should hold four events through a stall")
        self.expect_only(got, {(int(PKT_STREAM), int(STREAM_START)), (int(PKT_COMPL), int(COMPL_STREAM_END)),
                               (int(PKT_ERROR), int(ERR_EVENT_DROPPED))}, "drop")
        self.log.info(f"phase drop: {issued} events issued, {delivered} delivered, {reported} reported dropped in {len(drops)} report(s)")

    async def phase_clear(self):
        """clear while idle: every counter to zero, nothing emitted, busy low."""
        d = self.dut
        await self.settle(10)
        if int(d.busy.value) != 0:
            self._fail("clear: busy high while idle before clear")
        self.take()
        d.clear.value = 1
        await RisingEdge(d.aclk)
        d.clear.value = 0
        await self.settle(10)
        for name in ('packet_count', 'error_count', 'dropped_count', 'busy', 'in_packet'):
            if int(getattr(d, name).value) != 0:
                self._fail(f"clear: {name} = {int(getattr(d, name).value)} after clear")
        if self.take():
            self._fail("clear: packets emitted by an idle clear")
        # and the monitor still works afterwards
        await self.send(2, tid=1 & self.id_mask)
        await self.settle()
        got = self.take()
        if len(self.sel(got, PKT_COMPL, COMPL_STREAM_END)) != 1 or int(d.packet_count.value) != 1:
            self._fail("clear: the monitor did not resume cleanly after clear")
        self.log.info("phase clear: counters zero, nothing emitted, monitor live afterwards")

    async def phase_after(self):
        await self.settle(50)
        stray = self.take()
        if stray:
            self._fail(f"after: {len(stray)} stray packet(s) {[(p.pkt_type, p.event_code) for p in stray[:4]]}")
        if int(self.dut.busy.value) != 0:
            self._fail("after: busy still high with the stream idle and the monbus empty")

    async def run_suite(self):
        for phase in (self.phase_packets, self.phase_channel, self.phase_pause, self.phase_stall,
                      self.phase_gap_timeout, self.phase_strb, self.phase_valid_drop, self.phase_mask,
                      self.phase_drop, self.phase_clear, self.phase_after):
            self.mark_progress(phase.__name__)
            await phase()
        if self.errors:
            self.log.error(f"{len(self.errors)} violation(s):")
            for e in self.errors:
                self.log.error(f"  {e}")
        return not self.errors
