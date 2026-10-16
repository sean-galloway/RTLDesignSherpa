# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: cxs_monlite_tb
# Purpose: Exact-packet testbenches for cxs_master_monlite / cxs_slave_monlite
#
# Documentation: docs/markdown/rtl-amba/monitor/cxs_monitor_lite.md
# Subsystem: amba
# Author: sean galloway
# Created: 2026-10-15
"""cxs_monitor_lite, judged through the two endpoint wrappers.

The endpoint traffic and its flit scoreboard are the base testbenches'
(CXSMasterTB / CXSSlaveTB: GAXI on the FUB side, the framework CXS BFM on the
link, a CXSMonitor on the wires). This layer adds a MonbusSlave on the ocelus
bus and owns the monitor's expectations.

Exact where the stimulus decides the answer:
  - Completion/PACKET_END, Error/ENDERROR and Channel/STREAM_CHANGE are
    predicted flit by flit from the packetizer's own output (the tap is the
    FUB handshake, so the order is the flit order), payload and channel_id
    included;
  - Stream/LINK_* must be the sequence ACTIVATE, UP, DEACTIVATE, DOWN
    repeated, with as many ACTIVATEs as the wire-level CXSMonitor counted;
  - the drop phase accounts for every issued event: delivered + reported
    dropped == issued.
Bounded where the BFM timing decides it (credit starvation, the three
timeouts): at least one of each, every payload self-consistent (a Credit
event fires exactly at the threshold; a timeout's age is at least the
configured microseconds), and nothing outside the phase's allowed set.
Errors (protocol / parity) are provoked last, because both flags are sticky.
"""

import os

from cocotb.triggers import ClockCycles, RisingEdge

from CocoTBFramework.components.cxs import CXSCntl
from CocoTBFramework.components.shared.flex_randomizer import FlexRandomizer
from TBClasses.amba.amba_random_configs import AXI_RANDOMIZER_CONFIGS
from TBClasses.cxs.cxs_master_tb import CXSMasterTB
from TBClasses.cxs.cxs_tb_common import RX_PROFILES
from TBClasses.cxs.cxs_slave_tb import CXSSlaveTB
from TBClasses.monbus.monbus_slave import MonbusSlave
from TBClasses.monbus.monbus_types import (CXSChannelCode, CXSCompletionCode, CXSCreditCode,
                                           CXSErrorCode, CXSStreamCode, CXSTimeoutCode, PktType,
                                           ProtocolType)

PT_ERR, PT_TMO, PT_COMPL = int(PktType.PktTypeError), int(PktType.PktTypeTimeout), int(PktType.PktTypeCompletion)
PT_CREDIT, PT_CHAN, PT_STREAM = int(PktType.PktTypeCredit), int(PktType.PktTypeChannel), int(PktType.PktTypeStream)
TIMEOUT_US = 2                 # 200 cycles at the 100 MHz the wrapper is built for
STALL_THRESHOLD = 8            # cycles
UNIT_ID, AGENT_ID = 0x0A, 0x00C0


class _CXSMonliteMixin:
    """Monitor expectations shared by both roles. The host class provides
    the traffic (run_phase) and the role-specific stimulus hooks."""

    ROLE = None

    def _init_monlite(self):
        self.mbus = None
        self.mon_errors = []
        self._prev_stream = None       # stream of the last flit the monitor saw
        self._pkts_total = 0           # packets ended, as the monitor counts them

    # ---- configuration ----------------------------------------------------
    def _monlite_pins(self):
        d = self.dut
        d.cam_clear.value = 0
        d.cfg_monitor_enable.value = 1
        for n in ('cfg_error_enable', 'cfg_compl_enable', 'cfg_channel_enable', 'cfg_stream_enable'):
            getattr(d, n).value = 1
        d.cfg_timeout_enable.value = 1
        d.cfg_credit_enable.value = 0
        d.cfg_timeout_cycles.value = 0             # never
        d.cfg_freq_sel.value = 0                   # LUT entry 0 = the 100 MHz the wrapper is built for
        d.cfg_cxs_pkt_mask.value = 0
        d.cfg_stall_threshold.value = 0
        d.i_mon_time.value = 0

    async def start_monbus(self):
        self.mbus = MonbusSlave(dut=self.dut, title="MonBus", prefix="", clock=self.dut.aclk,
                                bus_name="monbus", pkt_prefix="", log=self.log)
        self.mbus.set_ready_randomizer(FlexRandomizer({'ready_delay': ([(0, 0)], [1])}))

    # ---- helpers ----------------------------------------------------------
    def _mfail(self, msg):
        self.log.error(msg)
        self.mon_errors.append(msg)

    def take(self):
        got = list(self.mbus.received_packets)
        self.mbus.clear_received_packets()
        # every link event, whichever phase's window it lands in
        self.link_events += [p for p in got if p.pkt_type == PT_STREAM]
        for p in got:
            if p.protocol != ProtocolType.PROTOCOL_CXS or p.unit_id != UNIT_ID or p.agent_id != AGENT_ID:
                self._mfail(f"packet with protocol/unit/agent {p.protocol}/{p.unit_id:#x}/{p.agent_id:#x}")
        return got

    @staticmethod
    def sel(got, ptype, code=None):
        return [p for p in got if p.pkt_type == ptype and (code is None or p.event_code == int(code))]

    def expect_only(self, got, allowed, where):
        bad = [p for p in got if (p.pkt_type, p.event_code) not in allowed]
        if bad:
            self._mfail(f"{where}: unexpected packets "
                        f"{[(p.pkt_type, p.event_code, hex(p.data)) for p in bad[:4]]}")

    async def drain(self, cycles=60):
        """Let the endpoint, the monitor's event stage and its queue empty:
        monbus_valid low for 20 consecutive cycles (a drop report is pushed
        only once the queue has emptied, so a single low cycle is not idle)."""
        await ClockCycles(self.dut.aclk, cycles)
        quiet = 0
        for _ in range(5000):
            quiet = 0 if int(self.dut.monbus_valid.value) else quiet + 1
            if quiet >= 20:
                break
            await RisingEdge(self.dut.aclk)

    def stream_of(self, flit):
        cfg = self.cfg
        return ((flit.get('prcltype') & 7) if cfg.has_prcltype else 0,
                flit.get('srcid') if cfg.srcid_width else 0,
                flit.get('tgtid') if cfg.tgtid_width else 0)

    def predict(self, flits):
        """The PACKET_END / ENDERROR / STREAM_CHANGE packets these flits must
        produce, in order: lists of (data, channel_id)."""
        cfg = self.cfg
        compl, enderr, chan = [], [], []
        for f in flits:
            if cfg.is_lite:
                ends, errs = 1, 0
            else:
                c = CXSCntl.decode(cfg, f.get('cntl'))
                ends, errs = len(c.ends), sum(c.end_errors)
            prcl, src, tgt = self.stream_of(f)
            s24 = (prcl << 16) | (src << 8) | tgt
            ch = ((prcl & 7) << 6) | (tgt & 0x3F)
            self._pkts_total += ends
            if ends:
                compl.append(((s24 << 40) | (ends << 32) | self._pkts_total, ch))
            if errs:
                enderr.append(((errs << 56) | (ends << 48) | self._pkts_total, ch))
            if self._prev_stream is not None and s24 != self._prev_stream:
                chan.append(((self._prev_stream << 40) | (s24 << 8), ch))
            self._prev_stream = s24
        return compl, enderr, chan

    def compare(self, got_pkts, want, where):
        """Delivered packets must be an IN-ORDER subsequence of the
        prediction, payload and channel exact. The lite queues two events a
        cycle and drops-and-counts the rest (a flit can raise PACKET_END,
        ENDERROR and STREAM_CHANGE at once), so a missing prediction is
        legal here -- the phase's accounting (delivered + reported == issued)
        is what proves nothing went missing uncounted."""
        got = [(p.data, p.channel_id) for p in got_pkts]
        it = iter(want)
        for k, g in enumerate(got):
            if not any(g == w for w in it):
                self._mfail(f"{where}: delivered #{k} {g} is not in the prediction (in order); "
                            f"{len(got)} delivered of {len(want)} predicted")
                return

    def account(self, got, predicted_n, where):
        delivered = len(self.sel(got, PT_COMPL)) + len(self.sel(got, PT_CHAN)) + \
                    len(self.sel(got, PT_ERR, CXSErrorCode.CXS_ERR_ENDERROR))
        reported = sum(p.data & 0xFFFF for p in self.sel(got, PT_ERR, CXSErrorCode.CXS_ERR_EVENT_DROPPED))
        if delivered + reported != predicted_n:
            self._mfail(f"{where}: {delivered} delivered + {reported} reported dropped != {predicted_n} issued")
        return delivered, reported

    # ---- phases -----------------------------------------------------------
    async def mphase_traffic(self, name, count, **kw):
        """Flit-exact: completions, ENDERRORs, stream changes."""
        start = len(self.expected)
        ok = await self.run_phase(name, count, **kw)
        await self.drain()
        got = self.take()
        compl, enderr, chan = self.predict(self.expected[start:])
        self.compare(self.sel(got, PT_COMPL, CXSCompletionCode.CXS_COMPL_PACKET_END), compl, f"{name} PACKET_END")
        self.compare(self.sel(got, PT_ERR, CXSErrorCode.CXS_ERR_ENDERROR), enderr, f"{name} ENDERROR")
        self.compare(self.sel(got, PT_CHAN, CXSChannelCode.CXS_CHAN_STREAM_CHANGE), chan, f"{name} STREAM_CHANGE")
        delivered, reported = self.account(got, len(compl) + len(enderr) + len(chan), name)
        self.expect_only(got, {(PT_COMPL, 0), (PT_ERR, int(CXSErrorCode.CXS_ERR_ENDERROR)), (PT_CHAN, 0),
                               (PT_ERR, int(CXSErrorCode.CXS_ERR_EVENT_DROPPED))}
                         | {(PT_STREAM, c) for c in range(4)}, name)
        self.log.info(f"monitor {name}: predicted {len(compl)} PACKET_END + {len(enderr)} ENDERROR + "
                      f"{len(chan)} STREAM_CHANGE; {delivered} delivered in order, {reported} reported dropped")
        return ok

    async def mphase_link(self):
        """Idle deactivation then reactivation: the link events in order."""
        if not self.cfg.link_control:
            return True
        ok = await self.run_idle_deactivate()
        await self.drain()
        return ok and await self.mphase_traffic('relink', 3)

    def check_link_sequence(self):
        codes = [p.event_code for p in self.link_events]
        if not self.cfg.link_control:
            if codes:
                self._mfail(f"link: {len(codes)} Stream events with no link control")
            return
        want = [i % 4 for i in range(len(codes))]
        if codes != want:
            self._mfail(f"link: Stream codes {codes[:12]} are not ACTIVATE,UP,DEACTIVATE,DOWN repeated")
        acts = codes.count(int(CXSStreamCode.CXS_STREAM_LINK_ACTIVATE))
        wire = self.mon.stats['activations']
        if acts != wire:
            self._mfail(f"link: {acts} LINK_ACTIVATE packets, the wire monitor saw {wire} activations")
        if acts == 0:
            self._mfail("link: the link never came up -- nothing proved")
        self.log.info(f"monitor link: {len(codes)} Stream events, {acts} full cycles, sequence exact")

    async def mphase_credit(self):
        """Starvation and FUB backpressure with an 8-cycle threshold."""
        d = self.dut
        d.cfg_stall_threshold.value = STALL_THRESHOLD
        d.cfg_credit_enable.value = 1
        self.take()
        await self.starve_traffic(self.cfg_counts // 2 + 2)
        await self.drain(200)
        d.cfg_credit_enable.value = 0
        got = self.take()
        self.predict(self.expected[self._credit_mark:])     # keep the stream model in step
        starved = self.sel(got, PT_CREDIT, CXSCreditCode.CXS_CREDIT_STARVED)
        bp = self.sel(got, PT_CREDIT, CXSCreditCode.CXS_CREDIT_BACKPRESSURE)
        for p in starved + bp:
            if (p.data >> 32, p.data & 0xFFFF_FFFF) != (STALL_THRESHOLD, STALL_THRESHOLD):
                self._mfail(f"credit: payload {p.data:#x} is not {{threshold, threshold}}")
        if not starved:
            self._mfail("credit: no CREDIT_STARVED with the credit pool starved")
        if not bp:
            self._mfail("credit: no CREDIT_BACKPRESSURE with the FUB blocked")
        self.log.info(f"monitor credit: {len(starved)} STARVED, {len(bp)} BACKPRESSURE, payloads exact")

    def _check_timeouts(self, got, code, where):
        tmo = self.sel(got, PT_TMO, code)
        for p in tmo:
            age, cfg = (p.data >> 16) & 0xFFFF, p.data & 0xFFFF
            if cfg != TIMEOUT_US or age < TIMEOUT_US:
                self._mfail(f"{where}: payload age {age} cfg {cfg}, expected cfg {TIMEOUT_US} and age >= it")
        if not tmo:
            self._mfail(f"{where}: no timeout packet")
        return tmo

    async def mphase_timeouts(self):
        d = self.dut
        d.cfg_timeout_cycles.value = TIMEOUT_US
        allowed = {(PT_COMPL, 0), (PT_ERR, int(CXSErrorCode.CXS_ERR_ENDERROR)), (PT_CHAN, 0),
                   (PT_ERR, int(CXSErrorCode.CXS_ERR_EVENT_DROPPED))} | {(PT_STREAM, c) for c in range(4)}
        # credit
        self.take()
        mark = len(self.expected)
        await self.credit_timeout_traffic()
        await self.drain(600)
        got = self.take()
        self.predict(self.expected[mark:])
        t = self._check_timeouts(got, CXSTimeoutCode.CXS_TIMEOUT_CREDIT, "timeout CREDIT")
        self.expect_only(got, allowed | {(PT_TMO, 0), (PT_TMO, 2)}, "timeout CREDIT")
        self.log.info(f"monitor timeout CREDIT: {len(t)}")
        # packet gap
        if not self.cfg.is_lite:
            mark = len(self.expected)
            await self.packet_timeout_traffic()
            await self.drain(600)
            got = self.take()
            self.predict(self.expected[mark:])
            t = self._check_timeouts(got, CXSTimeoutCode.CXS_TIMEOUT_PACKET, "timeout PACKET")
            for p in t:
                if (p.data >> 32) < 1:
                    self._mfail(f"timeout PACKET: {p.data >> 32} flits in the open packet")
            self.expect_only(got, allowed | {(PT_TMO, 2)}, "timeout PACKET")
            self.log.info(f"monitor timeout PACKET: {len(t)}")
        # stuck handshake
        if self.cfg.link_control:
            ok = await self.run_idle_deactivate()
            await self.drain()
            mark = len(self.expected)
            await self.link_timeout_traffic()
            await self.drain()
            got = self.take()
            self.predict(self.expected[mark:])
            t = self._check_timeouts(got, CXSTimeoutCode.CXS_TIMEOUT_LINK, "timeout LINK")
            if len(t) != 1 or ((t[0].data >> 32) & 0x3) != 0b10:
                self._mfail(f"timeout LINK: {len(t)} packets, want exactly one naming ACTIVATE")
            self.expect_only(got, allowed | {(PT_TMO, 1)}, "timeout LINK")
            self.log.info("monitor timeout LINK: one, in ACTIVATE")
            if not ok:
                self._mfail("timeout LINK: could not take the link down first")
        d.cfg_timeout_cycles.value = 0

    async def mphase_mask(self):
        self.dut.cfg_cxs_pkt_mask.value = 1 << PT_COMPL
        mark = len(self.expected)
        await self.run_phase('mask', 4)
        await self.drain()
        self.dut.cfg_cxs_pkt_mask.value = 0
        got = self.take()
        _, enderr, chan = self.predict(self.expected[mark:])
        if self.sel(got, PT_COMPL):
            self._mfail("mask: Completion packets with the Completion bit masked")
        self.compare(self.sel(got, PT_CHAN, 0), chan, "mask STREAM_CHANGE still flows")
        self.compare(self.sel(got, PT_ERR, CXSErrorCode.CXS_ERR_ENDERROR), enderr, "mask ENDERROR still flows")
        self.account(got, len(enderr) + len(chan), "mask")
        self.log.info("monitor mask: Completion masked, the other classes flow")

    async def mphase_drop(self):
        """Monbus held: every issued event is delivered or reported dropped."""
        self.mbus.set_ready_randomizer(FlexRandomizer({'ready_delay': ([(600, 600)], [1])}))
        mark = len(self.expected)
        self.take()
        await self.run_phase('drop', 12)
        self.mbus.set_ready_randomizer(FlexRandomizer({'ready_delay': ([(0, 0)], [1])}))
        await self.drain(1500)
        got = self.take()
        compl, enderr, chan = self.predict(self.expected[mark:])
        links = self.sel(got, PT_STREAM)
        issued = len(compl) + len(enderr) + len(chan) + len(links)
        drops = self.sel(got, PT_ERR, CXSErrorCode.CXS_ERR_EVENT_DROPPED)
        reported = sum(p.data & 0xFFFF for p in drops)
        delivered = len(got) - len(drops) - len(links)
        if delivered + reported != len(compl) + len(enderr) + len(chan):
            self._mfail(f"drop: {delivered} delivered + {reported} reported != {issued - len(links)} issued")
        if not drops or reported == 0:
            self._mfail("drop: the held bus lost nothing -- the phase proved nothing")
        if delivered < 4:
            self._mfail(f"drop: {delivered} delivered, the 4-deep queue holds four")
        self.log.info(f"monitor drop: {issued - len(links)} issued, {delivered} delivered, {reported} reported dropped")

    async def mphase_clear(self):
        d = self.dut
        await self.drain()
        self.take()
        d.cam_clear.value = 1
        await RisingEdge(d.aclk)
        d.cam_clear.value = 0
        await ClockCycles(d.aclk, 5)
        for n in ('packet_count', 'flit_count', 'error_count', 'dropped_count'):
            if int(getattr(d, n).value):
                self._mfail(f"clear: {n} = {int(getattr(d, n).value)}")
        if self.take():
            self._mfail("clear: an idle clear emitted packets")
        self._prev_stream, self._pkts_total = None, 0
        await self.mphase_traffic('after-clear', 3)
        if int(d.packet_count.value) != self._pkts_total:
            self._mfail(f"clear: packet_count {int(d.packet_count.value)} != {self._pkts_total} after clear")

    async def mphase_errors(self):
        """Sticky flags, provoked last: a malformed CXSCNTL -> PROTOCOL;
        a corrupted check bit -> PARITY. Each reported once."""
        d = self.dut
        self.take()
        provoked = []
        if not self.cfg.is_lite:
            await self.send_bad_cntl()
            provoked.append(int(CXSErrorCode.CXS_ERR_PROTOCOL))
        if self.cfg.check:
            await self.provoke_parity()
            provoked.append(int(CXSErrorCode.CXS_ERR_PARITY))
        await self.drain(200)
        got = self.take()
        for code in provoked:
            n = len(self.sel(got, PT_ERR, code))
            if n != 1:
                self._mfail(f"errors: {n} packets for error code {code}, want exactly one (sticky flag rose once)")
        if provoked and int(d.error_count.value) < len(provoked):
            self._mfail(f"errors: error_count {int(d.error_count.value)} < {len(provoked)}")
        self.log.info(f"monitor errors: provoked {provoked}")

    async def mphase_after(self):
        await self.drain(80)
        stray = [p for p in self.take() if p.pkt_type != PT_STREAM]
        if stray:
            self._mfail(f"after: {len(stray)} stray packets {[(p.pkt_type, p.event_code) for p in stray[:4]]}")

    async def run_monlite_suite(self):
        n = self.cfg_counts
        ok = await self.mphase_traffic('fast', n)
        ok = await self.mphase_traffic('gappy', n, **self.gappy_kw) and ok
        ok = await self.mphase_link() and ok
        self._credit_mark = len(self.expected)
        await self.mphase_credit()
        await self.mphase_timeouts()
        await self.mphase_mask()
        await self.mphase_drop()
        await self.mphase_clear()
        passed = self.check() and ok          # the endpoint's own scoreboard, before the bad flit
        self.check_link_sequence()
        await self.mphase_errors()
        await self.mphase_after()
        for e in self.mon_errors[:20]:
            self.log.error(e)
        return passed and not self.mon_errors


COUNTS = {'gate': 10, 'func': 30, 'full': 80}


def _level():
    lvl = os.environ.get('TEST_LEVEL', 'gate').lower()
    return lvl if lvl in COUNTS else 'gate'


class CXSMasterMonliteTB(_CXSMonliteMixin, CXSMasterTB):
    ROLE = 'master'

    def __init__(self, dut):
        super().__init__(dut)
        self._init_monlite()
        self.link_events = []
        self.cfg_counts = COUNTS[_level()]
        self.gappy_kw = {'rx_profile': 'gappy', 'fub_profile': 'fast'}

    def _pre_reset(self):
        super()._pre_reset()
        self._monlite_pins()

    async def setup_clocks_and_reset(self):
        await super().setup_clocks_and_reset()
        await self.start_monbus()

    async def starve_traffic(self, count):
        # more flits than the credits already held (a full idle pool), or the
        # pool never empties and nothing starves
        count = max(count, self.cfg.max_credit + 12)
        await self.run_phase('credit', count, 'starve', buffer_depth=1, fub_profile='backtoback')
        self.rx.buffer_depth = self.cfg.max_credit

    async def credit_timeout_traffic(self):
        self.rx.set_randomizer(FlexRandomizer({'grant_gap': ([(0, 0)], [1]),
                                               'drain_gap': ([(320, 400)], [1]),
                                               'ack_delay': ([(0, 0)], [1])}))
        self.rx.buffer_depth = 1
        await self._send_custom(self.cfg.max_credit + 3, None)     # past the held credits
        self.rx.buffer_depth = self.cfg.max_credit
        self.rx.set_randomizer(FlexRandomizer(RX_PROFILES['fast']))   # leave no slow drain behind

    async def packet_timeout_traffic(self):
        self.fub.set_randomizer(FlexRandomizer({'valid_delay': ([(300, 320)], [1])}))
        await self._send_custom(2, min_flits=3)
        self.fub.set_randomizer(FlexRandomizer(AXI_RANDOMIZER_CONFIGS['fixed']['master']))

    async def link_timeout_traffic(self):
        self.rx.rx_enable = False
        sent = self._queue_custom(1)
        await self.fub.send_burst(sent)
        await ClockCycles(self.dut.aclk, 400)      # stuck in ACTIVATE for 4 us
        self.rx.rx_enable = True
        await self.wait_until(lambda: self.rx.stats['flits'] >= len(self.expected), 4000, "link timeout flits")

    def _queue_custom(self, count, min_flits=None):
        pkts = self.make_packets(count)
        if min_flits:
            from CocoTBFramework.components.cxs import CXSPacket
            pkts = [CXSPacket(bytes((i + k) & 0xFF for k in range(self.cfg.flit_bytes * min_flits)))
                    for i in range(count)]
        flits = self.packetize(pkts)
        self.expected += flits
        self.packets += pkts
        return [self.to_gaxi(f) for f in flits]

    async def _send_custom(self, count, min_flits=None):
        before = len(self.expected)
        await self.fub.send_burst(self._queue_custom(count, min_flits))
        await self.wait_until(lambda: self.rx.stats['flits'] >= len(self.expected),
                              800 * (len(self.expected) - before) + 2000, "custom traffic")

    async def send_bad_cntl(self):
        """START = 0b10 (not a thermometer code): the core's cntl tracker flags it."""
        pkt = self.to_gaxi(self.expected[-1])
        pkt.cntl = 0b10
        await self.fub.send_burst([pkt])
        await ClockCycles(self.dut.aclk, 40)

    async def provoke_parity(self):
        self.rx.inject_check_error('crdgnt', 1)
        await ClockCycles(self.dut.aclk, 20)


class CXSSlaveMonliteTB(_CXSMonliteMixin, CXSSlaveTB):
    ROLE = 'slave'

    def __init__(self, dut):
        super().__init__(dut, rx_fifo_depth=int(os.environ.get('RX_FIFO_DEPTH', '0')) or None)
        self._init_monlite()
        self.link_events = []
        self.cfg_counts = COUNTS[_level()]
        self.gappy_kw = {'tx_profile': 'gappy', 'fub_profile': 'constrained'}

    def _pre_reset(self):
        super()._pre_reset()
        self._monlite_pins()

    async def setup_clocks_and_reset(self):
        await super().setup_clocks_and_reset()
        await self.start_monbus()

    async def starve_traffic(self, count):
        # a consumer slower than the link, and more flits than the FIFO holds
        await self.run_phase('credit', max(count, self.rx_fifo_depth + 6),
                             fub_profile={'ready_delay': ([(14, 20)], [1])})

    async def credit_timeout_traffic(self):
        self.fub.set_randomizer(FlexRandomizer({'ready_delay': ([(320, 400)], [1])}))
        await self._send_custom(self.rx_fifo_depth + 2)
        self.fub.set_randomizer(FlexRandomizer(AXI_RANDOMIZER_CONFIGS['fixed']['slave']))

    async def packet_timeout_traffic(self):
        self.tx.set_randomizer(FlexRandomizer({'valid_gap': ([(300, 320)], [1])}))
        await self._send_custom(2, min_flits=3)
        self.tx.set_randomizer(FlexRandomizer({'valid_gap': ([(0, 0)], [1])}))

    async def link_timeout_traffic(self):
        self.dut.cfg_rx_enable.value = 0
        for f in self._queue_custom(1):
            self.tx.send_flit(f)
        await ClockCycles(self.dut.aclk, 400)
        self.dut.cfg_rx_enable.value = 1
        await self.wait_until(lambda: len(self.got) >= len(self.expected), 4000, "link timeout flits")

    def _queue_custom(self, count, min_flits=None):
        pkts = self.make_packets(count)
        if min_flits:
            from CocoTBFramework.components.cxs import CXSPacket
            pkts = [CXSPacket(bytes((i + k) & 0xFF for k in range(self.cfg.flit_bytes * min_flits)))
                    for i in range(count)]
        flits = self.packetize(pkts)
        self.expected += flits
        self.packets += pkts
        return flits

    async def _send_custom(self, count, min_flits=None):
        before = len(self.expected)
        for f in self._queue_custom(count, min_flits):
            self.tx.send_flit(f)
        await self.wait_until(lambda: len(self.got) >= len(self.expected),
                              800 * (len(self.expected) - before) + 2000, "custom traffic")

    async def send_bad_cntl(self):
        """START = 0b10 on the link: the receiver's cntl tracker flags it."""
        from CocoTBFramework.components.cxs import CXSFlit
        bad = CXSFlit(self.cfg, data=0, cntl=0b10)
        self.tx.send_flit(bad)
        self.expected.append(bad)          # it reaches the FUB like any flit
        await ClockCycles(self.dut.aclk, 40)

    async def provoke_parity(self):
        self.tx.inject_check_error('data', 1)
        for f in self._queue_custom(1):
            self.tx.send_flit(f)
        await ClockCycles(self.dut.aclk, 40)
