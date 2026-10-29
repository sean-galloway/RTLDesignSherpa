"""
jet_monlite testbench

Drop-and-count MonBus observer for the jet MESI L1 J7 metrics (Task 10,
MAS ch04).  The DUT is the jet_monlite_th unit harness: a programmable
stub drives the MSHR/WB/stall taps and a simple functional-side counter
increments on alloc pulses.  The observer is read-only; the suite proves
it emits the right event classes/payloads, the occupancy gauges track the
tap values, drops are counted and reported, and the observer never
perturbs the measured path.

Author: RTL Design Sherpa
Created: 2026-10-29
"""

import os
import random

import cocotb
from cocotb.triggers import RisingEdge, FallingEdge, Timer

from TBClasses.shared.tbbase import TBBase

# jet_pkg encodings (TB-side independent copy)
JET_CLS_RNSD, JET_CLS_RU, JET_CLS_CU = 0, 1, 2

# J7 event codes (must match jet_pkg::jet_event_t)
EV_MSHR_ALLOC = 0x10
EV_MSHR_MERGE = 0x11
EV_MSHR_RETIRE = 0x12
EV_MSHR_OCCUPANCY = 0x13
EV_WB_OCCUPANCY = 0x14
EV_STALL_TAG_FULL = 0x15

# house ocelus_common_pkg layout (independent copy)
PKT_TYPE_PERF = 0x4
PKT_TYPE_ERROR = 0x0
PROTOCOL_CORE = 0x4

EV_NAMES = {
    EV_MSHR_ALLOC: 'MSHR_ALLOC',
    EV_MSHR_MERGE: 'MSHR_MERGE',
    EV_MSHR_RETIRE: 'MSHR_RETIRE',
    EV_MSHR_OCCUPANCY: 'MSHR_OCCUPANCY',
    EV_WB_OCCUPANCY: 'WB_OCCUPANCY',
    EV_STALL_TAG_FULL: 'STALL_TAG_FULL',
}


def _parse_packet(pkt):
    return {
        'pkt_type': (pkt >> 124) & 0xF,
        'reserved': (pkt >> 109) & 0x7FFF,
        'protocol': (pkt >> 105) & 0xF,
        'event_code': (pkt >> 97) & 0xFF,
        'channel_id': (pkt >> 88) & 0x1FF,
        'agent_id': (pkt >> 72) & 0xFFFF,
        'unit_id': (pkt >> 64) & 0xFF,
        'data': pkt & ((1 << 64) - 1),
    }


class JetMonliteTB(TBBase):
    """Unit TB for jet_monlite: stub taps + MonBus scoreboard."""

    def __init__(self, dut, **kwargs):
        super().__init__(dut)
        self.SEED = self.convert_to_int(os.environ.get('SEED', '12345'))
        self.TEST_LEVEL = os.environ.get('TEST_LEVEL', 'gate').lower()
        self.MON_CFG = os.environ.get('MON_CFG', 'tap')
        random.seed(self.SEED)

        self.MSHR_COUNT = self.convert_to_int(
            os.environ.get('MSHR_COUNT', '8'))
        self.SETS = self.convert_to_int(os.environ.get('SETS', '128'))
        self.WAYS = self.convert_to_int(os.environ.get('WAYS', '4'))
        self.SET_W = (self.SETS - 1).bit_length()
        self.MW = (self.MSHR_COUNT - 1).bit_length()
        self.OCC_W = self.MW + 1
        self.WB_OCC_W = (4).bit_length()  # VICTIM_DEPTH+1 max

        self.pkt_log = []          # (cyc, parsed_packet, timestamp, head_cyc)
        self.q_trace = []          # (cyc, fired_classes, valid, ready)
        self.exp_events = []       # ordered expected events
        self.last_mshr_occ = 0
        self.last_wb_occ = 0
        self.mon_mode = 'free'
        self.checks = 0
        self.mismatches = 0
        self.packets = 0
        self.cyc = 0
        self.scenarios = {}
        self.alloc_cycle = {}

        self.log.info(f"JetMonliteTB mshr={self.MSHR_COUNT} sets={self.SETS} "
                      f"ways={self.WAYS} cfg={self.MON_CFG} "
                      f"level={self.TEST_LEVEL} seed={self.SEED}")

    # ------------------------------------------------------------------
    # mandatory TBBase hooks
    # ------------------------------------------------------------------
    async def setup_clocks_and_reset(self, period_ns=10):
        await self.start_clock('clk', freq=period_ns, units='ns')
        self._drive_idle()
        self.dut.monbus_ready.value = 1
        cocotb.start_soon(self._cycle_counter())
        cocotb.start_soon(self._time_driver())
        cocotb.start_soon(self._monbus_ready_driver())
        cocotb.start_soon(self._monbus_monitor())
        cocotb.start_soon(self._monbus_fired_probe())
        await self.assert_reset()
        await self.wait_clocks('clk', 3)
        await self.deassert_reset()
        await self.wait_clocks('clk', 1)

    async def _cycle_counter(self):
        while True:
            await RisingEdge(self.dut.clk)
            self.cyc += 1

    async def _time_driver(self):
        """Keep mon_time equal to the current cycle so packet timestamps
        match the cycle the event was presented."""
        while True:
            await FallingEdge(self.dut.clk)
            self.dut.mon_time.value = self.cyc

    async def assert_reset(self):
        self.dut.rst_n.value = 0

    async def deassert_reset(self):
        self.dut.rst_n.value = 1

    # ------------------------------------------------------------------
    # drive / monitor helpers
    # ------------------------------------------------------------------
    def _drive_idle(self):
        d = self.dut
        d.mshr_alloc_i.value = 0
        d.mshr_alloc_set_i.value = 0
        d.mshr_alloc_cls_i.value = 0
        d.mshr_alloc_idx_i.value = 0
        d.mshr_merge_i.value = 0
        d.mshr_merge_idx_i.value = 0
        d.mshr_merge_depth_i.value = 0
        d.mshr_retire_i.value = 0
        d.mshr_retire_idx_i.value = 0
        d.mshr_occupancy_i.value = 0
        d.wb_occupancy_i.value = 0
        d.ctrl_stall_i.value = 0
        d.ctrl_stall_reason_i.value = 0
        d.mon_time.value = 0

    async def _negedge_settled(self):
        await FallingEdge(self.dut.clk)
        await Timer(500, units='ps')

    async def _posedge_settled(self):
        await RisingEdge(self.dut.clk)
        await Timer(500, units='ps')

    def _score(self, what, got, exp):
        self.checks += 1
        if got != exp:
            self.mismatches += 1
            if self.mismatches <= 20:
                self.log.error(f"{what}: got {got} expected {exp}")

    def _score_packet_format(self, cyc, p, ts):
        lab = f"pkt@{cyc}"
        self._score(f"{lab} protocol CORE", p['protocol'], PROTOCOL_CORE)
        self._score(f"{lab} reserved zero", p['reserved'], 0)
        self._score(f"{lab} channel zero", p['channel_id'], 0)
        if p['event_code'] != 0x09:  # drop report
            self._score(f"{lab} pkt type Perf", p['pkt_type'], PKT_TYPE_PERF)
        else:
            self._score(f"{lab} dropped is Error", p['pkt_type'], PKT_TYPE_ERROR)

    async def _monbus_ready_driver(self):
        d = self.dut
        while True:
            await FallingEdge(d.clk)
            if self.mon_mode == 'free':
                d.monbus_ready.value = 1
            elif self.mon_mode == 'stall':
                d.monbus_ready.value = 0
            else:  # random
                d.monbus_ready.value = 1 if random.random() < 0.65 else 0

    async def _monbus_fired_probe(self):
        """Record which event classes the DUT fired each cycle (hierarchical
        probe into u_monlite).  Sample after the pulse helpers have set/cleared
        inputs (they act at negedge + 500 ps)."""
        d = self.dut.u_monlite
        while True:
            await FallingEdge(self.dut.clk)
            await Timer(700, units='ps')
            if not int(self.dut.rst_n.value):
                continue
            fired = []
            for i in range(6):
                if int(d.c_fire[i].value):
                    fired.append(int(d.c_code[i].value))
            self.q_trace.append(
                (self.cyc, tuple(fired),
                 int(self.dut.monbus_valid.value),
                 int(self.dut.monbus_ready.value)))

    async def _monbus_monitor(self):
        """Record every accepted MonBus packet."""
        d = self.dut
        prev_valid = 0
        prev_popped = 0
        head_cyc = 0
        while True:
            await self._negedge_settled()
            valid = int(d.monbus_valid.value)
            if valid:
                popped = prev_valid and int(d.monbus_ready.value)
                if not prev_valid or prev_popped:
                    head_cyc = self.cyc
            prev_valid = valid
            prev_popped = valid and int(d.monbus_ready.value)
            if valid and int(d.monbus_ready.value):
                pkt = int(d.monbus_packet.value)
                ts = int(d.monbus_timestamp.value)
                self.pkt_log.append((self.cyc, _parse_packet(pkt), ts,
                                     head_cyc))
                self.packets += 1

    # ------------------------------------------------------------------
    # expectation helpers
    # ------------------------------------------------------------------
    def _exp_alloc(self, set_idx, cls, occ_after):
        self.exp_events.append({
            'event': EV_MSHR_ALLOC,
            'data': ((set_idx & 0xFFFF)
                     | ((cls & 0x3) << 16)
                     | ((occ_after & 0x3F) << 18))})

    def _exp_merge(self, idx, depth, age):
        self.exp_events.append({
            'event': EV_MSHR_MERGE,
            'data': ((idx & ((1 << self.MW) - 1))
                     | ((depth & 0xFF) << self.MW)
                     | ((age & 0xFFFF) << (self.MW + 8)))})

    def _exp_retire(self, idx, occ_before, latency):
        self.exp_events.append({
            'event': EV_MSHR_RETIRE,
            'data': ((idx & ((1 << self.MW) - 1))
                     | ((occ_before & 0xFF) << 16)
                     | ((latency & 0xFFFF) << 24))})

    def _exp_mshr_occ(self, occ):
        self.exp_events.append({
            'event': EV_MSHR_OCCUPANCY,
            'data': occ & 0xFF})

    def _exp_wb_occ(self, occ):
        self.exp_events.append({
            'event': EV_WB_OCCUPANCY,
            'data': occ & 0xFF})

    def _exp_stall(self, duration):
        self.exp_events.append({
            'event': EV_STALL_TAG_FULL,
            'data': 5 | ((duration & 0xFF) << 8)})

    # ------------------------------------------------------------------
    # strict stream matcher (exact queue replay, like amber_monlite_tb)
    # ------------------------------------------------------------------
    def _strict_stream_match(self, label='', pkt_base=0, exp_base=0,
                             trace_base=0):
        from collections import deque
        truth = [cls for row in self.q_trace[trace_base:]
                 for cls in row[1]]
        model = self.exp_events[exp_base:]
        self._score(f"{label} firing class sequence == model",
                    truth, [e['event'] for e in model])

        events = []
        ti = 0
        for row in self.q_trace[trace_base:]:
            for cls in row[1]:
                if ti < len(model):
                    events.append((model[ti], row[0]))
                ti += 1

        q = deque()
        dropped = 0
        r_dropped = 0
        expect = []
        ei = 0
        for cyc, fired, valid, ready in (r[:4] for r in
                                         self.q_trace[trace_base:]):
            room = 4 - len(q)
            for j, _cls in enumerate(fired):
                if j < room:
                    if ei < len(events):
                        q.append((events[ei][0], events[ei][1], None))
                else:
                    dropped += 1
                    r_dropped += 1
                ei += 1
            if r_dropped != 0 and not fired and len(q) == 0:
                q.append((None, None, r_dropped))
                r_dropped = 0
            if valid and ready and q:
                ev, fcyc, rcnt = q.popleft()
                expect.append((ev, fcyc, cyc, rcnt))

        obs = self.pkt_log[pkt_base:]
        self._score(f"{label} predicted stream length", len(expect), len(obs))
        for k, ((ev, fcyc, pcyc, rcnt), (ocyc, op, ots, ohead)) in enumerate(
                zip(expect, obs)):
            self._score_packet_format(ocyc, op, ots)
            if rcnt is not None:
                self._score(f"{label} report count", op['event_code'], 0x09)
                self._score(f"{label} report value", op['data'] & 0xFF, rcnt)
                continue
            self._score(f"{label} class", op['event_code'], ev['event'])
            self._score(f"{label} payload", op['data'], ev['data'])
            self._score(f"{label} ts == firing cycle", ots, fcyc)
            self._score(f"{label} acceptance cycle", ocyc, pcyc)
        return dropped

    # ------------------------------------------------------------------
    # low-level tap drivers (one cycle pulse)
    # ------------------------------------------------------------------
    async def _pulse_alloc(self, set_idx, cls, idx):
        """One-cycle alloc pulse.  Returns the cycle on which the input was
        presented (matches the packet timestamp)."""
        d = self.dut
        await self._negedge_settled()
        cyc = self.cyc
        d.mshr_alloc_i.value = 1
        d.mshr_alloc_set_i.value = set_idx
        d.mshr_alloc_cls_i.value = cls
        d.mshr_alloc_idx_i.value = idx
        await self._negedge_settled()
        d.mshr_alloc_i.value = 0
        return cyc

    async def _pulse_merge(self, idx, depth):
        d = self.dut
        await self._negedge_settled()
        cyc = self.cyc
        d.mshr_merge_i.value = 1
        d.mshr_merge_idx_i.value = idx
        d.mshr_merge_depth_i.value = depth
        await self._negedge_settled()
        d.mshr_merge_i.value = 0
        return cyc

    async def _pulse_retire(self, idx):
        d = self.dut
        await self._negedge_settled()
        cyc = self.cyc
        d.mshr_retire_i.value = 1
        d.mshr_retire_idx_i.value = idx
        await self._negedge_settled()
        d.mshr_retire_i.value = 0
        return cyc

    async def _set_mshr_occ(self, occ):
        self.dut.mshr_occupancy_i.value = occ
        await self._negedge_settled()
        await RisingEdge(self.dut.clk)

    async def _set_wb_occ(self, occ):
        self.dut.wb_occupancy_i.value = occ
        await self._negedge_settled()
        await RisingEdge(self.dut.clk)

    async def _stall_cycle(self, reason=5):
        d = self.dut
        d.ctrl_stall_i.value = 1
        d.ctrl_stall_reason_i.value = reason
        await self._negedge_settled()
        await RisingEdge(d.clk)

    async def _unstall(self):
        d = self.dut
        d.ctrl_stall_i.value = 0
        d.ctrl_stall_reason_i.value = 0
        await self._negedge_settled()
        await RisingEdge(d.clk)

    # ------------------------------------------------------------------
    # scenarios
    # ------------------------------------------------------------------
    async def _s_event_counts(self):
        """Directed pulse sequence: expected alloc/merge/retire counts and
        payload fields.  mshr_occupancy_i is held at zero so occupancy-gauge
        events do not pollute the event-count scenario."""
        self._scenario('EventCounts')
        self.mon_mode = 'free'
        d = self.dut
        # hold occupancy at zero for the whole scenario
        d.mshr_occupancy_i.value = 0

        # alloc entry 0 -> occupancy-after = 1 (occ tap is held at 0)
        alloc0_cyc = await self._pulse_alloc(set_idx=5,
                                              cls=JET_CLS_RNSD, idx=0)
        self.alloc_cycle[0] = alloc0_cyc
        self._exp_alloc(5, JET_CLS_RNSD, 1)

        # alloc entry 1
        alloc1_cyc = await self._pulse_alloc(set_idx=7,
                                              cls=JET_CLS_RU, idx=1)
        self.alloc_cycle[1] = alloc1_cyc
        self._exp_alloc(7, JET_CLS_RU, 1)

        # merge on entry 0, depth 2
        merge0_cyc = await self._pulse_merge(idx=0, depth=2)
        self._exp_merge(0, 2, merge0_cyc - self.alloc_cycle[0])

        # retire entry 0, occupancy-before 0
        retire0_cyc = await self._pulse_retire(idx=0)
        self._exp_retire(0, 0, retire0_cyc - self.alloc_cycle[0])

        # retire entry 1, occupancy-before 0
        retire1_cyc = await self._pulse_retire(idx=1)
        self._exp_retire(1, 0, retire1_cyc - self.alloc_cycle[1])

        # drain the bus
        self.mon_mode = 'free'
        for _ in range(40):
            await self._negedge_settled()
        self._strict_stream_match('counts')
        seen = {p['event_code'] for _, p, _, _ in self.pkt_log}
        for ev in (EV_MSHR_ALLOC, EV_MSHR_MERGE, EV_MSHR_RETIRE):
            self._score(f"counts: {EV_NAMES[ev]} observed",
                        ev in seen, True)

    async def _s_occupancy_gauge_tracks(self):
        """MSHR and WB occupancy gauges emit on every change and the emitted
        value equals the tap value at all times."""
        self._scenario('OccupancyGaugeTracks')
        self.mon_mode = 'free'
        d = self.dut

        # MSHR occupancy sweep
        for occ in (0, 1, 3, 7, 4, 0):
            await self._set_mshr_occ(occ)
            if occ != self.last_mshr_occ:
                self._exp_mshr_occ(occ)
            self.last_mshr_occ = occ

        # WB occupancy sweep
        for occ in (0, 1, 2, 1, 0):
            await self._set_wb_occ(occ)
            if occ != self.last_wb_occ:
                self._exp_wb_occ(occ)
            self.last_wb_occ = occ

        # drain
        for _ in range(30):
            await self._negedge_settled()
        self._strict_stream_match('gauge')

        # spot-check: the last emitted gauge values equal the current taps
        last_mshr = 0
        last_wb = 0
        for _, p, _, _ in self.pkt_log:
            if p['event_code'] == EV_MSHR_OCCUPANCY:
                last_mshr = p['data'] & 0xFF
            elif p['event_code'] == EV_WB_OCCUPANCY:
                last_wb = p['data'] & 0xFF
        self._score('gauge: last MSHR occ == tap',
                    last_mshr, int(d.mshr_occupancy_i.value))
        self._score('gauge: last WB occ == tap',
                    last_wb, int(d.wb_occupancy_i.value))

    async def _s_drop_and_count(self):
        """Sustained backpressure forces drops; the drop report re-emits the
        count once the bus frees."""
        self._scenario('DropAndCount')
        d = self.dut
        n_pkt0 = len(self.pkt_log)
        n_exp0 = len(self.exp_events)
        trace0 = len(self.q_trace)

        self.mon_mode = 'stall'
        d.mshr_occupancy_i.value = 0
        # burst of 6 allocs (6 events) against a 4-deep queue -> drops
        for i in range(6):
            await self._pulse_alloc(set_idx=i, cls=JET_CLS_RNSD, idx=i)
            self._exp_alloc(i, JET_CLS_RNSD, 1)

        d_val = int(d.monbus_dropped.value)
        self._score('drop: count accumulated under stall', d_val > 0, True)

        # release
        self.mon_mode = 'free'
        for _ in range(60):
            await self._negedge_settled()
            if len(self.pkt_log) > n_pkt0 and \
                    self.pkt_log[-1][1]['event_code'] == 0x09:
                break

        drop_pkts = [p for _, p, _, _ in self.pkt_log[n_pkt0:]
                     if p['event_code'] == 0x09]
        self._score('drop: DROPPED packet emitted', len(drop_pkts) > 0, True)
        if drop_pkts:
            cnt = drop_pkts[0]['data'] & 0xFF
            self._score('drop: count matches tap sample', cnt, d_val)
            self._score('drop: nonzero count', cnt > 0, True)
        for _ in range(20):
            await self._negedge_settled()
        self._score('drop: tap cleared after report',
                    int(d.monbus_dropped.value), 0)
        dropped = self._strict_stream_match('drop', n_pkt0, n_exp0, trace0)
        self._score('drop: drops were forced', dropped > 0, True)

    async def _s_observer_transparency(self):
        """The observer is read-only: a free run and a backpressured run of
        the same stimulus produce identical functional_count."""
        self._scenario('ObserverTransparency')
        if self.MON_CFG != 'tap':
            return
        d = self.dut

        # run A: free bus
        ev0 = len(self.exp_events)
        pkt0 = len(self.pkt_log)
        trace0 = len(self.q_trace)
        count0 = int(d.functional_count.value)
        self.mon_mode = 'free'
        d.mshr_occupancy_i.value = 0
        BURST = 6
        for i in range(BURST):
            await self._pulse_alloc(set_idx=i, cls=JET_CLS_RNSD, idx=i)
            self._exp_alloc(i, JET_CLS_RNSD, 1)
        for _ in range(20):
            await self._negedge_settled()
        free_pkts = len(self.pkt_log) - pkt0
        free_count = int(d.functional_count.value) - count0
        self._strict_stream_match('trans free', pkt0, ev0, trace0)

        # run B: same stimulus, stalled bus; functional_count must advance
        # the same amount (the observer never stalls the alloc pulse).
        ev1 = len(self.exp_events)
        pkt1 = len(self.pkt_log)
        trace1 = len(self.q_trace)
        count1 = int(d.functional_count.value)
        self.mon_mode = 'stall'
        d.mshr_occupancy_i.value = 0
        for i in range(BURST):
            await self._pulse_alloc(set_idx=10 + i, cls=JET_CLS_RU, idx=i)
            self._exp_alloc(10 + i, JET_CLS_RU, 1)
        self.mon_mode = 'free'
        for _ in range(60):
            await self._negedge_settled()
        stalled_count = int(d.functional_count.value) - count1
        self._score('trans: functional_count identical under backpressure',
                    stalled_count, free_count)
        self._strict_stream_match('trans stalled', pkt1, ev1, trace1)
        self._score('trans: backpressured run dropped packets',
                    len(self.pkt_log) - pkt1 < free_pkts, True)

    async def _s_observer_silent(self):
        """USE_MONITOR=0: no packets, dropped_count tied zero, functional
        counter still works."""
        self._scenario('ObserverSilent')
        if self.MON_CFG != 'notap':
            return
        d = self.dut
        d.mshr_occupancy_i.value = 0
        for i in range(3):
            d.mon_time.value = int(d.mon_time.value) + 1
            await self._pulse_alloc(set_idx=i, cls=JET_CLS_RNSD, idx=i)
        for _ in range(20):
            await self._negedge_settled()
        self._score('silent: monbus_valid never asserted',
                    self.packets, 0)
        self._score('silent: drop count tied zero',
                    int(d.monbus_dropped.value), 0)
        self._score('silent: functional_count advanced',
                    int(d.functional_count.value), 3)

    # ------------------------------------------------------------------
    # run
    # ------------------------------------------------------------------
    async def run(self):
        if self.MON_CFG == 'notap':
            await self._s_observer_silent()
            return self.mismatches == 0

        await self._s_event_counts()
        await self._s_occupancy_gauge_tracks()
        if self.TEST_LEVEL in ('func', 'full'):
            await self._s_drop_and_count()
            await self._s_observer_transparency()
        return self.mismatches == 0

    def _scenario(self, name):
        self.scenarios[name] = {'checks': self.checks,
                                'mismatches': self.mismatches}

    def get_test_report(self):
        return {
            'checks': self.checks,
            'mismatches': self.mismatches,
            'packets': self.packets,
            'scenarios': self.scenarios,
        }
