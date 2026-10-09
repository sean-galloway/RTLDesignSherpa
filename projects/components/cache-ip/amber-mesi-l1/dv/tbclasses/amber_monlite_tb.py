# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/seang-galloway/RTLDesignSherpa
#
# Module: AmberMonliteTB
# Purpose: Testbench for the amber_monlite drop-and-count MonBus observer
# (Task 8, MAS ch04)

"""
amber_monlite testbench

Drop-and-count MonBus observer bring-up (Task 8, DECISION D8 / MAS ch04):
the DUT closure is the harness amber_monlite_th -- the amber_frontend_th
closure (REAL amber_cpu_frontend + REAL amber_control + landed arrays)
plus amber_monlite tapped at the MAS ch04 emit points. The observer drives
nothing in the closure; its only outputs are the monbus handshake pins.

What this suite pins:
  * Table 4.1.1 event classes: every class observed at least once per run,
    emitted at the MAS ch04 emit point, payload fields per the documented
    packing (directed EventClassMatrix with hand-computed expectations)
  * house packet format on EVERY accepted packet: PktTypePerf (Error for
    the drop report), PROTOCOL_CORE, designer-allocated AGENT_ID/UNIT_ID,
    reserved == 0, timestamp == the side-band at emission
  * drop-and-count (MAS ch04/02): sustained monbus_ready low forces drops;
    the saturating 8-bit count is re-emitted as Error/AMBER_EV_DROPPED
    once the queue drains; accounting identity
    received == expected - dropped + n_dropped_packets over the run
  * causal order per transaction (MISS < FILL_START < FILL_END;
    EVICT <= DRAIN_START < DRAIN_END; HIT packets aligned with hit
    service) and per-class counts equal to the transaction model
  * present-vs-absent (Review Focus 5, D8 measurement integrity): the
    same seeded stimulus run twice -- monbus free vs monbus
    backpressured -- produces cycle-identical frontend behavior (accept
    cycles, response cycles, response data); only the packet stream
    differs. The USE_MONITOR=0 configuration (notap cells) ties the
    observer off (house gen_no_monitor idiom) and is asserted silent.

Snoop traffic is issued at quiescence (between CPU transactions): the
mid-transaction snoop compositions (pending-fill bypass, victim buffer)
are proven by the control/snoop suites; this suite scores the observer.

Golden models carried here (independent copies, kmap-TB rule):
  memory-side line content   self.mem (inherited)
  per-line MESI state        self.line_state
  (set, way) -> line tag     self.tags / self.slot_state
  true-LRU victim prediction LruModel (ported from the control TB)
  snoop CRRESP/next-state    dv/golden/amber_fsm_oracle decode helpers
                               (the project's pinned golden)

Levels (TEST_LEVEL) x MON_CFG ({tap, notap} via the wrapper's mon_mode):
  gate  -- EventClassMatrix + packet format + short present-vs-absent
  func  -- + directed DropAndCount + full present-vs-absent
  full  -- + randomized soak (random monbus backpressure) + accounting
           identity (seeds pinned by the repo-root conftest)

Author: RTL Design Sherpa
Created: 2026-10-08
"""

import os
import random

import cocotb
from cocotb.triggers import RisingEdge, FallingEdge, Timer

from TBClasses.shared.tbbase import TBBase

from projects.components.cache_ip.amber_mesi_l1.dv.golden.amber_fsm_oracle import (
    SNOOP_CODES,
    _decode_crresp,
    _decode_next,
)

from projects.components.cache_ip.amber_mesi_l1.dv.tbclasses.amber_frontend_tb import (
    AmberFrontendTB,
    ST_IDLE, ST_INIT, ST_LOOKUP, ST_HIT_RD, ST_HIT_WR, ST_MISS_VICTIM,
    ST_MISS_DRAIN, ST_MISS_FILL, ST_FILL_WRITE, ST_REPLAY, ST_SNOOP,
    ST_ERROR,
    ACE_READ_SHARED, ACE_READ_UNIQUE, ACE_CLEAN_UNIQUE,
)


# ---------------------------------------------------------------------------
# monitor_common_pkg layout + amber event encoding (independent copies for
# scoring; the RTL consumes the packages directly)
# ---------------------------------------------------------------------------
MONBUS_WIDTH = 128
PKT_TYPE_PERF = 0x4
PKT_TYPE_ERROR = 0x0
PROTOCOL_CORE = 0x4
AGENT_ID = 0x00A0          # designer-allocated for amber (module default)
UNIT_ID = 0x01             # amber_monlite sub-unit

EV_HIT, EV_MISS, EV_SNOOP, EV_EVICT, EV_TRANSITION, \
    EV_FILL_START, EV_FILL_END, EV_DRAIN_START, EV_DRAIN_END, \
    EV_DROPPED = range(10)

EV_NAMES = {EV_HIT: 'HIT', EV_MISS: 'MISS', EV_SNOOP: 'SNOOP',
            EV_EVICT: 'EVICT', EV_TRANSITION: 'TRANSITION',
            EV_FILL_START: 'FILL_START', EV_FILL_END: 'FILL_END',
            EV_DRAIN_START: 'DRAIN_START', EV_DRAIN_END: 'DRAIN_END',
            EV_DROPPED: 'DROPPED'}

STATE_CODE = {'I': 0x0, 'S': 0x1, 'E': 0x2, 'M': 0x3}
CODE_STATE = {v: k for k, v in STATE_CODE.items()}
SNOOP_NAME = {v: k for k, v in SNOOP_CODES.items()}

# candidate priority index -> MonBus event code (amber_monlite c_code)
CAND_EV = [EV_EVICT, EV_SNOOP, EV_HIT, EV_HIT, EV_MISS, EV_FILL_START,
           EV_DRAIN_START, EV_FILL_END, EV_DRAIN_END, EV_TRANSITION]

# TRANSITION cause codes (amber_monlite header contract)
CAUSE_HIT_WR = 1
CAUSE_FILL = 2
CAUSE_SNOOP = 4


class LruModel:
    """Rank array parity model: 0 = MRU, WAYS-1 = victim; hits and installs
    both update (matches amber_repl LRU reset + update semantics)."""

    def __init__(self, sets, ways):
        self.sets, self.ways = sets, ways
        self.rank = [[w for w in range(ways)] for _ in range(sets)]

    def victim(self, s):
        for w in range(self.ways):
            if self.rank[s][w] == self.ways - 1:
                return w
        raise RuntimeError("LruModel: no victim")

    def update(self, s, way):
        old = self.rank[s][way]
        for w in range(self.ways):
            if w == way:
                self.rank[s][w] = 0
            elif self.rank[s][w] < old:
                self.rank[s][w] += 1


def _parse_packet(pkt):
    """monitor_common_pkg 128-bit layout (scored independent copy)."""
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


class AmberMonliteTB(AmberFrontendTB):
    """Extends the frontend suite with the observer contract."""

    def __init__(self, dut, **kwargs):
        super().__init__(dut, **kwargs)
        self.MON_CFG = os.environ.get('MON_CFG', 'tap')
        random.seed(self.SEED)

        # observer model state
        self.pkt_log = []          # (cyc, parsed_packet, timestamp, head)
        self._scanned = 0          # _match_packets packet cursor
        self._exp_pos = 0          # _match_packets expectation cursor
        self.exp_events = []       # ordered expected event dicts
        self.fired_total = 0       # probe: candidate firings (u_monlite)
        self.q_trace = []          # probe: (cyc, fired classes, valid, ready)
        self.fired_trace = []      # probe: debug (cyc, fired classes)
        self.line_state = {}
        self.tags = {}
        self.slot_state = {}
        self.lru = LruModel(self.SETS, self.WAYS)

        # monbus ready drive: 'free' (1), 'stall' (0), 'random' (p=0.65)
        self.mon_mode = 'free'

        self.log.info(f"AmberMonliteTB cfg={self.MON_CFG}")

    # ------------------------------------------------------------------
    # setup overrides
    # ------------------------------------------------------------------
    async def setup_clocks_and_reset(self, period_ns=10):
        await super().setup_clocks_and_reset(period_ns)
        d = self.dut
        d.monbus_ready.value = 1
        cocotb.start_soon(self._monbus_ready_driver())
        cocotb.start_soon(self._monbus_monitor())
        cocotb.start_soon(self._monbus_fired_probe())

    async def _reset_dut(self):
        await super()._reset_dut()
        self.pkt_log = []
        self.q_trace = []
        self.fired_total = 0
        self._scanned = 0
        self._exp_pos = 0
        self.exp_events = []
        self.line_state = {}
        self.tags = {}
        self.slot_state = {}
        self.lru = LruModel(self.SETS, self.WAYS)

    # ------------------------------------------------------------------
    # monbus drive/monitor
    # ------------------------------------------------------------------
    async def _monbus_ready_driver(self):
        """Drive monbus_ready from mon_mode. Writes land on the bare
        falling edge (house stub convention): the value is stable for the
        DUT's sampling posedge AND for every negedge+settle monitor --
        a settle-timer write here races the monitors' same-timestamp
        sample and a handshake lands that the TB never records."""
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
        """Order-and-accounting ground truth: sample the observer's
        candidate firings (class-level), monbus_valid and monbus_ready at
        posedge+eps -- the same point in the cycle the DUT acts on.
        Hierarchical, TB-only. The trace replays the DUT's exact firing
        order (including where the async drain_done lands) through a
        queue model so the expected received stream is known packet-for-
        packet even under drops."""
        d = self.dut.u_monlite
        while True:
            # late-mid-cycle sampling: every TB write lands at negedge+500ps
            # (settled convention) or bare negedge (stub pulses), so 2ns
            # after the falling edge the whole cycle's tap values are stable
            # -- and a firing this cycle is queued by the DUT at the
            # upcoming posedge
            await FallingEdge(d.clk)
            await Timer(2000, units='ps')
            if not int(self.dut.rst_n.value):
                continue
            fired = tuple(CAND_EV[j] for j in range(10)
                          if int(d.c_fire[j].value))
            self.q_trace.append(
                (self.cyc, fired,
                 int(d.monbus_valid.value), int(d.monbus_ready.value),
                 int(self.dut.snoop_req.value),
                 int(self.dut.snoop_ready.value),
                 int(self.dut.ctrl_state.value),
                 int(d.u_out_q.count.value)))
            self.fired_total += len(fired)
            if fired:
                self.fired_trace.append((self.cyc,) + fired)

    def _strict_stream_match(self, label='', pkt_base=0, exp_base=0,
                             trace_base=0):
        """Replay the fired-class trace through an exact model of the
        observer's queue (DEPTH 4, two priority-ordered write slots, the
        empty-queue-only drop report) zipped with the model's expected
        events, and require the predicted received stream to equal the
        observed packets in class, payload, timestamp (== firing cycle)
        and acceptance cycle. This is exact under arbitrary backpressure
        and drops -- the drop-and-count contract end to end."""
        from collections import deque
        # 1. the DUT's firing-class sequence must equal the model's
        truth = [cls for row in self.q_trace[trace_base:]
                 for cls in row[1]]
        model = self.exp_events[exp_base:]
        self._score(f"{label} firing class sequence == model",
                    truth, [e['event'] for e in model])
        # 2. zip firings to model events with their firing cycle
        events = []           # (model_event, fire_cyc)
        ti = 0
        for row in self.q_trace[trace_base:]:
            for cls in row[1]:
                if ti < len(model):
                    events.append((model[ti], row[0]))
                ti += 1
        # 3. queue replay (entries: model event or drop-report marker);
        # the firing index advances on EVERY firing -- dropped ones are
        # skipped for the queue but still consume the truth/model zip
        q = deque()           # (model_event|None, fire_cyc|None, report_cnt)
        dropped = 0
        r_dropped = 0
        expect = []           # (model_event, fire_cyc, pop_cyc, report_cnt)
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
        # 4. strict comparison against the observed packets
        obs = self.pkt_log[pkt_base:]
        self._score(f"{label} predicted stream length", len(expect),
                    len(obs))
        n_scored = 0
        for k, ((ev, fcyc, pcyc, rcnt), (ocyc, op, ots, ohead)) in enumerate(
                zip(expect, obs)):
            if (rcnt is None and
                    (op['event_code'] != ev['event']
                     or op['data'] != ev['data'] or ots != fcyc
                     or ocyc != pcyc)):
                # debug fingerprint of the first divergence (logs only on
                # a mismatch; the scored checks below still record it)
                self.log.info(
                    f"{label} mismatch@{k}: expect "
                    f"(ev{ev['event']}, f{fcyc}, p{pcyc}) got "
                    f"(ev{op['event_code']}, ts{ots}, c{ocyc}); "
                    f"window {[(e[0]['event'] if e[0] else 'R', e[1]) for e in expect[max(0,k-3):k+4]]}")
                self.log.info(
                    f"{label} expect12: "
                    f"{[(e[0]['event'] if e[0] else 'R', e[1], e[2]) for e in expect[:12]]}")
                self.log.info(
                    f"{label} obs12: "
                    f"{[(pp['event_code'], t, c) for c, pp, t, _ in obs[:12]]}")
                self.log.info(
                    f"{label} qrows: "
                    f"{[r for r in self.q_trace[trace_base:] if fcyc - 15 <= r[0] <= pcyc]}")
            self._score_packet_format(ocyc, op, ots, ohead)
            if rcnt is not None:
                self._score(f"{label} report count", op['event_code'],
                            EV_DROPPED)
                self._score(f"{label} report value", op['data'] & 0xFF,
                            rcnt)
                continue
            self._score(f"{label} class", op['event_code'], ev['event'])
            self._score(f"{label} payload", op['data'], ev['data'])
            self._score(f"{label} ts == firing cycle", ots, fcyc)
            self._score(f"{label} acceptance cycle", ocyc, pcyc)
            n_scored += 1
        return dropped

    async def _monbus_monitor(self):
        """Record every accepted packet. The registered timestamp must be
        stable while the packet waits at the head and equal to the
        side-band value sampled at the push edge (the TB drives the
        side-band with the current cycle at each negedge, so the push
        edge -- the cycle the packet appears at the head -- is head_cyc
        and the sampled timestamp is head_cyc - 1)."""
        d = self.dut
        prev_valid = 0
        prev_popped = 0
        head_cyc = 0
        head_ts = None
        while True:
            await self._negedge_settled()
            valid = int(d.monbus_valid.value)
            if valid:
                popped = prev_valid and int(d.monbus_ready.value)
                if not prev_valid or prev_popped:
                    # a new head appeared this cycle
                    head_cyc = self.cyc
                    head_ts = int(d.monbus_timestamp.value)
                else:
                    self._score("monbus: timestamp stable while waiting",
                                int(d.monbus_timestamp.value), head_ts)
            prev_valid = valid
            prev_popped = valid and int(d.monbus_ready.value)
            if valid and int(d.monbus_ready.value):
                pkt = int(d.monbus_packet.value)
                ts = int(d.monbus_timestamp.value)
                self.pkt_log.append((self.cyc, _parse_packet(pkt), ts,
                                     head_cyc))
                self.packets += 1

    def _score_packet_format(self, cyc, p, ts, head_cyc):
        lab = f"pkt@{cyc}"
        self._score(f"{lab} protocol CORE", p['protocol'], PROTOCOL_CORE)
        self._score(f"{lab} agent id", p['agent_id'], AGENT_ID)
        self._score(f"{lab} unit id", p['unit_id'], UNIT_ID)
        self._score(f"{lab} reserved zero", p['reserved'], 0)
        self._score(f"{lab} channel zero", p['channel_id'], 0)
        if p['event_code'] == EV_DROPPED:
            self._score(f"{lab} dropped is Error", p['pkt_type'],
                        PKT_TYPE_ERROR)
        else:
            self._score(f"{lab} event pkt type Perf", p['pkt_type'],
                        PKT_TYPE_PERF)
            self._score(f"{lab} known event code",
                        p['event_code'] in EV_NAMES, True)
        # timestamp exactness (ts == the event's firing cycle) and
        # stability-while-waiting are scored by the strict stream matcher
        # and the monitor invariant respectively

    # ------------------------------------------------------------------
    # event expectations (appended in emission order)
    # ------------------------------------------------------------------
    def _exp_hit(self, set_idx, way, state_before, we):
        state_after = 'M' if we else state_before
        self.exp_events.append({
            'event': EV_HIT,
            'data': (set_idx & 0xFFFF) | ((way & 0xF) << 16)
                    | ((STATE_CODE[state_before] & 0x7) << 20)
                    | ((STATE_CODE[state_after] & 0x7) << 23)
                    | ((1 if we else 0) << 26)})

    def _exp_miss(self, set_idx, way, we):
        self.exp_events.append({
            'event': EV_MISS,
            'data': (set_idx & 0xFFFF) | ((way & 0xF) << 16)
                    | (0x3 << 20)                    # AMBER_MISS_UNKNOWN
                    | ((1 if we else 0) << 22)})

    def _exp_snoop(self, snoop_type, hit, crresp):
        self.exp_events.append({
            'event': EV_SNOOP,
            'data': (snoop_type & 0x7) | ((1 if hit else 0) << 3)
                    | ((crresp & 0x1F) << 4)})

    def _exp_evict(self, set_idx, way, dirty, line_addr):
        self.exp_events.append({
            'event': EV_EVICT,
            'data': (set_idx & 0xFFFF) | ((way & 0xF) << 16)
                    | ((1 if dirty else 0) << 20)
                    | ((line_addr & 0xFFFFFFFF) << 21)})

    def _exp_transition(self, set_idx, way, old, new, cause):
        self.exp_events.append({
            'event': EV_TRANSITION,
            'data': (set_idx & 0xFFFF) | ((way & 0xF) << 16)
                    | ((STATE_CODE[old] & 0x7) << 20)
                    | ((STATE_CODE[new] & 0x7) << 23)
                    | ((cause & 0xF) << 26)})

    def _exp_line(self, event, line_addr):
        self.exp_events.append({'event': event, 'data': line_addr})

    # ------------------------------------------------------------------
    # transaction model override: score + expect (every transaction in
    # EVERY inherited scenario routes through here)
    # ------------------------------------------------------------------
    def _hit_way(self, set_idx, line):
        for w in range(self.WAYS):
            if (self.tags.get((set_idx, w)) == line
                    and self.slot_state.get((set_idx, w), 'I') != 'I'):
                return w
        return None

    async def _txn(self, addr, we, be=None, wdata=None, label=''):
        """A scored transaction that also predicts the observer's event
        stream (hit/miss/upgrade classification, victim accounting)."""
        line = self._line_of(addr)
        set_idx = self._set_of_line(line)
        beat = (addr >> (self.STRB_W.bit_length() - 1)) & (self.FILL_BEATS - 1)
        hit_way = self._hit_way(set_idx, line)
        state = self.line_state.get(line, 'I')
        is_hit = hit_way is not None
        upgrade = is_hit and we and state == 'S'

        victim_way = None
        victim_line = None
        victim_dirty = False
        if not is_hit:
            victim_way = self.lru.victim(set_idx)
            victim_line = self.tags.get((set_idx, victim_way))
            victim_dirty = self.slot_state.get((set_idx, victim_way),
                                               'I') == 'M'

        accept_cyc, rsp_cyc, _ = await super()._txn(addr, we, be, wdata,
                                                    label)

        # expectations in emission order
        if is_hit:
            if upgrade:
                # upgrade: CLEAN_UNIQUE fill start, FILL_WRITE commits the
                # S->M tag write (cause = the FILL_WRITE state), the
                # replayed write then services as a hit at M
                self._exp_line(EV_FILL_START, line)
                self._exp_line(EV_FILL_END, line)
                self._exp_transition(set_idx, hit_way, 'S', 'M', CAUSE_FILL)
                self._exp_hit(set_idx, hit_way, 'M', we)
            else:
                self._exp_hit(set_idx, hit_way, state, we)
        else:
            self._exp_miss(set_idx, victim_way, we)
            if victim_dirty:
                self._exp_evict(set_idx, victim_way, 1,
                                victim_line if victim_line is not None else 0)
                self._exp_line(EV_DRAIN_START,
                               victim_line if victim_line is not None else 0)
                self._exp_line(EV_DRAIN_END,
                               victim_line if victim_line is not None else 0)
            self._exp_line(EV_FILL_START, line)
            # FILL_END and the install TRANSITION emit in the same cycle;
            # slot order: FILL_END then TRANSITION (priority table)
            self._exp_line(EV_FILL_END, line)
            install = 'M' if we else 'S'
            self._exp_transition(set_idx, victim_way, 'I', install,
                                 CAUSE_FILL)
            # the replayed request services as a hit at the install state
            self._exp_hit(set_idx, victim_way, install, we)

        # model advance
        if is_hit:
            if we:
                self.line_state[line] = 'M'
                self.slot_state[(set_idx, hit_way)] = 'M'
            self.lru.update(set_idx, hit_way)
        else:
            if victim_line is not None and victim_line != line:
                self.line_state[victim_line] = 'I'
            self.tags[(set_idx, victim_way)] = line
            self.slot_state[(set_idx, victim_way)] = install
            self.line_state[line] = install
            self.lru.update(set_idx, victim_way)
        return accept_cyc, rsp_cyc, None

    async def _ml_snoop(self, snoop_type, addr, label=''):
        """Quiescence snoop: predict SNOOP packet + any state-transition
        packet; advance the line model."""
        line = self._line_of(addr)
        set_idx = self._set_of_line(line)
        way = self._hit_way(set_idx, line)
        state = self.line_state.get(line, 'I')
        if way is None:
            state = 'I'
        name = SNOOP_NAME[snoop_type]
        crresp = _decode_crresp(state, name)
        nxt = _decode_next(state, name)
        hit = way is not None

        await self._snoop(snoop_type, addr, label)

        self._exp_snoop(snoop_type, hit, crresp)
        if hit and nxt != state:
            self._exp_transition(set_idx, way, state, nxt, CAUSE_SNOOP)
            self.line_state[line] = nxt
            self.slot_state[(set_idx, way)] = nxt

    # ------------------------------------------------------------------
    # packet stream scoring
    # ------------------------------------------------------------------
    # ------------------------------------------------------------------
    # scenarios
    # ------------------------------------------------------------------
    async def _s_event_class_matrix(self):
        """Directed sweep exercising EVERY Table 4.1.1 class with
        hand-computed payload expectations: read miss (fill), read hit,
        upgrade, true write hit, dirty-victim eviction (drain), and a
        quiescence snoop with a state change."""
        self._scenario('EventClassMatrix')
        self.mon_mode = 'free'
        # read miss + fill (clean ways)
        await self._txn(self._compose_addr(0x20, 8), 0, label='m_rd')
        # read hit on the installed S line
        await self._txn(self._compose_addr(0x20, 8), 0, label='m_rh')
        # upgrade: write to the S line (CLEAN_UNIQUE, no beats)
        await self._txn(self._compose_addr(0x20, 8), 1, be=0xF,
                           wdata=0x0DDA, label='m_up')
        # true write hit on the now-M line
        await self._txn(self._compose_addr(0x20, 8), 1, be=0x3,
                           wdata=0x00C0, label='m_wh')
        # dirty victim: write ALL the set's ways dirty, then read-miss a
        # fifth line in the same set -- the LRU victim is one of the
        # dirty lines: EVICT + DRAIN_START + DRAIN_END on the stream
        for w in range(self.WAYS):
            await self._txn(self._compose_addr(0x28 + w, 14), 1,
                            wdata=0x11 * (w + 1), label=f'm_d{w}')
        await self._txn(self._compose_addr(0x2C, 14), 0, label='m_dv')
        # upgrade the freshly installed S line to M (tag write S->M in
        # FILL_WRITE), then snoop it: M x READ_SHARED -> S with a
        # PassDirty data transfer -- a SNOOP hit WITH a state change
        await self._txn(self._compose_addr(0x2C, 14), 1, be=0xF,
                        wdata=0x00FF, label='m_up2')
        await self._ml_snoop(0, self._compose_addr(0x2C, 14), label='m_sn')
        # a snoop miss (no state change, no transition packet)
        await self._ml_snoop(1, self._compose_addr(0x777, 2), label='m_smiss')

        # let the queue drain, then score the stream exactly (the strict
        # matcher predicts the received stream packet-for-packet)
        for _ in range(40):
            await self._negedge_settled()
        self._strict_stream_match('matrix')
        seen = {p['event_code'] for _, p, _, _ in self.pkt_log}
        for ev in (EV_HIT, EV_MISS, EV_SNOOP, EV_EVICT, EV_TRANSITION,
                   EV_FILL_START, EV_FILL_END, EV_DRAIN_START, EV_DRAIN_END):
            self._score(f"matrix: {EV_NAMES[ev]} observed",
                        ev in seen, True)

        # causal order per transaction (first occurrence of each class):
        # the dirty-victim transaction must show MISS < FILL_START and
        # EVICT <= DRAIN_START < DRAIN_END
        def first_cyc(ev):
            for c, p, _, _ in self.pkt_log:
                if p['event_code'] == ev:
                    return c
            return None
        c_miss = first_cyc(EV_MISS)
        c_fs = first_cyc(EV_FILL_START)
        c_fe = first_cyc(EV_FILL_END)
        c_ev = first_cyc(EV_EVICT)
        c_ds = first_cyc(EV_DRAIN_START)
        c_de = first_cyc(EV_DRAIN_END)
        self._score('matrix: MISS before FILL_START',
                    None not in (c_miss, c_fs) and c_miss < c_fs, True)
        self._score('matrix: FILL_START before FILL_END',
                    None not in (c_fs, c_fe) and c_fs < c_fe, True)
        self._score('matrix: EVICT at/before DRAIN_START',
                    None not in (c_ev, c_ds) and c_ev <= c_ds, True)
        self._score('matrix: DRAIN_START before DRAIN_END',
                    None not in (c_ds, c_de) and c_ds < c_de, True)

    async def _s_drop_and_count(self):
        """Sustained monbus_ready low through a busy phase forces drops;
        the count re-emerges as Error/AMBER_EV_DROPPED when the bus frees,
        and the accounting identity holds."""
        self._scenario('DropAndCount')
        self.mon_mode = 'free'
        n_pkt0 = len(self.pkt_log)
        n_exp0 = len(self.exp_events)
        # busy phase with the bus stalled: 6 misses => 6+ events against a
        # 4-deep queue -> guaranteed drops
        self.mon_mode = 'stall'
        for w in range(6):
            await self._txn(self._compose_addr(0x50 + w, 30), 0,
                               label=f'dc{w}')
        # the saturating count must be non-zero while stalled (sample it;
        # exactly which events dropped is timing-dependent)
        d_val = int(self.dut.monbus_dropped.value)
        self._score('drop: count accumulated under stall', d_val > 0, True)
        # release the bus: the DROPPED report must be the next packet, and
        # the tap must clear once it emits
        self.mon_mode = 'free'
        for _ in range(100):
            await self._negedge_settled()
            if len(self.pkt_log) > n_pkt0 and \
                    self.pkt_log[-1][1]['event_code'] == EV_DROPPED:
                break
        drop_pkts = [p for _, p, _, _ in self.pkt_log[n_pkt0:]
                     if p['event_code'] == EV_DROPPED]
        self._score('drop: DROPPED packet emitted', len(drop_pkts) > 0, True)
        if drop_pkts:
            cnt = drop_pkts[0]['data'] & 0xFF
            self._score('drop: count matches tap sample', cnt, d_val)
            self._score('drop: nonzero count', cnt > 0, True)
        for _ in range(20):
            await self._negedge_settled()
        self._score('drop: tap cleared after report',
                    int(self.dut.monbus_dropped.value), 0)
        # exact stream prediction: the report counts, the dropped events,
        # and the surviving packets must all line up
        dropped = self._strict_stream_match('drop')
        self._score('drop: drops were forced', dropped > 0, True)

    def _behavior_signature(self, ev_start=0, rsp_start=0):
        """Frontend-visible behavior record for present-vs-absent: per
        transaction (accept offset, response offset, response data)."""
        accepts = [e for e in self.events[ev_start:] if e[1] == 'accept']
        base = accepts[0][0] if accepts else 0
        rsps = self.rsp_log[rsp_start:]
        sig = []
        for i, (cyc, _, p) in enumerate(accepts):
            r_cyc, r_data = rsps[i] if i < len(rsps) else (None, None)
            sig.append((cyc - base, None if r_cyc is None else r_cyc - base,
                        r_data, p['addr'], p['we']))
        return sig

    async def _stimulus_for_equivalence(self):
        """Fixed deterministic stimulus for the present-vs-absent runs."""
        random.seed(self.SEED + 7)
        await self._txn(self._compose_addr(0x60, 17), 0, label='pa0')
        await self._txn(self._compose_addr(0x61, 17), 0, label='pa1')
        await self._txn(self._compose_addr(0x60, 17), 1, be=0xFF,
                           wdata=0x5A5A5A5A5A5A5A5A & ((1 << self.DATA_WIDTH) - 1),
                           label='pa2')
        await self._ml_snoop(0, self._compose_addr(0x60, 17), label='pa3')
        await self._txn(self._compose_addr(0x62, 17), 0, label='pa4')
        for w in range(4):
            await self._txn(self._compose_addr(0x70 + w, 33), 1,
                               wdata=0xD1 * (w + 1),
                               label=f'pa5_{w}')
        await self._txn(self._compose_addr(0x74, 33), 0, label='pa6')

    async def _s_present_vs_absent(self):
        """Review Focus 5 / D8 measurement integrity: identical seeded
        stimulus with the observer free vs backpressured produces
        cycle-identical frontend behavior; only the packet stream
        differs (the backpressured run drops packets)."""
        self._scenario('PresentVsAbsent')
        # run A: bus free (slice markers keep the earlier scenarios out
        # of the comparison)
        ev0 = len(self.events)
        rsp0 = len(self.rsp_log)
        pkt0 = len(self.pkt_log)
        exp0 = len(self.exp_events)
        trace0 = len(self.q_trace)
        self.mon_mode = 'free'
        await self._stimulus_for_equivalence()
        for _ in range(60):
            await self._negedge_settled()
        sig_a = self._behavior_signature(ev0, rsp0)
        pkts_a = len(self.pkt_log) - pkt0
        exp_a = list(self.exp_events[exp0:])
        # exact stream prediction for the free run: no drops allowed
        dropped_a = self._strict_stream_match('pva free', pkt0, exp0,
                                              trace0)
        self._score('pva: free-run had no drops', dropped_a, 0)

        # run B: same stimulus, bus stalled through the busy phases (the
        # DUT reset clears the logs, so whole-list slices apply)
        await self._reset_dut()
        random.seed(self.SEED + 7)
        self.mon_mode = 'free'
        await self._txn(self._compose_addr(0x60, 17), 0, label='pb0')
        self.mon_mode = 'stall'
        await self._txn(self._compose_addr(0x61, 17), 0, label='pb1')
        await self._txn(self._compose_addr(0x60, 17), 1, be=0xFF,
                        wdata=0x5A5A5A5A5A5A5A5A
                        & ((1 << self.DATA_WIDTH) - 1), label='pb2')
        self.mon_mode = 'free'
        await self._ml_snoop(0, self._compose_addr(0x60, 17), label='pb3')
        self.mon_mode = 'stall'
        await self._txn(self._compose_addr(0x62, 17), 0, label='pb4')
        for w in range(4):
            await self._txn(self._compose_addr(0x70 + w, 33), 1,
                            wdata=0xD1 * (w + 1), label=f'pb5_{w}')
        self.mon_mode = 'free'
        await self._txn(self._compose_addr(0x74, 33), 0, label='pb6')
        for _ in range(80):
            await self._negedge_settled()
        sig_b = self._behavior_signature()
        pkts_b = len(self.pkt_log)
        exp_b = list(self.exp_events)

        self._score('pva: behavior identical (accepts/rsp cycles/data)',
                    sig_b, sig_a)
        self._score('pva: expectations identical', exp_b, exp_a)
        self._score('pva: packet streams differ under backpressure',
                    pkts_b < pkts_a, True)
        # run B's exact stream prediction: drops forced and accounted
        dropped_b = self._strict_stream_match('pva stalled')
        self._score('pva: backpressured run dropped packets',
                    dropped_b > 0, True)

    async def _s_observer_silent(self):
        """USE_MONITOR=0 (notap cells): the observer is tied off -- the
        monbus never valid, the drop count stays zero, and the frontend
        suite still passes underneath."""
        self._scenario('ObserverSilent')
        d = self.dut
        await self._s_hit_sequence()
        await self._s_miss_sequence()
        for _ in range(30):
            await self._negedge_settled()
        self._score('silent: monbus_valid never asserted', self.packets, 0)
        self._score('silent: drop count tied zero',
                    int(d.monbus_dropped.value), 0)

    async def _s_full_soak(self):
        """Randomized soak with randomized monbus backpressure; the strict
        stream matcher predicts the received packets packet-for-packet
        (classes, payloads, timestamps, acceptance cycles, drop reports)."""
        self._scenario('FullSoak')
        self.mon_mode = 'random'
        pkt0 = len(self.pkt_log)
        exp0 = len(self.exp_events)
        trace0 = len(self.q_trace)
        n = self.FULL_TXN[self.TEST_LEVEL]
        for i in range(n):
            tag = random.randrange(1, 1 << (self.ADDR_WIDTH - self.SET_BITS
                                            - self.OFFSET_BITS))
            set_idx = random.randrange(self.SETS)
            beat = random.randrange(self.FILL_BEATS)
            addr = self._compose_addr(tag, set_idx, beat)
            we = random.random() < 0.5
            await self._txn(addr, we, label=f'soak{i}')
            if random.random() < 0.1:
                sn = random.randrange(6)
                await self._ml_snoop(sn, addr, label=f'soak_s{i}')
            if i % 500 == 0:
                self.mark_progress(f"soak {i}/{n}")
        # drain the bus
        self.mon_mode = 'free'
        for _ in range(100):
            await self._negedge_settled()
        dropped = self._strict_stream_match('soak', pkt0, exp0, trace0)
        # drops are not guaranteed at 65% ready (the directed DropAndCount
        # scenario pins forced drops); require that backpressure was
        # genuinely exercised and report the drop count
        stalled = sum(1 for r in self.q_trace[trace0:]
                      if r[2] and not r[3])
        self._score('soak: backpressure exercised', stalled > 20, True)
        self.log.info(f"soak: random-backpressure drops = {dropped}, "
                      f"stalled-head cycles = {stalled}")
        n_acc = len([1 for _, k, _ in self.events if k == 'accept'])
        self._score('soak: responses == accepts', len(self.rsp_log), n_acc)

    # ------------------------------------------------------------------
    # run
    # ------------------------------------------------------------------
    async def run(self):
        if self.MON_CFG == 'notap':
            # the observer tie-off configuration: no packet stream exists
            await self._s_init_ready()
            await self._s_observer_silent()
            n_acc = len([1 for _, k, _ in self.events if k == 'accept'])
            self._score('global: responses == accepts', len(self.rsp_log),
                        n_acc)
            return self.mismatches == 0

        await self._s_init_ready()
        await self._s_event_class_matrix()
        if self.TEST_LEVEL == 'gate':
            await self._s_present_vs_absent()
        elif self.TEST_LEVEL == 'func':
            await self._s_drop_and_count()
            await self._s_present_vs_absent()
        else:
            await self._s_drop_and_count()
            await self._s_present_vs_absent()
            await self._s_full_soak()
        n_acc = len([1 for _, k, _ in self.events if k == 'accept'])
        self._score('global: responses == accepts', len(self.rsp_log), n_acc)
        return self.mismatches == 0
