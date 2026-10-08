"""
amber_control testbench

Blocking-pipeline control FUB bring-up (Task 3: CPU path), extended with
snoop-during-fill service (Task 4): the pending-fill bypass (MAS ch02/02)
and CTRL_SNOOP port-B service, scored lockstep against the Task 2
gem5-derived oracle (dv/golden/amber_fsm_oracle.py). The harness
(dv/tb/amber_control_th.sv) wires the DUT to the landed tag/data/repl arrays;
this TB models the partner handshakes (frontend/fill/drain/victim/snoop)
timing-only per D-12 -- never protocol. The snoop driver models the
amber_snoop_resp core-facing contract: req held until ready, CRRESP sampled
at the grant cycle, CD beats consumed on cdvalid && cdready.

Golden models carried here (independent copies, kmap-TB rule: no shared code
with the DUT):
  memory-side line content   self.mem -- written by drains, read by fills
  cache line content         self.cache_data -- installed by fills, merged
                             by CPU writes (D-4 merge on the replayed hit)
  per-line MESI state        self.line_state -- advanced with oracle.step()
  (set, way) -> line tag     self.tags -- eviction accounting
  true-LRU policy            LruModel -- reset + update parity with amber_repl

Snoop classes (Task 4 brief):
  SnoopPendingFillBypass       pre-RLAST snoop for the pending line:
                               post-fill state + received beats, CD stall
                               until a late beat arrives (cd_ready held)
  SnoopPostCommitApplies       snoop after fill commit applies normally
  SnoopOtherLineMidFill        other-line snoops interleaved mid-fill at
                               legal boundaries
  BypassNeverAnswersInvalid    TB invariant, asserted EVERY cycle while a
                               bypass-targeted snoop is open (the bypass
                               never answers with the pre-fill STATE_I)
Directed pins:
  ImStepPendingClearCorner     in-flight pending 'I' + shared-domain snoop:
                               invalidation-sticks (oracle corner closed)
  UpgradeNoBypassArm           upgrades do NOT arm the bypass (MAS ch02/02:
                               no fill data in flight; MINOR 1)
  UpgradeKilledByInvalidatingSnoop  SM x Inv -> IM conversion realized as
                               commit-I + replay re-fetch (gem5 .sm:1526)
  SnoopDrainingVictim          snoop hits the in-flight dirty victim:
                               served from the staged line at M (SINK_WB_ACK)
  SnoopStaleVictimMidFill      snoop for the already-drained victim during
                               the fill: no-transfer (WB completed, M_I x
                               WB_Ack -> I, .sm:1315)
  BeZeroWrite                  be == 0 write merges nothing (MINOR 2)
  StrayReqInInit               req_valid during INIT is ignored; ready is
                               IDLE-only (MINOR 2)

Levels (TEST_LEVEL):
  gate  -- InitWalk + directed HitSequence (rd/wr hits per reachable state,
           policy-update checks vs the oracle)
  func  -- + MissSequence (clean victim, dirty victim, upgrade), the sticky
           CTRL_ERROR illegal-state directed test, the snoop suite above,
           and the MINOR-2 directed tests
  full  -- + randomized stream, 10k transactions with interleaved idle
           snoops, oracle lockstep per transaction (seeds pinned by the
           repo-root conftest)

Author: RTL Design Sherpa
Created: 2026-10-07
"""

import os
import random

import cocotb
from cocotb.triggers import RisingEdge, FallingEdge, Timer

from TBClasses.shared.tbbase import TBBase

from projects.components.cache_ip.amber_mesi_l1.dv.golden.amber_fsm_oracle import (
    SNOOP_CODES,
    step as oracle_step,
)


# ---------------------------------------------------------------------------
# ctrl_state_t codes (amber_pkg) -- kept textual for log messages
# ---------------------------------------------------------------------------
ST_IDLE, ST_INIT, ST_LOOKUP, ST_HIT_RD, ST_HIT_WR, ST_MISS_VICTIM, \
    ST_MISS_DRAIN, ST_MISS_FILL, ST_FILL_WRITE, ST_REPLAY, ST_SNOOP, \
    ST_ERROR = range(0xC)

STATE_NAMES = {
    ST_IDLE: 'IDLE', ST_INIT: 'INIT', ST_LOOKUP: 'LOOKUP',
    ST_HIT_RD: 'HIT_RD', ST_HIT_WR: 'HIT_WR', ST_MISS_VICTIM: 'MISS_VICTIM',
    ST_MISS_DRAIN: 'MISS_DRAIN', ST_MISS_FILL: 'MISS_FILL',
    ST_FILL_WRITE: 'FILL_WRITE', ST_REPLAY: 'REPLAY', ST_SNOOP: 'SNOOP',
    ST_ERROR: 'ERROR',
}

# pkg cache_state_t encodings
STATE_CODE = {'I': 0x0, 'S': 0x1, 'E': 0x2, 'M': 0x3}

# amber_ace_req_t encodings (amber_pkg): fill request classes
ACE_READ_SHARED, ACE_READ_UNIQUE, ACE_CLEAN_UNIQUE = 0, 1, 2

# partner stub timing knobs (handshake timing only, D-12)
FILL_DONE_DELAY = 6          # cycles between last beat and fill_done
DRAIN_LATENCY = None         # set per-geometry: FILL_BEATS + 2

# request classes the oracle emits, mapped to the pkg encoding
ORACLE_REQ_TO_ACE = {
    'READ_SHARED': ACE_READ_SHARED,
    'READ_UNIQUE': ACE_READ_UNIQUE,
    'CLEAN_UNIQUE': ACE_CLEAN_UNIQUE,
}

# CRRESP bit positions (IHI0022 order, amber_pkg localparams)
CRRESP_DT = 0


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


class AmberControlTB(TBBase):
    """Scores amber_control's observable behavior against the oracle."""

    FULL_TXN = {'gate': 0, 'func': 0, 'full': 10_000}
    RSP_TIMEOUT_CYCLES = 500

    def __init__(self, dut, **kwargs):
        super().__init__(dut)
        self.SEED = self.convert_to_int(os.environ.get('SEED', '12345'))
        self.TEST_LEVEL = os.environ.get('TEST_LEVEL', 'gate').lower()
        random.seed(self.SEED)

        # geometry (the grid varies SETS/WAYS only; line/bus stay at the
        # pkg defaults, same convention as the other amber suites)
        self.SETS = int(os.environ.get('SETS', '128'))
        self.WAYS = int(os.environ.get('WAYS', '4'))
        self.ADDR_WIDTH = 32
        self.LINE_BYTES = 64
        self.STRB_W = 8
        self.FILL_BEATS = self.LINE_BYTES // self.STRB_W
        self.SET_BITS = (self.SETS - 1).bit_length()
        self.OFFSET_BITS = (self.LINE_BYTES - 1).bit_length()
        self.BEAT_BITS = (self.FILL_BEATS - 1).bit_length()
        self.WAY_BITS = max((self.WAYS - 1).bit_length(), 1)
        self.SET_MASK = self.SETS - 1
        self.LINE_MASK = (1 << (self.ADDR_WIDTH - self.OFFSET_BITS)) - 1

        self.drain_latency = self.FILL_BEATS + 2

        # golden models
        self.mem = {}
        self.cache_data = {}
        self.line_state = {}
        self.tags = {}
        # way-exact tag-slot state mirror (default Invalid): victim-dirty
        # prediction reads the SLOT, not the line -- a killed-fill replay
        # can leave a benign duplicate {tag, I} slot whose line state no
        # longer describes the slot's coherence content
        self.slot_state = {}
        self.lru = LruModel(self.SETS, self.WAYS)

        # observation log: (cyc, kind, payload); cyc ticks at negedge
        self.events = []
        self.cyc = 0
        self.stub_victim_way = 0

        # event-cursor for _wait_tap (directed tests)
        self._tap_pos = 0

        # pending-fill bypass model + open-snoop state, for the EVERY-CYCLE
        # invariant (BypassNeverAnswersInvalid)
        self.inv_pf_active = False
        self.inv_pf_line = None
        self.inv_pf_state = None
        self.inv_pf_beats = set()
        self.inv_sn_open = False
        self.inv_sn_line = None
        self.inv_sn_name = None
        self.inv_cd_beat = 0

        # scorekeeping
        self.checks = 0
        self.mismatches = 0
        self.txns = 0
        self.snoops = 0
        self.scenarios = {}

        self.log.info(f"AmberControlTB sets={self.SETS} ways={self.WAYS} "
                      f"level={self.TEST_LEVEL} seed={self.SEED}")

    # ------------------------------------------------------------------
    # helpers
    # ------------------------------------------------------------------
    def _score(self, what, got, exp):
        self.checks += 1
        if got != exp:
            self.mismatches += 1
            if self.mismatches <= 30:
                self.log.error(f"CHECK FAIL: {what}: got {got!r} expected {exp!r}")

    def _line_of(self, addr):
        return (addr >> self.OFFSET_BITS) & self.LINE_MASK

    def _set_of_line(self, line):
        return line & self.SET_MASK

    def _compose_addr(self, tag, set_idx, beat=0):
        line = (tag << (self.SET_BITS + self.OFFSET_BITS)) \
            | ((set_idx & self.SET_MASK) << self.OFFSET_BITS)
        return line | (beat << (self.STRB_W.bit_length() - 1))

    def _default_line(self, line):
        """Deterministic memory-side content for a never-touched line."""
        return bytes(((line + 0x11 * i) & 0xFF) for i in range(self.LINE_BYTES))

    def _mem_line(self, line):
        if line not in self.mem:
            self.mem[line] = bytearray(self._default_line(line))
        return self.mem[line]

    def _beat_of_line(self, line_data, beat):
        lo = beat * self.STRB_W
        return int.from_bytes(bytes(line_data[lo:lo + self.STRB_W]), 'little')

    def _hit_way(self, set_idx, line):
        for w in range(self.WAYS):
            if self.tags.get((set_idx, w)) == line:
                return w
        return None

    def _decode_state(self, code):
        for name, c in STATE_CODE.items():
            if c == code:
                return name
        return f'RSV{code}'

    # ------------------------------------------------------------------
    # clock/reset/monitor/stubs
    # ------------------------------------------------------------------
    async def setup_clocks_and_reset(self, period_ns=10):
        await self.start_clock('clk', freq=period_ns, units='ns')
        d = self.dut
        d.req_valid.value = 0
        d.req_addr.value = 0
        d.req_we.value = 0
        d.req_be.value = 0
        d.req_wdata.value = 0
        d.fill_done.value = 0
        d.drain_done.value = 0
        d.fillbeat_wr_en.value = 0
        d.fillbeat_wr_addr.value = 0
        d.fillbeat_wr_way.value = 0
        d.fillbeat_wr_data.value = 0
        d.fillbeat_wr_be.value = 0
        d.fill_beat_valid.value = 0
        d.fill_beat_idx.value = 0
        d.snoop_req.value = 0
        d.snoop_type.value = 0
        d.snoop_addr.value = 0
        d.cd_ready_in.value = 0
        d.tag_b_set.value = 0
        await self.assert_reset()
        # monitor + stubs + the bypass invariant run from reset assertion
        # so no observable cycle (including the first post-deassert init
        # walk cycle) is missed
        cocotb.start_soon(self._monitor())
        cocotb.start_soon(self._fill_stub())
        cocotb.start_soon(self._drain_stub())
        cocotb.start_soon(self._victim_way_tracker())
        cocotb.start_soon(self._pf_invariant())
        await self.wait_clocks('clk', 3)
        await self.deassert_reset()

    async def assert_reset(self):
        self.dut.rst_n.value = 0

    async def deassert_reset(self):
        self.dut.rst_n.value = 1

    async def _negedge_settled(self):
        await FallingEdge(self.dut.clk)
        await Timer(500, units='ps')

    async def _negedge(self):
        await FallingEdge(self.dut.clk)

    async def _monitor(self):
        d = self.dut
        prev_state = -1
        while True:
            await FallingEdge(d.clk)
            await Timer(100, units='ps')
            self.cyc += 1
            st = int(d.ctrl_state.value)
            if st != prev_state:
                self.events.append((self.cyc, 'state', st))
                prev_state = st
            if int(d.ctrl_rsp_valid.value):
                self.events.append((self.cyc, 'rsp', int(d.ctrl_rsp_data.value)))
            if int(d.tag_wr_en.value):
                self.events.append((self.cyc, 'tag_wr', {
                    'way_oh': int(d.tag_wr_way_onehot.value),
                    'set': int(d.tag_wr_set.value),
                    'tag_state': int(d.tag_wr_tag_state.value),
                }))
            if int(d.data_wr_en.value):
                kind = 'ctrl_wr' if int(d.ctrl_data_wr_en.value) else 'fill_wr'
                self.events.append((self.cyc, kind, {
                    'way_oh': int(d.data_wr_way_onehot.value),
                    'addr': int(d.data_wr_addr.value),
                    'data': int(d.data_wr_wdata.value),
                    'be': int(d.data_wr_be.value),
                }))
            if int(d.fill_start.value):
                self.events.append((self.cyc, 'fill_start', {
                    'addr': int(d.fill_addr.value),
                    'class': int(d.fill_req_class.value),
                }))
            if int(d.fill_done.value):
                self.events.append((self.cyc, 'fill_done', None))
            if int(d.drain_start.value):
                self.events.append((self.cyc, 'drain_start', None))
            if int(d.drain_done.value):
                self.events.append((self.cyc, 'drain_done', None))
            if int(d.victim_load.value):
                self.events.append((self.cyc, 'victim_load', {
                    'addr': int(d.victim_addr.value),
                    'data': int(d.victim_data.value),
                }))
            if int(d.repl_req.value):
                self.events.append((self.cyc, 'repl_req', {
                    'victim_way': int(d.repl_victim_way.value),
                }))
            if int(d.repl_hit.value):
                self.events.append((self.cyc, 'repl_hit', {
                    'way': int(d.repl_hit_way.value),
                }))
            if int(d.repl_update.value):
                self.events.append((self.cyc, 'repl_update', {
                    'way': int(d.repl_hit_way.value),
                }))
            if int(d.snoop_ready.value):
                self.events.append((self.cyc, 'snoop_ready', None))

    async def _pf_invariant(self):
        """BypassNeverAnswersInvalid: asserted EVERY cycle.

        Tracks the pending fill from the tap events (fill_start arms for
        READ_SHARED/READ_UNIQUE only -- an upgrade carries no fill data and
        must NOT arm the bypass, MAS ch02/02). While a snoop targeting the
        pending line is open (req raised through the final CD beat):
          - at the grant cycle the CRRESP must be the Table 3.0 decode at
            the POST-FILL state (never the pre-fill Invalid row);
          - the bypass's post-fill state is never STATE_I;
          - the DUT never presents a CD beat the fill has not delivered.
        """
        d = self.dut
        while True:
            await self._negedge_settled()
            if int(d.fill_start.value):
                cls = int(d.fill_req_class.value)
                self.inv_pf_line = int(d.fill_addr.value) >> self.OFFSET_BITS
                self.inv_pf_state = 'S' if cls == ACE_READ_SHARED else 'M'
                self.inv_pf_beats = set()
                self.inv_pf_active = cls != ACE_CLEAN_UNIQUE
            if int(d.data_wr_en.value) and not int(d.ctrl_data_wr_en.value):
                self.inv_pf_beats.add(int(d.data_wr_addr.value)
                                      & (self.FILL_BEATS - 1))
            if int(d.fill_done.value):
                self.inv_pf_active = False
            if (self.inv_sn_open and self.inv_pf_active
                    and self.inv_sn_line == self.inv_pf_line):
                res = oracle_step(self.inv_pf_state, self.inv_sn_name)
                if int(d.snoop_ready.value) and int(d.snoop_req.value):
                    got = int(d.ctrl_crresp.value)
                    self._score('pf invariant: answers at post-fill state',
                                got, res.crresp)
                self._score('pf invariant: post-fill state is not Invalid',
                            self.inv_pf_state == 'I', False)
                if int(d.ctrl_cdvalid.value):
                    self._score('pf invariant: no CD beat before received',
                                self.inv_cd_beat in self.inv_pf_beats, True)

    async def _victim_way_tracker(self):
        """The fill stub needs the install way; it observes the same repl
        tap the DUT uses (timing-only modeling, D-12)."""
        while True:
            await self._negedge_settled()
            if int(self.dut.repl_req.value):
                self.stub_victim_way = int(self.dut.repl_victim_way.value)

    async def _fill_stub(self):
        """amber_fill timing model: on fill_start, deliver FILL_BEATS beats
        into the data array (read-data class only -- CLEAN_UNIQUE carries no
        data), strobing each beat index to control (pf_data_valid update,
        MAS ch02/06), then fill_done after FILL_DONE_DELAY cycles. Drives
        land on the falling edge so the pulse is visible to the DUT's next
        sampling posedge and to the negedge monitor in the same cycle."""
        d = self.dut
        full_be = (1 << self.STRB_W) - 1
        while True:
            await self._negedge_settled()
            if not int(d.fill_start.value):
                continue
            addr = int(d.fill_addr.value)
            cls = int(d.fill_req_class.value)
            set_idx = (addr >> self.OFFSET_BITS) & self.SET_MASK
            if cls != ACE_CLEAN_UNIQUE:
                line = self._line_of(addr)
                line_data = bytes(self._mem_line(line))
                for b in range(self.FILL_BEATS):
                    await self._negedge()
                    d.fillbeat_wr_en.value = 1
                    d.fillbeat_wr_addr.value = (set_idx << self.BEAT_BITS) | b
                    d.fillbeat_wr_way.value = self.stub_victim_way
                    d.fillbeat_wr_data.value = self._beat_of_line(line_data, b)
                    d.fillbeat_wr_be.value = full_be
                    d.fill_beat_valid.value = 1
                    d.fill_beat_idx.value = b
                await self._negedge()
                d.fillbeat_wr_en.value = 0
                d.fill_beat_valid.value = 0
                d.fill_beat_idx.value = 0
            for _ in range(FILL_DONE_DELAY):
                await self._negedge()
            d.fill_done.value = 1
            await self._negedge()
            d.fill_done.value = 0

    async def _drain_stub(self):
        """amber_drain timing model: drain_start -> fixed-latency burst ->
        drain_done pulse. Protocol (the writeback itself) is scoreboard."""
        d = self.dut
        while True:
            await self._negedge_settled()
            if not int(d.drain_start.value):
                continue
            for _ in range(self.drain_latency):
                await self._negedge()
            d.drain_done.value = 1
            await self._negedge()
            d.drain_done.value = 0

    # ------------------------------------------------------------------
    # request driver (frontend stub timing: valid held until ready)
    # ------------------------------------------------------------------
    async def _req_issue(self, addr, we, be, wdata, label=''):
        d = self.dut
        await self._negedge_settled()
        d.req_valid.value = 1
        d.req_addr.value = addr
        d.req_we.value = we
        d.req_be.value = be
        d.req_wdata.value = wdata
        # wait for the accept (req_ready in the current cycle)
        waited = 0
        while True:
            await Timer(500, units='ps')
            if int(d.ctrl_req_ready.value):
                break
            waited += 1
            if waited > 50:
                raise RuntimeError(f"{label}: request never accepted; "
                                   f"state={int(d.ctrl_state.value):#x}")
            await FallingEdge(d.clk)
        accept_cyc = self.cyc
        await RisingEdge(d.clk)
        d.req_valid.value = 0
        return accept_cyc

    async def _req_await_rsp(self, accept_cyc, label=''):
        # Event-driven: the monitor records every response pulse, so a
        # response raised while the TB is busy elsewhere (e.g. draining a
        # snoop) is still observed. Exactly one response belongs to the
        # accepted request (blocking pipeline).
        for _ in range(self.RSP_TIMEOUT_CYCLES):
            for cyc, kind, p in self.events:
                if kind == 'rsp' and cyc > accept_cyc:
                    return accept_cyc, cyc, p
            await self._negedge_settled()
        recent = [e for e in self.events[-40:]]
        raise RuntimeError(
            f"{label}: response timeout; recent events: {self._fmt_events(recent)}")

    async def _do_req(self, addr, we, be, wdata, label=''):
        accept = await self._req_issue(addr, we, be, wdata, label)
        return await self._req_await_rsp(accept, label)

    # ------------------------------------------------------------------
    # tap helpers (directed tests)
    # ------------------------------------------------------------------
    async def _wait_tap(self, kind, timeout=1000, pred=None):
        """Await the next tap event of `kind` (from the cursor) matching
        pred; returns (cyc, payload)."""
        start = self.cyc
        while True:
            while self._tap_pos < len(self.events):
                cyc, k, p = self.events[self._tap_pos]
                self._tap_pos += 1
                if k == kind and (pred is None or pred(p)):
                    return cyc, p
            if self.cyc - start > timeout:
                raise RuntimeError(
                    f"_wait_tap({kind}) timed out; state="
                    f"{int(self.dut.ctrl_state.value):#x}")
            await self._negedge_settled()

    async def _wait_fill_beats(self, n, timeout=600):
        start = self.cyc
        got = 0
        while got < n:
            await self._wait_tap('fill_wr', timeout=timeout)
            got += 1
        return self.cyc - start

    def _slice(self, accept_cyc, rsp_cyc):
        return [e for e in self.events if accept_cyc < e[0] <= rsp_cyc]

    def _replay_models(self, sl, set_idx, merge_line, merge_be=None,
                       merge_wdata=None, label=''):
        """Chronological model replay for bespoke (directed) transactions:
        keeps cache_data / line_state / tags / lru correct from the tap
        events. Assertions stay in the directed tests."""
        for cyc, kind, p in sl:
            if kind in ('repl_update', 'repl_hit'):
                self.lru.update(set_idx, p['way'])
            elif kind == 'fill_start':
                if p['class'] != ACE_CLEAN_UNIQUE:
                    line = p['addr'] >> self.OFFSET_BITS
                    self.cache_data[line] = bytearray(self._mem_line(line))
            elif kind == 'ctrl_wr':
                # the directed merges always target beat 0
                if merge_be is not None:
                    for i in range(self.STRB_W):
                        if merge_be & (1 << i):
                            self.cache_data[merge_line][i] = \
                                (merge_wdata >> (8 * i)) & 0xFF
            elif kind == 'tag_wr':
                way = p['way_oh'].bit_length() - 1
                new_line = ((p['tag_state'] >> 3) << self.SET_BITS) | p['set']
                old = self.tags.get((p['set'], way))
                if old is not None and old != new_line:
                    self.line_state[old] = 'I'
                self.tags[(p['set'], way)] = new_line
                dec = self._decode_state(p['tag_state'] & 0x7)
                self.line_state[new_line] = dec
                self.slot_state[(p['set'], way)] = dec

    # ------------------------------------------------------------------
    # snoop driver: models the amber_snoop_resp core-facing contract
    # ------------------------------------------------------------------
    async def _snoop(self, line, snoop, label, exp_ref=None, exp_crresp=None,
                     exp_line=None, cd_hold=0, exp_tag_write=None,
                     update_model=True):
        """Issue one snoop (held until ready), score the response against
        the oracle decode at exp_ref (default: the line's model state), and
        consume the CD beats when CRRESP.DataTransfer is set. exp_line is
        the expected beat content (defaults to the model cache content).
        exp_tag_write overrides the tag-downgrade expectation (the
        draining-victim and stale-victim cases suppress it)."""
        d = self.dut
        addr = (line & self.LINE_MASK) << self.OFFSET_BITS
        st = self.line_state.get(line, 'I')
        if exp_crresp is None:
            res = oracle_step(exp_ref if exp_ref is not None else st, snoop)
            exp_crresp = res.crresp
            exp_next = res.next_state
        else:
            exp_next = None
        if exp_tag_write is None:
            exp_tag_write = (st != 'I' and exp_next is not None
                             and exp_next != st)
        if exp_line is None and (exp_crresp >> CRRESP_DT) & 1:
            exp_line = bytes(self.cache_data.get(
                line, bytearray(self.LINE_BYTES)))

        # invariant + CD bookkeeping for the EVERY-CYCLE pf checks
        self.inv_sn_open = True
        self.inv_sn_line = line
        self.inv_sn_name = snoop
        self.inv_cd_beat = 0

        grant_cyc = None
        try:
            await self._negedge_settled()
            d.snoop_req.value = 1
            d.snoop_type.value = SNOOP_CODES[snoop]
            d.snoop_addr.value = addr
            for _ in range(self.RSP_TIMEOUT_CYCLES):
                await Timer(500, units='ps')
                if int(d.snoop_ready.value):
                    grant_cyc = self.cyc
                    got_crresp = int(d.ctrl_crresp.value)
                    break
                await FallingEdge(d.clk)
            if grant_cyc is None:
                raise RuntimeError(
                    f"{label}: snoop never granted; state="
                    f"{int(d.ctrl_state.value):#x}")
            # the pf invariant owns the CRRESP check for pending-line
            # snoops; otherwise the driver scores it here
            if not (self.inv_pf_active and line == self.inv_pf_line):
                self._score(f"{label} crresp", got_crresp, exp_crresp)
            await FallingEdge(d.clk)          # grant handshake posedge
            await Timer(500, units='ps')
            d.snoop_req.value = 0

            if (exp_crresp >> CRRESP_DT) & 1:
                self._score(f"{label} exp_line provided",
                            exp_line is not None, True)
                for b in range(self.FILL_BEATS):
                    beat_exp = self._beat_of_line(exp_line, b)
                    # wait for the beat mid-cycle; the DUT may stall it
                    # (pf bits). Data/last are sampled in the SAME cycle
                    # the beat is presented -- the handshake only happens
                    # at the cycle-ending posedge (cdready has been held
                    # high since the request, so each presented beat
                    # transfers at that posedge).
                    held = 0
                    while not int(d.ctrl_cdvalid.value):
                        await self._negedge_settled()
                        held += 1
                        if held > self.RSP_TIMEOUT_CYCLES:
                            raise RuntimeError(f"{label}: beat {b} never valid")
                    self.inv_cd_beat = b
                    if cd_hold and b == 0:
                        # backpressure: with cdready low no handshake can
                        # occur, so the presented beat must hold stable on
                        # CD until it is released; it is sampled BEFORE
                        # the release drive lands
                        d.cd_ready_in.value = 0
                        for _ in range(cd_hold):
                            await self._negedge_settled()
                            self._score(f"{label} stalled beat stable",
                                        int(d.ctrl_cddata.value), beat_exp)
                            self._score(f"{label} stalled cdvalid held",
                                        int(d.ctrl_cdvalid.value), 1)
                        self._score(f"{label} beat{b} data",
                                    int(d.ctrl_cddata.value), beat_exp)
                        self._score(f"{label} beat{b} last",
                                    int(d.ctrl_cdlast.value),
                                    1 if b == self.FILL_BEATS - 1 else 0)
                    else:
                        self._score(f"{label} beat{b} data",
                                    int(d.ctrl_cddata.value), beat_exp)
                        self._score(f"{label} beat{b} last",
                                    int(d.ctrl_cdlast.value),
                                    1 if b == self.FILL_BEATS - 1 else 0)
                    d.cd_ready_in.value = 1
                    await RisingEdge(d.clk)   # beat handshake posedge
                    await Timer(500, units='ps')
                # tail: no extra beats
                for _ in range(2):
                    self._score(f"{label} no extra beat",
                                int(d.ctrl_cdvalid.value), 0)
                    await self._negedge_settled()
            else:
                await self._negedge_settled()
                self._score(f"{label} no CD beats", int(d.ctrl_cdvalid.value),
                            0)
                await self._negedge_settled()

            self._score(f"{label} ctrl_state SNOOP entered",
                        self._state_seen(ST_SNOOP, grant_cyc - 1), True)

            # tag downgrade/invalidate write, applied on the next free
            # port-A cycle (inside the CTRL_SNOOP service -- the window is
            # exactly the SNOOP state's lifetime, so a fill install of the
            # same line right after the service is not mistaken for the
            # snoop's own write)
            wr = self._find_tag_write_snoop(grant_cyc, line)
            self._score(f"{label} tag write", wr is not None, exp_tag_write)
            if wr is not None:
                self._score(f"{label} tag write state", wr['tag_state'] & 0x7,
                            STATE_CODE[exp_next] if exp_next else None)
                self._score(f"{label} tag write set", wr['set'],
                            self._set_of_line(line))
                wr_way = wr['way_oh'].bit_length() - 1
                self.slot_state[(wr['set'], wr_way)] = exp_next

            if update_model and exp_next is not None:
                self.line_state[line] = exp_next
        finally:
            self.inv_sn_open = False
            d.snoop_req.value = 0
            d.cd_ready_in.value = 0
        self.snoops += 1
        return grant_cyc

    def _state_seen(self, st, since_cyc):
        return any(k == 'state' and p == st and c > since_cyc
                   for c, k, p in self.events)

    def _find_tag_write_snoop(self, grant_cyc, line):
        """The snoop-driven downgrade write for `line`, stamped within the
        CTRL_SNOOP state's lifetime (entry..exit state events)."""
        set_idx = self._set_of_line(line)
        tag = (line >> self.SET_BITS) & ((1 << (self.ADDR_WIDTH - self.SET_BITS
                                                - self.OFFSET_BITS)) - 1)
        entry = exit_cyc = None
        for cyc, kind, p in self.events:
            if kind != 'state' or cyc < grant_cyc:
                continue
            if entry is None:
                if p == ST_SNOOP:
                    entry = cyc
                continue
            exit_cyc = cyc
            break
        if entry is None:
            return None
        # Inclusive both ends: a one-cycle service (no-DT response) has
        # its complete-cycle write stamped at the SAME cycle as the
        # SNOOP-entry event, and a DT response's write stamps at the
        # exit boundary -- both must be inside.
        for cyc, kind, p in self.events:
            if (kind == 'tag_wr' and entry <= cyc <= (exit_cyc or entry)
                    and p['set'] == set_idx and (p['tag_state'] >> 3) == tag):
                return p
        return None

    # ------------------------------------------------------------------
    # one scored transaction, lockstep against the oracle
    # ------------------------------------------------------------------
    def _fmt_events(self, evts):
        out = []
        for cyc, kind, payload in evts:
            if kind == 'state':
                out.append(f"{cyc}:{STATE_NAMES.get(payload, payload)}")
            else:
                out.append(f"{cyc}:{kind}")
        return ' '.join(out)

    async def _txn(self, addr, we, be=None, wdata=None, label=''):
        if be is None:
            be = random.randrange(1, 1 << self.STRB_W) if we \
                else (1 << self.STRB_W) - 1
        if wdata is None:
            wdata = random.getrandbits(self.STRB_W * 8) if we else 0

        line = self._line_of(addr)
        set_idx = self._set_of_line(line)
        beat = (addr >> (self.STRB_W.bit_length() - 1)) & (self.FILL_BEATS - 1)
        st = self.line_state.get(line, 'I')
        res = oracle_step(st, 'CPU_WR' if we else 'CPU_RD')

        accept_cyc, rsp_cyc, rsp_data = await self._do_req(addr, we, be, wdata,
                                                           label)
        sl = self._slice(accept_cyc, rsp_cyc)
        self._score_slice(addr, line, set_idx, beat, we, be, wdata, res,
                          rsp_data, sl, label)
        self.txns += 1

    def _score_slice(self, addr, line, set_idx, beat, we, be, wdata, res,
                     rsp_data, sl, label):

        kinds = [k for _, k, _ in sl]
        states = [p for _, k, p in sl if k == 'state']
        upgrade = res.req == 'CLEAN_UNIQUE'
        miss = res.result == 'MISS'

        # Pre-transaction victim prediction (the slice processing mutates the
        # models: eviction accounting flips the victim's line state, so the
        # dirty/clean decision must be taken here, before the replay).
        model_victim_way = self.lru.victim(set_idx) if (miss and not upgrade) \
            else None
        model_victim_line = self.tags.get((set_idx, model_victim_way)) \
            if model_victim_way is not None else None
        # way-exact dirty check: the slot's own state decides (an evicted
        # line is re-accounted by line, but the slot may hold a different
        # line -- or a stale {tag, I} duplicate -- by the time it is
        # selected as a victim)
        victim_dirty = (model_victim_way is not None
                        and self.slot_state.get(
                            (set_idx, model_victim_way), 'I') == 'M')

        # ---- FSM path vs oracle result --------------------------------
        self._score(f"{label} LOOKUP entered", ST_LOOKUP in states, True)
        if not miss:
            exp_hit_state = ST_HIT_WR if we else ST_HIT_RD
            self._score(f"{label} hit service state", exp_hit_state in states,
                        True)
            self._score(f"{label} hit: no miss machinery",
                        any(k in kinds for k in
                            ('fill_start', 'drain_start', 'victim_load',
                             'repl_req')), False)
        else:
            if upgrade:
                self._score(f"{label} upgrade: no victim select",
                            ST_MISS_VICTIM in states, False)
            else:
                self._score(f"{label} MISS_VICTIM entered",
                            ST_MISS_VICTIM in states, True)
            self._score(f"{label} FILL_WRITE entered",
                        ST_FILL_WRITE in states, True)
            self._score(f"{label} REPLAY entered", ST_REPLAY in states, True)
            self._score(f"{label} replay hit state",
                        (ST_HIT_WR if we else ST_HIT_RD) in states, True)

        # ---- response --------------------------------------------------
        rsp_evts = [p for _, k, p in sl if k == 'rsp']
        self._score(f"{label} exactly one response", len(rsp_evts), 1)
        if we:
            exp_rsp = wdata
        elif miss:
            # read miss: the fill snapshot is the memory-side line
            exp_rsp = self._beat_of_line(self._mem_line(line), beat)
        else:
            exp_rsp = self._beat_of_line(self.cache_data.get(
                line, bytearray(self.LINE_BYTES)), beat)
        self._score(f"{label} rsp data", rsp_data, exp_rsp)

        # ---- model replay of the slice (chronological) -----------------
        tag_low = 3
        exp_class = ORACLE_REQ_TO_ACE[res.req] if res.req else None
        install_state = 'S' if res.req == 'READ_SHARED' else 'M'
        pending_victim = None
        installed_way = None
        n_fill_start = 0
        n_drain = 0
        n_vload = 0
        n_ctrl_wr = 0
        n_fill_wr = 0

        for cyc, kind, p in sl:
            if kind == 'repl_req':
                self._score(f"{label} victim way", p['victim_way'],
                            model_victim_way)
            elif kind == 'victim_load':
                n_vload += 1
                vline = self._line_of(p['addr'])
                self._score(f"{label} victim addr", vline,
                            model_victim_line)
                exp_data = int.from_bytes(bytes(self.cache_data[vline]),
                                          'little')
                self._score(f"{label} victim data", p['data'], exp_data)
                pending_victim = (vline, bytes(self.cache_data[vline]))
            elif kind == 'drain_start':
                n_drain += 1
            elif kind == 'drain_done':
                # the dirty victim retires to the memory side; a later fill
                # of this line (directed re-read / FULL random) is what
                # proves the writeback payload end to end
                if pending_victim is not None:
                    vline, vdata = pending_victim
                    self.mem[vline] = bytearray(vdata)
                    pending_victim = None
            elif kind == 'fill_start':
                n_fill_start += 1
                self._score(f"{label} fill addr", p['addr'] >> self.OFFSET_BITS,
                            line)
                self._score(f"{label} fill class", p['class'], exp_class)
                # the fill snapshot installs the raw memory-side line --
                # a CLEAN_UNIQUE upgrade carries NO beats and must not
                # reset the line's data model (the S line's bytes, merges
                # included, survive the upgrade)
                if p['class'] != ACE_CLEAN_UNIQUE:
                    self.cache_data[line] = bytearray(self._mem_line(line))
            elif kind == 'fill_wr':
                n_fill_wr += 1
                if installed_way is None and model_victim_way is not None:
                    exp_way_oh = 1 << model_victim_way
                    self._score(f"{label} fill beat way", p['way_oh'],
                                exp_way_oh)
                self._score(f"{label} fill beat be", p['be'],
                            (1 << self.STRB_W) - 1)
                b = p['addr'] & (self.FILL_BEATS - 1)
                self._score(f"{label} fill beat data", p['data'],
                            self._beat_of_line(self.cache_data[line], b))
            elif kind == 'ctrl_wr':
                n_ctrl_wr += 1
                # CPU write merge (hit or replayed D-4 merge)
                way = self._hit_way(set_idx, line)
                self._score(f"{label} ctrl wr way", p['way_oh'],
                            None if way is None else 1 << way)
                self._score(f"{label} ctrl wr be", p['be'], be)
                self._score(f"{label} ctrl wr addr", p['addr'],
                            (set_idx << self.BEAT_BITS) | beat)
                # apply the merge to the model
                lo = beat * self.STRB_W
                for i in range(self.STRB_W):
                    if be & (1 << i):
                        self.cache_data[line][lo + i] = (wdata >> (8 * i)) \
                            & 0xFF
            elif kind == 'tag_wr':
                wr_set = p['set']
                wr_state = p['tag_state'] & 0x7
                wr_tag = p['tag_state'] >> tag_low
                self._score(f"{label} tag wr set", wr_set, set_idx)
                if upgrade:
                    exp_way = self._hit_way(set_idx, line)
                    self._score(f"{label} upgrade tag wr way",
                                p['way_oh'], 1 << exp_way)
                    self._score(f"{label} upgrade install state", wr_state,
                                0x3)  # AMBER_STATE_M
                    self._score(f"{label} upgrade install tag", wr_tag,
                                line >> self.SET_BITS)
                    installed_way = exp_way
                    self.slot_state[(set_idx, exp_way)] = 'M'
                elif miss:
                    self._score(f"{label} install state", wr_state,
                                {'S': 0x1, 'M': 0x3}[install_state])
                    self._score(f"{label} install tag", wr_tag,
                                line >> self.SET_BITS)
                    self._score(f"{label} install way", p['way_oh'],
                                1 << model_victim_way)
                    installed_way = model_victim_way
                    self.slot_state[(set_idx, model_victim_way)] = \
                        install_state
                    # eviction accounting
                    evicted = self.tags.get((set_idx, model_victim_way))
                    if evicted is not None and evicted != line:
                        self.line_state[evicted] = 'I'
                    self.tags[(set_idx, model_victim_way)] = line
                else:
                    self._score(f"{label} hit: unexpected tag write",
                                True, False)
            elif kind == 'repl_update':
                self._score(f"{label} repl_update way", p['way'],
                            installed_way)
                self.lru.update(set_idx, p['way'])
            elif kind == 'repl_hit':
                way = self._hit_way(set_idx, line)
                self._score(f"{label} repl_hit way", p['way'], way)
                if way is not None:
                    self.lru.update(set_idx, way)

        # ---- machinery presence / absence per victim type ---------------
        if miss:
            self._score(f"{label} exactly one fill_start", n_fill_start, 1)
            self._score(f"{label} write merge count", n_ctrl_wr,
                        1 if we else 0)
            self._score(f"{label} fill beat count", n_fill_wr,
                        0 if upgrade else self.FILL_BEATS)
            if upgrade:
                self._score(f"{label} upgrade: no drain", n_drain, 0)
                self._score(f"{label} upgrade: no victim load", n_vload, 0)
            else:
                # victim_dirty was computed before the slice replay (the
                # eviction accounting below mutates line_state mid-slice)
                self._score(f"{label} dirty-victim drain", n_drain,
                            1 if victim_dirty else 0)
                self._score(f"{label} dirty-victim victim_load", n_vload,
                            1 if victim_dirty else 0)
                # ordering: victim_load < drain_start < drain_done < fill
                def idx(k):
                    return next((i for i, e in enumerate(sl) if e[1] == k),
                                None)
                if victim_dirty:
                    i_vl, i_ds, i_dd, i_fs = (idx('victim_load'),
                                              idx('drain_start'),
                                              idx('drain_done'),
                                              idx('fill_start'))
                    self._score(f"{label} drain ordering",
                                None in (i_vl, i_ds, i_dd, i_fs), False)
                    self._score(f"{label} victim_load<drain_start",
                                i_vl < i_ds, True)
                    self._score(f"{label} drain_start<drain_done",
                                i_ds < i_dd, True)
                    self._score(f"{label} drain_done<fill_start",
                                i_dd < i_fs, True)
        else:
            self._score(f"{label} hit: no fill", n_fill_start, 0)
            self._score(f"{label} hit: write merge count", n_ctrl_wr,
                        1 if we else 0)

        # ---- per-line state advance (oracle) ----------------------------
        if miss:
            self.line_state[line] = install_state
        else:
            self.line_state[line] = res.next_state

    def _reset_models(self):
        """Reset-side golden state: the DUT's arrays and repl policy reset
        to the all-Invalid / rank-identity state, so the per-cache models
        follow. The memory-side model survives reset (it is the DRAM)."""
        self.cache_data = {}
        self.line_state = {}
        self.tags = {}
        self.slot_state = {}
        self.lru = LruModel(self.SETS, self.WAYS)

    # ------------------------------------------------------------------
    # InitWalk (Review Focus 7): first req_ready only after every set of
    # every way holds STATE_I. Also covers StrayReqInInit (MINOR 2): a
    # request presented during the walk is ignored (ready is IDLE-only).
    # ------------------------------------------------------------------
    async def _check_init(self):
        d = self.dut
        self._reset_models()
        init_writes = []
        cycles = 0
        # StrayReqInInit: raise a valid request for the first three walk
        # cycles; it must be ignored -- req_ready stays low (IDLE-only),
        # the walk is undisturbed, no LOOKUP is entered, no response
        # raised. Interleaved with the write monitoring so no walk cycle
        # is consumed before the checks start watching.
        stray_left = 3
        d.req_addr.value = self._compose_addr(0x77, 1)
        d.req_we.value = 1
        d.req_be.value = 0xFF
        d.req_wdata.value = 0x5A5A5A5A5A5A5A5A
        walk_start_events = len(self.events)

        while True:
            await self._negedge_settled()
            cycles += 1
            if cycles > self.SETS * 4 + 100:
                raise RuntimeError("init walk never completed")
            if stray_left > 0:
                d.req_valid.value = 1
                stray_left -= 1
                self._score("stray init: req_ready low",
                            int(d.ctrl_req_ready.value), 0)
                if stray_left == 0:
                    d.req_valid.value = 0
            if not int(d.init_busy.value):
                break
            self._score("init: req_ready low while init busy",
                        int(d.ctrl_req_ready.value), 0)
            if int(d.tag_wr_en.value):
                init_writes.append((int(d.tag_wr_set.value),
                                    int(d.tag_wr_way_onehot.value),
                                    int(d.tag_wr_tag_state.value) & 0x7))
        d.req_valid.value = 0
        walk_events = self.events[walk_start_events:]
        self._score("stray init: no LOOKUP entered",
                    any(k == 'state' and p == ST_LOOKUP for _, k, p in
                        walk_events), False)
        self._score("stray init: no response raised",
                    any(k == 'rsp' for _, k, _ in walk_events), False)
        self._score("init: one write per set", len(init_writes), self.SETS)
        for i, (s, way_oh, state) in enumerate(init_writes):
            self._score(f"init: set order[{i}]", s, i)
            self._score(f"init: all ways[{i}]", way_oh, (1 << self.WAYS) - 1)
            self._score(f"init: STATE_I[{i}]", state, 0)
        # functional proof: every set of every way reads back Invalid
        tag_state_width = (self.ADDR_WIDTH - self.SET_BITS
                           - self.OFFSET_BITS) + 3
        for s in range(self.SETS):
            d.tag_b_set.value = s
            await Timer(1, units='ns')
            ts = int(d.tag_b_tag_state.value)
            for w in range(self.WAYS):
                st = (ts >> (w * tag_state_width)) & 0x7
                self._score(f"init: readback set {s} way {w}", st, 0)
        self.log.info(f"InitWalk: {len(init_writes)} sets walked, "
                      f"readback clean")

    # ------------------------------------------------------------------
    # directed scenarios
    # ------------------------------------------------------------------
    async def _hit_sequence(self):
        s0 = 0
        a1 = lambda beat=0: self._compose_addr(0x10, s0, beat)
        a2 = lambda beat=0: self._compose_addr(0x11, s0, beat)

        await self._txn(a1(), 0, label='hit:miss_rd')          # I -> S
        await self._txn(a1(), 0, label='hit:rd_S')            # S read hit
        await self._txn(a1(3), 0, label='hit:rd_S_b3')
        await self._txn(a1(), 1, be=0x0F, wdata=0x1122334455667788,
                        label='hit:upgrade_S')                # S -> M (CLEAN_UNIQUE)
        await self._txn(a1(), 1, be=0xFF, wdata=0xDEADBEEFCAFEF00D,
                        label='hit:wr_M')                     # M write hit (merge)
        await self._txn(a1(), 0, label='hit:rd_M')            # M read hit
        await self._txn(a2(), 0, label='hit:miss_rd_2')       # I -> S (2nd way)
        await self._txn(a2(), 0, label='hit:rd_S_2')
        await self._txn(a1(), 0, label='hit:rd_M_keep')       # still M, data intact
        self.log.info("HitSequence directed done")

    async def _miss_sequence(self):
        # clean victim: fill a fresh set with S lines, evict the eldest
        sc = self.SETS - 1 if self.SETS > 1 else 0
        for i in range(self.WAYS):
            await self._txn(self._compose_addr(0x30 + i, sc), 0,
                            label=f'miss_clean:fill[{i}]')
        await self._txn(self._compose_addr(0x38, sc), 0,
                        label='miss_clean:evict')            # clean eviction

        # dirty victim: write-miss the eldest slot to M, fill the rest, evict
        sd = self.SETS // 2
        await self._txn(self._compose_addr(0x40, sd), 1,
                        label='miss_dirty:wr_miss')          # I -> M
        for i in range(1, self.WAYS):
            await self._txn(self._compose_addr(0x40 + i, sd), 0,
                            label=f'miss_dirty:fill[{i}]')
        await self._txn(self._compose_addr(0x48, sd), 0,
                        label='miss_dirty:evict')            # dirty eviction
        # re-fetch the drained line: the fill must observe the writeback
        await self._txn(self._compose_addr(0x40, sd), 0,
                        label='miss_dirty:refetch')
        # and a write miss with partial be on a fresh line (D-4 merge path)
        se = (self.SETS // 4) * 3
        await self._txn(self._compose_addr(0x50, se, 2), 1, be=0x3C,
                        wdata=0xAABBCCDDEEFF0011,
                        label='miss_dirty:wr_miss_be')
        await self._txn(self._compose_addr(0x50, se, 2), 0,
                        label='miss_dirty:rd_back_be')       # merged data back
        self.log.info("MissSequence directed done")

    async def _illegal_state(self):
        # reach a quiescent point, then corrupt the one-hot FSM vector and
        # expect the sticky CTRL_ERROR contract (MAS ch02 illegal default)
        await self._txn(self._compose_addr(0x60, 1), 0, label='error:pre')
        await self._negedge_settled()
        self._score("error: quiescent in IDLE",
                    int(self.dut.ctrl_state.value), ST_IDLE)
        self.dut.u_control.state_q.value = 0x003   # IDLE|INIT: multi-hot
        await self.wait_clocks('clk', 3)
        await self._negedge_settled()
        self._score("error: CTRL_ERROR sticky", int(self.dut.ctrl_state.value),
                    ST_ERROR)
        self._score("error: req_ready low", int(self.dut.ctrl_req_ready.value),
                    0)
        await self.wait_clocks('clk', 5)
        await self._negedge_settled()
        self._score("error: still sticky", int(self.dut.ctrl_state.value),
                    ST_ERROR)
        # reset is the only exit
        await self.assert_reset()
        await self.wait_clocks('clk', 3)
        await self.deassert_reset()
        await self._check_init()
        await self._txn(self._compose_addr(0x61, 1), 0,
                        label='error:post_recover')
        self.log.info("IllegalStateError directed done")

    async def _be_zero_write(self):
        # MINOR 2: be == 0 merges nothing. Write miss with be=0 installs M
        # with the raw fill data intact; a be=0 write hit leaves the line
        # untouched; read backs return the fill bytes.
        sz = self.SETS // 8
        az = self._compose_addr(0x68, sz)
        line_z = self._line_of(az)
        await self._txn(az, 1, be=0x00, wdata=0x0123456789ABCDEF,
                        label='be0:wr_miss')
        await self._txn(az, 1, be=0x00, wdata=0xFEDCBA9876543210,
                        label='be0:wr_hit')
        self._score("be0: line still M", self.line_state.get(line_z), 'M')
        self._score("be0: no byte merged",
                    bytes(self.cache_data[line_z]),
                    self._mem_line(line_z))
        await self._txn(az, 0, label='be0:rd_back')
        self.log.info("BeZeroWrite directed done")

    # ------------------------------------------------------------------
    # Task 4 directed suite: snoop-during-fill service
    # ------------------------------------------------------------------
    async def _start_miss(self, addr, we, be=0xFF, wdata=0, label='',
                          wait_beats=0):
        """Issue a request and wait until its fill is in flight; returns
        (accept_cyc, fill_start payload) once `wait_beats` beats landed."""
        accept = await self._req_issue(addr, we, be, wdata, label)
        line = self._line_of(addr)
        self._tap_pos = len(self.events)   # this request's taps only
        _, p = await self._wait_tap(
            'fill_start', pred=lambda p: (p['addr'] >> self.OFFSET_BITS) == line)
        if wait_beats:
            await self._wait_fill_beats(wait_beats)
        return accept, p

    def _tag_wr_for(self, sl, line):
        set_idx = self._set_of_line(line)
        tag = line >> self.SET_BITS
        for _, kind, p in sl:
            if kind == 'tag_wr' and p['set'] == set_idx \
                    and (p['tag_state'] >> 3) == tag:
                return p
        return None

    async def _snoop_pending_fill(self):
        # Class (a): pre-RLAST snoop for the pending line is answered with
        # the post-fill state and the beats already received; cd_ready is
        # held low until the late beats arrive (the DUT must stall CD, not
        # forward unreceived beats). The RS downgrade then applies
        # post-commit: the write-miss fill commits S, the replayed write
        # re-upgrades (oracle IM x RS composition), and the line ends M
        # with the store merged.
        sp = 5
        line_x = self._line_of(self._compose_addr(0x70, sp))
        wdata = 0x1122334455667788
        accept, p = await self._start_miss(self._compose_addr(0x70, sp), 1,
                                           wdata=wdata,
                                           label='pf:wr_miss', wait_beats=2)
        self._score("pf: write miss class", p['class'], ACE_READ_UNIQUE)
        exp_line = bytes(self._mem_line(line_x))
        await self._snoop(line_x, 'SNOOP_READ_SHARED', 'pf:rs_mid_fill',
                          exp_ref='M', exp_line=exp_line, cd_hold=6)
        accept, rsp_cyc, rsp_data = await self._req_await_rsp(accept, 'pf:rsp')
        sl = self._slice(accept, rsp_cyc)

        # exactly two fills: READ_UNIQUE, then CLEAN_UNIQUE (re-upgrade)
        fills = [p for _, k, p in sl if k == 'fill_start']
        self._score("pf: two fills (fetch + re-upgrade)", len(fills), 2)
        self._score("pf: first fill class", fills[0]['class'],
                    ACE_READ_UNIQUE)
        self._score("pf: second fill class", fills[1]['class'],
                    ACE_CLEAN_UNIQUE)
        # post-commit downgrade: first install commits S ...
        wr1 = self._tag_wr_for(sl[:next(i for i, e in enumerate(sl)
                                        if e[1] == 'fill_start' and
                                        e[2] is fills[1])], line_x)
        self._score("pf: post-commit downgrade install", wr1['tag_state'] & 0x7,
                    STATE_CODE['S'])
        # ... and the re-upgrade commits M
        wr2 = self._tag_wr_for(
            sl[next(i for i, e in enumerate(sl)
                    if e[1] == 'fill_start' and e[2] is fills[1]):], line_x)
        self._score("pf: re-upgrade install", wr2['tag_state'] & 0x7,
                    STATE_CODE['M'])
        self._score("pf: rsp data", rsp_data, wdata)
        self._replay_models(sl, sp, line_x, merge_be=0xFF, merge_wdata=wdata,
                            label='pf')
        self.log.info("SnoopPendingFillBypass directed done")

    async def _snoop_post_commit(self):
        # Class (b): a snoop applied after the fill commit changes the
        # state normally (tag lookup on port B, downgrade write applied).
        sb = 7
        line_x = self._line_of(self._compose_addr(0x71, sb))
        wdata = 0xCAFEBABEDEADBEEF
        await self._txn(self._compose_addr(0x71, sb), 1, wdata=wdata,
                        label='post:wr_miss')                 # X -> M
        await self._snoop(line_x, 'SNOOP_CLEAN_INVALID', 'post:ci')
        self._score("post: line invalidated", self.line_state.get(line_x),
                    'I')
        # read back: misses again, refills Shared from the memory side
        await self._txn(self._compose_addr(0x71, sb), 0,
                        label='post:rd_back')
        self._score("post: refilled Shared", self.line_state.get(line_x),
                    'S')
        self.log.info("SnoopPostCommitApplies directed done")

    async def _snoop_other_line_mid_fill(self):
        # Class (c): snoops for OTHER lines interleaved mid-fill at legal
        # boundaries are answered from the installed state; the fill is
        # unaffected.
        s0, s1, s2 = 9, 10, 11
        line_x = self._line_of(self._compose_addr(0x72, s0))
        line_y = self._line_of(self._compose_addr(0x73, s1))
        line_z = self._line_of(self._compose_addr(0x74, s2))
        await self._txn(self._compose_addr(0x72, s0), 1, wdata=0x1111222233334444,
                        label='oth:wr_x')                    # X -> M
        await self._txn(self._compose_addr(0x73, s1), 0,
                        label='oth:rd_y')                    # Y -> S
        accept, p = await self._start_miss(self._compose_addr(0x74, s2), 0,
                                           label='oth:rd_z', wait_beats=2)
        self._score("oth: read miss class", p['class'], ACE_READ_SHARED)
        await self._snoop(line_x, 'SNOOP_READ_UNIQUE', 'oth:ru_x')
        await self._snoop(line_y, 'SNOOP_READ_SHARED', 'oth:rs_y')
        line_w = self._line_of(self._compose_addr(0x75, s2))
        await self._snoop(line_w, 'SNOOP_MAKE_INVALID', 'oth:mi_w')
        accept, rsp_cyc, rsp_data = await self._req_await_rsp(accept,
                                                              'oth:rsp')
        sl = self._slice(accept, rsp_cyc)
        fills = [q for _, k, q in sl if k == 'fill_start']
        self._score("oth: fill unaffected", len(fills), 1)
        self._score("oth: fill class", fills[0]['class'], ACE_READ_SHARED)
        wr = self._tag_wr_for(sl, line_z)
        self._score("oth: Z installed S", wr['tag_state'] & 0x7,
                    STATE_CODE['S'])
        self._score("oth: rsp = Z mem beat", rsp_data,
                    self._beat_of_line(self._mem_line(line_z), 0))
        self._replay_models(sl, s2, line_z, label='oth')
        # X was invalidated (refill now); Y is still Shared and hits
        await self._txn(self._compose_addr(0x72, s0), 0,
                        label='oth:rd_x_back')
        self._score("oth: X refilled S", self.line_state.get(line_x), 'S')
        await self._txn(self._compose_addr(0x73, s1), 0,
                        label='oth:rd_y_back')
        self._score("oth: Y still S", self.line_state.get(line_y), 'S')
        self.log.info("SnoopOtherLineMidFill directed done")

    async def _im_pending_clear_corner(self):
        # Pinned Task-2-review corner (ImStepPendingClearCorner): an
        # in-flight pending 'I' is NOT cleared by a later shared-domain
        # snoop -- invalidation-sticks. A write miss; an invalidating
        # snoop arms pending 'I'; a READ_SHARED snoop is STILL answered at
        # the post-fill M state (DT set, never the pre-fill Invalid row);
        # the fill commits I; the replayed write re-fetches and ends M.
        sc = 13
        line_x = self._line_of(self._compose_addr(0x76, sc))
        wdata = 0xA5A5A5A55A5A5A5A
        accept, _ = await self._start_miss(self._compose_addr(0x76, sc), 1,
                                           wdata=wdata, label='imc:wr_miss',
                                           wait_beats=1)
        await self._snoop(line_x, 'SNOOP_READ_UNIQUE', 'imc:ru', exp_ref='M',
                          exp_line=bytes(self._mem_line(line_x)))
        await self._snoop(line_x, 'SNOOP_READ_SHARED', 'imc:rs',
                          exp_ref='M',
                          exp_line=bytes(self._mem_line(line_x)))
        accept, rsp_cyc, rsp_data = await self._req_await_rsp(accept,
                                                              'imc:rsp')
        sl = self._slice(accept, rsp_cyc)
        fills = [p for _, k, p in sl if k == 'fill_start']
        self._score("imc: two fills (fetch + re-fetch)", len(fills), 2)
        self._score("imc: both fills READ_UNIQUE",
                    [p['class'] for p in fills],
                    [ACE_READ_UNIQUE, ACE_READ_UNIQUE])
        second = next(i for i, e in enumerate(sl)
                      if e[1] == 'fill_start' and e[2] is fills[1])
        wr1 = self._tag_wr_for(sl[:second], line_x)
        wr2 = self._tag_wr_for(sl[second:], line_x)
        self._score("imc: invalidation sticks (commit I)", wr1['tag_state'] & 0x7,
                    STATE_CODE['I'])
        self._score("imc: re-fetch installs M", wr2['tag_state'] & 0x7,
                    STATE_CODE['M'])
        self._score("imc: rsp data", rsp_data, wdata)
        self._replay_models(sl, sc, line_x, merge_be=0xFF, merge_wdata=wdata,
                            label='imc')
        self.log.info("ImStepPendingClearCorner directed done")

    async def _upgrade_snoop_suite(self):
        # MINOR 1 pin (UpgradeNoBypassArm): an upgrade has NO fill data in
        # flight, so it must NOT arm the bypass (MAS ch02/02). A shared
        # snoop during the upgrade is answered from the installed S entry
        # (no data transfer).
        su = min(15, self.SETS - 1)
        line_a = self._line_of(self._compose_addr(0x78, su))
        wdata = 0x0BADC0DE0DDC0DE0
        await self._txn(self._compose_addr(0x78, su), 0,
                        label='upa:rd_a')                    # A -> S
        accept, p = await self._start_miss(self._compose_addr(0x78, su), 1,
                                           wdata=wdata, label='upa:upgrade')
        self._score("upa: upgrade class", p['class'], ACE_CLEAN_UNIQUE)
        self._score("upa: bypass not armed during upgrade",
                    self.inv_pf_active, False)
        await self._snoop(line_a, 'SNOOP_READ_SHARED', 'upa:rs',
                          exp_ref='S')
        accept, rsp_cyc, rsp_data = await self._req_await_rsp(accept,
                                                              'upa:rsp')
        sl = self._slice(accept, rsp_cyc)
        fills = [q for _, k, q in sl if k == 'fill_start']
        self._score("upa: exactly one fill (the upgrade)", len(fills), 1)
        self._score("upa: no fill beats",
                    sum(1 for _, k, _ in sl if k == 'fill_wr'), 0)
        self._score("upa: rsp data", rsp_data, wdata)
        self._replay_models(sl, su, line_a, merge_be=0xFF, merge_wdata=wdata,
                            label='upa')
        self._score("upa: final state M", self.line_state.get(line_a), 'M')

        # UpgradeKilledByInvalidatingSnoop: SM x Inv -> IM (gem5
        # .sm:1526) realized as commit-I + replay re-fetch.
        sv = min(17, self.SETS - 2)
        line_b = self._line_of(self._compose_addr(0x79, sv))
        wdata_b = 0x13579BDF2468ACE0
        await self._txn(self._compose_addr(0x79, sv), 0,
                        label='upk:rd_b')                    # B -> S
        accept, p = await self._start_miss(self._compose_addr(0x79, sv), 1,
                                           wdata=wdata_b, label='upk:upgrade')
        self._score("upk: upgrade class", p['class'], ACE_CLEAN_UNIQUE)
        await self._snoop(line_b, 'SNOOP_READ_UNIQUE', 'upk:ru', exp_ref='S',
                          exp_tag_write=False)
        accept, rsp_cyc, rsp_data = await self._req_await_rsp(accept,
                                                              'upk:rsp')
        sl = self._slice(accept, rsp_cyc)
        fills = [q for _, k, q in sl if k == 'fill_start']
        self._score("upk: upgrade converted to a fetch", len(fills), 2)
        self._score("upk: classes",
                    [q['class'] for q in fills],
                    [ACE_CLEAN_UNIQUE, ACE_READ_UNIQUE])
        second = next(i for i, e in enumerate(sl)
                      if e[1] == 'fill_start' and e[2] is fills[1])
        wr1 = self._tag_wr_for(sl[:second], line_b)
        wr2 = self._tag_wr_for(sl[second:], line_b)
        self._score("upk: killed upgrade commits I", wr1['tag_state'] & 0x7,
                    STATE_CODE['I'])
        self._score("upk: re-fetch installs M", wr2['tag_state'] & 0x7,
                    STATE_CODE['M'])
        self._score("upk: rsp data", rsp_data, wdata_b)
        self._replay_models(sl, sv, line_b, merge_be=0xFF, merge_wdata=wdata_b,
                            label='upk')
        self.log.info("Upgrade snoop suite directed done")

    async def _victim_snoop_suite(self):
        # SnoopDrainingVictim: a snoop for the dirty victim while the
        # drain is outstanding is served from the staged line at M
        # (SINK_WB_ACK; gem5 .sm:1352 -- the victim buffer still owns the
        # data until the WB ack).
        sdv = self.SETS // 2 - 2
        line_v = self._line_of(self._compose_addr(0x7A, sdv))
        await self._txn(self._compose_addr(0x7A, sdv), 1,
                        wdata=0xC001D00DFEEDFACE,
                        label='vic:wr_v')                    # V -> M
        for i in range(1, self.WAYS):
            await self._txn(self._compose_addr(0x7A + i, sdv), 0,
                            label=f'vic:fill[{i}]')
        accept = await self._req_issue(self._compose_addr(0x7F, sdv), 0,
                                       (1 << self.STRB_W) - 1, 0,
                                       'vic:evict_miss')
        await self._wait_tap('victim_load',
                             pred=lambda p: self._line_of(p['addr']) == line_v)
        await self._wait_tap('drain_start')
        await self._snoop(line_v, 'SNOOP_READ_UNIQUE', 'vic:ru_mid_drain',
                          exp_ref='M', exp_line=bytes(self.cache_data[line_v]),
                          exp_tag_write=False)
        accept, rsp_cyc, _ = await self._req_await_rsp(accept, 'vic:rsp')
        sl = self._slice(accept, rsp_cyc)
        self._score("vic: drain ran after the snoop",
                    any(k == 'drain_done' for _, k, _ in sl), True)
        self._score("vic: fill ran after the drain",
                    any(k == 'fill_start' for _, k, _ in sl), True)
        # the generic slice scorer owns the models for this transaction
        # (victim dirty path, refill round trip, WB payload retirement)
        line_new = self._line_of(self._compose_addr(0x7F, sdv))
        set_idx = self._set_of_line(line_new)
        st = self.line_state.get(line_new, 'I')
        res = oracle_step(st, 'CPU_RD')
        rsp_evts = [p for _, k, p in sl if k == 'rsp']
        rsp_data = rsp_evts[0] if rsp_evts else None
        self._score_slice(self._compose_addr(0x7F, sdv), line_new, set_idx,
                          0, 0, (1 << self.STRB_W) - 1, 0, res, rsp_data,
                          sl, 'vic')
        self.txns += 1
        self._score("vic: victim retired to memory",
                    bytes(self._mem_line(line_v)),
                    bytes(self.cache_data[line_v]))
        # re-fetch the victim: the writeback payload must come back
        await self._txn(self._compose_addr(0x7A, sdv), 0,
                        label='vic:refetch')
        self._score("vic: refetch returns the drained data",
                    self.line_state.get(line_v), 'S')

        # SnoopStaleVictimMidFill: once the drain has completed (WB ack
        # ordering: drain_done < fill_start), the victim line belongs to
        # the memory side; a snoop for it during the fill is answered
        # Invalid, no transfer (M_I x WB_Ack -> I, gem5 .sm:1315 -- the
        # local copy is being overwritten by the fill beats and must not
        # be re-served). Same set-up shape as the draining case: dirty
        # victim, evicting miss, but the snoop fires after fill_start.
        sds = self.SETS // 2 - 4
        line_vs = self._line_of(self._compose_addr(0x6A, sds))
        await self._txn(self._compose_addr(0x6A, sds), 1,
                        wdata=0x0DDBADC0FFEE1234,
                        label='stale:wr_v')                  # V -> M
        for i in range(1, self.WAYS):
            await self._txn(self._compose_addr(0x6A + i, sds), 0,
                            label=f'stale:fill[{i}]')
        accept = await self._req_issue(self._compose_addr(0x6F, sds), 0,
                                       (1 << self.STRB_W) - 1, 0,
                                       'stale:evict_miss')
        line_n = self._line_of(self._compose_addr(0x6F, sds))
        await self._wait_tap('fill_start',
                             pred=lambda p: (p['addr'] >> self.OFFSET_BITS)
                             == line_n)
        await self._wait_fill_beats(2)
        self._score("stale: victim still the installed tag (pre-install)",
                    self._hit_way(self._set_of_line(line_vs), line_vs) is not
                    None, True)
        await self._snoop(line_vs, 'SNOOP_CLEAN_INVALID', 'stale:ci_mid_fill',
                          exp_crresp=0, exp_tag_write=False,
                          update_model=False)
        accept, rsp_cyc, rsp_data = await self._req_await_rsp(accept,
                                                              'stale:rsp')
        sl = self._slice(accept, rsp_cyc)
        set_idx = self._set_of_line(line_n)
        st = self.line_state.get(line_n, 'I')
        res = oracle_step(st, 'CPU_RD')
        self._score_slice(self._compose_addr(0x6F, sds), line_n, set_idx, 0,
                          0, (1 << self.STRB_W) - 1, 0, res, rsp_data, sl,
                          'stale')
        self.txns += 1
        # the evicting transaction's install evicted the victim: a
        # refetch proves the writeback payload survived the race
        await self._txn(self._compose_addr(0x6A, sds), 0,
                        label='stale:refetch')
        self._score("stale: refetch returns the drained data",
                    self.line_state.get(line_vs), 'S')
        self.log.info("Victim snoop suite directed done")

    async def _full_random(self):
        n = self.FULL_TXN[self.TEST_LEVEL]
        pool_tags = 4 * self.WAYS + 2
        prev_line = None
        for i in range(n):
            if prev_line is not None and random.random() < 0.3:
                line = prev_line
            else:
                s = random.randrange(self.SETS)
                t = random.randrange(pool_tags)
                line = (t << (self.SET_BITS + self.OFFSET_BITS)) \
                    | (s << self.OFFSET_BITS)
            prev_line = line
            beat = random.randrange(self.FILL_BEATS)
            addr = line | (beat << (self.STRB_W.bit_length() - 1))
            we = random.random() < 0.5
            await self._txn(addr, 1 if we else 0, label=f'full[{i}]')
            # idle snoop soak: a random snoop on a random pool line while
            # the pipeline is quiescent; the response is decoded at the
            # line's model state and the downgrade/invalidate applies
            if random.random() < 0.25:
                s = random.randrange(self.SETS)
                t = random.randrange(pool_tags)
                sline = (t << (self.SET_BITS + self.OFFSET_BITS)) \
                    | (s << self.OFFSET_BITS)
                await self._snoop(sline, random.choice(list(SNOOP_CODES)),
                                  f'full_sn[{i}]')
            if i % 2000 == 0:
                self.mark_progress(f"full random {i}/{n}")
        self.log.info(f"FULL random lockstep: {n} transactions scored, "
                      f"{self.snoops} idle snoops soaked")

    # ------------------------------------------------------------------
    async def run(self):
        await self._check_init()
        self.scenarios['InitWalk'] = True
        self.scenarios['StrayReqInInit'] = True
        await self._hit_sequence()
        self.scenarios['HitSequence'] = True
        if self.TEST_LEVEL in ('func', 'full'):
            await self._miss_sequence()
            self.scenarios['MissSequence'] = True
            await self._illegal_state()
            self.scenarios['IllegalStateError'] = True
            await self._be_zero_write()
            self.scenarios['BeZeroWrite'] = True
            await self._snoop_pending_fill()
            self.scenarios['SnoopPendingFillBypass'] = True
            await self._snoop_post_commit()
            self.scenarios['SnoopPostCommitApplies'] = True
            await self._snoop_other_line_mid_fill()
            self.scenarios['SnoopOtherLineMidFill'] = True
            await self._im_pending_clear_corner()
            self.scenarios['ImStepPendingClearCorner'] = True
            await self._upgrade_snoop_suite()
            self.scenarios['UpgradeNoBypassArm'] = True
            self.scenarios['UpgradeKilledByInvalidatingSnoop'] = True
            await self._victim_snoop_suite()
            self.scenarios['SnoopDrainingVictim'] = True
            self.scenarios['SnoopStaleVictimMidFill'] = True
        if self.TEST_LEVEL == 'full':
            await self._full_random()
            self.scenarios['FullRandomLockstep'] = True
            self.scenarios['IdleSnoopSoak'] = True
        return self.mismatches == 0

    def get_test_report(self):
        return {'checks': self.checks, 'mismatches': self.mismatches,
                'transactions': self.txns, 'snoops': self.snoops,
                'scenarios': self.scenarios}
