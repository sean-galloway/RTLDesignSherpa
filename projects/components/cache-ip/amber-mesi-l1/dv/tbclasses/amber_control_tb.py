"""
amber_control testbench

Blocking-pipeline control FUB bring-up (Task 3), scored lockstep against the
Task 2 gem5-derived oracle (dv/golden/amber_fsm_oracle.py). The harness
(dv/tb/amber_control_th.sv) wires the DUT to the landed tag/data/repl arrays;
this TB models the partner handshakes (frontend/fill/drain/victim/snoop)
timing-only per D-12 -- never protocol.

Golden models carried here (independent copies, kmap-TB rule: no shared code
with the DUT):
  memory-side line content   self.mem -- written by drains, read by fills
  cache line content         self.cache_data -- installed by fills, merged
                             by CPU writes (D-4 merge on the replayed hit)
  per-line MESI state        self.line_state -- advanced with oracle.step()
  (set, way) -> line tag     self.tags -- eviction accounting
  true-LRU policy            LruModel -- reset + update parity with amber_repl

Levels (TEST_LEVEL):
  gate  -- InitWalk + directed HitSequence (rd/wr hits per reachable state,
           policy-update checks vs the oracle)
  func  -- + MissSequence (clean victim, dirty victim, upgrade) and the
           sticky CTRL_ERROR illegal-state directed test
  full  -- + randomized stream, 10k transactions, oracle lockstep per
           transaction (seeds pinned by the repo-root conftest)

Author: RTL Design Sherpa
Created: 2026-10-07
"""

import os
import random

import cocotb
from cocotb.triggers import RisingEdge, FallingEdge, Timer

from TBClasses.shared.tbbase import TBBase

from projects.components.cache_ip.amber_mesi_l1.dv.golden.amber_fsm_oracle import (
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

# amber_ace_req_t encodings (amber_pkg): fill request classes
ACE_READ_SHARED, ACE_READ_UNIQUE, ACE_CLEAN_UNIQUE = 0, 1, 2

# partner stub timing knobs (handshake timing only, D-12)
FILL_DONE_DELAY = 2          # cycles between last beat and fill_done
DRAIN_LATENCY = None         # set per-geometry: FILL_BEATS + 2

# request classes the oracle emits, mapped to the pkg encoding
ORACLE_REQ_TO_ACE = {
    'READ_SHARED': ACE_READ_SHARED,
    'READ_UNIQUE': ACE_READ_UNIQUE,
    'CLEAN_UNIQUE': ACE_CLEAN_UNIQUE,
}


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
        self.lru = LruModel(self.SETS, self.WAYS)

        # observation log: (cyc, kind, payload); cyc ticks at negedge
        self.events = []
        self.cyc = 0
        self.stub_victim_way = 0

        # scorekeeping
        self.checks = 0
        self.mismatches = 0
        self.txns = 0
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
        d.snoop_req.value = 0
        d.snoop_type.value = 0
        d.snoop_addr.value = 0
        d.cd_ready_in.value = 0
        d.tag_b_set.value = 0
        await self.assert_reset()
        # monitor + stubs run from reset assertion so no observable cycle
        # (including the first post-deassert init walk cycle) is missed
        cocotb.start_soon(self._monitor())
        cocotb.start_soon(self._fill_stub())
        cocotb.start_soon(self._drain_stub())
        cocotb.start_soon(self._victim_way_tracker())
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
        data), then fill_done after FILL_DONE_DELAY cycles. Drives land on
        the falling edge so the pulse is visible to the DUT's next sampling
        posedge and to the negedge monitor in the same cycle."""
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
                await self._negedge()
                d.fillbeat_wr_en.value = 0
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
    async def _do_req(self, addr, we, be, wdata):
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
                raise RuntimeError("request never accepted; "
                                   f"state={int(d.ctrl_state.value):#x}")
            await FallingEdge(d.clk)
        accept_cyc = self.cyc
        await RisingEdge(d.clk)
        d.req_valid.value = 0
        # wait the response
        rsp_data = None
        for _ in range(self.RSP_TIMEOUT_CYCLES):
            await self._negedge_settled()
            if int(d.ctrl_rsp_valid.value):
                rsp_data = int(d.ctrl_rsp_data.value)
                break
        if rsp_data is None:
            recent = [e for e in self.events[-40:]]
            raise RuntimeError(
                f"response timeout; recent events: {self._fmt_events(recent)}")
        rsp_cyc = self.cyc
        return accept_cyc, rsp_cyc, rsp_data

    def _fmt_events(self, evts):
        out = []
        for cyc, kind, payload in evts:
            if kind == 'state':
                out.append(f"{cyc}:{STATE_NAMES.get(payload, payload)}")
            else:
                out.append(f"{cyc}:{kind}")
        return ' '.join(out)

    # ------------------------------------------------------------------
    # one scored transaction, lockstep against the oracle
    # ------------------------------------------------------------------
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

        accept_cyc, rsp_cyc, rsp_data = await self._do_req(addr, we, be, wdata)
        sl = [e for e in self.events if accept_cyc < e[0] <= rsp_cyc]
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
        victim_dirty = (model_victim_line is not None
                        and self.line_state.get(model_victim_line) == 'M')

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
                # the fill snapshot installs the raw memory-side line
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
                elif miss:
                    self._score(f"{label} install state", wr_state,
                                {'S': 0x1, 'M': 0x3}[install_state])
                    self._score(f"{label} install tag", wr_tag,
                                line >> self.SET_BITS)
                    self._score(f"{label} install way", p['way_oh'],
                                1 << model_victim_way)
                    installed_way = model_victim_way
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
        self.lru = LruModel(self.SETS, self.WAYS)

    # ------------------------------------------------------------------
    # InitWalk (Review Focus 7): first req_ready only after every set of
    # every way holds STATE_I.
    # ------------------------------------------------------------------
    async def _check_init(self):
        d = self.dut
        self._reset_models()
        init_writes = []
        cycles = 0
        while True:
            await self._negedge_settled()
            cycles += 1
            if cycles > self.SETS * 4 + 100:
                raise RuntimeError("init walk never completed")
            if not int(d.init_busy.value):
                break
            self._score("init: req_ready low while init busy",
                        int(d.ctrl_req_ready.value), 0)
            if int(d.tag_wr_en.value):
                init_writes.append((int(d.tag_wr_set.value),
                                    int(d.tag_wr_way_onehot.value),
                                    int(d.tag_wr_tag_state.value) & 0x7))
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
            if i % 2000 == 0:
                self.mark_progress(f"full random {i}/{n}")
        self.log.info(f"FULL random lockstep: {n} transactions scored")

    # ------------------------------------------------------------------
    async def run(self):
        await self._check_init()
        self.scenarios['InitWalk'] = True
        await self._hit_sequence()
        self.scenarios['HitSequence'] = True
        if self.TEST_LEVEL in ('func', 'full'):
            await self._miss_sequence()
            self.scenarios['MissSequence'] = True
            await self._illegal_state()
            self.scenarios['IllegalStateError'] = True
        if self.TEST_LEVEL == 'full':
            await self._full_random()
            self.scenarios['FullRandomLockstep'] = True
        return self.mismatches == 0

    def get_test_report(self):
        return {'checks': self.checks, 'mismatches': self.mismatches,
                'transactions': self.txns, 'scenarios': self.scenarios}
