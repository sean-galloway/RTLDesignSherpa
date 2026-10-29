"""
jet_control lookup-stage testbench

The lookup half of the jet control core (MAS ch02_blocks/01): one request,
one window -- tag read + MSHR CAM + WB match + set claim count in the same
cycle, classified HIT / MERGE / MISS_ALLOC / STALL with stall sub-reasons
{mshr_full, wb_full_dirty_victim, set_oversubscribed, cross_class_wait,
tag_full}.  The harness (dv/tb/jet_control_th.sv) wires the DUT to the REAL
l1_tag_array / l1_data_array / l1_repl / jet_mshr / jet_wb_buffer /
jet_rsp_seq; this TB models the partner handshakes timing-only (fill
engine, drain engine) and stubs the Task 6 commit pipeline TB-side
(cmt_retire_* retire, bd_tag_wr_* tag install, tb_cpl_* response deposit).

Timing convention (same rhythm as the amber control TB): every coroutine
drives at negedge+500ps and samples at negedge+900ps, so combinational
responses to this cycle's drives are always seen settled.

Model inventory (independent of the RTL, updated from the taps):
  slot_state[(set,way)] / tags[(set,way)]  -- tag-array mirror (init walk,
                                              backdoor installs, hit
                                              promotions, commit installs)
  array_data[(set,way)]  -- data-array mirror (fill beats, write-hit
                            merges, backdoor writes; all byte-enable exact)
  mem[line]              -- memory side; fill source, drain sink
  arch_data[line]        -- architectural line content (fill + D-4 merges
                            at commit); response data golden
  LruModel               -- l1_repl parity (repl_hit/repl_update taps)
  entries                -- MSHR mirror (alloc/merge/retire from the taps)
  wb_expect              -- expected WB capture FIFO (checked at drain)
  deposits / rel order   -- jet_rsp_seq deposit map + release order check

Task-5 scope notes (gaps the commit pipeline, Task 6, will close):
  - the D-4 store-data merge at commit exists only in the TB's arch model;
    the data array holds raw fill beats until Task 6 lands the merge, so
    no scenario read-hits a line whose committed entry carried a write.
  - upgrade (CLEAN_UNIQUE) requests launch but never complete: the lookup
    stage launches them and holds same-line writes; the response/install
    is Task 6.  Scenarios reset the pipeline after an upgrade.

Author: RTL Design Sherpa
Created: 2026-10-28
"""

import os
import random
from collections import deque

import cocotb
from cocotb.triggers import RisingEdge, FallingEdge, Timer

from TBClasses.shared.tbbase import TBBase

# jet_pkg encodings (kept as ints; the TB must not import the SV package)
CLS_RNSD, CLS_RU, CLS_CU = 0, 1, 2
# jet_control stall sub-reasons (jet_control.sv localparams)
STALL_NONE, STALL_MSHR_FULL, STALL_WB, STALL_SET_OVERSUB, STALL_XCLASS, \
    STALL_TAG_FULL = range(6)

STATE_CODE = {'I': 0x0, 'S': 0x1, 'E': 0x2, 'M': 0x3}
CODE_STATE = {v: k for k, v in STATE_CODE.items()}


class LruModel:
    """Rank array parity with l1_repl LRU: 0 = MRU, WAYS-1 = victim."""

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


class JetControlTB(TBBase):
    """Drives the lookup stage and scores every observable against the model."""

    def __init__(self, dut, **kwargs):
        super().__init__(dut)
        self.SEED = self.convert_to_int(os.environ.get('SEED', '12345'))
        self.TEST_LEVEL = os.environ.get('TEST_LEVEL', 'gate').lower()
        random.seed(self.SEED)

        self.SETS = self.convert_to_int(os.environ.get('SETS', '128'))
        self.WAYS = self.convert_to_int(os.environ.get('WAYS', '4'))
        self.MSHR_COUNT = self.convert_to_int(os.environ.get('MSHR_COUNT', '8'))
        self.RSP_DEPTH = self.MSHR_COUNT + 2
        self.VICTIM_DEPTH = self.convert_to_int(os.environ.get('VICTIM_DEPTH', '2'))
        self.ADDR_WIDTH = 32
        self.LINE_BYTES = 64
        self.STRB_W = 8
        self.BUS_WIDTH = 64
        self.FILL_BEATS = self.LINE_BYTES // self.STRB_W
        self.SET_BITS = (self.SETS - 1).bit_length()
        self.OFFSET_BITS = (self.LINE_BYTES - 1).bit_length()
        self.BEAT_BITS = (self.FILL_BEATS - 1).bit_length()
        self.SET_MASK = self.SETS - 1
        self.LINE_MASK = (1 << (self.ADDR_WIDTH - self.OFFSET_BITS)) - 1
        self.TAG_W = self.ADDR_WIDTH - self.SET_BITS - self.OFFSET_BITS

        self.REQ_TIMEOUT = 400

        # partner stub knobs (handshake timing only)
        self.fill_accept_latency = 0
        self.fill_beat_latency = 2
        self.fill_done_latency = 3
        self.drain_latency = 6

        # golden models
        self.tags = {}
        self.slot_state = {}
        self.array_data = {}
        self.mem = {}
        self.arch_data = {}
        self.lru = LruModel(self.SETS, self.WAYS)
        self.entries = []        # MSHR mirror, alloc order
        self.wb_expect = deque()  # (line, full-line int) capture order
        self.deposits = {}       # tag -> response data (outstanding)
        self.release_count = 0
        self.next_tag = 0
        self.rel_tag = 0

        # event log for _wait_event cursors
        self.events = []
        self._ev_pos = 0
        self.cyc = 0

        # stub state
        self._fills_started = []   # (line, cls) in launch order
        self._fill_queue = deque()
        self._fills_in_flight = 0

        self.checks = 0
        self.mismatches = 0
        self.scenarios = {}

        self.log.info(f"JetControlTB sets={self.SETS} ways={self.WAYS} "
                      f"mshr={self.MSHR_COUNT} victim={self.VICTIM_DEPTH} "
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

    def _note(self, kind, payload=None):
        self.events.append((self.cyc, kind, payload))

    def _line_of(self, addr):
        return (addr >> self.OFFSET_BITS) & self.LINE_MASK

    def _set_of_line(self, line):
        return line & self.SET_MASK

    def _compose_addr(self, tag, set_idx, beat=0):
        return ((tag << (self.SET_BITS + self.OFFSET_BITS))
                | ((set_idx & self.SET_MASK) << self.OFFSET_BITS)
                | (beat << 3))

    def _default_line(self, line):
        return bytes(((line + 0x5A * i) & 0xFF) for i in range(self.LINE_BYTES))

    def _mem_line(self, line):
        if line not in self.mem:
            self.mem[line] = bytearray(self._default_line(line))
        return self.mem[line]

    def _beat_of(self, line_data, beat):
        lo = beat * self.STRB_W
        return int.from_bytes(bytes(line_data[lo:lo + self.STRB_W]), 'little')

    def _line_int(self, line_data):
        return int.from_bytes(bytes(line_data), 'little')

    def _hit_way(self, set_idx, line):
        for w in range(self.WAYS):
            if (self.tags.get((set_idx, w)) == line
                    and self.slot_state.get((set_idx, w), 'I') != 'I'):
                return w
        return None

    # ------------------------------------------------------------------
    # clock/reset + timing points
    # ------------------------------------------------------------------
    async def setup_clocks_and_reset(self, period_ns=10):
        await self.start_clock('clk', freq=period_ns, units='ns')
        self._drive_idle()
        cocotb.start_soon(self._fill_stub())
        cocotb.start_soon(self._drain_stub())
        cocotb.start_soon(self._release_watch())
        await self.assert_reset()
        await self.wait_clocks('clk', 3)
        await self.deassert_reset()
        await self._await_init(stray_check=True)

    async def assert_reset(self):
        self.dut.rst_n.value = 0

    async def deassert_reset(self):
        self.dut.rst_n.value = 1

    def _drive_idle(self):
        d = self.dut
        d.lkup_valid_i.value = 0
        d.lkup_addr_i.value = 0
        d.lkup_we_i.value = 0
        d.lkup_be_i.value = 0
        d.lkup_wdata_i.value = 0
        d.rsp_ready_i.value = 1
        d.fill_accept_i.value = 0
        d.fill_beat_valid_i.value = 0
        d.fill_beat_idx_i.value = 0
        d.fill_beat_num_i.value = 0
        d.fill_done_i.value = 0
        d.fillbeat_wr_en.value = 0
        d.fillbeat_wr_addr.value = 0
        d.fillbeat_wr_way.value = 0
        d.fillbeat_wr_data.value = 0
        d.fillbeat_wr_be.value = 0
        d.drain_done_i.value = 0
        d.cmt_retire_i.value = 0
        d.cmt_retire_idx_i.value = 0
        d.tb_cpl_valid_i.value = 0
        d.tb_cpl_tag_i.value = 0
        d.tb_cpl_data_i.value = 0
        d.bd_tag_wr_en.value = 0
        d.bd_tag_wr_way.value = 0
        d.bd_tag_wr_set.value = 0
        d.bd_tag_wr_tag_state.value = 0
        d.tag_b_set_i.value = 0

    async def _drive_pt(self):
        """Advance to this cycle's drive point (negedge + 500ps)."""
        await FallingEdge(self.dut.clk)
        await Timer(500, units='ps')
        self.cyc += 1

    async def _settle(self):
        """Same-cycle sample point (negedge + 900ps), after the drives."""
        await Timer(400, units='ps')

    # ------------------------------------------------------------------
    # init walk (D-3): exactly SETS all-ways STATE_I writes; a stray
    # request during the walk is ignored (ready stays low).
    # ------------------------------------------------------------------
    async def _await_init(self, stray_check=False):
        d = self.dut
        seen = []
        stray_left = 3 if stray_check else 0
        if stray_left:
            d.lkup_valid_i.value = 1
            d.lkup_addr_i.value = self._compose_addr(0x77, 1)
            d.lkup_we_i.value = 1
            d.lkup_be_i.value = 0xFF
            d.lkup_wdata_i.value = 0x5A5A5A5A5A5A5A5A
        for _ in range(self.SETS * 4 + 100):
            await self._drive_pt()
            await self._settle()
            if stray_left:
                self._score("init: stray req not accepted",
                            int(d.lkup_ready_o.value), 0)
                stray_left -= 1
                if stray_left == 0:
                    d.lkup_valid_i.value = 0
            if not int(d.init_busy_o.value):
                break
            if int(d.tag_wr_en_o.value):
                seen.append((int(d.tag_wr_set_o.value),
                             int(d.tag_wr_way_onehot_o.value),
                             int(d.tag_wr_tag_state_o.value) & 0x7))
        else:
            raise RuntimeError("init walk never completed")
        # The walk covers every set exactly once, ascending, all ways,
        # STATE_I.  The first write can land in the reset-deassertion
        # half-cycle -- before this loop's first sample point -- so anchor
        # the count on the tail (the readback below is the full proof).
        self._score("init: walk length", len(seen) in (self.SETS - 1,
                                                       self.SETS), True)
        for i, (st_set, way_oh, st) in enumerate(seen):
            self._score(f"init: all-ways[{i}]", way_oh, (1 << self.WAYS) - 1)
            self._score(f"init: STATE_I[{i}]", st, 0)
            self._score(f"init: consecutive[{i}]", st_set, seen[0][0] + i)
        self._score("init: walk covers the top set", seen[-1][0],
                    self.SETS - 1)
        # readback: every set/way is Invalid (port-B backdoor)
        tsw = self.TAG_W + 3
        for s in range(self.SETS):
            d.tag_b_set_i.value = s
            await Timer(1, units='ns')
            ts = int(d.tag_b_tag_state_o.value)
            for w in range(self.WAYS):
                self._score(f"init: readback set {s} way {w}",
                            (ts >> (w * tsw)) & 0x7, 0)
        # models: every slot Invalid
        self.tags = {}
        self.slot_state = {}
        for s in range(self.SETS):
            for w in range(self.WAYS):
                self.slot_state[(s, w)] = 'I'

    # ------------------------------------------------------------------
    # partner stubs (timing only)
    # ------------------------------------------------------------------
    async def _fill_stub(self):
        """Fill engine timing model: accept the launch after
        fill_accept_latency, deliver FILL_BEATS beats into the victim way
        (never before the victim capture completes -- the fill engine
        contract), strobe the MSHR beat marks, then fill_done after
        fill_done_latency.  Fills are served one at a time in launch order
        (single AXI4 read ID, in-order completion)."""
        d = self.dut
        while True:
            await self._drive_pt()
            await self._settle()
            if not int(d.fill_start_o.value):
                continue
            addr = int(d.fill_addr_o.value)
            cls = int(d.fill_cls_o.value)
            line = self._line_of(addr)
            self._fills_started.append((line, cls))
            self._note('fill_start', {'line': line, 'cls': cls})
            self._fills_in_flight += 1
            for _ in range(self.fill_accept_latency):
                await self._drive_pt()
                await self._settle()
                self._score("fill: start held until accept",
                            int(d.fill_start_o.value), 1)
            d.fill_accept_i.value = 1
            await self._drive_pt()
            d.fill_accept_i.value = 0
            entry = None
            if cls != CLS_CU:
                cands = [e for e in self.entries
                         if e['line'] == line and not e['fill_done']]
                assert cands, f"fill for unknown line {line:#x}"
                entry = cands[0]
                # never write fill beats while a victim capture is reading
                # the data array (the fill-engine contract)
                for _ in range(self.fill_beat_latency):
                    await self._drive_pt()
                    await self._settle()
                while int(d.cap_busy_o.value):
                    await self._drive_pt()
                    await self._settle()
                full_be = (1 << self.STRB_W) - 1
                set_idx = entry['set']
                way = entry['way']
                if (set_idx, way) not in self.array_data:
                    self.array_data[(set_idx, way)] = bytearray(self.LINE_BYTES)
                for b in range(self.FILL_BEATS):
                    beat_data = self._beat_of(self._mem_line(line), b)
                    d.fillbeat_wr_en.value = 1
                    d.fillbeat_wr_addr.value = (set_idx << self.BEAT_BITS) | b
                    d.fillbeat_wr_way.value = way
                    d.fillbeat_wr_data.value = beat_data
                    d.fillbeat_wr_be.value = full_be
                    d.fill_beat_valid_i.value = 1
                    d.fill_beat_idx_i.value = entry['idx']
                    d.fill_beat_num_i.value = b
                    self._note('fill_beat', {'line': line, 'beat': b})
                    self.array_data[(set_idx, way)][b * self.STRB_W:
                                                    (b + 1) * self.STRB_W] = \
                        beat_data.to_bytes(self.STRB_W, 'little')
                    await self._drive_pt()
                d.fillbeat_wr_en.value = 0
                d.fillbeat_wr_be.value = 0
                d.fill_beat_valid_i.value = 0
            for _ in range(self.fill_done_latency):
                await self._drive_pt()
            d.fill_done_i.value = 1
            self._note('fill_done', {'line': line, 'cls': cls})
            if entry is not None:
                entry['fill_done'] = True
            self._fills_in_flight -= 1
            await self._drive_pt()
            d.fill_done_i.value = 0

    async def _drain_stub(self):
        """Drain engine timing model: drain_start -> drain_latency ->
        drain_done.  The WB head is checked against the expected capture
        FIFO and retired to memory at the done.  Samples EVERY cycle -- the
        drain_start pulse is one cycle and a new one can land the cycle
        after a done."""
        d = self.dut
        countdown = -1
        done_active = False
        while True:
            await self._drive_pt()
            if done_active:
                d.drain_done_i.value = 0
                done_active = False
            if countdown == 0:
                d.drain_done_i.value = 1
                done_active = True
                countdown = -1
            elif countdown > 0:
                countdown -= 1
            await self._settle()
            if int(d.drain_done_i.value):
                # the done lands on the posedge ending this cycle; retire
                # the expected head to the memory model
                self._note('drain_done', None)
                if self.wb_expect:
                    line, data = self.wb_expect.popleft()
                    self.mem[line] = bytearray(
                        data.to_bytes(self.LINE_BYTES, 'little'))
            elif countdown < 0 and int(d.drain_start_o.value):
                self._note('drain_start', None)
                self._score("drain: a capture was expected",
                            len(self.wb_expect) > 0, True)
                if self.wb_expect:
                    exp_line, exp_data = self.wb_expect[0]
                    self._score("drain: head addr",
                                int(d.wb_drain_addr_o.value),
                                exp_line << self.OFFSET_BITS)
                    self._score("drain: head data",
                                int(d.wb_drain_data_o.value), exp_data)
                countdown = self.drain_latency
            elif countdown >= 0 and self.wb_expect:
                # address held until BRESP (Chinnakonda 10.10.1)
                self._score("drain: addr held",
                            int(d.wb_drain_addr_o.value),
                            self.wb_expect[0][0] << self.OFFSET_BITS)

    async def _release_watch(self):
        """GAXI response channel: every release must match the outstanding
        deposit at the release pointer, in tag order."""
        d = self.dut
        while True:
            await self._drive_pt()
            await self._settle()
            if int(d.rst_n.value) == 0:
                continue
            if int(d.rsp_valid_o.value) and int(d.rsp_ready_i.value):
                # releases leave in tag order, independent of deposit order
                self._score("release: a deposit is outstanding",
                            self.rel_tag in self.deposits, True)
                if self.rel_tag in self.deposits:
                    self._score(f"release: data tag {self.rel_tag}",
                                int(d.rsp_data_o.value),
                                self.deposits.pop(self.rel_tag))
                self._note('release', {'tag': self.rel_tag})
                self.rel_tag = (self.rel_tag + 1) % self.RSP_DEPTH
                self.release_count += 1

    # ------------------------------------------------------------------
    # backdoor line install (models a commit's tag install + fill data)
    # ------------------------------------------------------------------
    async def _install_line(self, line, state, data=None, way=None):
        set_idx = self._set_of_line(line)
        if way is None:
            way = self._hit_way(set_idx, line)
        if way is None:
            way = next(w for w in range(self.WAYS)
                       if self.slot_state.get((set_idx, w), 'I') == 'I')
        if data is None:
            data = self._mem_line(line)
        d = self.dut
        full_be = (1 << self.STRB_W) - 1
        for b in range(self.FILL_BEATS):
            beat = self._beat_of(data, b)
            await self._drive_pt()
            d.fillbeat_wr_en.value = 1
            d.fillbeat_wr_addr.value = (set_idx << self.BEAT_BITS) | b
            d.fillbeat_wr_way.value = way
            d.fillbeat_wr_data.value = beat
            d.fillbeat_wr_be.value = full_be
            if (set_idx, way) not in self.array_data:
                self.array_data[(set_idx, way)] = bytearray(self.LINE_BYTES)
            self.array_data[(set_idx, way)][b * self.STRB_W:
                                            (b + 1) * self.STRB_W] = \
                beat.to_bytes(self.STRB_W, 'little')
        await self._drive_pt()
        d.fillbeat_wr_en.value = 0
        d.fillbeat_wr_be.value = 0
        d.bd_tag_wr_en.value = 1
        d.bd_tag_wr_way.value = way
        d.bd_tag_wr_set.value = set_idx
        d.bd_tag_wr_tag_state.value = ((line >> self.SET_BITS)
                                       << 3) | STATE_CODE[state]
        await self._drive_pt()
        d.bd_tag_wr_en.value = 0
        old = self.tags.get((set_idx, way))
        self.tags[(set_idx, way)] = line
        self.slot_state[(set_idx, way)] = state
        self.arch_data[line] = bytearray(data)
        return way

    # ------------------------------------------------------------------
    # request driver: present one request, hold until accept, score the
    # accept-cycle observables against the model.
    # ------------------------------------------------------------------
    async def _req(self, addr, we, be, wdata, label='', exp_stall=None,
                   max_stall_cycles=80):
        d = self.dut
        line = self._line_of(addr)
        set_idx = self._set_of_line(line)
        beat = (addr >> 3) & (self.FILL_BEATS - 1)
        await self._drive_pt()
        d.lkup_valid_i.value = 1
        d.lkup_addr_i.value = addr
        d.lkup_we_i.value = we
        d.lkup_be_i.value = be
        d.lkup_wdata_i.value = wdata
        stalls = 0
        yields = 0
        for _ in range(self.REQ_TIMEOUT):
            await self._settle()
            if int(d.lkup_ready_o.value):
                rec = self._accept(addr, we, be, wdata, label, stalls, yields)
                await RisingEdge(d.clk)
                d.lkup_valid_i.value = 0
                # record the deposit only after the accept posedge: on the
                # rsp_seq recirculation corner the release of the tag's old
                # record lands on the same edge and must be popped first
                if rec['deposit'] is not None:
                    self.deposits[rec['tag']] = rec['deposit']
                rec['line'] = line
                rec['set'] = set_idx
                rec['beat'] = beat
                return rec
            if int(d.lkup_stall_o.value):
                stalls += 1
                if exp_stall is not None:
                    self._score(f"{label} stall reason",
                                int(d.lkup_stall_reason_o.value), exp_stall)
            # (a non-stall wait cycle is an internal hold -- e.g. the fill
            # launch register draining between the retire and the retry)
            if int(d.lkup_wr_yield_o.value):
                yields += 1
                self._score(f"{label} yield implies fill busy",
                            int(d.fill_beat_valid_i.value), 1)
                self._score(f"{label} yield: no ctrl write",
                            int(d.ctrl_dat_wr_en_o.value), 0)
            if stalls + yields > max_stall_cycles:
                raise RuntimeError(f"{label}: request never accepted "
                                   f"(stalls={stalls} yields={yields})")
            await self._drive_pt()
        raise RuntimeError(f"{label}: request timeout")

    def _accept(self, addr, we, be, wdata, label, stalls, yields):
        """Score every accept-cycle observable; update the models."""
        d = self.dut
        line = self._line_of(addr)
        set_idx = self._set_of_line(line)
        beat = (addr >> 3) & (self.FILL_BEATS - 1)
        cls = {'hit': int(d.lkup_hit_o.value),
               'merge': int(d.lkup_merge_o.value),
               'alloc': int(d.lkup_miss_alloc_o.value),
               'upgrade': int(d.lkup_upgrade_o.value)}
        self._score(f"{label} exactly one class",
                    sum(cls.values()), 1)
        tag = self.next_tag
        self.next_tag = (self.next_tag + 1) % self.RSP_DEPTH
        rec = {'tag': tag, 'cls': cls, 'stalls': stalls, 'yields': yields,
               'we': we, 'be': be, 'wdata': wdata, 'deposit': None}

        # repl policy taps -> LRU parity
        if int(d.repl_update_o.value):
            way = int(d.repl_hit_way_o.value)
            self._score(f"{label} alloc victim way",
                        int(d.repl_victim_way_o.value), way)
            exp_victim = self.lru.victim(set_idx)
            self._score(f"{label} victim way vs LRU model",
                        way, exp_victim)
            rec['victim_way'] = way
            self.lru.update(set_idx, way)
        if int(d.repl_hit_o.value):
            way = int(d.repl_hit_way_o.value)
            if cls['hit']:
                exp_way = self._hit_way(set_idx, line)
                self._score(f"{label} repl_hit way", way, exp_way)
            self.lru.update(set_idx, way)

        if cls['hit']:
            way = self._hit_way(set_idx, line)
            self._score(f"{label} hit: line resident", way is not None, True)
            # response deposit: read returns the array beat, write echoes
            self._score(f"{label} hit deposit valid",
                        int(d.cpl_valid_o.value), 1)
            self._score(f"{label} hit deposit tag",
                        int(d.cpl_tag_o.value), tag)
            if we:
                exp_data = wdata
            else:
                exp_data = self._beat_of(self.array_data[(set_idx, way)],
                                         beat)
            self._score(f"{label} hit deposit data",
                        int(d.cpl_data_o.value), exp_data)
            rec['deposit'] = exp_data
            if we:
                # write merge lands on the W port this cycle
                self._score(f"{label} write merge en",
                            int(d.ctrl_dat_wr_en_o.value), 1)
                self._score(f"{label} write merge way",
                            int(d.dat_wr_way_onehot_o.value), 1 << way)
                self._score(f"{label} write merge addr",
                            int(d.dat_wr_addr_o.value),
                            (set_idx << self.BEAT_BITS) | beat)
                self._score(f"{label} write merge data",
                            int(d.dat_wr_wdata_o.value), wdata)
                self._score(f"{label} write merge be",
                            int(d.dat_wr_be_o.value), be)
                for i in range(self.STRB_W):
                    if be & (1 << i):
                        self.array_data[(set_idx, way)][beat * self.STRB_W
                                                        + i] = \
                            (wdata >> (8 * i)) & 0xFF
                self.arch_data[line] = bytearray(
                    self.array_data[(set_idx, way)])
                # E -> M promotion on the tag port (suppressed when M)
                st = self.slot_state[(set_idx, way)]
                self._score(f"{label} promotion write",
                            int(d.ctrl_tag_wr_en_o.value),
                            1 if st == 'E' else 0)
                if st == 'E':
                    exp_ts = ((line >> self.SET_BITS) << 3) | STATE_CODE['M']
                    self._score(f"{label} promotion tag_state",
                                int(d.tag_wr_tag_state_o.value), exp_ts)
                    self.slot_state[(set_idx, way)] = 'M'
        elif cls['merge']:
            cands = [e for e in self.entries
                     if e['line'] == line and not e['committed']]
            self._score(f"{label} merge: entry exists",
                        len(cands) == 1, True)
            self._score(f"{label} merge: no alloc",
                        int(d.mshr_alloc_gnt_o.value), 0)
            self._score(f"{label} merge: no deposit",
                        int(d.cpl_valid_o.value), 0)
            if cands:
                cands[0]['requesters'].append(
                    {'tag': tag, 'we': we, 'beat': beat, 'be': be,
                     'wdata': wdata})
        elif cls['alloc']:
            self._score(f"{label} alloc gnt",
                        int(d.mshr_alloc_gnt_o.value), 1)
            self._score(f"{label} alloc: no deposit",
                        int(d.cpl_valid_o.value), 0)
            way = rec['victim_way']
            vline = self.tags.get((set_idx, way))
            vdirty = (vline is not None
                      and self.slot_state.get((set_idx, way), 'I') == 'M')
            rec['victim_dirty'] = vdirty
            if vdirty:
                # the victim is captured to the WB buffer (J5)
                self.wb_expect.append(
                    (vline,
                     self._line_int(self.array_data[(set_idx, way)])))
            self.entries.append({
                'idx': int(d.mshr_alloc_idx_o.value),
                'line': line, 'set': set_idx, 'way': way,
                'fill_cls': CLS_RU if we else CLS_RNSD,
                'fill_done': False, 'committed': False,
                'requesters': [{'tag': tag, 'we': we, 'beat': beat,
                                'be': be, 'wdata': wdata}],
            })
        elif cls['upgrade']:
            self._score(f"{label} upgrade: no alloc",
                        int(d.mshr_alloc_gnt_o.value), 0)
            self._score(f"{label} upgrade: no deposit",
                        int(d.cpl_valid_o.value), 0)
            self._score(f"{label} upgrade: line resident S",
                        self.slot_state.get(
                            (set_idx, self._hit_way(set_idx, line))), 'S')
        return rec

    # ------------------------------------------------------------------
    # TB-side commit stub (stands in for the Task 6 commit pipeline):
    # wait for the fill, backdoor-install the tag, deposit one response
    # per requester in tag order, retire the entry.
    # ------------------------------------------------------------------
    async def _commit_entry(self, entry, label='commit'):
        d = self.dut
        line = entry['line']
        set_idx = entry['set']
        way = entry['way']
        for _ in range(self.REQ_TIMEOUT):
            if entry['fill_done']:
                break
            await self._drive_pt()
            await self._settle()
        else:
            raise RuntimeError(f"{label}: fill never completed")
        # install state: RNSD -> S, RU -> M (amber #106 PassDirty is Task 6)
        state = 'M' if entry['fill_cls'] == CLS_RU else 'S'
        await self._drive_pt()
        d.bd_tag_wr_en.value = 1
        d.bd_tag_wr_way.value = way
        d.bd_tag_wr_set.value = set_idx
        d.bd_tag_wr_tag_state.value = ((line >> self.SET_BITS)
                                       << 3) | STATE_CODE[state]
        await self._drive_pt()
        d.bd_tag_wr_en.value = 0
        self.tags[(set_idx, way)] = line
        self.slot_state[(set_idx, way)] = state
        # architectural line: fill data + D-4 merges in requester order
        arch = bytearray(self._mem_line(line))
        for r in entry['requesters']:
            if r['we']:
                lo = r['beat'] * self.STRB_W
                for i in range(self.STRB_W):
                    if r['be'] & (1 << i):
                        arch[lo + i] = (r['wdata'] >> (8 * i)) & 0xFF
        self.arch_data[line] = arch
        # one deposit per requester, in tag order
        for r in entry['requesters']:
            data = r['wdata'] if r['we'] else self._beat_of(arch, r['beat'])
            await self._drive_pt()
            d.tb_cpl_valid_i.value = 1
            d.tb_cpl_tag_i.value = r['tag']
            d.tb_cpl_data_i.value = data
            for _ in range(self.REQ_TIMEOUT):
                await self._settle()
                if int(d.tb_cpl_gnt_o.value):
                    break
                await self._drive_pt()
            else:
                raise RuntimeError(f"{label}: deposit never granted")
            await RisingEdge(d.clk)   # the deposit lands on this edge
            self.deposits[r['tag']] = data
            await self._drive_pt()
            d.tb_cpl_valid_i.value = 0
        # retire the MSHR entry (frees the entry + the victim-way claim)
        await self._drive_pt()
        d.cmt_retire_i.value = 1
        d.cmt_retire_idx_i.value = entry['idx']
        await self._drive_pt()
        d.cmt_retire_i.value = 0
        entry['committed'] = True
        self._note('commit', {'line': line})

    async def _wait_event(self, kind, pred=None, timeout=400):
        start = self.cyc
        while True:
            while self._ev_pos < len(self.events):
                cyc, k, p = self.events[self._ev_pos]
                self._ev_pos += 1
                if k == kind and (pred is None or pred(p)):
                    return cyc, p
            if self.cyc - start > timeout:
                raise RuntimeError(f"_wait_event({kind}) timed out")
            await self._drive_pt()
            await self._settle()

    async def _wait_releases(self, mark, n, timeout=400):
        """Wait until release_count reaches mark + n (the watcher scores each
        release).  Mark-based because releases can land while the scenario is
        doing other work (e.g. during a commit)."""
        start = self.cyc
        while self.release_count < mark + n:
            if self.cyc - start > timeout:
                raise RuntimeError(f"release timeout ({self.release_count} "
                                   f"< {mark + n})")
            await self._drive_pt()
            await self._settle()

    async def _idle_cycles(self, n):
        for _ in range(n):
            await self._drive_pt()
            await self._settle()

    async def _reset_pipeline(self):
        """Quiesce and reset the control state (the arrays keep their data;
        the init walk re-invalidates every tag)."""
        d = self.dut
        for _ in range(self.REQ_TIMEOUT):
            if self._fills_in_flight == 0:
                break
            await self._drive_pt()
            await self._settle()
        self._score("reset: WB buffer drained", len(self.wb_expect), 0)
        await self._drive_pt()
        d.rst_n.value = 0
        await self._idle_cycles(3)
        d.rst_n.value = 1
        self.entries = []
        self.deposits = {}
        self.next_tag = 0
        self.rel_tag = 0
        self.lru = LruModel(self.SETS, self.WAYS)
        self._fills_started = []
        await self._await_init(stray_check=False)

    # ------------------------------------------------------------------
    # scenarios
    # ------------------------------------------------------------------
    async def _scen_hit_read(self):
        """hit_read (J2): a resident line serves a read hit while a miss
        is outstanding; the hit's deposit lands immediately, its release
        waits behind the miss's tag (J4), and both release in order after
        the commit."""
        r0 = self.release_count
        line_x = (0x10 << self.SET_BITS) | 3
        await self._install_line(line_x, 'S')
        # plain read hit first (nothing outstanding)
        rec = await self._req(self._compose_addr(0x10, 3), 0, 0xFF, 0,
                              label='hit_read:warm')
        self._score("hit_read: warm no stall", rec['stalls'], 0)
        self._score("hit_read: warm class", rec['cls']['hit'], 1)
        await self._wait_releases(r0, 1)
        # miss outstanding, then a read hit to X
        miss = await self._req(self._compose_addr(0x11, 5), 0, 0xFF, 0,
                               label='hit_read:miss')
        self._score("hit_read: miss class", miss['cls']['alloc'], 1)
        hit = await self._req(self._compose_addr(0x10, 3, 3), 0, 0xFF, 0,
                              label='hit_read:under_miss')
        self._score("hit_read: under-miss accepted at once",
                    hit['stalls'] + hit['yields'], 0)
        self._score("hit_read: under-miss class", hit['cls']['hit'], 1)
        self._score("hit_read: hit tag after miss tag",
                    (hit['tag'] - miss['tag']) % self.RSP_DEPTH, 1)
        # the hit deposited but cannot release behind the miss's tag
        await self._idle_cycles(4)
        self._score("hit_read: hit release blocked by J4 order",
                    int(self.dut.rsp_valid_o.value), 0)
        entry = self.entries[-1]
        await self._commit_entry(entry, label='hit_read:commit')
        await self._wait_releases(r0, 3)   # warm hit, miss, under-miss hit
        self.scenarios['hit_read'] = True

    async def _scen_hit_write(self):
        """hit_write (J2): write hits merge through the W port with the
        E->M promotion tag write, and proceed while a miss is
        outstanding."""
        r0 = self.release_count
        line_y = (0x20 << self.SET_BITS) | 7
        await self._install_line(line_y, 'E')
        wdata = 0x1122334455667788
        rec = await self._req(self._compose_addr(0x20, 7), 1, 0x0F, wdata,
                              label='hit_write:promote')
        self._score("hit_write: promote class", rec['cls']['hit'], 1)
        self._score("hit_write: promoted to M",
                    self.slot_state[(7, self._hit_way(7, line_y))], 'M')
        # read back the merged beat
        await self._req(self._compose_addr(0x20, 7), 0, 0xFF, 0,
                        label='hit_write:readback')
        # write hit under an outstanding miss (already M: no promotion)
        miss = await self._req(self._compose_addr(0x21, 9), 0, 0xFF, 0,
                               label='hit_write:miss')
        wdata2 = 0xDEADBEEFCAFEF00D
        hit = await self._req(self._compose_addr(0x20, 7, 2), 1, 0xFF,
                              wdata2, label='hit_write:under_miss')
        self._score("hit_write: under-miss accepted at once",
                    hit['stalls'] + hit['yields'], 0)
        entry = self.entries[-1]
        await self._commit_entry(entry, label='hit_write:commit')
        await self._wait_releases(r0, 4)
        self.scenarios['hit_write'] = True

    async def _scen_miss_alloc(self):
        """miss_alloc: the entry is allocated, the victim way claimed, the
        fill launched, and the request is not held; after the commit the
        line serves hits."""
        r0 = self.release_count
        rec = await self._req(self._compose_addr(0x30, 11), 0, 0xFF, 0,
                              label='miss_alloc:miss')
        self._score("miss_alloc: not held", rec['stalls'] + rec['yields'], 0)
        self._score("miss_alloc: class", rec['cls']['alloc'], 1)
        await self._idle_cycles(1)
        self._score("miss_alloc: occupancy",
                    int(self.dut.mshr_occupancy_o.value), 1)
        entry = self.entries[-1]
        await self._commit_entry(entry, label='miss_alloc:commit')
        await self._wait_releases(r0, 1)
        self._score("miss_alloc: fill launched once",
                    self._fills_started.count((entry['line'], CLS_RNSD)), 1)
        hit = await self._req(self._compose_addr(0x30, 11, 5), 0, 0xFF, 0,
                              label='miss_alloc:hit_after')
        self._score("miss_alloc: post-commit hit", hit['cls']['hit'], 1)
        await self._wait_releases(r0, 2)
        self.scenarios['miss_alloc'] = True

    async def _scen_merge_read_onto_ru(self):
        """merge_read_onto_ru (J3): a read miss matching an outstanding
        write fill (RU) joins the entry's merge list -- no new alloc, no
        new fill; both requesters respond in tag order at commit."""
        r0 = self.release_count
        wdata = 0xA5A5A5A55A5A5A5A
        wr = await self._req(self._compose_addr(0x40, 13), 1, 0xFF, wdata,
                             label='merge:wr_miss')
        self._score("merge: write miss allocs", wr['cls']['alloc'], 1)
        rd = await self._req(self._compose_addr(0x40, 13, 2), 0, 0xFF, 0,
                             label='merge:rd_onto_ru')
        self._score("merge: read merges", rd['cls']['merge'], 1)
        await self._idle_cycles(1)
        self._score("merge: occupancy still 1",
                    int(self.dut.mshr_occupancy_o.value), 1)
        entry = self.entries[-1]
        self._score("merge: two requesters", len(entry['requesters']), 2)
        await self._commit_entry(entry, label='merge:commit')
        self._score("merge: exactly one fill for the line",
                    sum(1 for ln, _ in self._fills_started
                        if ln == entry['line']), 1)
        await self._wait_releases(r0, 2)   # write's echo, then the read's beat
        self.scenarios['merge_read_onto_ru'] = True

    async def _scen_stall_cross_class(self):
        """stall_cross_class (J3): a write miss behind an outstanding RNSD
        entry waits (cross_class_wait), then proceeds after the commit and
        issues its own upgrade (CLEAN_UNIQUE) against the installed S."""
        r0 = self.release_count
        rd = await self._req(self._compose_addr(0x50, 15), 0, 0xFF, 0,
                             label='xclass:rd_miss')
        self._score("xclass: read miss allocs RNSD", rd['cls']['alloc'], 1)
        entry = self.entries[-1]
        wdata = 0x13579BDF2468ACE0
        wr_task = cocotb.start_soon(
            self._req(self._compose_addr(0x50, 15), 1, 0xFF, wdata,
                      label='xclass:wr_miss', exp_stall=STALL_XCLASS))
        await self._idle_cycles(8)
        # exactly the read miss's fill exists for the line -- the stalled
        # write launched none of its own
        self._score("xclass: no fill for the stalled write",
                    sum(1 for ln, _ in self._fills_started
                        if ln == entry['line']), 1)
        await self._commit_entry(entry, label='xclass:commit')
        rec = await wr_task
        self._score("xclass: stalled before proceeding", rec['stalls'] >= 6,
                    True)
        # the line committed S; the retried write is an upgrade (J3)
        self._score("xclass: proceeds as an upgrade", rec['cls']['upgrade'],
                    1)
        # the upgrade launches CLEAN_UNIQUE and completes (no beats); the
        # CU class is unique to upgrades, so the event log needs no anchor
        await self._wait_event('fill_start',
                               pred=lambda p: p['cls'] == CLS_CU)
        await self._wait_event('fill_done',
                               pred=lambda p: p['cls'] == CLS_CU)
        await self._idle_cycles(4)
        await self._wait_releases(r0, 1)
        self.scenarios['stall_cross_class'] = True
        # the upgrade's response/install is Task 6; reset the pipeline
        await self._reset_pipeline()

    async def _scen_stall_mshr_full(self):
        """stall_mshr_full: MSHR_COUNT allocs fill the file; the next miss
        stalls mshr_full until a commit retires an entry."""
        r0 = self.release_count
        base_set = 20
        for i in range(self.MSHR_COUNT):
            rec = await self._req(self._compose_addr(0x60 + i, base_set + i),
                                  0, 0xFF, 0, label=f'mshrfull:alloc[{i}]')
            self._score(f"mshrfull: alloc[{i}]", rec['cls']['alloc'], 1)
        await self._idle_cycles(1)
        self._score("mshrfull: occupancy at cap",
                    int(self.dut.mshr_occupancy_o.value), self.MSHR_COUNT)
        task = cocotb.start_soon(
            self._req(self._compose_addr(0x70, base_set + self.MSHR_COUNT),
                      0, 0xFF, 0, label='mshrfull:stalled',
                      exp_stall=STALL_MSHR_FULL))
        await self._idle_cycles(8)
        await self._commit_entry(self.entries[0], label='mshrfull:commit')
        rec = await task
        self._score("mshrfull: stalled at the cap", rec['stalls'] >= 6, True)
        self._score("mshrfull: allocs after the retire",
                    rec['cls']['alloc'], 1)
        await self._wait_releases(r0, 1)
        self.scenarios['stall_mshr_full'] = True
        await self._reset_pipeline()

    async def _scen_stall_wb_full_only_dirty(self):
        """stall_wb_full_only_dirty (J6): WB-full stalls ONLY new
        dirty-victim misses; a clean-victim miss allocates freely with the
        WB full, and the dirty-victim miss proceeds once a drain
        completes."""
        d = self.dut
        self.drain_latency = 60   # keep the WB full through the stall window
        # sets A/B hold only dirty (M) lines; C dirty; D clean (S)
        for i, st in ((0, 'M'), (1, 'M'), (2, 'M'), (3, 'S')):
            for w in range(self.WAYS):
                await self._install_line(
                    ((0x80 + 0x10 * i + w) << self.SET_BITS) | (40 + i), st)
        # two dirty-victim misses fill the WB (captures verified at drain)
        ra = await self._req(self._compose_addr(0x800, 40), 0, 0xFF, 0,
                             label='wbfull:miss_a')
        self._score("wbfull: miss A allocs", ra['cls']['alloc'], 1)
        self._score("wbfull: A victim dirty", ra['victim_dirty'], True)
        rb = await self._req(self._compose_addr(0x810, 41), 0, 0xFF, 0,
                             label='wbfull:miss_b')
        self._score("wbfull: miss B allocs", rb['cls']['alloc'], 1)
        self._score("wbfull: B victim dirty", rb['victim_dirty'], True)
        # wait for both captures to complete and the buffer to fill
        for _ in range(self.REQ_TIMEOUT):
            await self._drive_pt()
            await self._settle()
            if int(d.wb_full_o.value) and not int(d.cap_busy_o.value):
                break
        else:
            raise RuntimeError("wbfull: WB never filled")
        # J6: a clean-victim miss allocates freely with the WB full
        rc = await self._req(self._compose_addr(0x830, 43), 0, 0xFF, 0,
                             label='wbfull:clean_victim')
        self._score("wbfull: clean victim allocs with WB full (J6)",
                    rc['cls']['alloc'], 1)
        self._score("wbfull: clean victim not dirty",
                    rc['victim_dirty'], False)
        # a dirty-victim miss stalls wb_full_dirty_victim until a drain
        task = cocotb.start_soon(
            self._req(self._compose_addr(0x820, 42), 0, 0xFF, 0,
                      label='wbfull:dirty_victim', exp_stall=STALL_WB))
        await self._idle_cycles(8)
        self._score("wbfull: still stalled before the drain",
                    int(d.lkup_ready_o.value), 0)
        self.drain_latency = 3   # let the drains run
        rec = await task
        self._score("wbfull: dirty victim stalled on WB full",
                    rec['stalls'] >= 6, True)
        self._score("wbfull: dirty victim allocs after a drain",
                    rec['cls']['alloc'], 1)
        # everything drains (the drain stub checks order + payload)
        for _ in range(self.REQ_TIMEOUT):
            await self._drive_pt()
            await self._settle()
            if len(self.wb_expect) == 0 and int(d.wb_full_o.value) == 0:
                break
        self._score("wbfull: all victims drained", len(self.wb_expect), 0)
        self.scenarios['stall_wb_full_only_dirty'] = True
        await self._reset_pipeline()

    async def _scen_stall_set_oversubscribed(self):
        """stall_set_oversubscribed: WAYS outstanding claims in one set
        refuse a further alloc to that set (a different set is unaffected)
        until one of the set's entries retires."""
        r0 = self.release_count
        set_hot = 60
        for i in range(self.WAYS):
            rec = await self._req(self._compose_addr(0x90 + i, set_hot),
                                  0, 0xFF, 0, label=f'setover:alloc[{i}]')
            self._score(f"setover: alloc[{i}]", rec['cls']['alloc'], 1)
        # a different set still allocates
        rec = await self._req(self._compose_addr(0x99, set_hot + 1),
                              0, 0xFF, 0, label='setover:other_set')
        self._score("setover: other set unaffected", rec['cls']['alloc'], 1)
        # the (WAYS+1)-th miss to the hot set stalls
        task = cocotb.start_soon(
            self._req(self._compose_addr(0x9A, set_hot), 0, 0xFF, 0,
                      label='setover:stalled', exp_stall=STALL_SET_OVERSUB))
        await self._idle_cycles(8)
        hot = [e for e in self.entries
               if e['set'] == set_hot and not e['committed']]
        await self._commit_entry(hot[0], label='setover:commit')
        rec = await task
        self._score("setover: stalled at WAYS claims", rec['stalls'] >= 6,
                    True)
        self._score("setover: allocs after the retire", rec['cls']['alloc'],
                    1)
        await self._wait_releases(r0, 1)
        self.scenarios['stall_set_oversubscribed'] = True
        await self._reset_pipeline()

    async def _scen_fill_beats_win_wport(self):
        """fill_beats_win_wport (J2): a write hit yields the W port for a
        bounded 8-beat fill stream, then proceeds; a read hit in the same
        window does not yield."""
        r0 = self.release_count
        line_x = (0xA0 << self.SET_BITS) | 70
        await self._install_line(line_x, 'M')
        self.fill_beat_latency = 2
        miss = await self._req(self._compose_addr(0xA1, 72), 0, 0xFF, 0,
                               label='wport:miss')
        self._score("wport: miss allocs", miss['cls']['alloc'], 1)
        # wait for THIS fill's beat stream to start (cursor anchored here:
        # earlier fills already left beat-1 events in the log), then present
        # a read hit mid-stream
        self._ev_pos = len(self.events)
        await self._wait_event('fill_beat',
                               pred=lambda p: p['beat'] == 1)
        rd = await self._req(self._compose_addr(0xA0, 70, 4), 0, 0xFF, 0,
                             label='wport:read_hit')
        self._score("wport: read hit does not yield",
                    rd['stalls'] + rd['yields'], 0)
        self._score("wport: read hit accepted mid-stream",
                    int(self.dut.fill_beat_valid_i.value), 1)
        # the write hit yields the W port for the rest of the stream
        wdata = 0x0BADC0DE0DDC0DE0
        wr = await self._req(self._compose_addr(0xA0, 70, 1), 1, 0xFF,
                             wdata, label='wport:write_hit')
        self._score("wport: write hit yielded", wr['yields'] > 0, True)
        self._score("wport: yield bounded by the beat stream",
                    wr['yields'] <= self.FILL_BEATS, True)
        self._score("wport: no stall reason for a yield", wr['stalls'], 0)
        self._score("wport: write accepted after the stream",
                    wr['cls']['hit'], 1)
        entry = self.entries[-1]
        await self._commit_entry(entry, label='wport:commit')
        await self._wait_releases(r0, 3)
        self.scenarios['fill_beats_win_wport'] = True

    async def _scen_stall_tag_full(self):
        """stall_tag_full: RSP_DEPTH accepted requests with rsp_ready low
        fill the sequencer; the next request stalls tag_full until a
        release frees a slot -- the freed tag is re-granted and deposited
        in the release's own cycle (the recirculation corner)."""
        d = self.dut
        r0 = self.release_count
        line_x = (0xB0 << self.SET_BITS) | 80
        await self._install_line(line_x, 'M')
        d.rsp_ready_i.value = 0
        for i in range(self.RSP_DEPTH):
            rec = await self._req(self._compose_addr(0xB0, 80, i % 8),
                                  0, 0xFF, 0, label=f'tagfull:hit[{i}]')
            self._score(f"tagfull: hit[{i}] accepted", rec['cls']['hit'], 1)
        task = cocotb.start_soon(
            self._req(self._compose_addr(0xB0, 80, 3), 0, 0xFF, 0,
                      label='tagfull:stalled', exp_stall=STALL_TAG_FULL))
        await self._idle_cycles(6)
        self._score("tagfull: held while the ring is full",
                    int(d.lkup_ready_o.value), 0)
        await self._drive_pt()
        d.rsp_ready_i.value = 1
        rec = await task
        self._score("tagfull: stalled on a full ring", rec['stalls'] >= 2,
                    True)
        self._score("tagfull: hit after a release frees a slot",
                    rec['cls']['hit'], 1)
        await self._wait_releases(r0, self.RSP_DEPTH + 1)
        self.scenarios['stall_tag_full'] = True

    # ------------------------------------------------------------------
    # test
    # ------------------------------------------------------------------
    async def _run_all(self):
        await self._scen_hit_read()
        await self._scen_hit_write()
        await self._scen_miss_alloc()
        await self._scen_merge_read_onto_ru()
        await self._scen_stall_cross_class()
        await self._scen_stall_mshr_full()
        await self._scen_stall_wb_full_only_dirty()
        await self._scen_stall_set_oversubscribed()
        await self._scen_fill_beats_win_wport()
        await self._scen_stall_tag_full()

    async def run(self) -> bool:
        await self._run_all()
        if self.TEST_LEVEL in ('func', 'full'):
            # second pass with perturbed partner-stub latencies (timing
            # robustness: the fill launch hold and the stall release paths
            # see different alignments)
            self.log.info("jet_control: FUNC second pass, perturbed "
                          "fill/drain latencies")
            self.fill_accept_latency = 2
            self.fill_beat_latency = 5
            self.fill_done_latency = 6
            self.drain_latency = 8
            self.scenarios = {}
            await self._reset_pipeline()
            await self._run_all()
        missing = [k for k, v in self.scenarios.items() if not v]
        self._score("all scenarios ran", len(missing), 0)
        # quiescence: no response record leaks, no WB capture leaks
        self._score("final: no outstanding deposits",
                    len(self.deposits), 0)
        self._score("final: WB empty", len(self.wb_expect), 0)
        return self.mismatches == 0

    def get_test_report(self):
        return {'checks': self.checks, 'mismatches': self.mismatches,
                'scenarios': sorted(self.scenarios)}
