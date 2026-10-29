"""
jet_control lookup+commit+snoop testbench

The jet control core (MAS ch02_blocks/01): the lookup stage classifies one
request in one window (tag read + MSHR CAM + WB match + set claims) into
HIT / MERGE / MISS_ALLOC / STALL, and the commit pipeline retires fills in
completion order: D-4 store-data merge onto the just-filled beats, tag
install (amber #106: S for RNSD unless PassDirty, M otherwise), deferred
snoop effects applied AFTER the install, one response deposit per merge-list
sequence tag in tag order, then the MSHR retire.  The harness
(dv/tb/jet_control_th.sv) wires the DUT to the REAL l1_tag_array /
l1_data_array / l1_repl / jet_mshr / jet_wb_buffer / jet_rsp_seq; this TB
models the partner handshakes timing-only (fill engine incl. PassDirty,
drain engine) and drives the snoop side through the l1_snoop_resp
core-facing contract (sn_req only when sn_safe; the grant-cycle CRRESP
sampled combinationally; CD beats on cdvalid/cdready -- the transport is
amber's, unit-verified in amber-mesi-l1).

Snoop answer sources scored (MAS ch02_blocks/05, match order WB > MSHR >
array): the WB snarf (snapshot at the grant; the BRESP-cycle race corner),
the pending-fill bypass (post-fill install state; PF_GUARD: DataTransfer
and PassDirty suppressed unless every fill beat has landed; never the
Invalid row), and the array hit (installed state; downgrade/invalidate on
the tag write port).  pend_eff I-sticks is pinned by
snoop_hit_pending_entry; the anti-livelock hold-off (sn_safe low from the
CLEAN_UNIQUE grant to the commit) is measured in cycles.

Timing convention (same rhythm as the amber control TB): every coroutine
drives at negedge+500ps and samples at negedge+900ps, so combinational
responses to this cycle's drives are always seen settled.

Model inventory (independent of the RTL, updated from the taps):
  slot_state[(set,way)] / tags[(set,way)]  -- tag-array mirror (init walk,
                                              backdoor installs, hit
                                              promotions, commit installs,
                                              snoop downgrades)
  array_data[(set,way)]  -- data-array mirror, maintained ONLY by the
                            passive W-port monitor (fill beats, hit merges,
                            commit merges, backdoor writes; all byte-exact)
  mem[line]              -- memory side; fill source, drain sink
  entries                -- MSHR mirror (alloc/merge from the accept taps,
                            pend effects from the snoop driver, commit
                            state from the commit watcher)
  wb_expect              -- expected WB capture FIFO (checked at drain)
  deposits / rel order   -- jet_rsp_seq deposit map + release order check

Commit observability: the _commit_watch coroutine consumes the commit queue
(in fill-done order = commit order) and scores, per fill: the D-4 W-port
store merges (way/addr/data/be, in merge-list order), the tag install value
and the optional pend_eff write landing AFTER it, exactly one deposit per
requester in tag order (consecutive cycles), and the retire.

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
# jet_pend_eff_t encodings
PEND_NONE, PEND_DOWNGRADE_S, PEND_INVALIDATE_I = 0, 1, 2
# l1_pkg amber_snoop_t encodings (the core-facing 3-bit snoop type)
SN_READ_SHARED, SN_READ_ONCE, SN_READ_UNIQUE, SN_CLEAN_SHARED, \
    SN_CLEAN_INVALID, SN_MAKE_INVALID = range(6)
# jet_control stall sub-reasons (jet_control.sv localparams)
STALL_NONE, STALL_MSHR_FULL, STALL_WB, STALL_SET_OVERSUB, STALL_XCLASS, \
    STALL_TAG_FULL, STALL_COMMIT = range(7)

STATE_CODE = {'I': 0x0, 'S': 0x1, 'E': 0x2, 'M': 0x3}
CODE_STATE = {v: k for k, v in STATE_CODE.items()}

# HAS Table 3.0 (l1_pkg amber_snoop_crresp / amber_snoop_next_state),
# ported bit-exactly for the snoop scoreboard.
_CRRESP_DT, _CRRESP_PD, _CRRESP_IS, _CRRESP_WU = 1, 4, 8, 16
_CRRESP_TABLE = {
    'M': {SN_READ_SHARED: _CRRESP_DT | _CRRESP_PD | _CRRESP_IS,
          SN_READ_ONCE: _CRRESP_DT | _CRRESP_PD,
          SN_READ_UNIQUE: _CRRESP_DT | _CRRESP_PD,
          SN_CLEAN_SHARED: _CRRESP_DT | _CRRESP_PD | _CRRESP_IS,
          SN_CLEAN_INVALID: _CRRESP_DT | _CRRESP_PD | _CRRESP_IS,
          SN_MAKE_INVALID: 0},
    'E': {SN_READ_SHARED: _CRRESP_DT | _CRRESP_IS | _CRRESP_WU,
          SN_READ_ONCE: _CRRESP_DT | _CRRESP_IS | _CRRESP_WU,
          SN_READ_UNIQUE: _CRRESP_DT | _CRRESP_WU,
          SN_CLEAN_SHARED: _CRRESP_IS | _CRRESP_WU,
          SN_CLEAN_INVALID: 0,
          SN_MAKE_INVALID: 0},
    'S': {SN_READ_SHARED: _CRRESP_IS, SN_READ_ONCE: _CRRESP_IS},
    'I': {},
}
_NEXT_STATE_TABLE = {
    'M': {SN_READ_SHARED: 'S', SN_CLEAN_SHARED: 'S'},
    'E': {SN_READ_SHARED: 'S', SN_READ_ONCE: 'S', SN_CLEAN_SHARED: 'E'},
    'S': {SN_READ_SHARED: 'S', SN_READ_ONCE: 'S', SN_CLEAN_SHARED: 'S'},
}


def _sn_crresp(ref_state, stype):
    """HAS Table 3.0 CRRESP at a reference state (IHI0022 bit order:
    {WU, IS, PD, Err, DT})."""
    return _CRRESP_TABLE.get(ref_state, {}).get(stype, 0)


def _sn_next_state(ref_state, stype):
    """HAS Table 3.0 next state at a reference state."""
    return _NEXT_STATE_TABLE.get(ref_state, {}).get(stype, 'I')


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
        # PassDirty knob: consumed by the fill stub for the NEXT fill served
        self.pass_dirty_next = False
        # CD backpressure knob (the FUNC pass turns it on): drop cdready
        # for one cycle mid-stream of every data-carrying snoop
        self.sn_cd_gap = False

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
        self._fill_serve_q = deque()  # accepted fills awaiting their burst
        self._fills_in_flight = 0

        # commit tracking: fills become commits in completion order; the
        # watcher pops one item per commit ({'entry': e} or {'cu': True})
        self._commit_queue = deque()
        self._commit_active = False
        self._pending_upgrade = None   # rec of the in-flight upgrade (CU)

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

    @staticmethod
    def _apply_store(line_bytes, beat, be, wdata, strb_w):
        """D-4 byte-enable merge of one store beat onto a line image."""
        lo = beat * strb_w
        for i in range(strb_w):
            if be & (1 << i):
                line_bytes[lo + i] = (wdata >> (8 * i)) & 0xFF

    # ------------------------------------------------------------------
    # clock/reset + timing points
    # ------------------------------------------------------------------
    async def setup_clocks_and_reset(self, period_ns=10):
        await self.start_clock('clk', freq=period_ns, units='ns')
        self._drive_idle()
        cocotb.start_soon(self._fill_accept_stub())
        cocotb.start_soon(self._fill_serve_stub())
        cocotb.start_soon(self._drain_stub())
        cocotb.start_soon(self._release_watch())
        cocotb.start_soon(self._wport_model())
        cocotb.start_soon(self._commit_watch())
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
        d.fill_pass_dirty_i.value = 0
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
        d.sn_req_i.value = 0
        d.sn_addr_i.value = 0
        d.sn_type_i.value = 0
        d.sn_cdready_i.value = 0
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
    async def _fill_accept_stub(self):
        """Fill engine accept side: a launch is accepted after
        fill_accept_latency and queued for the serial burst server
        (single AXI4 read ID: bursts and completions run in launch order,
        but launches are accepted promptly -- AR pipelining -- so the
        one-deep launch-hold register never serializes allocs)."""
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
            for _ in range(self.fill_accept_latency):
                await self._drive_pt()
                await self._settle()
                self._score("fill: start held until accept",
                            int(d.fill_start_o.value), 1)
            d.fill_accept_i.value = 1
            await self._drive_pt()
            d.fill_accept_i.value = 0
            # PassDirty (RRESP[2]) is consumed by the burst server; the
            # DUT samples it at fill_done (amber l1_fill contract)
            pd = self.pass_dirty_next
            self.pass_dirty_next = False
            entry = None
            if cls != CLS_CU:
                cands = [e for e in self.entries
                         if e['line'] == line and not e['fill_accepted']]
                assert cands, f"fill for unknown line {line:#x}"
                entry = cands[0]
                entry['fill_accepted'] = True
                entry['pass_dirty'] = pd
            self._fill_serve_q.append((line, cls, entry))
            self._fills_in_flight += 1

    async def _fill_serve_stub(self):
        """Fill engine burst server: one burst at a time, in accept order.
        Delivers FILL_BEATS beats into the victim way (never before the
        victim capture completes -- the fill-engine contract), strobes the
        MSHR beat marks, then fill_done (carrying PassDirty) after
        fill_done_latency.  Each fill_done enqueues the commit the DUT
        must now perform."""
        d = self.dut
        while True:
            await self._drive_pt()
            await self._settle()
            if not self._fill_serve_q:
                continue
            line, cls, entry = self._fill_serve_q.popleft()
            if entry is not None:
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
                entry['fill_line_data'] = bytes(self._mem_line(line))
                # align the first beat to the +500ps drive point (the wait
                # loop ends at the +900ps sample point; driving there would
                # race the W-port monitor's sample)
                await self._drive_pt()
                d.fill_pass_dirty_i.value = 1 if entry['pass_dirty'] else 0
                for b in range(self.FILL_BEATS):
                    beat_data = self._beat_of(entry['fill_line_data'], b)
                    d.fillbeat_wr_en.value = 1
                    d.fillbeat_wr_addr.value = (set_idx << self.BEAT_BITS) | b
                    d.fillbeat_wr_way.value = way
                    d.fillbeat_wr_data.value = beat_data
                    d.fillbeat_wr_be.value = full_be
                    d.fill_beat_valid_i.value = 1
                    d.fill_beat_idx_i.value = entry['idx']
                    d.fill_beat_num_i.value = b
                    self._note('fill_beat', {'line': line, 'beat': b})
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
            d.fill_pass_dirty_i.value = 0
            # enqueue the commit one cycle after the done: a merge accept
            # is still legal ON the fill_done cycle (the RTL blocks joins
            # from the next cycle), and the watcher reads the requester
            # list only after this append
            if entry is not None:
                self._commit_queue.append({'entry': entry})
            else:
                self._commit_queue.append({'cu': True})

    async def _drain_stub(self):
        """Drain engine timing model: drain_start -> drain_latency ->
        drain_done.  The WB head is checked against the expected capture
        FIFO and retired to memory at the done.  Samples EVERY cycle -- the
        drain_start pulse is one cycle and a new one can land the cycle
        after a done.  _drain_cd exposes the countdown (post-decrement, at
        the settle) so a scenario can present a snoop in the exact BRESP
        cycle (the drive point after a settle that saw _drain_cd == 0)."""
        d = self.dut
        countdown = -1
        done_active = False
        self._drain_cd = -1
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
            self._drain_cd = countdown
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
    # passive data-array model: EVERY muxed W-port write lands here
    # (fill beats, hit merges, commit store merges, backdoor installs).
    # ------------------------------------------------------------------
    async def _wport_model(self):
        d = self.dut
        while True:
            await self._drive_pt()
            await self._settle()
            if int(d.rst_n.value) == 0:
                continue
            if int(d.dat_wr_en_o.value):
                way = int(d.dat_wr_way_onehot_o.value).bit_length() - 1
                addr = int(d.dat_wr_addr_o.value)
                set_idx = (addr >> self.BEAT_BITS) & self.SET_MASK
                beat = addr & (self.FILL_BEATS - 1)
                data = int(d.dat_wr_wdata_o.value)
                be = int(d.dat_wr_be_o.value)
                key = (set_idx, way)
                if key not in self.array_data:
                    self.array_data[key] = bytearray(self.LINE_BYTES)
                self._apply_store(self.array_data[key], beat, be, data,
                                  self.STRB_W)

    # ------------------------------------------------------------------
    # commit watcher: consumes the commit queue in fill-done order (= the
    # DUT's commit order) and scores each commit's observable sequence:
    # D-4 store merges on the W port, the tag install (and the deferred
    # snoop effect AFTER it), one deposit per requester in tag order on
    # consecutive cycles, and the MSHR retire.
    # ------------------------------------------------------------------
    async def _commit_watch(self):
        while True:
            await self._drive_pt()
            await self._settle()
            if not self._commit_queue:
                continue
            cur = self._commit_queue.popleft()
            self._commit_active = True
            if cur.get('cu'):
                await self._watch_cu_commit()
            else:
                await self._watch_entry_commit(cur['entry'])
            self._commit_active = False

    def _exp_read_data(self, entry, upto_slot):
        """Read-deposit golden for the requester at upto_slot: the fill
        image with the D-4 merges of all EARLIER writes applied (request
        order -- a read must not observe a later write)."""
        arch = bytearray(entry['fill_line_data'])
        for r in entry['requesters'][:upto_slot]:
            if r['we']:
                self._apply_store(arch, r['beat'], r['be'], r['wdata'],
                                  self.STRB_W)
        return self._beat_of(arch, entry['requesters'][upto_slot]['beat'])

    async def _watch_entry_commit(self, entry):
        d = self.dut
        reqs = entry['requesters']
        exp_tags = [r['tag'] for r in reqs]
        exp_writes = [r for r in reqs if r['we']]
        exp_state = ('M' if (entry['fill_cls'] == CLS_RU
                             or entry['pass_dirty']) else 'S')
        exp_tag_writes = [((entry['line'] >> self.SET_BITS), exp_state)]
        if entry['pend'] == 'S':
            exp_tag_writes.append((entry['line'] >> self.SET_BITS, 'S'))
        elif entry['pend'] == 'I':
            exp_tag_writes.append((entry['line'] >> self.SET_BITS, 'I'))
        got_tags = []        # deposit tags in order (+ watch cycle, adjacency)
        got_writes = []      # (beat, be, wdata) commit store merges
        got_tag_writes = []  # (tag, state) on the entry's (set, way)
        retired = False
        wcyc = 0             # local watch-cycle count (self.cyc is shared)
        start = self.cyc
        while not retired:
            if self.cyc - start > 4000:
                raise RuntimeError(f"commit watch: entry {entry['idx']} "
                                   f"(line {entry['line']:#x}) never retired")
            await self._drive_pt()
            await self._settle()
            wcyc += 1
            # D-4 store merge on the W port: control-attributed write to
            # the entry's claimed (set, way) -- hits on claimed ways are
            # suppressed, so no lookup merge can alias this
            if int(d.ctrl_dat_wr_en_o.value):
                way_oh = int(d.dat_wr_way_onehot_o.value)
                addr = int(d.dat_wr_addr_o.value)
                if (way_oh == (1 << entry['way'])
                        and ((addr >> self.BEAT_BITS) & self.SET_MASK)
                            == entry['set']):
                    got_writes.append(
                        (addr & (self.FILL_BEATS - 1),
                         int(d.dat_wr_be_o.value),
                         int(d.dat_wr_wdata_o.value)))
            # tag install + deferred snoop effect, in that order
            if int(d.ctrl_tag_wr_en_o.value):
                if (int(d.tag_wr_way_onehot_o.value) == (1 << entry['way'])
                        and int(d.tag_wr_set_o.value) == entry['set']):
                    ts = int(d.tag_wr_tag_state_o.value)
                    got_tag_writes.append((ts >> 3, ts & 0x7))
            # response deposits: one per requester, in tag order
            if int(d.cpl_valid_o.value):
                tag = int(d.cpl_tag_o.value)
                data = int(d.cpl_data_o.value)
                if tag in exp_tags:
                    k = len(got_tags)
                    self._score(f"commit[{entry['idx']}]: deposit order "
                                f"(tag {tag})", k < len(exp_tags)
                                and tag == exp_tags[k], True)
                    if k < len(reqs):
                        r = reqs[k]
                        exp_data = (r['wdata'] if r['we']
                                    else self._exp_read_data(entry, k))
                        self._score(f"commit[{entry['idx']}]: deposit data "
                                    f"tag {tag}", data, exp_data)
                    got_tags.append((tag, wcyc))
                    self._score(f"commit[{entry['idx']}]: no double deposit "
                                f"tag {tag}", tag in self.deposits, False)
                    self.deposits[tag] = data
            if int(d.mshr_retire_o.value) \
                    and int(d.mshr_retire_idx_o.value) == entry['idx']:
                retired = True
        # whole-commit sequence checks
        self._score(f"commit[{entry['idx']}]: one deposit per requester",
                    [t for t, _ in got_tags], exp_tags)
        self._score(f"commit[{entry['idx']}]: deposits consecutive",
                    [c for _, c in got_tags],
                    [got_tags[0][1] + i for i in range(len(got_tags))]
                    if got_tags else [])
        exp_w = [(r['beat'], r['be'], r['wdata']) for r in exp_writes]
        self._score(f"commit[{entry['idx']}]: D-4 store merges "
                    f"(order + payload)", got_writes, exp_w)
        exp_tw = [(t, STATE_CODE[s]) for t, s in exp_tag_writes]
        self._score(f"commit[{entry['idx']}]: install state "
                    f"{exp_state} (pend {entry['pend'] or 'none'}) "
                    f"applied after install", got_tag_writes, exp_tw)
        # arch model: fill image + all stores, in requester order
        arch = bytearray(entry['fill_line_data'])
        for r in reqs:
            if r['we']:
                self._apply_store(arch, r['beat'], r['be'], r['wdata'],
                                  self.STRB_W)
        self.arch_data[entry['line']] = arch
        self.tags[(entry['set'], entry['way'])] = entry['line']
        self.slot_state[(entry['set'], entry['way'])] = \
            entry['pend'] or exp_state
        entry['committed'] = True
        self._note('commit', {'line': entry['line'], 'idx': entry['idx']})

    async def _watch_cu_commit(self):
        """The upgrade (CLEAN_UNIQUE) commit: one D-4 store merge of the
        held write, a tag write installing M at the resident way, one
        deposit echoing the write data, and the tracker clears (a
        subsequent access to the line proceeds)."""
        d = self.dut
        rec = self._pending_upgrade
        assert rec is not None, "CU commit with no pending upgrade"
        got_writes = []
        got_tag_writes = []
        deposited = False
        start = self.cyc
        while not deposited:
            if self.cyc - start > 4000:
                raise RuntimeError("commit watch: CU commit never deposited")
            await self._drive_pt()
            await self._settle()
            if int(d.ctrl_dat_wr_en_o.value):
                way_oh = int(d.dat_wr_way_onehot_o.value)
                addr = int(d.dat_wr_addr_o.value)
                if (way_oh == (1 << rec['way'])
                        and ((addr >> self.BEAT_BITS) & self.SET_MASK)
                            == rec['set']):
                    got_writes.append(
                        (addr & (self.FILL_BEATS - 1),
                         int(d.dat_wr_be_o.value),
                         int(d.dat_wr_wdata_o.value)))
            if int(d.ctrl_tag_wr_en_o.value):
                if (int(d.tag_wr_way_onehot_o.value) == (1 << rec['way'])
                        and int(d.tag_wr_set_o.value) == rec['set']):
                    ts = int(d.tag_wr_tag_state_o.value)
                    got_tag_writes.append((ts >> 3, ts & 0x7))
            if int(d.cpl_valid_o.value) \
                    and int(d.cpl_tag_o.value) == rec['tag']:
                self._score("cu commit: deposit data (write echo)",
                            int(d.cpl_data_o.value), rec['wdata'])
                self._score("cu commit: no double deposit",
                            rec['tag'] in self.deposits, False)
                self.deposits[rec['tag']] = rec['wdata']
                deposited = True
        self._score("cu commit: one D-4 store merge",
                    got_writes, [(rec['beat'], rec['be'], rec['wdata'])])
        self._score("cu commit: tag install M",
                    got_tag_writes,
                    [(rec['line'] >> self.SET_BITS, STATE_CODE['M'])])
        # models: the held write merged onto the resident line, state M
        self._apply_store(self.array_data[(rec['set'], rec['way'])],
                          rec['beat'], rec['be'], rec['wdata'], self.STRB_W)
        # (the W-port monitor already applied the same merge; idempotent)
        self.arch_data[rec['line']] = bytearray(
            self.array_data[(rec['set'], rec['way'])])
        self.slot_state[(rec['set'], rec['way'])] = 'M'
        self._pending_upgrade = None
        self._note('cu_commit', {'line': rec['line']})

    async def _await_commit(self, entry, label='commit'):
        start = self.cyc
        while not entry['committed']:
            if self.cyc - start > 6000:
                raise RuntimeError(f"{label}: entry {entry['idx']} never "
                                   f"committed")
            await self._drive_pt()
            await self._settle()

    async def _await_cu_commit(self, label='cu_commit'):
        start = self.cyc
        while self._pending_upgrade is not None:
            if self.cyc - start > 6000:
                raise RuntimeError(f"{label}: upgrade never committed")
            await self._drive_pt()
            await self._settle()

    # ------------------------------------------------------------------
    # snoop driver: the l1_snoop_resp core-facing contract (the AC accept
    # cycle IS the grant -- present sn_req only when sn_safe; CRRESP is
    # combinational at the grant; CD beats handshake on cdvalid/cdready).
    # ------------------------------------------------------------------
    async def _snoop(self, line, stype, label, ref, deliver, exp_cd=None,
                     max_wait=400, sync_drain_cd=False):
        """Issue one snoop at the core-facing interface and score it.

        ref:     the reference state the DUT must resolve (the WB match is
                 M; an MSHR match is the post-fill install state -- M for an
                 RU fill, S for RNSD; an array hit is the installed state;
                 an absent/stale line is I).
        deliver: whether the DUT may promise DataTransfer (a WB snarf or an
                 array answer: always; an MSHR match: only with every fill
                 beat landed -- PF_GUARD).  When False, DT and PD are masked
                 off the Table 3.0 decode (the answer still carries the
                 post-fill row's IsShared/WasUnique -- never the Invalid
                 row).
        exp_cd:  expected CD beat values (implies a full-line transfer).
        sync_drain_cd: present the request in the drain engine's BRESP
                 cycle (the drive point after the settle that observed the
                 drain stub's countdown at 0) -- the ships-in-the-night
                 corner.

        Returns {'crresp', 'beats', 'wb_eff', 'bresp'}: the grant-cycle
        CRRESP, the CD beats, the wb_sn_eff values ORed over the service,
        and the sn_bresp_cycle flag at the grant.
        """
        d = self.dut
        addr = (line & self.LINE_MASK) << self.OFFSET_BITS
        wb_eff = 0
        bresp = 0
        granted = False
        present_next = False
        for _ in range(max_wait * 4):
            await self._drive_pt()
            if sync_drain_cd and not present_next:
                # wait at the settle for the countdown to hit 0; the next
                # drive point is the BRESP cycle
                await self._settle()
                if self._drain_cd == 0:
                    present_next = True
                continue
            if int(d.sn_safe_o.value):
                d.sn_req_i.value = 1
                d.sn_addr_i.value = addr
                d.sn_type_i.value = stype
                await self._settle()
                self._score(f"{label} grant cycle marked ready",
                            int(d.sn_ready_o.value), 1)
                crresp = int(d.sn_crresp_o.value)
                wb_eff |= int(d.wb_sn_eff_o.value)
                bresp |= int(d.wb_sn_bresp_cycle_o.value)
                self._note('sn_grant', {'line': line, 'type': stype})
                granted = True
                break
            await self._settle()
        if not granted:
            raise RuntimeError(f"{label}: snoop never became safe")
        exp = _sn_crresp(ref, stype)
        if not deliver:
            exp &= _CRRESP_IS | _CRRESP_WU   # PF_GUARD: never promise DT/PD
        self._score(f"{label} crresp (ref {ref}, deliver {deliver})",
                    crresp, exp)
        beats = []
        gap_done = False
        if crresp & _CRRESP_DT:
            for _ in range(max_wait * 4):
                await self._drive_pt()
                d.sn_req_i.value = 0
                ready = 1
                if self.sn_cd_gap and len(beats) == 1 and not gap_done:
                    ready = 0
                    gap_done = True
                d.sn_cdready_i.value = ready
                await self._settle()
                wb_eff |= int(d.wb_sn_eff_o.value)
                bresp |= int(d.wb_sn_bresp_cycle_o.value)
                if int(d.sn_cdvalid_o.value) and ready:
                    beats.append(int(d.sn_cddata_o.value))
                    self._score(f"{label} cdlast on the final beat only",
                                int(d.sn_cdlast_o.value),
                                1 if len(beats) == self.FILL_BEATS else 0)
                    if int(d.sn_cdlast_o.value):
                        break
            else:
                raise RuntimeError(f"{label}: CD stream never completed")
        else:
            for _ in range(3):
                await self._drive_pt()
                d.sn_req_i.value = 0
                await self._settle()
                self._score(f"{label} no CD beat for a non-DT answer",
                            int(d.sn_cdvalid_o.value), 0)
                wb_eff |= int(d.wb_sn_eff_o.value)
                bresp |= int(d.wb_sn_bresp_cycle_o.value)
        # trailing cycle(s): the effect slot follows the CD stream
        for _ in range(2):
            await self._drive_pt()
            d.sn_cdready_i.value = 0
            await self._settle()
            wb_eff |= int(d.wb_sn_eff_o.value)
            bresp |= int(d.wb_sn_bresp_cycle_o.value)
        if exp_cd is not None:
            self._score(f"{label} cd beat count", len(beats), self.FILL_BEATS)
            for i, got in enumerate(beats):
                self._score(f"{label} cd[{i}]", got, exp_cd[i])
        else:
            self._score(f"{label} no CD beats", len(beats), 0)
        return {'crresp': crresp, 'beats': beats, 'wb_eff': wb_eff,
                'bresp': bresp}

    def _snoop_eff_model(self, entry, ref, stype):
        """Mirror the pend_eff record of a snoop that matched `entry`
        (invalidate sticks over an armed downgrade -- amber's rule)."""
        nxt = _sn_next_state(ref, stype)
        if nxt == ref:
            return
        if nxt == 'I':
            entry['pend'] = 'I'
        elif entry['pend'] is None:
            entry['pend'] = 'S'

    # ------------------------------------------------------------------
    # backdoor line install (models a committed line for scenario setup)
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
        self.tags[(set_idx, way)] = line
        self.slot_state[(set_idx, way)] = state
        self.arch_data[line] = bytearray(data)
        return way

    # ------------------------------------------------------------------
    # request driver: present one request, hold until accept, score the
    # accept-cycle observables against the model.
    # ------------------------------------------------------------------
    async def _req(self, addr, we, be, wdata, label='', exp_stall=None,
                   max_stall_cycles=400):
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
        for _ in range(self.REQ_TIMEOUT * 4):
            await self._settle()
            if int(d.lkup_ready_o.value):
                rec = self._accept(addr, we, be, wdata, label, stalls, yields)
                await RisingEdge(d.clk)
                d.lkup_valid_i.value = 0
                # record the deposit only after the accept posedge: on the
                # rsp_seq recirculation corner the release of the tag's old
                # record lands on the same edge and must be popped first
                if rec['deposit'] is not None:
                    self._score(f"{label} no double deposit",
                                rec['tag'] in self.deposits, False)
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
            # (a non-stall wait cycle is an internal hold: the fill launch
            # register draining, a commit phase owning the deposit/data/tag
            # port for a cycle -- all bounded)
            if int(d.lkup_wr_yield_o.value):
                yields += 1
                self._score(f"{label} yield implies W port busy",
                            int(d.fill_beat_valid_i.value)
                            | int(d.ctrl_dat_wr_en_o.value), 1)
                self._score(f"{label} yield: no accepted write",
                            int(d.lkup_ready_o.value), 0)
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
                # arch model (the W-port monitor maintains array_data)
                self._apply_store(self.arch_data[line], beat, be, wdata,
                                  self.STRB_W)
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
                'fill_accepted': False, 'fill_done': False,
                'committed': False,
                'pass_dirty': False, 'pend': None, 'fill_line_data': None,
                'requesters': [{'tag': tag, 'we': we, 'beat': beat,
                                'be': be, 'wdata': wdata}],
            })
        elif cls['upgrade']:
            self._score(f"{label} upgrade: no alloc",
                        int(d.mshr_alloc_gnt_o.value), 0)
            self._score(f"{label} upgrade: no deposit",
                        int(d.cpl_valid_o.value), 0)
            way = self._hit_way(set_idx, line)
            self._score(f"{label} upgrade: line resident S",
                        self.slot_state.get((set_idx, way)), 'S')
            self._pending_upgrade = {
                'tag': tag, 'line': line, 'set': set_idx, 'way': way,
                'beat': beat, 'be': be, 'wdata': wdata}
        return rec

    # ------------------------------------------------------------------
    # misc sync helpers
    # ------------------------------------------------------------------
    async def _wait_event(self, kind, pred=None, timeout=2000):
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

    async def _wait_releases(self, mark, n, timeout=6000):
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
        for _ in range(self.REQ_TIMEOUT * 40):
            await self._drive_pt()
            await self._settle()
            if (self._fills_in_flight == 0
                    and not self._commit_queue
                    and not self._commit_active
                    and self._pending_upgrade is None
                    and int(d.mshr_occupancy_o.value) == 0
                    and len(self.deposits) == 0):
                break
        else:
            raise RuntimeError("reset: pipeline never quiesced")
        await self._idle_cycles(4)
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
        self._fill_serve_q = deque()
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
        await self._await_commit(self.entries[-1], label='hit_read:commit')
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
        await self._await_commit(self.entries[-1], label='hit_write:commit')
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
        await self._await_commit(entry, label='miss_alloc:commit')
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
        await self._await_commit(entry, label='merge:commit')
        self._score("merge: exactly one fill for the line",
                    sum(1 for ln, _ in self._fills_started
                        if ln == entry['line']), 1)
        await self._wait_releases(r0, 2)   # write's echo, then the read's beat
        self.scenarios['merge_read_onto_ru'] = True

    async def _scen_stall_cross_class(self):
        """stall_cross_class (J3): a write miss behind an outstanding RNSD
        entry waits (cross_class_wait), then proceeds after the commit and
        issues its own upgrade (CLEAN_UNIQUE) against the installed S.  The
        upgrade commits through the CU path: the held write merges into the
        line, the tag installs M, and the write echoes its response."""
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
        await self._await_commit(entry, label='xclass:commit')
        rec = await wr_task
        self._score("xclass: stalled before proceeding", rec['stalls'] >= 6,
                    True)
        # the line committed S; the retried write is an upgrade (J3)
        self._score("xclass: proceeds as an upgrade", rec['cls']['upgrade'],
                    1)
        # the upgrade launches CLEAN_UNIQUE and commits through the CU path
        await self._wait_event('fill_start',
                               pred=lambda p: p['cls'] == CLS_CU)
        await self._await_cu_commit(label='xclass:cu_commit')
        await self._wait_releases(r0, 2)
        # the committed write is readable back (the CU merge landed)
        await self._req(self._compose_addr(0x50, 15), 0, 0xFF, 0,
                        label='xclass:readback')
        await self._wait_releases(r0, 3)
        self.scenarios['stall_cross_class'] = True

    async def _scen_stall_mshr_full(self):
        """stall_mshr_full: MSHR_COUNT allocs fill the file; the next miss
        stalls mshr_full until a commit retires an entry.  (Fills are
        slowed so all eight entries stay live until the cap is reached --
        with real commits, the early entries retire as soon as their fills
        complete.)"""
        r0 = self.release_count
        base_set = 20
        saved_latency = self.fill_done_latency
        self.fill_done_latency = 40
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
        self._score("mshrfull: still stalled before any commit",
                    int(self.dut.lkup_ready_o.value), 0)
        self.fill_done_latency = saved_latency
        # the fills retire in order; the first commit frees an entry
        rec = await task
        self._score("mshrfull: stalled at the cap", rec['stalls'] >= 6, True)
        self._score("mshrfull: allocs after the retire",
                    rec['cls']['alloc'], 1)
        for e in self.entries:
            await self._await_commit(e, label='mshrfull:commit')
        await self._wait_releases(r0, self.MSHR_COUNT + 1)
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
        for _ in range(self.REQ_TIMEOUT * 4):
            await self._drive_pt()
            await self._settle()
            if len(self.wb_expect) == 0 and int(d.wb_full_o.value) == 0:
                break
        self._score("wbfull: all victims drained", len(self.wb_expect), 0)
        for e in self.entries:
            await self._await_commit(e, label='wbfull:commit')
        self.scenarios['stall_wb_full_only_dirty'] = True
        await self._reset_pipeline()

    async def _scen_stall_wb_drain_race(self):
        """stall_wb_drain_race (Chinnakonda 10.10.1): a miss whose line
        sits in the WB buffer (a dirty victim mid-capture / awaiting
        drain) stalls wb_full_dirty_victim until the drain completes --
        the refetch must not race the outstanding writeback.  The
        refetched line returns the DRAINED (dirty) data."""
        r0 = self.release_count
        set_r = 44
        # fill the set with dirty lines; the LRU victim (way WAYS-1 at
        # reset ranks) is V
        for w in range(self.WAYS):
            await self._install_line(
                ((0x900 + w) << self.SET_BITS) | set_r, 'M')
        vline = ((0x900 + self.WAYS - 1) << self.SET_BITS) | set_r
        vdata = self._line_int(self.array_data[(set_r, self.WAYS - 1)])
        # miss A evicts V (dirty -> capture into the WB buffer)
        ra = await self._req(self._compose_addr(0x910, set_r), 0, 0xFF, 0,
                             label='drace:miss_a')
        self._score("drace: miss A allocs", ra['cls']['alloc'], 1)
        self._score("drace: A victim dirty", ra['victim_dirty'], True)
        # hold the drain; request V's line again: the line is in the WB
        # buffer (or mid-capture) -> the drain-race stall
        self.drain_latency = 60
        task = cocotb.start_soon(
            self._req(vline << self.OFFSET_BITS, 0, 0xFF, 0,
                      label='drace:refetch', exp_stall=STALL_WB))
        await self._idle_cycles(10)
        self._score("drace: refetch stalled on the WB race",
                    int(self.dut.lkup_ready_o.value), 0)
        self.drain_latency = 3   # drain V; the refetch may then allocate
        rec = await task
        self._score("drace: stalled on the race", rec['stalls'] >= 6, True)
        self._score("drace: refetch allocs after the drain",
                    rec['cls']['alloc'], 1)
        # the refetched line's commit deposits the drained (dirty) data --
        # the commit watcher scores the deposit against the memory model,
        # which the drain stub updated at drain_done
        await self._await_commit(self.entries[-1], label='drace:commit_v')
        self._score("drace: drained data reached memory",
                    self._line_int(self._mem_line(vline)), vdata)
        await self._await_commit(self.entries[0], label='drace:commit_a')
        await self._wait_releases(r0, 2)
        self.scenarios['stall_wb_drain_race'] = True
        await self._reset_pipeline()

    async def _scen_stall_set_oversubscribed(self):
        """stall_set_oversubscribed: WAYS outstanding claims in one set
        refuse a further alloc to that set (a different set is unaffected)
        until one of the set's entries retires.  (Fills are slowed so all
        WAYS claims stay live until the stalled request is presented --
        with real commits, entries retire as their fills complete.)"""
        r0 = self.release_count
        set_hot = 60
        saved_latency = self.fill_done_latency
        self.fill_done_latency = 40
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
        self._score("setover: still stalled before any hot-set commit",
                    int(self.dut.lkup_ready_o.value), 0)
        self.fill_done_latency = saved_latency
        # the fills retire in launch order; the first hot-set commit
        # frees the set claim that releases the stall
        rec = await task
        self._score("setover: stalled at WAYS claims", rec['stalls'] >= 6,
                    True)
        self._score("setover: allocs after the retire", rec['cls']['alloc'],
                    1)
        for e in self.entries:
            await self._await_commit(e, label='setover:commit')
        await self._wait_releases(r0, self.WAYS + 2)
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
        await self._await_commit(self.entries[-1], label='wport:commit')
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
    # Task 6: commit pipeline scenarios
    # ------------------------------------------------------------------
    async def _scen_commit_installs_tag(self):
        """commit_installs_tag: the commit installs the tag with the entry's
        install state -- S for an RNSD fill without PassDirty, M when
        PassDirty was received (amber #106), M for a write (RU) fill.  The
        watcher scores the install write itself; a following write's
        classify (upgrade iff S) proves the installed state end-to-end."""
        r0 = self.release_count
        # (a) RNSD read miss, no PassDirty -> installs S
        rd = await self._req(self._compose_addr(0xC0, 90), 0, 0xFF, 0,
                             label='cinstall:rnsd')
        self._score("cinstall: rnsd allocs", rd['cls']['alloc'], 1)
        await self._await_commit(self.entries[-1], label='cinstall:rnsd')
        # a write to the S line is an upgrade (proves S, not M/E)
        wr = await self._req(self._compose_addr(0xC0, 90), 1, 0xFF,
                             0xC0FFEE00C0FFEE00, label='cinstall:rnsd_wr')
        self._score("cinstall: S line upgrades on a write",
                    wr['cls']['upgrade'], 1)
        await self._await_cu_commit(label='cinstall:rnsd_cu')
        # (b) RNSD read miss WITH PassDirty -> installs M (amber #106)
        self.pass_dirty_next = True
        rd2 = await self._req(self._compose_addr(0xC1, 92), 0, 0xFF, 0,
                              label='cinstall:passdirty')
        self._score("cinstall: pd rnsd allocs", rd2['cls']['alloc'], 1)
        await self._await_commit(self.entries[-1], label='cinstall:pd')
        # a write to the M line is a plain write hit (no upgrade)
        wr2 = await self._req(self._compose_addr(0xC1, 92), 1, 0xFF,
                              0xD15EA5ED15EA5E00, label='cinstall:pd_wr')
        self._score("cinstall: PD line is M (plain write hit)",
                    wr2['cls']['hit'], 1)
        # (c) RU write miss -> installs M
        wr3 = await self._req(self._compose_addr(0xC2, 94), 1, 0xFF,
                              0xFEEDFACE12345678, label='cinstall:ru')
        self._score("cinstall: write miss allocs RU", wr3['cls']['alloc'], 1)
        await self._await_commit(self.entries[-1], label='cinstall:ru')
        wr4 = await self._req(self._compose_addr(0xC2, 94, 4), 1, 0xFF,
                              0x0DDC0FFEEBAAC0DE, label='cinstall:ru_wr')
        self._score("cinstall: RU line is M (plain write hit)",
                    wr4['cls']['hit'], 1)
        await self._wait_releases(r0, 6)
        self.scenarios['commit_installs_tag'] = True

    async def _scen_commit_merges_store_data(self):
        """commit_merges_store_data (amber D-4): the committing entry's
        store data merges onto the just-filled beats with byte enables, in
        requester order; a read between two writes to the same beat sees
        the earlier write but NOT the later one (request order pinned by
        the watcher's per-slot golden)."""
        r0 = self.release_count
        tag, set_idx = 0xD0, 100
        w0 = await self._req(self._compose_addr(tag, set_idx, 0), 1, 0x0F,
                             0x1111111111111111, label='d4:wr_alloc')
        self._score("d4: write miss allocs RU", w0['cls']['alloc'], 1)
        w1 = await self._req(self._compose_addr(tag, set_idx, 3), 1, 0xF0,
                             0x2222222222222222, label='d4:wr_merge1')
        self._score("d4: second write merges", w1['cls']['merge'], 1)
        rd = await self._req(self._compose_addr(tag, set_idx, 3), 0, 0xFF,
                             0, label='d4:rd_between')
        self._score("d4: read merges between writes", rd['cls']['merge'], 1)
        w2 = await self._req(self._compose_addr(tag, set_idx, 3), 1, 0x0F,
                             0x3333333333333333, label='d4:wr_merge2')
        self._score("d4: third write merges", w2['cls']['merge'], 1)
        entry = self.entries[-1]
        self._score("d4: four requesters", len(entry['requesters']), 4)
        # a read presented once the fill is done finds the entry committing
        # (the merge list froze at fill_done): it stalls commit_in_progress
        # until the retire, then hits the installed line
        self._ev_pos = len(self.events)
        await self._wait_event('fill_done',
                               pred=lambda p: p['line'] == entry['line'])
        rd2 = await self._req(self._compose_addr(tag, set_idx, 3), 0, 0xFF,
                              0, label='d4:rd_committing',
                              exp_stall=STALL_COMMIT)
        self._score("d4: read stalled on the committing entry",
                    rd2['stalls'] >= 1, True)
        self._score("d4: read hits after the retire", rd2['cls']['hit'], 1)
        await self._await_commit(entry, label='d4:commit')
        await self._wait_releases(r0, 5)
        # the committed line reads back with ALL stores merged
        line = entry['line']
        for b in (0, 3):
            await self._req(self._compose_addr(tag, set_idx, b), 0, 0xFF,
                            0, label=f'd4:readback[{b}]')
        self._score("d4: final line image",
                    bytes(self.array_data[(set_idx, entry['way'])]),
                    bytes(self.arch_data[line]))
        self._score("d4: store bytes landed",
                    self._beat_of(self.array_data[(set_idx, entry['way'])],
                                  3),
                    self._beat_of(self.arch_data[line], 3))
        await self._wait_releases(r0, 7)
        self.scenarios['commit_merges_store_data'] = True

    async def _scen_merge_response_completeness(self):
        """merge_response_completeness (Review Focus 2): allocator + 3
        merged requesters + 1 cross-class waiter -> exactly one response
        per sequence tag, in tag order, at the response port.  The watcher
        pins the deposit stream (order, adjacency, no double deposits); the
        release watcher pins J4 order at the wire."""
        r0 = self.release_count
        tag, set_idx = 0xD4, 102
        recs = []
        for i in range(4):
            rec = await self._req(self._compose_addr(tag, set_idx, i),
                                  0, 0xFF, 0, label=f'mrc:rd[{i}]')
            recs.append(rec)
        self._score("mrc: allocator allocs", recs[0]['cls']['alloc'], 1)
        for i in range(1, 4):
            self._score(f"mrc: rd[{i}] merges", recs[i]['cls']['merge'], 1)
        entry = self.entries[-1]
        exp_tags = [r['tag'] for r in recs]
        self._score("mrc: merge list in tag order",
                    [r['tag'] for r in entry['requesters']], exp_tags)
        # the cross-class waiter: a write behind the RNSD fill
        wdata = 0x5EAF00D5EAF00D00
        wr_task = cocotb.start_soon(
            self._req(self._compose_addr(tag, set_idx), 1, 0xFF, wdata,
                      label='mrc:xclass_wr', exp_stall=STALL_XCLASS))
        await self._idle_cycles(8)
        await self._await_commit(entry, label='mrc:commit')
        rec = await wr_task
        self._score("mrc: waiter proceeds as an upgrade",
                    rec['cls']['upgrade'], 1)
        await self._await_cu_commit(label='mrc:cu_commit')
        # five responses total, released in tag order (watcher-scored)
        await self._wait_releases(r0, 5)
        self.scenarios['merge_response_completeness'] = True

    async def _scen_commit_retires_entry(self):
        """commit_retires_entry: the commit retires the MSHR entry (the
        occupancy gauge returns to 0), frees the victim-way claim (the
        freed entry is the lowest free slot and is reused by the next
        alloc), and the line serves hits afterwards."""
        r0 = self.release_count
        rec = await self._req(self._compose_addr(0xD8, 104), 0, 0xFF, 0,
                              label='retire:miss')
        self._score("retire: allocs", rec['cls']['alloc'], 1)
        idx0 = self.entries[-1]['idx']
        await self._idle_cycles(1)
        self._score("retire: occupancy before commit",
                    int(self.dut.mshr_occupancy_o.value), 1)
        await self._await_commit(self.entries[-1], label='retire:commit')
        await self._idle_cycles(1)
        self._score("retire: occupancy after commit",
                    int(self.dut.mshr_occupancy_o.value), 0)
        # the freed entry is the lowest free slot: the next alloc reuses it
        rec2 = await self._req(self._compose_addr(0xD9, 106), 0, 0xFF, 0,
                               label='retire:realloc')
        self._score("retire: realloc allocs", rec2['cls']['alloc'], 1)
        self._score("retire: freed entry reused",
                    self.entries[-1]['idx'], idx0)
        await self._await_commit(self.entries[-1], label='retire:commit2')
        await self._idle_cycles(1)
        self._score("retire: occupancy back to 0",
                    int(self.dut.mshr_occupancy_o.value), 0)
        # both committed lines serve hits (the claims are gone)
        h1 = await self._req(self._compose_addr(0xD8, 104, 2), 0, 0xFF, 0,
                             label='retire:hit1')
        self._score("retire: line 1 hits", h1['cls']['hit'], 1)
        h2 = await self._req(self._compose_addr(0xD9, 106, 2), 0, 0xFF, 0,
                             label='retire:hit2')
        self._score("retire: line 2 hits", h2['cls']['hit'], 1)
        await self._wait_releases(r0, 4)
        self.scenarios['commit_retires_entry'] = True

    async def _scen_pend_eff_applied_after_install(self):
        """pend_eff_applied_after_install: a snoop hitting an in-flight
        entry records its post-commit effect through the REAL snoop
        service (Task 7) and the commit lands it AFTER the tag install --
        the watcher pins the two-write order; the post-commit classify
        proves the final state.  (With the real path the reference is the
        post-fill state the snoop can resolve: M for an RU fill, S for an
        RNSD fill -- a PassDirty RNSD install is indistinguishable from S
        before fill_done, so the downgrade case uses an RU fill.)"""
        r0 = self.release_count
        saved = self.fill_done_latency
        self.fill_done_latency = 12
        # (a) RU write fill (install M) + mid-fill ReadShared snoop ->
        # DOWNGRADE_S: the commit writes install M, then S.
        wr = await self._req(self._compose_addr(0xE0, 110), 1, 0xFF,
                             0xABCDABCDABCDABCD, label='pend:ru')
        self._score("pend: ru allocs", wr['cls']['alloc'], 1)
        entry = self.entries[-1]
        self._ev_pos = len(self.events)
        await self._wait_event('fill_beat',
                               pred=lambda p: p['line'] == entry['line'])
        await self._snoop(entry['line'], SN_READ_SHARED, 'pend:rs',
                          ref='M', deliver=False)
        self._snoop_eff_model(entry, 'M', SN_READ_SHARED)
        # (b) RNSD read fill (install S) + mid-fill MakeInvalid snoop ->
        # INVALIDATE_I: the commit writes install S, then I.
        rd2 = await self._req(self._compose_addr(0xE1, 112), 0, 0xFF, 0,
                              label='pend:rnsd')
        self._score("pend: rnsd allocs", rd2['cls']['alloc'], 1)
        entry2 = self.entries[-1]
        self._ev_pos = len(self.events)
        await self._wait_event('fill_beat',
                               pred=lambda p: p['line'] == entry2['line'])
        await self._snoop(entry2['line'], SN_MAKE_INVALID, 'pend:mi',
                          ref='S', deliver=False)
        self._snoop_eff_model(entry2, 'S', SN_MAKE_INVALID)
        self.fill_done_latency = saved
        await self._await_commit(entry, label='pend:commit_a')
        # final state S: a write upgrades (the classify proves it)
        wr2 = await self._req(self._compose_addr(0xE0, 110), 1, 0xFF,
                              0xDCBADCBA0DDC0DDC, label='pend:wr_after_s')
        self._score("pend: downgraded line is S (upgrade)",
                    wr2['cls']['upgrade'], 1)
        await self._await_cu_commit(label='pend:cu')
        await self._await_commit(entry2, label='pend:commit_b')
        # final state I: the same line misses again (new alloc)
        rd3 = await self._req(self._compose_addr(0xE1, 112), 0, 0xFF, 0,
                              label='pend:after_i')
        self._score("pend: invalidated line misses again",
                    rd3['cls']['alloc'], 1)
        await self._await_commit(self.entries[-1], label='pend:commit_c')
        await self._wait_releases(r0, 4)
        self.scenarios['pend_eff_applied_after_install'] = True

    # ------------------------------------------------------------------
    # Task 7: snoop path under concurrency
    # ------------------------------------------------------------------
    async def _scen_snoop_hit_pending_entry(self):
        """snoop_hit_pending_entry: a snoop matching an in-flight MSHR
        entry is answered at the entry's post-fill install state (never
        the Invalid row), with CD from the array once every fill beat has
        landed; the effect is recorded in pend_eff.  Also pins the carried
        I-sticks review item: an armed invalidate is NOT overwritten by a
        later downgrade (the commit's pend write must be I)."""
        r0 = self.release_count
        saved = self.fill_done_latency
        self.fill_done_latency = 12   # wide post-beats window for snoop 2
        wdata = 0x6666777788889999
        wr = await self._req(self._compose_addr(0x100, 8), 1, 0xFF, wdata,
                             label='snpe:wr_miss')
        self._score("snpe: write miss allocs RU", wr['cls']['alloc'], 1)
        entry = self.entries[-1]
        line = entry['line']
        # (1) mid-fill: MakeInvalid -- answered at the post-fill M row
        # (the M-row MakeInvalid decode carries no DT); effect INVALIDATE.
        self._ev_pos = len(self.events)
        await self._wait_event('fill_beat', pred=lambda p: p['line'] == line)
        res = await self._snoop(line, SN_MAKE_INVALID, 'snpe:mi',
                                ref='M', deliver=False)
        self._snoop_eff_model(entry, 'M', SN_MAKE_INVALID)
        self._score("snpe: mi armed the invalidate", entry['pend'], 'I')
        # (2) all beats landed, fill not done: ReadShared answers at the
        # post-fill M row WITH the fill data (PF_GUARD open); the downgrade
        # effect must NOT overwrite the armed invalidate (I-sticks).
        await self._wait_event('fill_beat',
                               pred=lambda p: p['line'] == line
                               and p['beat'] == self.FILL_BEATS - 1)
        exp_cd = [self._beat_of(entry['fill_line_data'], b)
                  for b in range(self.FILL_BEATS)]
        res = await self._snoop(line, SN_READ_SHARED, 'snpe:rs',
                                ref='M', deliver=True, exp_cd=exp_cd)
        self._snoop_eff_model(entry, 'M', SN_READ_SHARED)
        self._score("snpe: I-sticks (invalidate survives the downgrade)",
                    entry['pend'], 'I')
        self.fill_done_latency = saved
        # the commit watcher scores install M then pend I on the tag port
        await self._await_commit(entry, label='snpe:commit')
        # the invalidated line misses again
        rd = await self._req(self._compose_addr(0x100, 8, 2), 0, 0xFF, 0,
                             label='snpe:after_i')
        self._score("snpe: invalidated line misses again",
                    rd['cls']['alloc'], 1)
        await self._await_commit(self.entries[-1], label='snpe:commit2')
        await self._wait_releases(r0, 2)
        self.scenarios['snoop_hit_pending_entry'] = True

    async def _scen_snoop_pf_guard(self):
        """snoop_pf_guard (Review Focus 4): a snoop matching a pending
        entry presents CD ONLY for beats the fill has landed -- with beats
        outstanding, DataTransfer and PassDirty are suppressed and no beat
        is ever presented -- and the answer is never the Invalid row."""
        r0 = self.release_count
        saved = self.fill_done_latency
        self.fill_done_latency = 14
        # (a) RU fill, two beats landed: CleanInvalid -> guarded answer
        # (DT/PD cleared), zero CD beats, IsShared still set (never the
        # Invalid row).
        wdata = 0x1212343456567878
        wr = await self._req(self._compose_addr(0x110, 12), 1, 0xFF, wdata,
                             label='pfg:wr_miss')
        self._score("pfg: write miss allocs RU", wr['cls']['alloc'], 1)
        entry = self.entries[-1]
        line = entry['line']
        self._ev_pos = len(self.events)
        await self._wait_event('fill_beat', pred=lambda p: p['line'] == line
                               and p['beat'] == 1)
        res = await self._snoop(line, SN_CLEAN_INVALID, 'pfg:ci',
                                ref='M', deliver=False)
        self._score("pfg: guarded answer carries the post-fill row (IS)",
                    res['crresp'] & 0b01000, 0b01000)
        self._score("pfg: guarded answer drops DT/PD",
                    res['crresp'] & 0b00101, 0)
        self._score("pfg: no CD beat presented", len(res['beats']), 0)
        self._snoop_eff_model(entry, 'M', SN_CLEAN_INVALID)
        # (b) every beat landed: ReadUnique -> the full M-row decode and
        # the fill data beat by beat.
        await self._wait_event('fill_beat',
                               pred=lambda p: p['line'] == line
                               and p['beat'] == self.FILL_BEATS - 1)
        exp_cd = [self._beat_of(entry['fill_line_data'], b)
                  for b in range(self.FILL_BEATS)]
        res = await self._snoop(line, SN_READ_UNIQUE, 'pfg:ru',
                                ref='M', deliver=True, exp_cd=exp_cd)
        self._snoop_eff_model(entry, 'M', SN_READ_UNIQUE)
        self.fill_done_latency = saved
        await self._await_commit(entry, label='pfg:commit')
        # (c) RNSD fill with ZERO beats landed: ReadShared answers the
        # post-fill S row ({IS}) -- never the Invalid row -- with no
        # effect (a fixed-point snoop).
        rd = await self._req(self._compose_addr(0x111, 14), 0, 0xFF, 0,
                             label='pfg:rd_miss')
        self._score("pfg: read miss allocs RNSD", rd['cls']['alloc'], 1)
        entry2 = self.entries[-1]
        res = await self._snoop(entry2['line'], SN_READ_SHARED, 'pfg:rs0',
                                ref='S', deliver=False)
        self._score("pfg: zero-beat answer is the S row (never Invalid)",
                    res['crresp'], 0b01000)
        self._snoop_eff_model(entry2, 'S', SN_READ_SHARED)
        self._score("pfg: fixed point records no effect",
                    entry2['pend'], None)
        await self._await_commit(entry2, label='pfg:commit2')
        await self._wait_releases(r0, 2)
        self.scenarios['snoop_pf_guard'] = True

    async def _scen_snoop_snarf_bresp_race(self):
        """snoop_snarf_bresp_race (Review Focus 3): a snoop matching a WB
        entry is answered from the buffer (SINK_WB_ACK semantics) -- even
        in the entry's BRESP cycle: the grant snapshots the line, the CD
        stream serves the snapshot after the entry has retired, and the
        drain still completes the memory update."""
        r0 = self.release_count
        d = self.dut
        set_r = 16
        saved_drain = self.drain_latency
        self.drain_latency = 40   # sampled by the stub at drain_start
        for w in range(self.WAYS):
            await self._install_line(((0x200 + w) << self.SET_BITS) | set_r,
                                     'M')
        vline = ((0x200 + self.WAYS - 1) << self.SET_BITS) | set_r
        vdata = bytes(self.array_data[(set_r, self.WAYS - 1)])
        ra = await self._req(self._compose_addr(0x210, set_r), 0, 0xFF, 0,
                             label='snarf:miss')
        self._score("snarf: miss allocs", ra['cls']['alloc'], 1)
        self._score("snarf: victim dirty (captured)", ra['victim_dirty'],
                    True)
        # wait for the capture to complete (the WB entry validates)
        for _ in range(self.REQ_TIMEOUT * 4):
            await self._drive_pt()
            await self._settle()
            if not int(d.cap_busy_o.value):
                break
        else:
            raise RuntimeError("snarf: capture never completed")
        # snoop 1: ReadOnce the victim line mid-drain -- snarfed at M with
        # the buffered data; the effect is recorded on the WB entry.
        exp_cd = [self._beat_of(vdata, b) for b in range(self.FILL_BEATS)]
        res = await self._snoop(vline, SN_READ_ONCE, 'snarf:ro',
                                ref='M', deliver=True, exp_cd=exp_cd)
        self._score("snarf: effect recorded on the WB entry",
                    res['wb_eff'], PEND_INVALIDATE_I)
        # the race: present snoop 2 so its grant cycle IS the entry's
        # BRESP cycle (the drain stub exposes its countdown; the drive
        # point after a settle that observed it at 0 is the BRESP cycle)
        res = await self._snoop(vline, SN_CLEAN_SHARED, 'snarf:bresp',
                                ref='M', deliver=True, exp_cd=exp_cd,
                                sync_drain_cd=True)
        self._score("snarf: grant landed in the BRESP cycle",
                    res['bresp'], 1)
        # the drain retired the victim to memory with the original data
        self._score("snarf: the drain completed the memory update",
                    self._line_int(self._mem_line(vline)),
                    self._line_int(vdata))
        await self._await_commit(self.entries[-1], label='snarf:commit')
        await self._wait_releases(r0, 1)
        self.drain_latency = saved_drain
        self.scenarios['snoop_snarf_bresp_race'] = True
        await self._reset_pipeline()

    async def _scen_snoop_priority(self):
        """snoop_priority (J6): a snoop presented with a CPU request
        pending is served first -- the lookup stage holds the CPU request
        (no accept, no stall reason) through the grant, the CD stream, and
        the effect cycle, then accepts it."""
        r0 = self.release_count
        d = self.dut
        line_a = (0x300 << self.SET_BITS) | 24
        line_c = (0x301 << self.SET_BITS) | 26
        await self._install_line(line_a, 'M')
        await self._install_line(line_c, 'M')
        set_c = self._set_of_line(line_c)
        way_c = self._hit_way(set_c, line_c)
        cdata = bytes(self.array_data[(set_c, way_c)])
        # baseline: a lone read hit accepts the presenting cycle
        rec = await self._req(self._compose_addr(0x300, 24, 1), 0, 0xFF, 0,
                              label='prio:baseline')
        self._score("prio: baseline no hold", rec['stalls'] + rec['yields'],
                    0)
        # coincidence: a CPU read hit to A and a ReadShared snoop to C in
        # the same cycle
        await self._drive_pt()
        d.lkup_valid_i.value = 1
        d.lkup_addr_i.value = self._compose_addr(0x300, 24, 2)
        d.lkup_we_i.value = 0
        d.lkup_be_i.value = 0xFF
        d.lkup_wdata_i.value = 0
        self._score("prio: safe for the snoop", int(d.sn_safe_o.value), 1)
        d.sn_req_i.value = 1
        d.sn_addr_i.value = (line_c & self.LINE_MASK) << self.OFFSET_BITS
        d.sn_type_i.value = SN_READ_SHARED
        await self._settle()
        self._score("prio: CPU held at the grant",
                    int(d.lkup_ready_o.value), 0)
        self._score("prio: snoop granted", int(d.sn_ready_o.value), 1)
        self._score("prio: grant-cycle CRRESP (M row, ReadShared)",
                    int(d.sn_crresp_o.value),
                    _sn_crresp('M', SN_READ_SHARED))
        # through the CD stream the CPU request stays held (no accept, no
        # stall reason), beats come from the array on port B
        beats = 0
        for _ in range(64):
            await self._drive_pt()
            d.sn_req_i.value = 0
            d.sn_cdready_i.value = 1
            await self._settle()
            self._score("prio: CPU held during the service",
                        int(d.lkup_ready_o.value), 0)
            self._score("prio: no stall reason during a snoop hold",
                        int(d.lkup_stall_o.value), 0)
            if int(d.sn_cdvalid_o.value):
                self._score(f"prio: cd[{beats}]",
                            int(d.sn_cddata_o.value),
                            self._beat_of(cdata, beats))
                beats += 1
                if int(d.sn_cdlast_o.value):
                    break
        else:
            raise RuntimeError("prio: CD stream never completed")
        self._score("prio: full line served", beats, self.FILL_BEATS)
        # the effect cycle (M -> S tag write) still holds the CPU
        await self._drive_pt()
        d.sn_cdready_i.value = 0
        await self._settle()
        self._score("prio: CPU held through the effect cycle",
                    int(d.lkup_ready_o.value), 0)
        # then the CPU hit is accepted
        await self._drive_pt()
        await self._settle()
        self._score("prio: CPU accepted after the service",
                    int(d.lkup_ready_o.value), 1)
        self._score("prio: accepted class hit", int(d.lkup_hit_o.value), 1)
        # the _accept bookkeeping inline (the snoop touched no CPU state)
        tag = self.next_tag
        self.next_tag = (self.next_tag + 1) % self.RSP_DEPTH
        way_a = self._hit_way(24, line_a)
        exp_data = self._beat_of(self.array_data[(24, way_a)], 2)
        self._score("prio: hit deposit tag", int(d.cpl_tag_o.value), tag)
        self._score("prio: hit deposit data", int(d.cpl_data_o.value),
                    exp_data)
        await RisingEdge(d.clk)
        d.lkup_valid_i.value = 0
        self._score("prio: no double deposit", tag in self.deposits, False)
        self.deposits[tag] = exp_data
        self.lru.update(24, way_a)
        # model: the snoop downgraded C to S
        self.slot_state[(set_c, way_c)] = 'S'
        # and C's downgrade is visible: a write to C now upgrades
        wr = await self._req(self._compose_addr(0x301, 26, 0), 1, 0xFF,
                             0x5A6B7C8D9EAF0011, label='prio:wr_c')
        self._score("prio: downgraded line is S (upgrade)",
                    wr['cls']['upgrade'], 1)
        await self._await_cu_commit(label='prio:cu')
        await self._wait_releases(r0, 3)
        self.scenarios['snoop_priority'] = True

    async def _scen_anti_livelock_window(self):
        """anti_livelock_window (J4/Chinnakonda 10.9): after a CLEAN_UNIQUE
        grant for line L, snoop service is held off EXACTLY until the
        granted write's commit lands (a fixed, small cycle bound -- the
        commit needs the W port for one beat and the tag port for one
        write), then served: the answer is the committed M line with the
        held write merged."""
        r0 = self.release_count
        d = self.dut
        tag, set_idx = 0x400, 32
        line_l = (tag << self.SET_BITS) | set_idx
        # bring L in S (a read miss commit), then a write hit upgrades
        rd = await self._req(self._compose_addr(tag, set_idx), 0, 0xFF, 0,
                             label='alw:rd_miss')
        self._score("alw: read miss allocs", rd['cls']['alloc'], 1)
        await self._await_commit(self.entries[-1], label='alw:rd_commit')
        wdata = 0x0BADF00D12345678
        beat = 5
        wr = await self._req(self._compose_addr(tag, set_idx, beat), 1,
                             0xFF, wdata, label='alw:upgrade')
        self._score("alw: S write upgrades", wr['cls']['upgrade'], 1)
        # sample sn_safe every cycle from here; find the CU grant
        # (fill_done) and measure the hold-off to the commit's landing.
        # self.cyc is a shared drive-point counter (every coroutine
        # increments it), so measure in scenario-loop iterations -- one per
        # cycle -- instead.
        self._ev_pos = len(self.events)
        start = self.cyc
        iters = 0
        cu_done_iter = None
        safe_log = {}
        while True:
            await self._drive_pt()
            await self._settle()
            safe_log[iters] = int(d.sn_safe_o.value)
            while self._ev_pos < len(self.events):
                cyc, kind, p = self.events[self._ev_pos]
                self._ev_pos += 1
                if kind == 'fill_done' and p['cls'] == CLS_CU:
                    cu_done_iter = iters
            if cu_done_iter is not None and int(d.sn_safe_o.value):
                break
            iters += 1
            if self.cyc - start > 1400:
                raise RuntimeError("alw: sn_safe never returned")
        # the hold-off covers the grant cycle and ends with the commit
        self._score("alw: hold-off covers the CU grant cycle",
                    safe_log.get(cu_done_iter), 0)
        holdoff = iters - cu_done_iter
        self._score("alw: hold-off bounded by the commit (<= 6 cycles)",
                    holdoff <= 6, True)
        self._score("alw: hold-off real (the grant is covered)",
                    holdoff >= 2, True)
        await self._await_cu_commit(label='alw:cu_commit')
        # served after the window: the answer is the committed M line with
        # the held write merged (the CU commit's D-4 merge)
        exp_cd = [self._beat_of(self.arch_data[line_l], b)
                  for b in range(self.FILL_BEATS)]
        res = await self._snoop(line_l, SN_READ_UNIQUE, 'alw:ru',
                                ref='M', deliver=True, exp_cd=exp_cd)
        # the invalidate landed: L misses afterwards
        rd2 = await self._req(self._compose_addr(tag, set_idx, 1), 0, 0xFF,
                              0, label='alw:after')
        self._score("alw: invalidated line misses again",
                    rd2['cls']['alloc'], 1)
        await self._await_commit(self.entries[-1], label='alw:commit2')
        await self._wait_releases(r0, 3)
        self.scenarios['anti_livelock_window'] = True

    async def _scen_snoop_never_waits_on_wb_full(self):
        """snoop_never_waits_on_wb_full: snoop acceptance and service never
        gate on WB occupancy or drain state -- with the WB full and the
        drains held, snoops to a resident line (array), to a WB-buffered
        line (snarf), and to an absent line are all granted immediately
        and answered correctly."""
        r0 = self.release_count
        d = self.dut
        saved_drain = self.drain_latency
        self.drain_latency = 100   # drains held through the snoop phase
        # a resident unrelated line (set 52); dirty victims in sets 48/49
        line_u = (0x500 << self.SET_BITS) | 52
        await self._install_line(line_u, 'M')
        for s, tbase in ((48, 0x510), (49, 0x520)):
            for w in range(self.WAYS):
                await self._install_line(
                    ((tbase + w) << self.SET_BITS) | s, 'M')
        va = ((0x510 + self.WAYS - 1) << self.SET_BITS) | 48
        va_data = bytes(self.array_data[(48, self.WAYS - 1)])
        ra = await self._req(self._compose_addr(0x530, 48), 0, 0xFF, 0,
                             label='wbwait:miss_a')
        rb = await self._req(self._compose_addr(0x540, 49), 0, 0xFF, 0,
                             label='wbwait:miss_b')
        self._score("wbwait: both victims dirty",
                    bool(ra['victim_dirty']) and bool(rb['victim_dirty']),
                    True)
        # both captures complete, both fills commit; the drains are held,
        # so the WB fills and stays full
        for e in self.entries[-2:]:
            await self._await_commit(e, label='wbwait:commit')
        for _ in range(self.REQ_TIMEOUT * 4):
            await self._drive_pt()
            await self._settle()
            if int(d.wb_full_o.value) and not int(d.cap_busy_o.value):
                break
        else:
            raise RuntimeError("wbwait: WB never filled")
        # (a) the resident line: granted at once with the WB full
        await self._drive_pt()
        self._score("wbwait: safe with the WB full",
                    int(d.sn_safe_o.value), 1)
        way_u = self._hit_way(52, line_u)
        exp_cd_u = [self._beat_of(self.array_data[(52, way_u)], b)
                    for b in range(self.FILL_BEATS)]
        res = await self._snoop(line_u, SN_READ_SHARED, 'wbwait:resident',
                                ref='M', deliver=True, exp_cd=exp_cd_u)
        self._score("wbwait: still full after the resident snoop",
                    int(d.wb_full_o.value), 1)
        self.slot_state[(52, way_u)] = 'S'   # model: M -> S downgrade
        # (b) the WB head's line: snarfed with the WB full
        exp_cd_a = [self._beat_of(va_data, b) for b in range(self.FILL_BEATS)]
        res = await self._snoop(va, SN_READ_ONCE, 'wbwait:snarf',
                                ref='M', deliver=True, exp_cd=exp_cd_a)
        self._score("wbwait: snarf recorded the effect",
                    res['wb_eff'], PEND_INVALIDATE_I)
        # (c) an absent line: the Invalid row, no CD
        res = await self._snoop((0x5F0 << self.SET_BITS) | 60,
                                SN_READ_UNIQUE, 'wbwait:absent',
                                ref='I', deliver=False)
        self._score("wbwait: WB still full (the snoops never waited)",
                    int(d.wb_full_o.value), 1)
        # release the drains; the stub checks order + payload
        self.drain_latency = 3
        for _ in range(self.REQ_TIMEOUT * 4):
            await self._drive_pt()
            await self._settle()
            if len(self.wb_expect) == 0 and not int(d.wb_full_o.value):
                break
        self._score("wbwait: both victims drained", len(self.wb_expect), 0)
        await self._wait_releases(r0, 2)
        self.drain_latency = saved_drain
        self.scenarios['snoop_never_waits_on_wb_full'] = True
        await self._reset_pipeline()


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
        await self._scen_stall_wb_drain_race()
        await self._scen_stall_set_oversubscribed()
        await self._scen_fill_beats_win_wport()
        await self._scen_stall_tag_full()
        await self._scen_commit_installs_tag()
        await self._scen_commit_merges_store_data()
        await self._scen_merge_response_completeness()
        await self._scen_commit_retires_entry()
        await self._scen_pend_eff_applied_after_install()
        await self._scen_snoop_hit_pending_entry()
        await self._scen_snoop_pf_guard()
        await self._scen_snoop_snarf_bresp_race()
        await self._scen_snoop_priority()
        await self._scen_anti_livelock_window()
        await self._scen_snoop_never_waits_on_wb_full()

    async def run(self) -> bool:
        await self._run_all()
        if self.TEST_LEVEL in ('func', 'full'):
            # second pass with perturbed partner-stub latencies (timing
            # robustness: the fill launch hold, the stall release paths,
            # the commit/lookup port arbitration, and the snoop service
            # see different alignments) plus CD backpressure mid-stream
            self.log.info("jet_control: FUNC second pass, perturbed "
                          "fill/drain latencies + CD gap")
            self.fill_accept_latency = 2
            self.fill_beat_latency = 5
            self.fill_done_latency = 6
            self.drain_latency = 8
            self.sn_cd_gap = True
            self.scenarios = {}
            await self._reset_pipeline()
            await self._run_all()
        missing = [k for k, v in self.scenarios.items() if not v]
        self._score("all scenarios ran", len(missing), 0)
        # quiescence: no response record leaks, no WB capture leaks, no
        # uncommitted entries
        self._score("final: no outstanding deposits",
                    len(self.deposits), 0)
        self._score("final: WB empty", len(self.wb_expect), 0)
        self._score("final: no uncommitted entries",
                    sum(1 for e in self.entries if not e['committed']), 0)
        return self.mismatches == 0

    def get_test_report(self):
        return {'checks': self.checks, 'mismatches': self.mismatches,
                'scenarios': sorted(self.scenarios)}
