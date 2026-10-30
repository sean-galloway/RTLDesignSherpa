"""
jet pair rig testbench (Task 9)

Two jet_top caches + the jet_pair_fabric snoopy manager + the house
sdpram_slave_axi4_axi4 shared memory, coherent end-to-end -- the amber
pair rig (amber_pair_rig_tb) re-run with two jets.  The DUT is the rig
harness (dv/tb/jet_pair_rig_tb.sv).  The TB drives BOTH CPU GAXI ports
concurrently and scores coherence against a 2-cache Python lockstep
model.

Model design (the JetCoreTB event-stream machinery, per cache, plus the
fabric layer ported from AmberPairRigTB):
  * Per cache (Side): tags/slot_state/pw (accepted-write overlay),
    MSHR entries (alloc -> launch -> AR -> beats -> done -> commit),
    the WB capture snapshots, the upgrade tracker, the LruModel, and the
    issue-order response queue.  Everything is observation-driven at the
    same events the core TB uses (lookup accept, alloc, snoop grant,
    fill beat, fill_done, launch, tag write, drain, retire, response).
  * jet has no replay path, so the amber killed-pass machinery is
    replaced by the pre-AR rule (jet_control, Task 9): a snoop matching
    an MSHR entry whose fill AR has not been accepted yet answers at the
    Invalid row with no effect and no data (the fill's data necessarily
    post-dates the snoop on this serializing fabric).  The fabric's kill
    rule still fires (a queued same-line peer fill is always pre-AR --
    the fabric itself holds its AR), so a killed snoop and a normal
    snoop produce the same I-row answer; the TB scores the fabric's
    dbg_kill against its queue model regardless.
  * Fabric layer: coh_req pulses latch per-direction pending queues; the
    serialized grant is observed on the fabric dbg taps; the snoop
    resolution is recorded at the peer's observed grant (oracle_step on
    the peer's CURRENT model state) and bound to the requester's fill as
    its data source.  PassDirty resolutions absorb the forwarded line
    into the memory model (the fabric keeps the sdpram the point of
    coherence); WRITE_BACK pulses update the memory model from the WB
    capture snapshot.
  * Memory model: line content initialized identically to the sdpram
    backdoor; audited against the sdpram r_mem at quiescence and per
    drain.

What this suite pins (the pair-rig contract on jets):
  (a) M->remote-fill PassDirty forwarding -- fill data from the peer,
      not the (poisoned) memory; the memory AR is suppressed.
  (b) S->M upgrade invalidates the peer; the peer's later read misses
      and the fabric forwards.
  (c) Dirty eviction WriteBack (WB buffer + l1_drain) visible to the
      memory AND to the peer.
  (d) E->S downgrade on ReadShared (tag-word promotion backdoor).
  (e) Simultaneous same-line misses serialize fairly, both correct --
      with jet's pre-AR answer instead of amber's kill+replay.
  (f) pair_ships_in_the_night -- a pre-BRESP WriteBack meets the peer's
      same-line request: the snoop is answered from the WB buffer
      snapshot (DT+PD), the peer fills from it, the absorption lands.
  (g) Randomized dual-CPU lockstep soak (func/full).
  (h) MonBus present-vs-absent equivalence (USE_MONITOR=0 gate cell).

Levels (TEST_LEVEL):
  gate  -- InitWalk + directed (a)-(f)
  func  -- + RandomDualCpuLockstep (g)
  full  -- + dual-CPU soak

Author: RTL Design Sherpa
Created: 2026-10-29
"""

import os
import random
from collections import deque

import cocotb
from cocotb.triggers import FallingEdge, Timer

from TBClasses.shared.tbbase import TBBase

from CocoTBFramework.components.shared.flex_randomizer import FlexRandomizer
from CocoTBFramework.components.shared.field_config import FieldConfig
from CocoTBFramework.components.gaxi.gaxi_master import GAXIMaster
from CocoTBFramework.components.gaxi.gaxi_slave import GAXISlave
from CocoTBFramework.components.ace.ace_compliance_checker import ACEComplianceChecker
from CocoTBFramework.components.ace.ace_transaction import (
    CRRESP,
    SnoopType,
)

from projects.components.cache_ip.common_ip.dv.golden.l1_fsm_oracle import (
    SNOOP_CODES,
    step as oracle_step,
)
from projects.components.cache_ip.jet_mesi_l1.dv.tbclasses.jet_repl_models import (
    REPL_LRU,
    REPL_NAMES,
    make_repl_model,
)

# jet_fill_class_t (jet_pkg)
JET_CLS_RNSD, JET_CLS_RU, JET_CLS_CU = 0, 1, 2

# jet_control commit FSM states (rtl/fub/jet_control.sv localparams)
C_IDLE, C_MERGE, C_INSTALL, C_PEND, C_DEPOSIT, C_RETIRE = range(6)
C_CU_MERGE, C_CU_INSTALL, C_CU_DEPOSIT = 6, 7, 8
# snoop service FSM
SN_IDLE, SN_DATA, SN_EFFECT = 0, 1, 2
# l1_pkg
AMBER_STATE_I, AMBER_STATE_S, AMBER_STATE_E, AMBER_STATE_M = 0, 1, 2, 3
AMBER_CTRL_ERROR = 0xB
STATE_CODE = {'I': 0, 'S': 1, 'E': 2, 'M': 3}
CRRESP_DT = 0
CRRESP_PD = 2
CRRESP_NO_DT_MASK = 0b11000   # PF_GUARD: keep IS|WU, drop DT/PD/Err

# amber_ace_req_t encodings (l1_pkg) -- the coh_req sideband classes
ACE_READ_SHARED, ACE_READ_UNIQUE, ACE_CLEAN_UNIQUE = 0, 1, 2
ACE_MAKE_UNIQUE = 3
ACE_WRITE_BACK = 4
ACE_READ_NOT_SHARED_DIRTY = 6

# fabric ACSNOOP encodings (IHI0022 4-bit, framework SnoopType)
FAB_SNOOP_RS = 0x1   # SnoopType.READ_SHARED
FAB_SNOOP_RU = 0x7   # SnoopType.READ_UNIQUE
FAB_SNOOP_MI = 0xC   # SnoopType.MAKE_INVALID
SNOOP_NAME_BY_FAB = {FAB_SNOOP_RS: 'SNOOP_READ_SHARED',
                     FAB_SNOOP_RU: 'SNOOP_READ_UNIQUE',
                     FAB_SNOOP_MI: 'SNOOP_MAKE_INVALID'}
FAB_SNOOP_BY_TYPE = {ACE_READ_SHARED: FAB_SNOOP_RS,
                     ACE_READ_UNIQUE: FAB_SNOOP_RU,
                     ACE_CLEAN_UNIQUE: FAB_SNOOP_MI,
                     ACE_MAKE_UNIQUE: FAB_SNOOP_MI,
                     ACE_READ_NOT_SHARED_DIRTY: FAB_SNOOP_RS}
# the fabric's true-miss classes (the kill rule matches these)
TRUE_MISS_TYPES = (ACE_READ_SHARED, ACE_READ_NOT_SHARED_DIRTY,
                   ACE_READ_UNIQUE)

# fabric FSM states (jet_pair_fabric dbg encoding)
FAB_F_IDLE = 0
FAB_F_AC = 1
FAB_F_RESP = 2
FAB_F_REPLAY_AR = 3
FAB_F_REPLAY_R = 4
FAB_F_PASS_AR = 5
FAB_F_PASS_R = 6
FAB_F_DONE = 7
FAB_F_NODATA_AR = 8
FAB_F_NODATA_R = 9

# ACE framework mapping for the compliance checker
FRAMEWORK_SNOOPS = {
    'SNOOP_READ_SHARED': SnoopType.READ_SHARED,
    'SNOOP_READ_UNIQUE': SnoopType.READ_UNIQUE,
    'SNOOP_MAKE_INVALID': SnoopType.MAKE_INVALID,
}

NAME_BY_CODE = {code: name for name, code in SNOOP_CODES.items()}


class Side:
    """Golden model of ONE jet cache in the pair (no DUT references).

    Ported from the Task-8 JetCoreTB per-cache machinery: the model is
    observation-driven -- coherence effects land at the same observable
    events the RTL applies them at, so a peer transaction granted at any
    cycle is scored against exactly the resolution the RTL used.
    """

    def __init__(self, idx, tb):
        self.idx = idx
        self.tb = tb
        self.tags = {}           # (set, way) -> line (installed view)
        self.slot_state = {}     # (set, way) -> 'I'/'S'/'E'/'M'
        self.cache_data = {}     # line -> bytearray (resident content:
                                 # fill source + merges; independent of
                                 # the memory model -- a poisoned memory
                                 # must not corrupt it)
        self.entries = {}        # line -> entry dict (pending fills)
        self.entry_by_idx = {}   # mshr idx -> line
        self.unlaunched = deque()   # alloc order (launch order == alloc)
        self.launch_q = deque()  # fill-completion order ('entry'/'cu')
        self.upgr = {'valid': False, 'line': None, 'set': 0, 'way': 0,
                     'killed': False}
        self.wb = {}             # line -> capture-time content snapshot
        self.wb_order = deque()  # WB drain order (oldest first)
        self.draining = None
        self.committing = None
        self.promo = None        # pending E->M promotion tag write
        # victim-way parity model per policy (update-at-alloc for all;
        # hits move the policy state only under LRU -- l1_repl's
        # FIFO/RANDOM branches ignore repl_hit, and the models mirror
        # that)
        self.lru = make_repl_model(tb.REPL_POLICY, tb.SETS, tb.WAYS)
        self.exp_sn_tagwr = deque()
        self.rspq = deque()      # issue-order expected responses
        self.pending_slot = None  # the alloc-causing request's slot
        # stats
        self.txns = 0
        self.snoops = 0
        self.launch_waits = []
        self.launch_count = 0
        self.cu_launches = 0
        self.wb_grants = 0
        self.pre_ar_answers = 0
        self.pf_grants = 0
        self.kill_count = 0
        self.pend_installs = 0


class JetPairRigTB(TBBase):
    """Scores the jet pair rig against the 2-cache lockstep model."""

    FULL_TXN = {'gate': 0, 'func': 250, 'full': 2000}
    RSP_TIMEOUT_CYCLES = 8000

    def __init__(self, dut, **kwargs):
        super().__init__(dut)
        self.SEED = self.convert_to_int(os.environ.get('SEED', '12345'))
        self.TEST_LEVEL = os.environ.get('TEST_LEVEL', 'gate').lower()
        random.seed(self.SEED)

        self.SETS = int(os.environ.get('SETS', '128'))
        self.WAYS = int(os.environ.get('WAYS', '4'))
        self.ADDR_WIDTH = 32
        self.LINE_BYTES = int(os.environ.get('LINE_BYTES', '64'))
        self.BUS_WIDTH = int(os.environ.get('BUS_WIDTH', '64'))
        self.REPL_POLICY = int(os.environ.get('REPL_POLICY', '0'))
        self.USE_MONITOR = int(os.environ.get('USE_MONITOR', '1'))
        self.MSHR_COUNT = int(os.environ.get('MSHR_COUNT', '8'))
        self.VICTIM_DEPTH = int(os.environ.get('VICTIM_DEPTH', '2'))
        # hits move the policy state only under LRU (l1_repl's FIFO and
        # RANDOM branches ignore repl_hit; jet fires repl_update at the
        # alloc for every policy)
        self._hit_updates_repl = (self.REPL_POLICY == REPL_LRU)
        self.STRB_W = self.BUS_WIDTH // 8
        self.FILL_BEATS = self.LINE_BYTES // self.STRB_W
        self.SET_BITS = (self.SETS - 1).bit_length()
        self.OFFSET_BITS = (self.LINE_BYTES - 1).bit_length()
        self.SET_MASK = self.SETS - 1
        self.LINE_MASK = (1 << (self.ADDR_WIDTH - self.OFFSET_BITS)) - 1
        self.CPU_REQ_W = self.ADDR_WIDTH + 1 + self.STRB_W + self.BUS_WIDTH

        self.SPAN = min(max(self.SETS * 16, 32 << self.SET_BITS, 64), 4096)
        assert self.SPAN >= (self.WAYS + 10) * self.SETS
        self.MAX_TAG = (self.SPAN >> self.SET_BITS) - 1
        assert self.MAX_TAG >= self.WAYS + 13, "directed tag budget"

        # golden models
        self.sides = [Side(i, self) for i in range(2)]
        self.mem = {}            # memory model: line -> bytearray
        # per-direction pending-request queues, mirroring the fabric's
        # PEND_DEPTH FIFO
        self.ft_queue = [[], []]
        self.cur_ft = None       # in-flight fabric transaction (serial)
        self.stats = {
            'grants': [0, 0], 'kills': 0, 'kill_pred_ok': 0,
            'kill_pred_bad': 0, 'dt_forwards': 0, 'pass_throughs': 0,
            'absorbs': 0, 'mem_ar': 0, 'wb_bursts': 0, 'upgrades': 0,
            'first_grant': [],
        }

        # observation
        self.cyc = 0
        self.events = []
        self.rsp_log = [[], []]
        self.send_count = [0, 0]
        self.checks = 0
        self.mismatches = 0
        self.scenarios = {}
        self._prev_fab_state = -1
        self._ace_seq = [0, 0]
        self._cd_seq = [0, 0]
        self._cd_started = [False, False]
        self._cur_snoop_type = [None, None]
        self._cd_beats = [0, 0]
        self.ace_checkers = [ACEComplianceChecker(log=self.log),
                             ACEComplianceChecker(log=self.log)]
        self._mon_pkts = [0, 0]

        # directed-scenario tag allocator (tags map inside the pre-filled span)
        self._tag_next = 0

        self.log.info(f"JetPairRigTB sets={self.SETS} ways={self.WAYS} "
                      f"line={self.LINE_BYTES} bus={self.BUS_WIDTH} "
                      f"mshr={self.MSHR_COUNT} victim={self.VICTIM_DEPTH} "
                      f"repl={REPL_NAMES[self.REPL_POLICY]} "
                      f"monitor={self.USE_MONITOR} "
                      f"level={self.TEST_LEVEL} seed={self.SEED}")

    # ------------------------------------------------------------------
    # helpers
    # ------------------------------------------------------------------
    def _score(self, what, got, exp):
        self.checks += 1
        if got != exp:
            self.mismatches += 1
            if self.mismatches <= 40:
                self.log.error(f"CHECK FAIL: {what}: got {got!r} "
                               f"expected {exp!r}")

    def _scenario(self, name):
        self.scenarios[name] = {'checks': self.checks,
                                'mismatches': self.mismatches}

    def _line_of(self, addr):
        return (addr >> self.OFFSET_BITS) & self.LINE_MASK

    def _base_of(self, line):
        return (line & self.LINE_MASK) << self.OFFSET_BITS

    def _set_of_line(self, line):
        return line & self.SET_MASK

    def _compose_addr(self, tag, set_idx, beat=0):
        line = (tag << (self.SET_BITS + self.OFFSET_BITS)) \
            | ((set_idx & self.SET_MASK) << self.OFFSET_BITS)
        return line \
            | ((beat & (self.FILL_BEATS - 1)) << (self.STRB_W.bit_length() - 1))

    def _dtag(self):
        self._tag_next += 1
        if self._tag_next > self.MAX_TAG:
            raise RuntimeError("directed scenario tag budget exhausted")
        return self._tag_next

    def _default_line(self, line):
        return bytearray(((line + 0x11 * i) & 0xFF)
                         for i in range(self.LINE_BYTES))

    def _mem_line(self, line):
        return bytes(self.mem[line])

    def _beat_of_line(self, line_data, beat):
        lo = beat * self.STRB_W
        return int.from_bytes(bytes(line_data[lo:lo + self.STRB_W]), 'little')

    def _hit_way(self, side, set_idx, line):
        for w in range(self.WAYS):
            if (side.tags.get((set_idx, w)) == line
                    and side.slot_state.get((set_idx, w), 'I') != 'I'):
                return w
        return None

    def _installed_state(self, side, line):
        s = self._set_of_line(line)
        for w in range(self.WAYS):
            if (side.tags.get((s, w)) == line
                    and side.slot_state.get((s, w), 'I') != 'I'):
                return side.slot_state[(s, w)]
        return 'I'

    def _content(self, side, line):
        """The cache-resident line content: tracked independently of the
        memory model (the fill source + every merge, in order).  Only
        meaningful for a resident (or WB-held) line."""
        return bytes(side.cache_data.get(line, self._mem_line(line)))

    def _merge_into(self, data, beat, be, wdata):
        lo = beat * self.STRB_W
        for i in range(self.STRB_W):
            if be & (1 << i):
                data[lo + i] = (wdata >> (8 * i)) & 0xFF

    def _claimed(self, side, set_idx, way):
        """A live MSHR entry claims (set, way): a tag hit there is the
        doomed victim's stale tag (the Invalid row, amber's rule)."""
        for e in side.entries.values():
            if e['set'] == set_idx and e['way'] == way:
                return True
        return False

    def _jet(self, c):
        return getattr(self.dut, f'u_jet{c}')

    async def _negedge_settled(self):
        await FallingEdge(self.dut.clk)
        await Timer(100, units='ps')

    # ------------------------------------------------------------------
    # setup: clocks, BFMs, memory backdoor, reset
    # ------------------------------------------------------------------
    async def setup_clocks_and_reset(self, period_ns=10):
        await self.start_clock('clk', freq=period_ns, units='ns')
        d = self.dut

        req_fields = FieldConfig.from_dict(
            field_dict={'data': {'bits': self.CPU_REQ_W, 'default': 0}},
            lsb_first=True)
        rsp_fields = FieldConfig.from_dict(
            field_dict={'data': {'bits': self.BUS_WIDTH, 'default': 0}},
            lsb_first=True)

        zero_delay = FlexRandomizer({'valid_delay': ([(0, 0)], [1])})
        soak_delay = FlexRandomizer(
            {'valid_delay': ([(0, 0), (1, 3), (4, 10)], [6, 3, 1])})

        self.masters = []
        self.slaves = []
        for c in range(2):
            m = GAXIMaster(
                dut=d, title=f'cpu{c}_req', prefix='',
                clock=d.clk, field_config=req_fields,
                timeout_cycles=self.RSP_TIMEOUT_CYCLES,
                mode='skid', bus_name=f'cpu{c}_req_wr', pkt_prefix='',
                multi_sig=False,
                randomizer=soak_delay if self.TEST_LEVEL == 'full'
                else zero_delay,
                log=self.log)
            s = GAXISlave(
                dut=d, title=f'cpu{c}_rsp', prefix='',
                clock=d.clk, field_config=rsp_fields,
                timeout_cycles=self.RSP_TIMEOUT_CYCLES,
                mode='skid', bus_name=f'cpu{c}_rsp_rd', pkt_prefix='',
                multi_sig=False,
                randomizer=FlexRandomizer({'ready_delay': ([(0, 0)], [1])}),
                log=self.log)
            s.add_callback(self._on_rsp_factory(c))
            s.set_ready_policy('always')
            self.masters.append(m)
            self.slaves.append(s)

        # memory model + sdpram backdoor share the same initial content
        for line in range(self.SPAN):
            self.mem[line] = self._default_line(line)
        mem_words = self.dut.u_mem.u_core.r_mem
        for line in range(self.SPAN):
            base_word = (self._base_of(line) >> (self.STRB_W.bit_length() - 1))
            for b in range(self.FILL_BEATS):
                mem_words[base_word + b].value = self._beat_of_line(
                    self.mem[line], b)

        d.mon0_ready.value = 1
        d.mon1_ready.value = 1

        await self.assert_reset()
        cocotb.start_soon(self._monitor())
        await self.wait_clocks('clk', 3)
        await self.deassert_reset()

    def _on_rsp_factory(self, c):
        def _on_rsp(packet):
            data = int(getattr(packet, 'fields', {}).get('data', 0))
            self.rsp_log[c].append((self.cyc, data))
        return _on_rsp

    async def assert_reset(self):
        self.dut.rst_n.value = 0

    async def deassert_reset(self):
        self.dut.rst_n.value = 1

    # ------------------------------------------------------------------
    # monitor: per-cycle observation of both caches + the fabric.
    # Per-cache event order mirrors JetCoreTB (allocs are visible to a
    # same-cycle snoop grant -- the alloc-first rule; the snoop resolution
    # sees the AR state BEFORE this cycle's handshake -- the pre-AR rule).
    # ------------------------------------------------------------------
    async def _monitor(self):
        d = self.dut
        while True:
            await FallingEdge(d.clk)
            await Timer(100, units='ps')
            self.cyc += 1

            fab_state = int(d.u_fabric.dbg_state.value)
            if fab_state != self._prev_fab_state:
                self._on_fab_state(fab_state)
                self._prev_fab_state = fab_state

            for c in range(2):
                a = self._jet(c)
                uc = a.u_control
                side = self.sides[c]

                # 0. coh sideband (the fabric request/WB pulse)
                if int(a.coh_req_valid.value):
                    self._on_coh_req(c, int(a.coh_req_addr.value),
                                     int(a.coh_req_type.value))

                # 1. lookup-stage accept
                if int(uc.lkup_valid_i.value) and int(uc.lkup_ready_o.value):
                    self._mon_accept(c, uc)

                # 2. MSHR alloc (before the snoop resolution: alloc-first)
                if int(uc.mshr_alloc_o.value) and int(uc.mshr_alloc_gnt_i.value):
                    self._mon_alloc(c, uc)

                # 3. snoop grant: oracle resolution in the RTL's match order
                if int(a.u_snoop.ctrl_snoop_req.value) \
                        and int(uc.sn_ready_o.value):
                    self._mon_snoop_grant(c, a, uc)

                # 4. fill beats (register at the cycle's end -- a grant
                #    sees only prior beats, PF_GUARD)
                if int(uc.fill_beat_valid_i.value):
                    self._mon_fill_beat(c, a, uc)

                # 5. fill_done: oldest un-done launch completes
                if int(uc.fill_done_i.value):
                    self._mon_fill_done(c, uc)

                # 6. fill launch accept: the windowed property + the
                #    engine's outstanding-AR identity
                if int(uc.fill_start_o.value) and int(uc.fill_accept_i.value):
                    self._mon_launch(c, uc)

                # 7. tag writes: attribution by the commit/snoop FSM taps
                if int(uc.tag_a_wr_en_o.value):
                    self._mon_tag_wr(c, uc, int(a.init_busy.value))

                # 8. drains: the mem model update at the start pulse, the
                #    payload audit at done
                if int(uc.drain_start_o.value):
                    self._mon_drain_start(c, a)
                if int(uc.drain_done_i.value):
                    self._mon_drain_done(c)

                # 9. entry retire
                if int(uc.mshr_retire_o.value):
                    self._mon_retire(c, uc)

                # 10. AR handshake observation (AFTER the snoop grant: a
                #     grant in the AR-handshake cycle still sees pre-AR)
                if int(getattr(d, f'm{c}_arvalid').value) \
                        and int(getattr(d, f'm{c}_arready').value):
                    self._mon_ar_accept(c)

                # 11. ACE channel observation (compliance + fabric scoring)
                self._on_ace_channels(c)

                # 12. response release: pop the issue-order head (J4)
                if int(getattr(d, f'cpu{c}_rsp_rd_valid').value) \
                        and int(getattr(d, f'cpu{c}_rsp_rd_ready').value):
                    self._mon_response(c)

                # 13. MonBus packet counting (present-vs-absent only)
                if int(getattr(d, f'mon{c}_valid').value) \
                        and int(getattr(d, f'mon{c}_ready').value):
                    self._mon_pkts[c] += 1

            # memory-side AR observation (suppression counting)
            if int(d.u_fabric.mem_arvalid.value) \
                    and int(d.u_fabric.mem_arready.value):
                self.stats['mem_ar'] += 1
                self.events.append((self.cyc, 'mem_ar',
                                    int(d.u_fabric.mem_araddr.value)))

    # ------------------------------------------------------------------
    # per-cache monitor handlers
    # ------------------------------------------------------------------
    def _mon_accept(self, c, uc):
        side = self.sides[c]
        addr = int(uc.lkup_addr_i.value)
        we = int(uc.lkup_we_i.value)
        be = int(uc.lkup_be_i.value)
        wdata = int(uc.lkup_wdata_i.value)
        line = self._line_of(addr)
        beat = (addr >> (self.STRB_W.bit_length() - 1)) & (self.FILL_BEATS - 1)
        set_idx = self._set_of_line(line)

        rsp = {'line': line, 'we': we, 'exp': None, 'ready': False}
        side.rspq.append(rsp)
        side.txns += 1

        if int(uc.lkup_hit_o.value):
            # hit: the data is captured at the accept
            way = self._hit_way(side, set_idx, line)
            if we:
                rsp['exp'] = wdata
                rsp['ready'] = True
                if self._hit_updates_repl and int(uc.repl_hit_o.value):
                    side.lru.update(set_idx, int(uc.repl_hit_way_o.value))
                st = side.slot_state.get((set_idx, way), 'I') \
                    if way is not None else 'I'
                if st == 'E':
                    # the E->M promotion tag write lands this cycle
                    side.promo = (line, set_idx, way)
                # the write merges into the array at the accept
                self._merge_into(side.cache_data[line], beat, be, wdata)
            else:
                rsp['exp'] = self._beat_of_line(self._content(side, line),
                                                beat)
                rsp['ready'] = True
                if self._hit_updates_repl and int(uc.repl_hit_o.value):
                    side.lru.update(set_idx, int(uc.repl_hit_way_o.value))
        elif int(uc.lkup_upgrade_o.value):
            # S->M upgrade: the write is held in the tracker (it merges
            # only at the CU commit); the response echoes
            side.upgr = {'valid': True, 'line': line, 'set': set_idx,
                         'way': self._hit_way(side, set_idx, line),
                         'beat': beat, 'be': be, 'wdata': wdata,
                         'killed': False}
            rsp['exp'] = wdata
            rsp['ready'] = True
            if self._hit_updates_repl and int(uc.repl_hit_o.value):
                side.lru.update(set_idx, int(uc.repl_hit_way_o.value))
        elif int(uc.lkup_merge_o.value):
            # a join onto an in-flight fill: the slot rides to the commit
            e = side.entries[line]
            slot = {'we': we, 'beat': beat, 'be': be, 'wdata': wdata,
                    'rsp': rsp}
            e['slots'].append(slot)
            if we:
                rsp['exp'] = wdata
                rsp['ready'] = True
        elif int(uc.lkup_miss_alloc_o.value):
            # the alloc handler (next step, same cycle) creates the entry;
            # a write's response echoes its data (released at the commit
            # deposit, known now)
            if we:
                rsp['exp'] = wdata
                rsp['ready'] = True
            side.pending_slot = {'we': we, 'beat': beat, 'be': be,
                                 'wdata': wdata, 'rsp': rsp}
        else:
            self._score(f"accept{c}: unclassified accept "
                        f"(line={line:#x})", 1, 0)

    def _mon_alloc(self, c, uc):
        side = self.sides[c]
        line = int(uc.mshr_alloc_line_o.value) & self.LINE_MASK
        set_idx = int(uc.mshr_alloc_set_o.value)
        cls = int(uc.mshr_alloc_cls_o.value)
        way = int(uc.mshr_alloc_victim_way_o.value)
        wb_valid = int(uc.mshr_alloc_wb_valid_o.value)
        idx = int(uc.mshr_alloc_idx_i.value)

        # victim-way parity with the repl engine, then the update-at-alloc
        self._score(f"alloc{c} victim way line={line:#x}", way,
                    side.lru.victim(set_idx))
        side.lru.update(set_idx, way)

        # the victim leaves the cache domain now (dirty: into the WB
        # buffer with a content snapshot; clean: silently).  The
        # BUG-001/002 pre-install-valid guard: only a VALID slot's line is
        # genuinely evicted.
        vline = side.tags.get((set_idx, way))
        vstate = side.slot_state.get((set_idx, way), 'I')
        if vline is not None and vstate != 'I' and vline != line:
            self._score(f"alloc{c} wb_valid line={line:#x}", wb_valid,
                        1 if vstate == 'M' else 0)
            if vstate == 'M':
                side.wb[vline] = self._content(side, vline)
                side.wb_order.append(vline)
            side.cache_data.pop(vline, None)

        slot = side.pending_slot
        side.pending_slot = None
        if slot is None:
            self._score(f"alloc{c}: no pending requester slot", 1, 0)
            slot = {'we': 0, 'beat': 0, 'be': 0, 'wdata': 0, 'rsp': None}
        e = {'line': line, 'set': set_idx, 'cls': cls, 'way': way,
             'idx': idx, 'pend': None, 'beats': set(), 'done': False,
             'ar': False, 'src': None, 'slots': [slot],
             'alloc_cyc': self.cyc, 'launch_cyc': None}
        side.entries[line] = e
        side.entry_by_idx[idx] = line
        side.unlaunched.append(e)

    def _mon_snoop_grant(self, c, a, uc):
        """A fabric snoop is granted inside cache c: resolve it against the
        model in the RTL's match order (WB snarf > MSHR pending fill --
        with the Task-9 pre-AR rule -- > in-flight upgrade > array), score
        the grant-cycle CRRESP, and record the fabric transaction's actual
        resolution (the fabric is serial: the in-flight transaction always
        targets this cache)."""
        side = self.sides[c]
        addr = int(uc.sn_addr_i.value)
        line = self._line_of(addr)
        name = NAME_BY_CODE[int(uc.sn_type_i.value)]
        got_crresp = int(uc.sn_crresp_o.value)
        side.snoops += 1

        cd = None
        pre_ar = False
        if line in side.wb:
            # WB snarf: the buffer owns the line until the WB ack --
            # answered at M (SINK_WB_ACK) from the capture snapshot
            res = oracle_step('M', name)
            side.wb_grants += 1
            if (res.crresp >> CRRESP_DT) & 1:
                cd = side.wb[line]
        elif line in side.entries:
            e = side.entries[line]
            if not e['ar']:
                # the Task-9 pre-AR rule: the fill's AR has not been
                # accepted (it is unlaunched, or the fabric itself holds
                # it) -- the fill's data necessarily post-dates this
                # snoop, so the answer is the Invalid row with no effect
                # and no data.  jet needs no replay: the entry's own
                # fabric transaction re-resolves at its grant.
                res = oracle_step('I', name)
                pre_ar = True
                side.pre_ar_answers += 1
            else:
                # post-AR pending fill (unreachable on the serial pair
                # fabric -- the fill's beats only flow during its own
                # transaction -- but modeled for lockstep completeness)
                side.pf_grants += 1
                if e['cls'] == JET_CLS_RU:
                    res = oracle_step('IM', name, pending=e['pend'])
                else:
                    st = 'IS_I' if e['pend'] == 'I' else 'IS'
                    res = oracle_step(st, name, fill='S',
                                      pending=None if e['pend'] == 'I'
                                      else e['pend'])
                crresp = res.crresp
                if len(e['beats']) < self.FILL_BEATS:
                    crresp &= CRRESP_NO_DT_MASK
                if e['pend'] != 'I':
                    if res.next_state == 'IS_I':
                        e['pend'] = 'I'
                    else:
                        e['pend'] = res.pending
                res = res._replace(crresp=crresp)
                if (crresp >> CRRESP_DT) & 1:
                    cd = e['src']
        elif side.upgr['valid'] and line == side.upgr['line']:
            # the in-flight upgrade's line: legitimately resident S until
            # the CU commit lands; the effect writes the tag (array hit)
            res = oracle_step('S', name)
            if res.next_state != 'S':
                side.exp_sn_tagwr.append({
                    'line': line, 'set': side.upgr['set'],
                    'way': side.upgr['way'], 'next': res.next_state})
                if res.next_state == 'I':
                    side.upgr['killed'] = True
                    side.kill_count += 1
        else:
            set_idx = self._set_of_line(line)
            way = self._hit_way(side, set_idx, line)
            ref = 'I'
            if way is not None and not self._claimed(side, set_idx, way):
                ref = side.slot_state.get((set_idx, way), 'I')
            res = oracle_step(ref, name)
            if (res.crresp >> CRRESP_DT) & 1:
                cd = self._content(side, line)
            if ref != 'I' and res.next_state != ref:
                side.exp_sn_tagwr.append({
                    'line': line, 'set': set_idx, 'way': way,
                    'next': res.next_state})

        self._score(f"snoop{c} {name} line={line:#x} crresp (grant)",
                    got_crresp, res.crresp)

        # the fabric transaction's actual resolution: this grant resolves
        # cur_ft (the granting cache IS the transaction's peer)
        if self.cur_ft is not None and c == 1 - self.cur_ft['dir']:
            self.cur_ft['resolution'] = res.crresp
            if (res.crresp >> CRRESP_DT) & 1:
                self.cur_ft['data_actual'] = cd
                if (res.crresp >> CRRESP_PD) & 1:
                    # PassDirty: the fabric absorbs the forwarded line
                    # into the shared memory (the point of coherence);
                    # the line stays resident (downgrade) or leaves
                    # (invalidate) -- its content is now in memory either
                    # way
                    self.mem[line] = bytearray(cd)
                    self.stats['absorbs'] += 1
            else:
                self.cur_ft['data_actual'] = self._mem_line(line)
            # bind the data source to the requester's entry (the fill
            # beats -- which follow the AR accept, which follows this
            # resolution -- are scored against it)
            req_side = self.sides[self.cur_ft['dir']]
            e = req_side.entries.get(self.cur_ft['line'])
            if e is not None:
                e['src'] = self.cur_ft['data_actual']

    def _mon_fill_beat(self, c, a, uc):
        side = self.sides[c]
        idx = int(uc.fill_beat_idx_i.value)
        num = int(uc.fill_beat_num_i.value)
        line = side.entry_by_idx.get(idx)
        if line is None:
            self._score(f"fill beat{c} on an unknown entry", idx, None)
            return
        e = side.entries[line]
        e['beats'].add(num)
        got = int(a.u_fill.fill_beat_data.value)
        if e['src'] is None:
            self._score(f"fill beat{c} line={line:#x} b{num}: no data "
                        f"source bound (fabric resolution missing)", 1, 0)
        else:
            self._score(f"fill beat{c} data line={line:#x} b{num}",
                        got, self._beat_of_line(e['src'], num))

    def _mon_fill_done(self, c, uc):
        side = self.sides[c]
        for item in side.launch_q:
            if not item['done']:
                item['done'] = True
                if item['kind'] == 'entry':
                    item['e']['done'] = True
                return
        self._score(f"fill_done{c} with no outstanding launch", 1, 0)

    def _mon_launch(self, c, uc):
        side = self.sides[c]
        cls = int(uc.fill_cls_o.value)
        if cls != JET_CLS_CU:
            if not side.unlaunched:
                self._score(f"fill launch{c} with no pending alloc",
                            cls, None)
                return
            e = side.unlaunched.popleft()
            e['launch_cyc'] = self.cyc
            side.launch_waits.append(self.cyc - e['alloc_cyc'])
            side.launch_count += 1
            side.launch_q.append({'kind': 'entry', 'e': e, 'done': False})
        else:
            side.cu_launches += 1
            side.launch_q.append({'kind': 'cu', 'done': False})

    def _mon_tag_wr(self, c, uc, init):
        side = self.sides[c]
        way_oh = int(uc.tag_a_wr_way_onehot_o.value)
        way = way_oh.bit_length() - 1
        set_idx = int(uc.tag_a_wr_set_o.value)
        ts = int(uc.tag_a_wr_tag_state_o.value)
        tag, state = ts >> 3, ts & 0x7
        line = ((tag << self.SET_BITS) | set_idx) & self.LINE_MASK
        cmt = int(uc.r_cmt_state.value)
        sn = int(uc.r_sn_state.value)

        if init:
            return   # the D-3 walk: every slot to I (model starts there)
        if cmt == C_INSTALL:
            # the fill commit's install write
            head = side.launch_q[0] if side.launch_q else None
            if head is None or head['kind'] != 'entry':
                self._score(f"C_INSTALL{c} with no entry at the commit "
                            f"head", 1, 0)
                return
            self._score(f"commit{c} head is done", head['done'], True)
            e = head['e']
            # no PassDirty reaches a jet fill on this fabric (the cache-
            # side RRESP is plain AXI4 2'b00): RNSD installs S, RU M
            exp_state = (AMBER_STATE_S if e['cls'] == JET_CLS_RNSD
                         else AMBER_STATE_M)
            self._score(f"install{c} tag line={e['line']:#x}", line,
                        e['line'])
            self._score(f"install{c} set line={e['line']:#x}", set_idx,
                        e['set'])
            self._score(f"install{c} way line={e['line']:#x}", way,
                        e['way'])
            self._score(f"install{c} state line={e['line']:#x}", state,
                        exp_state)
            # the eviction accounting happened at the ALLOC (the victim
            # leaves the cache domain then; cache_data popped there).
            # The slot's tag/state cannot change between the alloc and
            # this install (a snoop hit on the claimed way is the
            # stale-tag Invalid row, no effect) -- nothing to account
            # here, and re-popping by the slot's stale tag would clobber
            # the resident content of a line RE-INCARNATED (re-filled)
            # in the alloc->commit window (the Task-12 drain-payload
            # find in the core TB).
            side.tags[(e['set'], e['way'])] = e['line']
            side.slot_state[(e['set'], e['way'])] = (
                'S' if exp_state == AMBER_STATE_S else 'M')
            # the fill's requester responses: read slots capture their
            # beat at their own position (a read observes exactly the
            # merges that precede it); write slots echo
            if e['src'] is None:
                self._score(f"commit{c} line={e['line']:#x}: no data "
                            f"source bound (fabric resolution missing)",
                            1, 0)
                e['src'] = self._mem_line(e['line'])
            data = bytearray(e['src'])
            for slot in e['slots']:
                if slot['we']:
                    self._merge_into(data, slot['beat'], slot['be'],
                                     slot['wdata'])
                else:
                    rsp = slot['rsp']
                    rsp['exp'] = self._beat_of_line(data, slot['beat'])
                    rsp['ready'] = True
            # the merged content is now the resident content
            side.cache_data[e['line']] = data
            # consume the fabric transaction this fill rode on
            self._take_ft(c, e['line'])
            side.committing = e
        elif cmt == C_PEND:
            # the deferred snoop effect after the install.  On this
            # fabric a pending fill is only ever snooped pre-AR (no
            # effect), so C_PEND should not fire -- if it does, model it
            # (lockstep) and count it.
            side.pend_installs += 1
            e = side.committing
            if e is None:
                self._score(f"C_PEND{c} with no committing entry", 1, 0)
                return
            exp = 'I' if e['pend'] == 'I' else 'S'
            self._score(f"pend effect{c} line={e['line']:#x}", state,
                        STATE_CODE[exp])
            side.slot_state[(e['set'], e['way'])] = exp
            if exp == 'I':
                # the killed fill: merged write data never lands
                side.cache_data.pop(e['line'], None)
        elif cmt == C_CU_INSTALL:
            u = side.upgr
            if not u['valid']:
                self._score(f"CU install{c} with no in-flight upgrade",
                            1, 0)
                return
            exp = AMBER_STATE_I if u['killed'] else AMBER_STATE_M
            self._score(f"CU install{c} tag line={u['line']:#x}", line,
                        u['line'])
            self._score(f"CU install{c} way line={u['line']:#x}", way,
                        u['way'])
            # the Task-8 killed-upgrade pin: demote to I, never
            # resurrect M
            self._score(f"CU install{c} state line={u['line']:#x} "
                        f"(killed={u['killed']})", state, exp)
            side.slot_state[(u['set'], way)] = 'I' if u['killed'] else 'M'
            if u['killed']:
                # the held write's data drops with the invalidated line
                # (the fabric-contract demote corner)
                side.cache_data.pop(u['line'], None)
            else:
                # the held write merged at the CU commit
                self._merge_into(side.cache_data[u['line']],
                                 u['beat'], u['be'], u['wdata'])
            side.upgr = {'valid': False, 'line': None, 'set': 0, 'way': 0,
                         'killed': False}
            if side.launch_q and side.launch_q[0]['kind'] == 'cu':
                side.launch_q.popleft()
            else:
                self._score(f"CU install{c} but the commit head is not "
                            f"CU", 1, 0)
            self._take_ft(c, u['line'])
        elif sn == SN_EFFECT:
            # the deferred snoop effect on an array hit
            if not side.exp_sn_tagwr:
                self._score(f"unanticipated snoop-effect tag write{c}",
                            1, 0)
                return
            exp = side.exp_sn_tagwr.popleft()
            self._score(f"snoop effect{c} line={exp['line']:#x}", line,
                        exp['line'])
            self._score(f"snoop effect{c} way line={exp['line']:#x}",
                        way, exp['way'])
            self._score(f"snoop effect{c} state line={exp['line']:#x}",
                        state, STATE_CODE[exp['next']])
            side.slot_state[(exp['set'], way)] = exp['next']
            if exp['next'] == 'I':
                # an invalidation without a forward (e.g. MakeInvalid on
                # S, or the fabric-contract M-kill corner) drops the
                # resident content; a forwarded line's content moved to
                # the memory model at the resolution
                side.cache_data.pop(exp['line'], None)
        elif side.promo is not None:
            # the E->M promotion at a write hit
            pline, pset, pway = side.promo
            side.promo = None
            self._score(f"promotion{c} line={pline:#x}", line, pline)
            self._score(f"promotion{c} way", way, pway)
            self._score(f"promotion{c} state", state, AMBER_STATE_M)
            side.slot_state[(pset, pway)] = 'M'
        else:
            self._score(f"unattributed tag write{c} "
                        f"(line={line:#x} state={state})", 1, 0)

    def _mon_drain_start(self, c, a):
        side = self.sides[c]
        if not side.wb_order:
            self._score(f"drain_start{c} with empty WB model", 1, 0)
            return
        side.draining = side.wb_order[0]
        line = side.draining
        self._score(f"drain{c} addr is the oldest WB line",
                    int(a.u_wb.drain_addr_o.value), self._base_of(line))
        # the write-back carries the capture-time snapshot to the shared
        # memory (the model's launch-time view; the DUT's W beats land
        # before the BRESP, and no pass-through read of the line can
        # interpose -- the RAW guard and the WB snarf cover both sides)
        self.mem[line] = bytearray(side.wb[line])
        self.stats['wb_bursts'] += 1
        self.events.append((self.cyc, 'wb', c, line))

    def _mon_drain_done(self, c):
        side = self.sides[c]
        if side.draining is None:
            self._score(f"drain_done{c} with no drain in flight", 1, 0)
            return
        line = side.draining
        # the W beats landed in the sdpram before the BRESP that produced
        # this drain_done: the writeback payload round-trips through the
        # real write path
        mem_words = self.dut.u_mem.u_core.r_mem
        base_word = (self._base_of(line) >> (self.STRB_W.bit_length() - 1))
        got = bytearray()
        for b in range(self.FILL_BEATS):
            got += int(mem_words[base_word + b].value).to_bytes(
                self.STRB_W, 'little')
        self._score(f"drain{c} payload line={line:#x}", bytes(got),
                    bytes(side.wb[line]))
        del side.wb[line]
        side.wb_order.popleft()
        side.draining = None

    def _mon_retire(self, c, uc):
        side = self.sides[c]
        idx = int(uc.mshr_retire_idx_o.value)
        line = side.entry_by_idx.pop(idx, None)
        if line is None:
            self._score(f"retire{c} of an unknown entry", idx, None)
        else:
            side.entries.pop(line, None)
        if not side.launch_q or side.launch_q[0]['kind'] != 'entry':
            self._score(f"retire{c} while the commit head is not an "
                        f"entry", 1, 0)
        else:
            e = side.launch_q.popleft()['e']
            self._score(f"retire{c} matches the commit head", line,
                        e['line'])
        side.committing = None

    def _mon_ar_accept(self, c):
        """The engine's outstanding AR was accepted (by the fabric): the
        oldest un-done entry launch is no longer pre-AR."""
        side = self.sides[c]
        for item in side.launch_q:
            if not item['done'] and item['kind'] == 'entry':
                item['e']['ar'] = True
                return
        # a CU's AR (no entry): nothing to mark

    def _mon_response(self, c):
        side = self.sides[c]
        got = int(getattr(self.dut, f'cpu{c}_rsp_rd_data').value)
        if not side.rspq:
            self._score(f"unsolicited response{c}", got, None)
            return
        req = side.rspq.popleft()
        if not req['ready']:
            self._score(f"response{c} line={req['line']:#x} released "
                        f"before its commit assigned the expectation",
                        1, 0)
            return
        self._score(f"rsp{c} data line={req['line']:#x} we={req['we']}",
                    got, req['exp'])

    # ------------------------------------------------------------------
    # fabric model: coh_req pulse -> queue; grant -> transaction
    # ------------------------------------------------------------------
    def _on_coh_req(self, c, addr, req_type):
        line = self._line_of(addr)
        if req_type == ACE_WRITE_BACK:
            return   # the drain handler updates the memory model
        ctx = {'cyc': self.cyc, 'dir': c, 'line': line, 'type': req_type,
               'resolution': None, 'data_actual': None}
        self.ft_queue[c].append(ctx)
        self.events.append((self.cyc, 'coh_req', c, ctx))
        if req_type == ACE_CLEAN_UNIQUE:
            self.stats['upgrades'] += 1

    def _on_fab_state(self, st):
        d = self.dut
        if st == FAB_F_AC:
            # grant latched: the direction's QUEUE HEAD becomes the
            # transaction (the RTL pops its pending FIFO in F_IDLE)
            g = int(d.u_fabric.dbg_grant_dir.value)
            if not self.ft_queue[g]:
                self._score("fabric grant without a pending coh_req",
                            g, None)
                return
            self.cur_ft = self.ft_queue[g].pop(0)
            self.stats['grants'][g] += 1
            if len(self.stats['first_grant']) == 0 or \
                    self.stats['first_grant'][-1] != g:
                self.stats['first_grant'].append(g)
        elif st == FAB_F_DONE:
            if self.cur_ft is not None:
                if self.cur_ft['resolution'] is not None \
                        and (self.cur_ft['resolution'] >> CRRESP_DT) & 1:
                    self.stats['dt_forwards'] += 1
                else:
                    self.stats['pass_throughs'] += 1
                self.cur_ft = None

    def _take_ft(self, c, line):
        """The fabric transaction for this line must have completed
        (F_DONE precedes the commit by construction); jet has no killed
        passes, so there is nothing to discard."""
        return None

    def _on_ace_channels(self, c):
        """Observe the fabric<->cache c ACE responder channels: AC
        handshakes (score the fabric's kill decision + snoop type against
        the queue model), CD beats, CR handshakes (score CRRESP + beat
        count against the recorded resolution), and feed the per-cache
        compliance checker (the onyx D7 subset: CR only after CDLAST,
        check_cr_order per transaction)."""
        d = self.dut
        acvalid = int(getattr(d, f's{c}_acvalid').value)
        acready = int(getattr(d, f's{c}_acready').value)
        cdvalid = int(getattr(d, f's{c}_cdvalid').value)
        cdready = int(getattr(d, f's{c}_cdready').value)
        crvalid = int(getattr(d, f's{c}_crvalid').value)
        crready = int(getattr(d, f's{c}_crready').value)

        # AC handshake: the fabric launches a snoop on this cache
        if acvalid and acready:
            snoop = int(getattr(d, f's{c}_acsnoop').value)
            acaddr = int(getattr(d, f's{c}_acaddr').value)
            self._cur_snoop_type[c] = FRAMEWORK_SNOOPS.get(
                SNOOP_NAME_BY_FAB.get(snoop))
            if self.cur_ft is not None and self.cur_ft['dir'] != c:
                ft = self.cur_ft
                # the kill rule: a same-line TRUE MISS sits in the peer's
                # queue (or pulses this very cycle) -- on jet that fill
                # is always pre-AR (the fabric holds its AR), so the kill
                # and the normal map produce the same I-row answer
                live = [e for e in self.ft_queue[c]
                        if e['type'] in TRUE_MISS_TYPES]
                raw_v = int(self._jet(c).coh_req_valid.value)
                raw_t = int(self._jet(c).coh_req_type.value)
                if raw_v and raw_t in TRUE_MISS_TYPES:
                    live.append({'line': self._line_of(
                        int(self._jet(c).coh_req_addr.value))})
                kill_pred = any(e['line'] == ft['line'] for e in live)
                rtl_kill = bool(int(d.u_fabric.dbg_kill.value))
                if ft['type'] == ACE_CLEAN_UNIQUE:
                    # CU maps to MakeInvalid by construction; the kill
                    # bit is don't-care
                    exp_snoop = FAB_SNOOP_MI
                else:
                    if rtl_kill != kill_pred:
                        self.stats['kill_pred_bad'] += 1
                    else:
                        self.stats['kill_pred_ok'] += 1
                    if kill_pred:
                        self.stats['kills'] += 1
                    exp_snoop = FAB_SNOOP_MI if kill_pred \
                        else FAB_SNOOP_BY_TYPE[ft['type']]
                self._score(f"ft{ft['cyc']}: acsnoop", snoop, exp_snoop)
                self._score(f"ft{ft['cyc']}: acaddr line-aligned",
                            acaddr & (self.LINE_BYTES - 1), 0)
                self._score(f"ft{ft['cyc']}: acaddr", acaddr,
                            self._base_of(ft['line']))
        # CD beats (count; content is scored via the requester's fill)
        if cdvalid and cdready:
            self._cd_beats[c] += 1
            if not self._cd_started[c]:
                self._cd_started[c] = True
                res = self.cur_ft.get('resolution') \
                    if self.cur_ft is not None else None
                if res is not None and (res >> CRRESP_DT) & 1:
                    self.ace_checkers[c].set_expected_cd_beats(
                        self.FILL_BEATS)
            last = int(getattr(d, f's{c}_cdlast').value)
            self.ace_checkers[c].check_cd_order(
                self._cd_seq[c], last,
                self._base_of(self.cur_ft['line'])
                if self.cur_ft is not None else 0,
                self._cur_snoop_type[c])
            if last:
                self._cd_seq[c] += 1
                self._cd_started[c] = False
        # CR handshake: score against the recorded resolution
        if crvalid and crready:
            crresp = int(getattr(d, f's{c}_crresp').value)
            if self.cur_ft is not None and self.cur_ft['dir'] != c:
                res = self.cur_ft.get('resolution')
                self._score(f"ft{self.cur_ft['cyc']}: crresp", crresp,
                            res)
                exp_beats = self.FILL_BEATS \
                    if res is not None and (res >> CRRESP_DT) & 1 else 0
                self._score(f"ft{self.cur_ft['cyc']}: cd beats",
                            self._cd_beats[c], exp_beats)
            self.ace_checkers[c].check_cr_order(
                self._ace_seq[c],
                self._base_of(self.cur_ft['line'])
                if self.cur_ft is not None else 0,
                self._cur_snoop_type[c])
            if self._cur_snoop_type[c] is not None:
                self.ace_checkers[c].check_crresp_validity(
                    CRRESP(crresp), self._cur_snoop_type[c],
                    self._base_of(self.cur_ft['line'])
                    if self.cur_ft is not None else 0)
            self._ace_seq[c] += 1
            self._cd_beats[c] = 0

    # ------------------------------------------------------------------
    # transaction drivers
    # ------------------------------------------------------------------
    def _pack_req(self, addr, we, be, wdata):
        return ((addr & ((1 << self.ADDR_WIDTH) - 1))
                << (1 + self.STRB_W + self.BUS_WIDTH)) \
            | ((we & 1) << (self.STRB_W + self.BUS_WIDTH)) \
            | ((be & ((1 << self.STRB_W) - 1)) << self.BUS_WIDTH) \
            | (wdata & ((1 << self.BUS_WIDTH) - 1))

    async def _send(self, c, addr, we, be=None, wdata=None, label=''):
        """Issue one request on cache c's CPU port; returns its response
        ordinal (send order == accept order == release order, J4)."""
        if be is None:
            be = random.randrange(1, 1 << self.STRB_W) if we \
                else (1 << self.STRB_W) - 1
        if wdata is None:
            wdata = random.getrandbits(self.BUS_WIDTH) if we else 0
        n = self.send_count[c]
        pkt = self.masters[c].create_packet(data=self._pack_req(
            addr, we, be, wdata))
        await self.masters[c].send(pkt)
        self.send_count[c] += 1
        return n

    async def _await_rsp(self, c, n, label=''):
        for _ in range(self.RSP_TIMEOUT_CYCLES):
            if len(self.rsp_log[c]) > n:
                return self.rsp_log[c][n]
            await self._negedge_settled()
        # hang trace before raising: the fabric + both caches' key state
        d = self.dut
        f = d.u_fabric
        for _ in range(10):
            await self._negedge_settled()
            self.log.info(
                f"HANG c{self.cyc} fstate {int(f.dbg_state.value)} "
                f"pend {int(f.dbg_pend_vld.value):02b} "
                f"buf {int(f.dbg_buf_vld.value):02b} "
                f"absp {int(f.dbg_abs_pend.value):02b} "
                f"c0st {int(self._jet(0).ctrl_state.value):x} "
                f"c1st {int(self._jet(1).ctrl_state.value):x} "
                f"c0ar {int(d.m0_arvalid.value)}{int(d.m0_arready.value)} "
                f"c1ar {int(d.m1_arvalid.value)}{int(d.m1_arready.value)} "
                f"c0aw {int(d.m0_awvalid.value)}{int(d.m0_awready.value)} "
                f"c1aw {int(d.m1_awvalid.value)}{int(d.m1_awready.value)} "
                f"s0ac {int(d.s0_acvalid.value)}{int(d.s0_acready.value)} "
                f"s1ac {int(d.s1_acvalid.value)}{int(d.s1_acready.value)} "
                f"c0rspq {len(self.sides[0].rspq)} "
                f"c1rspq {len(self.sides[1].rspq)} "
                f"c0entries {list(self.sides[0].entries.keys())} "
                f"c1entries {list(self.sides[1].entries.keys())} "
                f"c0wb {list(self.sides[0].wb.keys())} "
                f"c1wb {list(self.sides[1].wb.keys())}")
        raise RuntimeError(
            f"{label}: response {n} on cache{c} timeout; "
            f"ctrl_state={int(self._jet(c).ctrl_state.value):#x} "
            f"fab={int(self.dut.u_fabric.dbg_state.value):#x}")

    async def _txn(self, c, addr, we, be=None, wdata=None, label=''):
        n = await self._send(c, addr, we, be, wdata, label)
        return await self._await_rsp(c, n, label)

    # ------------------------------------------------------------------
    # directed scenarios
    # ------------------------------------------------------------------
    async def _s_init_walk(self):
        d = self.dut

        async def _walk_wait(c):
            cycles = 0
            saw_busy = False
            # a REAL request presented mid-walk: jet's GAXI boundary admits
            # it into the D-6 request skid (ready stays high), but the
            # lookup stage must never accept it before the walk completes
            # (MAS ch03 option 1 -- the jet_core InitWalk contract)
            addr = self._compose_addr(0, 0)
            send_task = cocotb.start_soon(self._send(
                c, addr, 0, be=(1 << self.STRB_W) - 1, wdata=0,
                label=f'init{c}'))
            while True:
                await self._negedge_settled()
                cycles += 1
                if cycles > self.SETS * 4 + 400:
                    raise RuntimeError(f"init walk never completed "
                                       f"(cache{c})")
                busy = int(self._jet(c).init_busy.value)
                if busy:
                    saw_busy = True
                    uc = self._jet(c).u_control
                    self._score(
                        f"init{c}: no lookup-stage accept during the walk",
                        int(uc.lkup_valid_i.value)
                        & int(uc.lkup_ready_o.value), 0)
                else:
                    break
            await send_task
            self._score(f"init{c}: walk observed", saw_busy, True)
            await self._await_rsp(c, 0, f'init{c}')

        # both caches walk concurrently after the shared reset release
        waits = [cocotb.start_soon(_walk_wait(c)) for c in range(2)]
        for w in waits:
            await w
        self._scenario('InitWalk')

    async def _s_pass_dirty_forwarding(self):
        """(a) M -> remote-fill PassDirty forwarding; stale memory behind."""
        sset = 1 % self.SETS
        t0 = self._dtag()
        addr = self._compose_addr(t0, sset)
        line = self._line_of(addr)
        # cache1 write miss -> fill from memory, merge, M
        wdata = 0x5A5A_5A5A_5A5A_5A5A & ((1 << self.BUS_WIDTH) - 1)
        await self._txn(1, addr, 1, be=(1 << self.STRB_W) - 1,
                        wdata=wdata, label='a_wr')
        s1 = self.sides[1]
        self._score("a: cache1 line M",
                    self._installed_state(s1, line), 'M')
        # poison the shared memory for this line (byte-distinct stale data)
        stale = bytearray(((0xC3 + i) & 0xFF) for i in range(self.LINE_BYTES))
        self.mem[line] = bytearray(stale)
        mem_words = self.dut.u_mem.u_core.r_mem
        base_word = (self._base_of(line) >> (self.STRB_W.bit_length() - 1))
        for b in range(self.FILL_BEATS):
            mem_words[base_word + b].value = self._beat_of_line(stale, b)

        # cache0 read miss: fill MUST come from cache1's CD, not memory
        ar_count0 = self.stats['mem_ar']
        await self._txn(0, addr, 0, label='a_rd')
        s0 = self.sides[0]
        exp = self._beat_of_line(self._content(s1, line), 0)
        got = self.rsp_log[0][-1][1]
        self._score("a: cache0 got peer bytes, not stale memory",
                    got, exp)
        self._score("a: memory AR suppressed for the fill",
                    self.stats['mem_ar'], ar_count0)
        self._score("a: cache0 installed S",
                    self._installed_state(s0, line), 'S')
        self._score("a: cache1 downgraded S",
                    self._installed_state(s1, line), 'S')
        # both copies agree
        self._score("a: cache0 content == cache1 content",
                    self._content(s0, line), self._content(s1, line))
        # absorption: the memory model now shows cache1's bytes
        self._score("a: memory absorbed the dirty line",
                    bytes(self.mem[line]), self._content(s1, line))
        # cache1 still hits with the merged content
        await self._txn(1, addr, 0, label='a_rb1')
        got = self.rsp_log[1][-1][1]
        self._score("a: cache1 hit data kept", got, exp)
        self._scenario('PassDirtyForwarding')

    async def _s_upgrade_invalidates_peer(self):
        """(b) S->M upgrade invalidates the peer; peer re-read forwards."""
        sset = 2 % self.SETS
        t0 = self._dtag()
        addr = self._compose_addr(t0, sset)
        line = self._line_of(addr)
        await self._txn(0, addr, 0, label='b_r0')   # cache0 S
        await self._txn(1, addr, 0, label='b_r1')   # cache1 S (pass-through)
        self._score("b: both S", (self._installed_state(self.sides[0], line),
                                  self._installed_state(self.sides[1], line)),
                    ('S', 'S'))
        # cache0 upgrades (CLEAN_UNIQUE): fabric MakeInvalids cache1
        await self._txn(0, addr, 1, be=0xF,
                        wdata=0x00C0_FF00_0000_0000
                        & ((1 << self.BUS_WIDTH) - 1), label='b_up')
        self._score("b: cache0 M",
                    self._installed_state(self.sides[0], line), 'M')
        self._score("b: peer invalidated",
                    self._installed_state(self.sides[1], line), 'I')
        # peer read now misses and the fabric forwards cache0's merge
        await self._txn(1, addr, 0, label='b_rdp')
        exp = self._beat_of_line(self._content(self.sides[0], line), 0)
        got = self.rsp_log[1][-1][1]
        self._score("b: peer read got cache0's merge", got, exp)
        self._score("b: peer installed S",
                    self._installed_state(self.sides[1], line), 'S')
        self._score("b: cache0 downgraded after forward",
                    self._installed_state(self.sides[0], line), 'S')
        self._score("b: memory absorbed",
                    bytes(self.mem[line]),
                    self._content(self.sides[0], line))
        self._scenario('UpgradeInvalidatesPeer')

    async def _s_dirty_eviction_writeback(self):
        """(c) dirty eviction WriteBack visible to memory AND peers."""
        sset = 3 % self.SETS
        t0 = self._dtag()
        addr = self._compose_addr(t0, sset)
        line = self._line_of(addr)
        wdata = 0xDEAD_0000_0000_BEEF & ((1 << self.BUS_WIDTH) - 1)
        await self._txn(0, addr, 1, be=(1 << self.STRB_W) - 1,
                        wdata=wdata, label='c_wr')
        s0 = self.sides[0]
        self._score("c: cache0 M", self._installed_state(s0, line), 'M')
        # fill the whole set to evict the dirty line
        vtags = [self._dtag() for _ in range(self.WAYS)]
        for w, tag in enumerate(vtags):
            a = self._compose_addr(tag, sset)
            await self._txn(0, a, 0, label=f'c_f{w}')
        self._score("c: line evicted",
                    self._installed_state(s0, line), 'I')
        # memory model carries the write-back; the actual sdpram must too
        exp_line = bytes(self.mem[line])
        # peer reads the line: miss, peer Invalid -> memory read of the WB
        await self._txn(1, addr, 0, label='c_peer')
        got = self.rsp_log[1][-1][1]
        self._score("c: peer sees the write-back", got,
                    self._beat_of_line(exp_line, 0))
        self._scenario('DirtyEvictionWriteback')

    async def _s_e_downgrade_read_shared(self):
        """(d) E->S downgrade on ReadShared (tag promotion backdoor)."""
        sset = 4 % self.SETS
        t0 = self._dtag()
        addr = self._compose_addr(t0, sset)
        line = self._line_of(addr)
        await self._txn(0, addr, 0, label='d_r0')
        s0 = self.sides[0]
        self._score("d: cache0 S", self._installed_state(s0, line), 'S')
        # promote cache0's tag word S -> E (quiescent deposit; the CPU
        # path never installs E -- the documented reachability gap)
        set_idx = self._set_of_line(line)
        way = self._hit_way(s0, set_idx, line)
        tag_word = self.dut.u_jet0.u_tag.mem[way * self.SETS + set_idx]
        tag_word.value = ((line >> self.SET_BITS) << 3) | 2   # 2 = E
        s0.slot_state[(set_idx, way)] = 'E'
        # cache1 misses the line: fabric READ_SHARED snoop hits E
        await self._txn(1, addr, 0, label='d_r1')
        exp = self._beat_of_line(self._content(s0, line), 0)
        got = self.rsp_log[1][-1][1]
        self._score("d: cache1 got E line data", got, exp)
        # E x READ_SHARED: DT+IS+WU; the peer downgrades to S
        rd_ts = int(tag_word.value)
        self._score("d: cache0 downgraded E->S", rd_ts & 7,
                    STATE_CODE['S'])
        s0.slot_state[(set_idx, way)] = 'S'
        self._score("d: cache1 installed S",
                    self._installed_state(self.sides[1], line), 'S')
        self._scenario('EDowngradeReadShared')

    async def _s_simultaneous_misses(self):
        """(e) simultaneous same-line misses serialize fairly, both
        correct.  With jet the loser's pre-AR fill answers the snoop at
        the Invalid row (no kill, no replay): its own grant then
        re-resolves against the winner's committed line.  Writes go to
        distinct beats so the final line provably carries BOTH stores."""
        sset = 5 % self.SETS
        n_start = len(self.stats['first_grant'])
        mixes = [(0, 0), (1, 1), (0, 1), (1, 0), (0, 0), (1, 1), (0, 1),
                 (1, 0)]
        full_be = (1 << self.STRB_W) - 1
        for it, (w0, w1) in enumerate(mixes):
            t0 = self._dtag()
            line_base = (t0 << (self.SET_BITS + self.OFFSET_BITS)) \
                | ((sset & self.SET_MASK) << self.OFFSET_BITS)
            line = self._line_of(line_base)
            # per-CPU beat + data (distinct beats for write/write)
            a0 = line_base + (0 % self.FILL_BEATS) * self.STRB_W
            a1 = line_base + (1 % self.FILL_BEATS) * self.STRB_W
            d0 = 0xAAAA_0000_0000_0000 | (it + 1)
            d1 = 0xBBBB_0000_0000_0000 | (it + 1)
            tasks = []
            for c, we, a, wd in ((0, w0, a0, d0), (1, w1, a1, d1)):
                tasks.append(cocotb.start_soon(self._txn(
                    c, a, we, be=full_be, wdata=wd,
                    label=f'e{it}_c{c}')))
            for t in tasks:
                await t
            # quiesce the fabric between iterations
            for _ in range(4):
                await self._negedge_settled()
            st0 = self._installed_state(self.sides[0], line)
            st1 = self._installed_state(self.sides[1], line)
            if w0 and w1:
                # exactly one owner (M) holding BOTH stores
                owners = [c for c, s in enumerate((st0, st1)) if s == 'M']
                self._score(f"e{it}: write/write exactly one owner",
                            len(owners), 1)
                if owners:
                    oc = self.sides[owners[0]]
                    content = self._content(oc, line)
                    self._score(f"e{it}: owner holds c0's store",
                                self._beat_of_line(
                                    content, 0 % self.FILL_BEATS), d0)
                    self._score(f"e{it}: owner holds c1's store",
                                self._beat_of_line(
                                    content, 1 % self.FILL_BEATS), d1)
            elif w0 or w1:
                # write granted first: both end S (the read forwarded
                # with PD); read granted first: writer M, reader I
                wc = 0 if w0 else 1
                rc = 1 - wc
                wst, rst = (st0, st1)[wc], (st0, st1)[rc]
                ok = ((wst == 'M' and rst == 'I')
                      or (wst == 'S' and rst == 'S'))
                self._score(f"e{it}: mixed outcome coherent "
                            f"(w={wst} r={rst})", ok, True)
            else:
                self._score(f"e{it}: read/read both S", (st0, st1),
                            ('S', 'S'))
        # Fairness audit: the fabric round-robin must serve both caches
        # first across the window.
        win = self.stats['first_grant'][n_start:]
        fair = (len(win) >= 2 and set(win) == {0, 1})
        self._score("e: fabric grants cover both caches", fair, True)
        self._score("e: grants happened",
                    sum(self.stats['grants']) >= 2, True)
        self._scenario('SimultaneousSameLineMisses')

    async def _s_ships_in_the_night(self):
        """(f) jet0's pre-BRESP WriteBack + jet1's same-line read: the
        snoop must be answered from the WB buffer snapshot (the entry may
        retire mid-stream in its BRESP cycle), never "not present".

        Construction: fill all but one way, then drive the evicting fill
        and jet1's read back-to-back (read fired 2 cycles later).  The
        evicting fill's launch is held by the victim capture (the
        launch-level cap_busy contract), so its coh pulse reaches the
        fabric AFTER jet1's -- the fabric grants jet1 first, and jet1's
        AC waits out the capture at jet0's responder (sn_safe), granting
        with the WB entry valid and pre-BRESP.  The margin is the full
        drain length; the bounded retry covers the FULL-level
        randomizer's worst-case send skew (a miss is still coherent --
        the memory path answers -- it just isn't the WB-source pin)."""
        sset = 6 % self.SETS
        full_be = (1 << self.STRB_W) - 1
        hit = False
        for attempt in range(3):
            t0 = self._dtag()
            addr = self._compose_addr(t0, sset)
            line = self._line_of(addr)
            # jet0: write miss -> M with a recognizable pattern
            wdata = (0x5A17_0000_0000_0000 + attempt) \
                & ((1 << self.BUS_WIDTH) - 1)
            await self._txn(0, addr, 1, be=full_be, wdata=wdata,
                            label=f'f{attempt}_wr')
            s0 = self.sides[0]
            self._score(f"f{attempt}: jet0 M",
                        self._installed_state(s0, line), 'M')
            exp_line = self._content(s0, line)

            vtags = [self._dtag() for _ in range(self.WAYS)]
            wb_grants0 = s0.wb_grants
            for w, tag in enumerate(vtags[:-1]):
                await self._txn(0, self._compose_addr(tag, sset), 0,
                                label=f'f{attempt}_ev{w}')
            # the evicting fill (its alloc opens the dirty capture) ...
            ev_n = await self._send(0, self._compose_addr(vtags[-1], sset),
                                    0, be=full_be, wdata=0,
                                    label=f'f{attempt}_evL')
            # ... and jet1's read two cycles behind it
            for _ in range(2):
                await self._negedge_settled()
            rd_n = await self._send(1, addr, 0, label=f'f{attempt}_rd')
            await self._await_rsp(1, rd_n, f'f{attempt}_rd')
            await self._await_rsp(0, ev_n, f'f{attempt}_evL')

            got = self.rsp_log[1][rd_n][1]
            self._score(f"f{attempt}: jet1 got the dirty line's data",
                        got, self._beat_of_line(exp_line, 0))
            self._score(f"f{attempt}: jet1 installed S",
                        self._installed_state(self.sides[1], line), 'S')
            self._score(f"f{attempt}: jet0 line evicted",
                        self._installed_state(s0, line), 'I')
            # quiesce, then the memory must hold the dirty bytes (the
            # drain AND, on a snarf hit, the absorption carry the same
            # snapshot)
            for _ in range(60):
                await self._negedge_settled()
            self._score(f"f{attempt}: memory has the dirty line",
                        bytes(self.mem[line]), bytes(exp_line))
            if s0.wb_grants > wb_grants0:
                hit = True
                break
            self.log.info(f"ships_in_the_night: attempt {attempt} missed "
                          f"the pre-BRESP window (coherent via memory); "
                          f"retrying")
        self._score("f: snoop answered from the WB buffer "
                    "(within 3 attempts)", hit, True)
        self._scenario('PairShipsInTheNight')

    # ------------------------------------------------------------------
    # randomized dual-CPU lockstep
    # ------------------------------------------------------------------
    def _rand_addr(self, rng):
        line = rng.randrange(self.SPAN)
        beat = rng.randrange(self.FILL_BEATS)
        return self._base_of(line) + beat * self.STRB_W

    async def _cpu_loop(self, c, n, rng):
        i = 0
        while i < n:
            # occasionally pipeline a short burst (jet's in-cache
            # concurrency: hit-under-miss, merges) before awaiting
            burst = 1 + (rng.randrange(3) if rng.random() < 0.3 else 0)
            ns = []
            for _ in range(min(burst, n - i)):
                addr = self._rand_addr(rng)
                we = 1 if rng.random() < 0.5 else 0
                be = rng.randrange(1, 1 << self.STRB_W) if we \
                    else (1 << self.STRB_W) - 1
                wdata = rng.getrandbits(self.BUS_WIDTH) if we else 0
                ns.append(await self._send(c, addr, we, be=be,
                                           wdata=wdata,
                                           label=f'r{c}_{i}'))
                i += 1
            for m in ns:
                await self._await_rsp(c, m, f'r{c}')
            for _ in range(rng.randrange(2)):
                await self._negedge_settled()

    async def _random_lockstep(self, n):
        rng0 = random.Random((self.SEED << 1) | 0)
        rng1 = random.Random((self.SEED << 1) | 1)
        t0 = cocotb.start_soon(self._cpu_loop(0, n, rng0))
        t1 = cocotb.start_soon(self._cpu_loop(1, n, rng1))
        await t0
        await t1

    # ------------------------------------------------------------------
    # audits / cross-checks
    # ------------------------------------------------------------------
    async def _memory_audit(self):
        """Every touched line: sdpram content == memory model."""
        mem_words = self.dut.u_mem.u_core.r_mem
        word_shift = self.STRB_W.bit_length() - 1
        for line in range(self.SPAN):
            base_word = self._base_of(line) >> word_shift
            got = bytearray()
            for b in range(self.FILL_BEATS):
                got += int(mem_words[base_word + b].value).to_bytes(
                    self.STRB_W, 'little')
            self._score(f"mem audit line {line:#x}", bytes(got),
                        bytes(self.mem[line]))

    def _check_fabric_stats(self):
        self._score("fabric: no unresolved transaction",
                    self.cur_ft is None, True)
        self._score("fabric: kill predictions correct",
                    self.stats['kill_pred_bad'], 0)
        self._score("fabric: pending queue never overflowed",
                    int(self.dut.u_fabric.pend_ovf_q.value), 0)
        self._score("fabric: at least one coherence grant",
                    sum(self.stats['grants']) > 0, True)
        for c in range(2):
            rep = self.ace_checkers[c].get_compliance_report()
            self._score(f"ACE compliance violations (cache{c})",
                        rep['total_violations'], 0)
        if self.USE_MONITOR == 0:
            for c in range(2):
                self._score(f"nomon{c}: observer silent",
                            self._mon_pkts[c], 0)

    async def _quiescence(self):
        for _ in range(40):
            await self._negedge_settled()
        self._score("quiescent: fabric idle",
                    int(self.dut.u_fabric.dbg_state.value), FAB_F_IDLE)
        self._score("quiescent: no pending",
                    int(self.dut.u_fabric.dbg_pend_vld.value), 0)
        for c in range(2):
            side = self.sides[c]
            self._score(f"quiescent: cache{c} not ERROR",
                        int(self._jet(c).ctrl_state.value)
                        == AMBER_CTRL_ERROR, False)
            self._score(f"quiescent: cache{c} responses drained",
                        len(side.rspq), 0)
            self._score(f"quiescent: cache{c} no live MSHR entries",
                        len(side.entries), 0)
            self._score(f"quiescent: cache{c} WB drained",
                        len(side.wb), 0)
            self._score(f"quiescent: cache{c} no in-flight upgrade",
                        side.upgr['valid'], False)
            self._score(f"quiescent: cache{c} no pending snoop effects",
                        len(side.exp_sn_tagwr), 0)
            self._score(f"quiescent: cache{c} no launch backlog",
                        len(side.unlaunched), 0)

    # ------------------------------------------------------------------
    # top-level run
    # ------------------------------------------------------------------
    async def run(self):
        await self._s_init_walk()
        await self._s_pass_dirty_forwarding()
        await self._s_upgrade_invalidates_peer()
        await self._s_dirty_eviction_writeback()
        await self._s_e_downgrade_read_shared()
        await self._s_simultaneous_misses()
        await self._s_ships_in_the_night()

        if self.TEST_LEVEL in ('func', 'full'):
            await self._random_lockstep(self.FULL_TXN[self.TEST_LEVEL])
            self._scenario('RandomDualCpuLockstep')
            if self.USE_MONITOR == 0:
                self._scenario('MonbusPresentVsAbsent')

        self._check_fabric_stats()
        await self._memory_audit()
        await self._quiescence()
        return self.mismatches == 0

    def get_test_report(self):
        return {
            'checks': self.checks,
            'mismatches': self.mismatches,
            'txns': [s.txns for s in self.sides],
            'snoops': [s.snoops for s in self.sides],
            'wb_snarfs': [s.wb_grants for s in self.sides],
            'pre_ar_answers': [s.pre_ar_answers for s in self.sides],
            'pend_installs': [s.pend_installs for s in self.sides],
            'kill_count': [s.kill_count for s in self.sides],
            'stats': self.stats,
            'scenarios': self.scenarios,
        }
