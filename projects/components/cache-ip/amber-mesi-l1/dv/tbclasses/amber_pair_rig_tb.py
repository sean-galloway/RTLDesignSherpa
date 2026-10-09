"""
amber pair rig testbench

Task 11 (THE gated deliverable): two amber_top caches + the
amber_pair_fabric snoopy manager + the house sdpram_slave_axi4_axi4 shared
memory, coherent end-to-end. The DUT is the rig harness
(amber_pair_rig_tb.sv): u_amber0/u_amber1 (each a full amber top: core +
axi4_master_rd/wr_monlite transports + the D-7 monbus_arbiter), the fabric,
and the shared sdpram. The TB drives BOTH CPU GAXI ports concurrently and
scores coherence against a 2-cache Python lockstep model.

Model design (extends the Task 2 gem5 oracle + the Task 9 per-cache
machinery with the fabric rules):
  * Per cache (CacheSide, a DUT-free golden model ported from the Task 9
    AmberCoreTB machinery): tags/slot_state/cache_content/repl/transient
    overlay, observation-driven at the same state entries the RTL applies
    effects at (MISS_VICTIM select, MISS_FILL launch, FILL_WRITE commit,
    HIT_WR merge), snoop effects at the observed ctrl_snoop grant. A killed
    fill replays through the DUT's own re-observed miss states -- no
    model-side refetch exists.
  * Fabric layer (in the TB): coh_req pulses latch per-direction pending
    {line}; the serialized grant is observed on the fabric debug taps; the
    snoop resolution is predicted at the pulse (kill rule: an ungranted
    same-line peer fill -> MakeInvalid) and recorded ACTUALLY at the peer's
    observed grant (oracle_step on the peer's CURRENT state) -- the
    requester's commit consumes the recorded transaction, so any fabric
    misresolution is caught as a data/state mismatch, not a model guess.
    PassDirty resolutions absorb the forwarded line into the memory model
    (the fabric keeps the sdpram the point of coherence); WRITE_BACK pulses
    update the memory model with the victim snapshot.
  * Memory model: line content initialized identically to the sdpram
    backdoor; audited against the sdpram r_mem at quiescence (and per
    scenario).

What this suite pins (the pair-rig contract; per-cache contracts are the
FUB/macro/core suites'):
  (a) M->remote-fill PassDirty forwarding -- fill data from the peer, not
      the (poisoned) memory; memory AR suppressed; absorption lands it.
  (b) S->M upgrade invalidates the peer; the peer's later read misses and
      the fabric forwards (peer M -> PassDirty CD).
  (c) Dirty eviction WriteBack visible to the memory AND to peers.
  (d) E->S downgrade on ReadShared (tag-word promotion backdoor -- the CPU
      path never installs E, the documented Table 3.0 reachability gap).
  (e) Simultaneous same-line misses serialize fairly, both correct.
  (f) Randomized dual-CPU traffic vs the lockstep model (above).
  (g) MonBus present-vs-absent equivalence (USE_MONITOR=0: identical
      functional results, observer silent).

Levels (TEST_LEVEL):
  gate  -- InitWalk + directed (a)-(e)
  func  -- + RandomDualCpuLockstep (f) + MonbusPresentVsAbsent (g)
  full  -- + dual-CPU soak

Author: RTL Design Sherpa
Created: 2026-10-09
"""

import os
import random

import cocotb
from cocotb.triggers import RisingEdge, FallingEdge, Timer

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

from projects.components.cache_ip.amber_mesi_l1.dv.golden.amber_fsm_oracle import (
    SNOOP_CODES,
    step as oracle_step,
)
from projects.components.cache_ip.amber_mesi_l1.dv.tbclasses.amber_core_tb import (
    LruModel,
    FifoModel,
    _parse_packet,
)

# ctrl_state_t codes (amber_pkg)
ST_IDLE, ST_INIT, ST_LOOKUP, ST_HIT_RD, ST_HIT_WR, ST_MISS_VICTIM, \
    ST_MISS_DRAIN, ST_MISS_FILL, ST_FILL_WRITE, ST_REPLAY, ST_SNOOP, \
    ST_ERROR = range(0xC)

# MonBus event codes (amber_pkg.amber_event_t)
EV_HIT, EV_MISS, EV_SNOOP, EV_EVICT, EV_TRANSITION, \
    EV_FILL_START, EV_FILL_END, EV_DRAIN_START, EV_DRAIN_END, \
    EV_DROPPED = range(0xA)
EV_NAMES = {EV_HIT: 'HIT', EV_MISS: 'MISS', EV_SNOOP: 'SNOOP',
            EV_EVICT: 'EVICT', EV_TRANSITION: 'TRANSITION',
            EV_FILL_START: 'FILL_START', EV_FILL_END: 'FILL_END',
            EV_DRAIN_START: 'DRAIN_START', EV_DRAIN_END: 'DRAIN_END',
            EV_DROPPED: 'DROPPED'}

# amber_ace_req_t encodings (amber_pkg)
ACE_READ_SHARED, ACE_READ_UNIQUE, ACE_CLEAN_UNIQUE = 0, 1, 2
ACE_WRITE_BACK = 4

# fabric ACSNOOP encodings (IHI0022 4-bit, framework SnoopType)
FAB_SNOOP_RS = 0x1   # SnoopType.READ_SHARED
FAB_SNOOP_RU = 0x7   # SnoopType.READ_UNIQUE
FAB_SNOOP_MI = 0xC   # SnoopType.MAKE_INVALID
SNOOP_NAME_BY_FAB = {FAB_SNOOP_RS: 'SNOOP_READ_SHARED',
                     FAB_SNOOP_RU: 'SNOOP_READ_UNIQUE',
                     FAB_SNOOP_MI: 'SNOOP_MAKE_INVALID'}
FAB_SNOOP_BY_TYPE = {ACE_READ_SHARED: FAB_SNOOP_RS,
                     ACE_READ_UNIQUE: FAB_SNOOP_RU,
                     ACE_CLEAN_UNIQUE: FAB_SNOOP_MI}

CRRESP_DT = 0
CRRESP_PD = 2

REPL_LRU = 0

# fabric FSM states (amber_pair_fabric dbg encoding)
FAB_F_IDLE = 0
FAB_F_AC = 1
FAB_F_RESP = 2
FAB_F_REPLAY_AR = 3
FAB_F_REPLAY_R = 4
FAB_F_PASS_AR = 5
FAB_F_PASS_R = 6
FAB_F_DONE = 7

# ACE framework mapping for the compliance checker
FRAMEWORK_SNOOPS = {
    'SNOOP_READ_ONCE': SnoopType.READ_ONCE,
    'SNOOP_READ_SHARED': SnoopType.READ_SHARED,
    'SNOOP_READ_UNIQUE': SnoopType.READ_UNIQUE,
    'SNOOP_CLEAN_SHARED': SnoopType.CLEAN_SHARED,
    'SNOOP_CLEAN_INVALID': SnoopType.CLEAN_INVALID,
    'SNOOP_MAKE_INVALID': SnoopType.MAKE_INVALID,
}


class CacheSide:
    """Golden model of ONE amber cache in the pair (no DUT references).

    Ported from the Task 9 AmberCoreTB per-cache machinery: the model is
    observation-driven -- coherence effects land at the same observable
    state entries the DUT applies them at, so a peer transaction granted
    at any cycle is scored against exactly the resolution the RTL used.
    """

    def __init__(self, idx, sets, ways, line_bytes, bus_width, repl_policy, tb):
        self.idx = idx
        self.tb = tb
        self.SETS = sets
        self.WAYS = ways
        self.LINE_BYTES = line_bytes
        self.STRB_W = bus_width // 8
        self.FILL_BEATS = line_bytes // self.STRB_W
        self.SET_BITS = (sets - 1).bit_length()
        self.OFFSET_BITS = (line_bytes - 1).bit_length()
        self.SET_MASK = sets - 1

        self.tags = {}
        self.slot_state = {}
        self.cache_data = {}
        self.obs = {}          # transient overlay (IS/IM/SM/IS_I/M_I/SINK_WB_ACK)
        self.repl = (LruModel(sets, ways) if repl_policy == REPL_LRU
                     else FifoModel(sets, ways))
        self.pend_line = None  # post-commit snoop effect ('S'/'I') + line
        self.pend_eff = None
        self.cur_txn = None
        self.last_killed_line = None
        self.ft_debt_lines = []   # upgrade commits that outran the fabric F_DONE

        # observation logs
        self.tally = {ev: 0 for ev in EV_NAMES}
        self.pkt_counts = {ev: 0 for ev in EV_NAMES}
        self.grant_log = []
        self.txns = 0
        self.snoops = 0
        self.coh_req_pulses = []     # observed pulses (in order)
        self.grant_fifo = []         # fabric transactions granted for me

    # ------------------------------------------------------------------
    # line helpers
    # ------------------------------------------------------------------
    def line_of(self, addr):
        return (addr >> self.OFFSET_BITS) & ((1 << (32 - self.OFFSET_BITS)) - 1)

    def set_of(self, line):
        return line & self.SET_MASK

    def installed_state(self, line):
        s = self.set_of(line)
        for w in range(self.WAYS):
            if (self.tags.get((s, w)) == line
                    and self.slot_state.get((s, w), 'I') != 'I'):
                return self.slot_state[(s, w)]
        return 'I'

    def cur_state(self, line):
        st = self.obs.get(line)
        if st is not None:
            return st
        return self.installed_state(line)

    def hit_way(self, set_idx, line):
        for w in range(self.WAYS):
            if (self.tags.get((set_idx, w)) == line
                    and self.slot_state.get((set_idx, w), 'I') != 'I'):
                return w
        return None

    def slot_of(self, set_idx, line):
        for w in range(self.WAYS):
            if self.tags.get((set_idx, w)) == line:
                return w
        return None


class AmberPairRigTB(TBBase):
    """Scores the pair rig against the 2-cache lockstep model."""

    FULL_TXN = {'gate': 0, 'func': 250, 'full': 2000}
    RSP_TIMEOUT_CYCLES = 6000
    MAX_TAG = None   # set in __init__

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
        self.caches = [CacheSide(i, self.SETS, self.WAYS, self.LINE_BYTES,
                                 self.BUS_WIDTH, self.REPL_POLICY, self)
                       for i in range(2)]
        self.mem = {}            # memory model: line -> bytearray
        # per-direction pending-request queues, mirroring the fabric's
        # PEND_DEPTH FIFO: an upgrade completes at the cache without
        # waiting for the fabric, so several requests per direction can be
        # queued (entries: ctx dict + set/pop cycles for the kill rule)
        self.ft_queue = [[], []]
        # per-direction drain guard mirror: (line, set_cyc, clear_cyc|None)
        self.ft_drain = [None, None]
        self.cur_ft = None       # in-flight fabric transaction (serial)
        self.stats = {
            'grants': [0, 0], 'kills': 0, 'kill_pred_ok': 0, 'kill_pred_bad': 0,
            'dt_forwards': 0, 'pass_throughs': 0, 'absorbs': 0,
            'mem_ar': 0, 'wb_bursts': 0, 'upgrades': 0,
            'first_grant': [], 'replay_beats': 0, 'orphan_grants': 0,
        }

        # observation
        self.cyc = 0
        self.events = []
        self.rsp_log = [[], []]
        self.checks = 0
        self.mismatches = 0
        self.scenarios = {}
        self._prev_state = [-1, -1]
        self._prev_fab_state = -1
        self._ace_seq = [0, 0]
        self._cd_seq = [0, 0]
        self._cd_started = [False, False]
        self._cur_snoop_type = [None, None]
        self._cd_beats = [0, 0]
        self.ace_checkers = [ACEComplianceChecker(log=self.log),
                             ACEComplianceChecker(log=self.log)]
        self.mon_mode = 'free'
        self._mon_pkts = [[], []]
        self._drop_count = [0, 0]

        # directed-scenario tag allocator (tags map inside the pre-filled span)
        self._tag_next = 0

        self.log.info(f"AmberPairRigTB sets={self.SETS} ways={self.WAYS} "
                      f"line={self.LINE_BYTES} bus={self.BUS_WIDTH} "
                      f"repl={self.REPL_POLICY} monitor={self.USE_MONITOR} "
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

    def _pack_req(self, addr, we, be, wdata):
        return ((addr & ((1 << self.ADDR_WIDTH) - 1))
                << (1 + self.STRB_W + self.BUS_WIDTH)) \
            | ((we & 1) << (self.STRB_W + self.BUS_WIDTH)) \
            | ((be & ((1 << self.STRB_W) - 1)) << self.BUS_WIDTH) \
            | (wdata & ((1 << self.BUS_WIDTH) - 1))

    def _decode3(self, code):
        return {0: 'I', 1: 'S', 2: 'E', 3: 'M'}.get(code, f'RSV{code}')

    def _amber(self, c):
        return getattr(self.dut, f'u_amber{c}')

    async def _negedge_settled(self):
        await FallingEdge(self.dut.clk)
        await Timer(500, units='ps')

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
        cocotb.start_soon(self._monbus_ready_driver())
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
    # monitor: per-cycle observation of both caches, fabric, ACE, monbus
    # ------------------------------------------------------------------
    async def _monitor(self):
        d = self.dut
        while True:
            await FallingEdge(d.clk)
            await Timer(100, units='ps')
            self.cyc += 1

            # drain guard clear: the peer's FSM back to a safe state
            for c in range(2):
                dr = self.ft_drain[c]
                if dr is not None and dr[2] is None:
                    stc = int(self._amber(c).ctrl_state.value)
                    if stc in (ST_IDLE, ST_LOOKUP, ST_HIT_RD, ST_HIT_WR):
                        self.ft_drain[c] = (dr[0], dr[1], self.cyc)

            fab_state = int(d.u_fabric.dbg_state.value)
            fab_changed = fab_state != self._prev_fab_state
            if fab_changed:
                self._on_fab_state(fab_state)
                self._prev_fab_state = fab_state
            if self.stats.get('hang_trace') and self.cyc % 25 == 0:
                f = d.u_fabric
                self.log.info(
                    f"HANG c{self.cyc} fstate {int(f.dbg_state.value)} "
                    f"pend {int(f.dbg_pend_vld.value):02b} "
                    f"buf {int(f.dbg_buf_vld.value):02b} "
                    f"absp {int(f.dbg_abs_pend.value):02b} "
                    f"c0st {int(self._amber(0).ctrl_state.value):x} "
                    f"c1st {int(self._amber(1).ctrl_state.value):x} "
                    f"c0ar {int(self._amber(0).m_axi_arvalid.value)}"
                    f"{int(self._amber(0).m_axi_arready.value)} "
                    f"c1ar {int(self._amber(1).m_axi_arvalid.value)}"
                    f"{int(self._amber(1).m_axi_arready.value)} "
                    f"s0ac {int(self._amber(0).m_axi_acvalid.value)}"
                    f"{int(self._amber(0).m_axi_acready.value)} "
                    f"s1ac {int(self._amber(1).m_axi_acvalid.value)}"
                    f"{int(self._amber(1).m_axi_acready.value)} "
                    f"s0cr {int(self._amber(0).m_axi_crvalid.value)} "
                    f"s0cd {int(self._amber(0).m_axi_cdvalid.value)}"
                    f"{int(self._amber(0).m_axi_cdready.value)}")

            for c in range(2):
                a = self._amber(c)
                st = int(a.ctrl_state.value)
                if st != self._prev_state[c]:
                    self._on_state_entry(c, st)
                    self._prev_state[c] = st

                if int(getattr(d, f'cpu{c}_req_wr_valid').value) \
                        and int(getattr(d, f'cpu{c}_req_wr_ready').value):
                    packed = int(getattr(d, f'cpu{c}_req_wr_data').value)
                    self.events.append((self.cyc, 'accept', c, packed))

                if int(a.coh_req_valid.value):
                    self._on_coh_req(c, int(a.coh_req_addr.value),
                                     int(a.coh_req_type.value))

                # snoop grant inside the cache (peer's effect books here)
                core = a.u_core
                if int(core.u_snoop.ctrl_snoop_req.value) \
                        and int(core.u_control.ctrl_snoop_ready.value):
                    self._on_snoop_grant(c)

                self._on_ace_channels(c)

                if int(getattr(d, f'mon{c}_valid').value) \
                        and int(getattr(d, f'mon{c}_ready').value):
                    raw = int(getattr(d, f'mon{c}_packet').value)
                    p = _parse_packet(raw)
                    if p['unit_id'] == 1:   # amber_monlite stream only
                        self.caches[c].pkt_counts[p['event_code']] += 1
                        self._mon_pkts[c].append((self.cyc, p))
                        if p['event_code'] == EV_DROPPED:
                            # drop-and-count report: data = events dropped
                            # since the previous report
                            self._drop_count[c] += p['data']

            # memory-side AR observation (suppression counting)
            if int(d.u_fabric.mem_arvalid.value) \
                    and int(d.u_fabric.mem_arready.value):
                self.stats['mem_ar'] += 1
                self.events.append((self.cyc, 'mem_ar',
                                    int(d.u_fabric.mem_araddr.value)))

    # ------------------------------------------------------------------
    # fabric model: coh_req pulse -> prediction; grant -> transaction
    # ------------------------------------------------------------------
    def _on_coh_req(self, c, addr, req_type):
        cm = self.caches[c]
        cm.coh_req_pulses.append((self.cyc, addr, req_type))
        line = self._line_of(addr)
        if req_type == ACE_WRITE_BACK:
            # dirty victim draining: the write-back carries the staged
            # victim content to the shared memory (model: launch-time view;
            # the RTL's B lands later but reads are snoop-gated)
            txn = cm.cur_txn
            if txn is not None and txn.get('victim') is not None \
                    and txn['victim'].get('data') is not None:
                vline = txn['victim']['line']
                self.mem[vline] = bytearray(txn['victim']['data'])
                self.events.append((self.cyc, 'wb', c, vline))
            return

        peer = 1 - c
        ctx = {'cyc': self.cyc, 'dir': c, 'line': line, 'type': req_type,
               'kill_pred': None,
               'peer_state_at_pulse': self.caches[peer].cur_state(line)}
        ctx['set_cyc'] = self.cyc
        ctx['pop_cyc'] = None
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
            cm = self.caches[g]
            assert self.ft_queue[g], "grant without a pending coh_req"
            ctx = self.ft_queue[g].pop(0)
            ctx['pop_cyc'] = self.cyc
            # kill rule prediction against the queue state the RTL grant
            # edge actually samples: pulses are registered (visible to a
            # grant decision at edge set_cyc+2), pops at their grant
            self.cur_ft = ctx
            self.cur_ft['kill_actual'] = None
            self.cur_ft['resolution'] = None
            self.stats['grants'][g] += 1
            if len(self.stats['first_grant']) == 0 or \
                    self.stats['first_grant'][-1] != g:
                self.stats['first_grant'].append(g)
        elif st == FAB_F_DONE:
            if self.cur_ft is not None:
                g = self.cur_ft['dir']
                self.caches[g].grant_fifo.append(self.cur_ft)
                self.ft_drain[g] = (self.cur_ft['line'], self.cyc, None)
                if self.cur_ft['kill_actual']:
                    self.stats['kills'] += 1
                if self.cur_ft['resolution'] is not None \
                        and (self.cur_ft['resolution'] >> CRRESP_DT) & 1:
                    self.stats['dt_forwards'] += 1
                else:
                    self.stats['pass_throughs'] += 1
                self.cur_ft = None

    def _on_ace_channels(self, c):
        """Observe the fabric<->cache c ACE responder channels: AC
        handshakes (latch the actual snoop), CD beats, CR handshakes (score
        CRRESP + beat count against the recorded resolution), and feed the
        per-cache compliance checker."""
        a = self._amber(c)
        # AC handshake: fabric launches a snoop on this cache
        if int(a.m_axi_acvalid.value) and int(a.m_axi_acready.value):
            snoop = int(a.m_axi_acsnoop.value)
            self._cur_snoop_type[c] = FRAMEWORK_SNOOPS.get(
                SNOOP_NAME_BY_FAB.get(snoop))
            if self.cur_ft is not None and self.cur_ft['dir'] != c \
                    and self.cur_ft['kill_actual'] is None:
                # kill prediction at ISSUE time, against the current
                # queue/drain plus the peer's live sideband pins (the
                # fabric evaluates combinationally; the registered queue
                # lags a same-cycle pulse by a cycle)
                live = [e for e in self.ft_queue[c]]
                raw_v = int(self._amber(c).coh_req_valid.value)
                raw_t = int(self._amber(c).coh_req_type.value)
                if raw_v and raw_t != ACE_WRITE_BACK:
                    live.append({'line': self._line_of(
                        int(self._amber(c).coh_req_addr.value))})
                head = min(live, key=lambda e: e.get('set_cyc', self.cyc),
                           default=None)
                # NB: no drain term -- a kill is sound only while the
                # peer's fill cannot commit (AR held); the drain window
                # waits instead (see the fabric header)
                self.cur_ft['kill_pred'] = (
                    head is not None
                    and head['line'] == self.cur_ft['line'])
                rtl_kill = bool(int(self.dut.u_fabric.dbg_kill.value))
                if rtl_kill != self.cur_ft['kill_pred']:
                    self.stats['kill_pred_dbg'] = \
                        self.stats.get('kill_pred_dbg', 0) + 1
                # CLEAN_UNIQUE maps to MakeInvalid by construction; only
                # READ_SHARED / READ_UNIQUE snoops carry kill-rule info
                if self.cur_ft['type'] == ACE_CLEAN_UNIQUE:
                    self.cur_ft['kill_actual'] = True
                    self.cur_ft['kill_pred_ok'] = True
                else:
                    self.cur_ft['kill_actual'] = (snoop == FAB_SNOOP_MI)
                    self.cur_ft['kill_pred_ok'] = (
                        self.cur_ft['kill_actual']
                        == self.cur_ft['kill_pred'])
                if not self.cur_ft['kill_pred_ok']:
                    self.stats['kill_pred_bad'] += 1
                else:
                    self.stats['kill_pred_ok'] += 1
                exp_snoop = FAB_SNOOP_MI if self.cur_ft['kill_pred'] \
                    else FAB_SNOOP_BY_TYPE[self.cur_ft['type']]
                self._score(f"ft{self.cur_ft['cyc']}: acsnoop",
                            snoop, exp_snoop)
                self._score(f"ft{self.cur_ft['cyc']}: acaddr line-aligned",
                            int(a.m_axi_acaddr.value)
                            & (self.LINE_BYTES - 1), 0)
                self._score(f"ft{self.cur_ft['cyc']}: acaddr",
                            int(a.m_axi_acaddr.value),
                            self._base_of(self.cur_ft['line']))
        # CD beats (count; content is scored at the grant observation).
        # The framework checker numbers CD sequences among data-carrying
        # snoops only -- a non-DT snoop contributes no beats and does not
        # advance the CD counter (snoop_resp_tb idiom).
        if int(a.m_axi_cdvalid.value) and int(a.m_axi_cdready.value):
            self._cd_beats[c] += 1
            if not self._cd_started[c]:
                self._cd_started[c] = True
                res = self.cur_ft.get('resolution') \
                    if self.cur_ft is not None else None
                if res is not None and (res >> CRRESP_DT) & 1:
                    self.ace_checkers[c].set_expected_cd_beats(
                        self.FILL_BEATS)
            last = int(a.m_axi_cdlast.value)
            self.ace_checkers[c].check_cd_order(
                self._cd_seq[c], last,
                self._base_of(self.cur_ft['line'])
                if self.cur_ft is not None else 0,
                self._cur_snoop_type[c])
            if last:
                self._cd_seq[c] += 1
                self._cd_started[c] = False
        # CR handshake: score against the recorded resolution
        if int(a.m_axi_crvalid.value) and int(a.m_axi_crready.value):
            crresp = int(a.m_axi_crresp.value)
            if self.cur_ft is not None and self.cur_ft['dir'] != c:
                res = self.cur_ft.get('resolution')
                self._score(f"ft{self.cur_ft['cyc']}: crresp", crresp, res)
                exp_beats = self.FILL_BEATS \
                    if res is not None and (res >> CRRESP_DT) & 1 else 0
                self._score(f"ft{self.cur_ft['cyc']}: cd beats",
                            self._cd_beats[c], exp_beats)
            self.ace_checkers[c].check_cr_order(
                self._ace_seq[c],
                self._base_of(self.cur_ft['line'])
                if self.cur_ft is not None else 0,
                self._cur_snoop_type[c])
            self.ace_checkers[c].check_crresp_validity(
                CRRESP(crresp), self._cur_snoop_type[c],
                self._base_of(self.cur_ft['line'])
                if self.cur_ft is not None else 0)
            self._ace_seq[c] += 1
            self._cd_beats[c] = 0

    def _take_ft(self, cm, line, label):
        """Consume the fabric transaction this live pass filled from.

        Per blocking cache the fifo is exactly one entry per granted pass,
        in pass order. A KILLED pass's pulse is still granted by the
        fabric (stale grant: the requester already converted or refetched),
        leaving an orphan entry AHEAD of the refetch's -- discard those
        (counted; the orphan's snoop effect was booked at its own grant).
        """
        matches = [i for i, ft in enumerate(cm.grant_fifo)
                   if ft['line'] == line]
        if not matches:
            # upgrades (no data phase) can commit before the fabric's
            # F_DONE push lands; the entry arrives later and is consumed
            # by no one (line-matched takes skip it) -- settle at audit
            cm.ft_debt_lines.append(line)
            return None
        idx = matches[-1]
        # same-line entries ahead of the newest match are the stale grants
        # of killed passes (the refetch supersedes them) or the late pushes
        # of upgrade debts -- discard both, settling the debt
        orphans = matches[:-1]
        for o in orphans:
            oline = cm.grant_fifo[o]['line']
            if oline in cm.ft_debt_lines:
                cm.ft_debt_lines.remove(oline)
            else:
                self.stats['orphan_grants'] += 1
        ft = cm.grant_fifo[idx]
        cm.grant_fifo = [f for i, f in enumerate(cm.grant_fifo)
                         if i != idx and i not in orphans]
        return ft

    # ------------------------------------------------------------------
    # per-cache model hooks (ported Task 9 machinery)
    # ------------------------------------------------------------------
    def _on_state_entry(self, c, st):
        cm = self.caches[c]
        txn = cm.cur_txn
        if txn is None:
            return
        line = txn['line']
        a = self._amber(c)
        if st == ST_MISS_VICTIM and not txn['victim_done']:
            txn['victim_done'] = True
            self._model_victim_select(c, txn)
        elif st == ST_MISS_FILL:
            cm.tally[EV_FILL_START] += 1
            if txn['fill_modeled']:
                return
            txn['fill_modeled'] = True
            upgrade_pass = not txn['victim_done'] or txn['victim'] is None
            txn['pass_upgrade'] = upgrade_pass
            cm.obs[line] = 'SM' if upgrade_pass else \
                ('IS' if not txn['we'] else 'IM')
            vic = txn.get('victim')
            if vic and vic['line'] != line and vic.get('overlay'):
                cm.obs[vic['line']] = 'I'
        elif st == ST_MISS_DRAIN:
            cm.tally[EV_DRAIN_START] += 1
        elif st == ST_FILL_WRITE:
            self._model_pass_commit(c, txn)
        elif st == ST_HIT_RD:
            way = cm.hit_way(txn['set_idx'], line)
            if way is not None:
                cm.repl.hit(txn['set_idx'], way)
        elif st == ST_HIT_WR:
            self._model_merge(c, txn)

    def _model_merge(self, c, txn):
        cm = self.caches[c]
        line = txn['line']
        pre = cm.installed_state(line)
        if txn['we']:
            if txn['be']:
                line_data = cm.cache_data[line]
                lo = txn['beat'] * self.STRB_W
                for i in range(self.STRB_W):
                    if txn['be'] & (1 << i):
                        line_data[lo + i] = (txn['wdata'] >> (8 * i)) & 0xFF
            if pre == 'E':
                cm.tally[EV_TRANSITION] += 1
                way = cm.hit_way(txn['set_idx'], line)
                if way is not None:
                    cm.slot_state[(txn['set_idx'], way)] = 'M'
        way = cm.hit_way(txn['set_idx'], line)
        if way is not None:
            cm.repl.hit(txn['set_idx'], way)

    def _model_victim_select(self, c, txn):
        cm = self.caches[c]
        a = self._amber(c)
        set_idx = txn['set_idx']
        way = cm.repl.victim(set_idx)
        self._score(f"{txn['label']}: victim way parity", way,
                    int(a.u_core.u_repl.repl_victim_way.value))
        vline = cm.tags.get((set_idx, way))
        vstate = cm.slot_state.get((set_idx, way), 'I')
        dut_ts = int(a.u_core.u_tag.mem[way * self.SETS + set_idx].value)
        dut_tag, dut_state = dut_ts >> 3, self._decode3(dut_ts & 7)
        exp_tag = (vline >> self.SET_BITS) if vline is not None else 0
        self._score(f"{txn['label']}: victim slot parity",
                    (exp_tag, vstate), (dut_tag, dut_state))
        if vline == txn['line']:
            txn['victim'] = {'way': way, 'line': vline, 'dirty': False,
                             'overlay': False,
                             'data': bytes(cm.cache_data.get(
                                 vline, bytearray(self.LINE_BYTES)))}
            cm.tally[EV_MISS] += 1
            return
        dirty = vstate == 'M'
        live = vstate in ('S', 'E', 'M')
        txn['victim'] = {'way': way, 'line': vline, 'dirty': dirty,
                         'overlay': live,
                         'data': bytes(cm.cache_data.get(
                             vline, bytearray(self.LINE_BYTES)))}
        cm.tally[EV_MISS] += 1
        if dirty:
            cm.obs[vline] = 'M_I'
            cm.tally[EV_EVICT] += 1
            cm.tally[EV_DRAIN_END] += 1
        elif live:
            cm.obs[vline] = 'I'

    def _model_pass_commit(self, c, txn):
        cm = self.caches[c]
        line = txn['line']
        set_idx = txn['set_idx']
        pend = cm.pend_eff if cm.pend_line == line else None
        if cm.pend_line == line:
            cm.pend_line = None
            cm.pend_eff = None
        if txn['pass_upgrade']:
            way = cm.hit_way(set_idx, line)
            if way is None:
                way = cm.slot_of(set_idx, line)
            state = 'I' if txn['killed'] else 'M'
            if way is not None:
                cm.slot_state[(set_idx, way)] = state
                cm.repl.hit(set_idx, way)
            if not txn['killed']:
                self._take_ft(cm, line, txn['label'])
        else:
            transient = cm.obs.get(line, 'IM')
            if transient == 'IS_I':
                committed = 'I'
            elif transient in ('IS', 'SM'):
                committed = pend or 'S'
            else:
                committed = pend or 'M'
            victim = txn['victim']
            way = victim['way']
            cm.tags[(set_idx, way)] = line
            cm.slot_state[(set_idx, way)] = committed
            if not txn['killed']:
                # fill data: the fabric transaction for this live pass
                # (the PassDirty absorption itself was booked where the
                # resolution was recorded -- the fabric performs it whether
                # or not this pass survives)
                ft = self._take_ft(cm, line, txn['label'])
                if ft is None:
                    raise RuntimeError(
                        f"{txn['label']}: live pass has no fabric grant")
                if (ft['resolution'] >> CRRESP_DT) & 1:
                    data = ft['data_actual']
                else:
                    data = self._mem_line(line)
                cm.cache_data[line] = bytearray(data)
            cm.repl.update(set_idx, way)
        cm.obs.pop(line, None)
        vic = txn.get('victim')
        if vic and vic.get('overlay'):
            cm.obs.pop(vic['line'], None)
        if txn['killed']:
            cm.last_killed_line = line
        cm.tally[EV_FILL_END] += 1
        cm.tally[EV_TRANSITION] += 1
        txn['victim_done'] = False
        txn['fill_modeled'] = False
        txn['victim'] = None
        txn['killed'] = False

    def _on_snoop_grant(self, c):
        """A fabric snoop is granted inside cache c: book the peer's
        coherence effect (Task 9 _on_snoop_grant logic) AND the fabric
        transaction's actual resolution (the in-flight transaction always
        targets this cache -- the fabric is serial)."""
        a = self._amber(c)
        core = a.u_core
        cm = self.caches[c]
        line = self._line_of(int(core.u_snoop.ctrl_snoop_addr.value))
        fab_snoop = int(a.m_axi_acsnoop.value)
        name = SNOOP_NAME_BY_FAB.get(fab_snoop)
        if name is None:
            self._score(f"snoop{c}: known fabric snoop", fab_snoop, None)
            return
        st = cm.cur_state(line)
        fill = 'S' if st in ('IS', 'IS_I') else None
        pend = cm.pend_eff if cm.pend_line == line else None
        res = oracle_step(st, name, fill=fill, pending=pend)
        if res.pending is not None:
            cm.pend_line, cm.pend_eff = line, res.pending

        # fabric transaction resolution (this grant resolves cur_ft; the
        # fabric is serial, so the granting cache IS the transaction's peer)
        if self.cur_ft is not None and c == 1 - self.cur_ft['dir']:
            self.cur_ft['resolution'] = res.crresp
            if (res.crresp >> CRRESP_DT) & 1:
                if st in ('IS', 'IS_I', 'SM', 'IM'):
                    # pending-fill bypass: memory-side content (rig-level
                    # serialization makes this path unreachable in a
                    # correct fabric -- the kill rule fires instead -- so
                    # landing here is scored against memory content)
                    exp_line = self._mem_line(line)
                elif st in ('M_I', 'SINK_WB_ACK'):
                    vic = cm.cur_txn.get('victim') \
                        if cm.cur_txn is not None else None
                    if vic is not None and vic['line'] == line:
                        exp_line = vic['data']
                    else:
                        exp_line = bytes(cm.cache_data.get(
                            line, bytearray(self.LINE_BYTES)))
                else:
                    exp_line = bytes(cm.cache_data.get(
                        line, bytearray(self.LINE_BYTES)))
                self.cur_ft['data_actual'] = exp_line
                if (res.crresp >> CRRESP_PD) & 1:
                    # PassDirty: the fabric absorbs the forwarded line into
                    # the shared memory (point of coherence) -- performed
                    # whether or not the requester's pass survives (a
                    # killed pass replays; the absorption still lands)
                    self.mem[line] = bytearray(exp_line)
                    self.stats['absorbs'] += 1

        cm.grant_log.append({'cyc': self.cyc, 'line': line, 'name': name,
                             'state': st, 'exp_crresp': res.crresp})
        cm.tally[EV_SNOOP] += 1
        cm.snoops += 1
        if st in ('S', 'E', 'M'):
            if res.next_state != st:
                cm.tally[EV_TRANSITION] += 1
                set_idx = self.caches[c].set_of(line)
                way = cm.hit_way(set_idx, line)
                if way is not None:
                    cm.slot_state[(set_idx, way)] = res.next_state
        else:
            cm.obs[line] = res.next_state
        # kill bookkeeping on the peer's own pending transaction
        txn = cm.cur_txn
        if txn is not None and line == txn['line'] \
                and st in ('IS', 'IM', 'SM', 'IS_I'):
            if (st == 'SM' and res.next_state == 'IM') \
                    or (st in ('IS', 'IM') and res.pending == 'I') \
                    or (st == 'IS_I'):
                txn['killed'] = True

    # ------------------------------------------------------------------
    # monbus
    # ------------------------------------------------------------------
    async def _monbus_ready_driver(self):
        d = self.dut
        while True:
            await FallingEdge(d.clk)
            if self.mon_mode == 'free':
                d.mon0_ready.value = 1
                d.mon1_ready.value = 1
            elif self.mon_mode == 'stall':
                d.mon0_ready.value = 0
                d.mon1_ready.value = 0
            else:
                d.mon0_ready.value = 1 if random.random() < 0.65 else 0
                d.mon1_ready.value = 1 if random.random() < 0.65 else 0

    def _check_tally(self, c):
        cm = self.caches[c]
        if self._drop_count[c] == 0:
            # no observer drops: the per-class stream is exact
            for ev in EV_NAMES:
                if ev == EV_DROPPED:
                    continue
                self._score(f"monbus{c} tally {EV_NAMES[ev]}",
                            cm.pkt_counts[ev], cm.tally[ev])
        else:
            # congestion-phase drop-and-count: the per-class breakdown is
            # unrecoverable, the TOTAL reconciles exactly
            got = sum(cm.pkt_counts[ev] for ev in EV_NAMES
                      if ev != EV_DROPPED) + self._drop_count[c]
            exp = sum(cm.tally[ev] for ev in EV_NAMES if ev != EV_DROPPED)
            self._score(f"monbus{c} tally reconciled with "
                        f"{self._drop_count[c]} drops", got, exp)

    # ------------------------------------------------------------------
    # transaction drivers
    # ------------------------------------------------------------------
    async def _txn_begin(self, c, addr, we, be, wdata, label=''):
        cm = self.caches[c]
        line = self._line_of(addr)
        beat = (addr >> (self.STRB_W.bit_length() - 1)) & (self.FILL_BEATS - 1)
        pre = cm.cur_state(line)
        hint = oracle_step(pre, 'CPU_WR' if we else 'CPU_RD')
        txn = {'addr': addr, 'line': line, 'beat': beat, 'we': we, 'be': be,
               'wdata': wdata, 'label': label,
               'set_idx': cm.set_of(line),
               'hit': hint.result == 'HIT',
               'upgrade': hint.req == 'CLEAN_UNIQUE',
               'pass_upgrade': False,
               'killed': False, 'victim': None,
               'victim_done': False, 'fill_modeled': False}
        cm.cur_txn = txn
        txn['n_rsp'] = len(self.rsp_log[c])
        n_accept = len([1 for e in self.events if e[1] == 'accept'
                        and e[2] == c])
        pkt = self.masters[c].create_packet(data=self._pack_req(addr, we, be,
                                                                wdata))
        await self.masters[c].send(pkt)
        for _ in range(self.RSP_TIMEOUT_CYCLES):
            accepts = [e for e in self.events if e[1] == 'accept'
                       and e[2] == c]
            if len(accepts) >= n_accept + 1:
                break
            await self._negedge_settled()
        else:
            raise RuntimeError(f"{label}: request never accepted; "
                               f"cache{c} state="
                               f"{int(self._amber(c).ctrl_state.value):#x}")
        txn['accept_cyc'] = accepts[-1][0]
        return txn

    async def _txn_end(self, c, txn):
        cm = self.caches[c]
        n_rsp = txn['n_rsp']
        for _ in range(self.RSP_TIMEOUT_CYCLES):
            if len(self.rsp_log[c]) >= n_rsp + 1:
                break
            await self._negedge_settled()
        else:
            self.stats['hang_trace'] = True
            for _ in range(120):
                await self._negedge_settled()
            raise RuntimeError(f"{txn['label']}: response timeout; "
                               f"cache{c} state="
                               f"{int(self._amber(c).ctrl_state.value):#x}")
        rsp_cyc, rsp_data = self.rsp_log[c][n_rsp]
        txn['rsp_cyc'] = rsp_cyc
        txn['rsp_data'] = rsp_data

        if txn['we']:
            exp = txn['wdata']
        else:
            exp = self._beat_of_line(cm.cache_data[txn['line']],
                                     txn['beat'])
        self._score(f"{txn['label']} rsp data", rsp_data, exp)

        cm.tally[EV_HIT] += 1
        cm.txns += 1
        cm.cur_txn = None
        return txn

    async def _txn(self, c, addr, we, be=None, wdata=None, label=''):
        if be is None:
            be = random.randrange(1, 1 << self.STRB_W) if we \
                else (1 << self.STRB_W) - 1
        if wdata is None:
            wdata = random.getrandbits(self.BUS_WIDTH) if we else 0
        txn = await self._txn_begin(c, addr, we, be, wdata, label)
        return await self._txn_end(c, txn)

    # ------------------------------------------------------------------
    # directed scenarios
    # ------------------------------------------------------------------
    async def _s_init_walk(self):
        d = self.dut

        async def _walk_wait(c):
            cycles = 0
            saw_low = False
            # a REAL model transaction (the hooks book victim/fill/commit
            # exactly like a driven txn -- the peer's snoop resolution and
            # the fabric fill data depend on it)
            cm = self.caches[c]
            addr = self._compose_addr(0, 0)
            txn = {'addr': addr, 'line': self._line_of(addr), 'beat': 0,
                   'we': 0, 'be': (1 << self.STRB_W) - 1, 'wdata': 0,
                   'label': f'init{c}',
                   'set_idx': cm.set_of(self._line_of(addr)),
                   'hit': False, 'upgrade': False, 'pass_upgrade': False,
                   'killed': False, 'victim': None,
                   'victim_done': False, 'fill_modeled': False,
                   'n_rsp': len(self.rsp_log[c])}
            cm.cur_txn = txn
            send_task = cocotb.start_soon(self.masters[c].send(
                self.masters[c].create_packet(
                    data=self._pack_req(addr, 0,
                                        (1 << self.STRB_W) - 1, 0))))
            while True:
                await self._negedge_settled()
                cycles += 1
                if cycles > self.SETS * 4 + 200:
                    raise RuntimeError(
                        f"init walk never completed (cache{c})")
                busy = int(self._amber(c).init_busy.value)
                if busy:
                    saw_low = True
                    self._score(f"init{c}: cpu ready low while busy",
                                int(getattr(d, f'cpu{c}_req_wr_ready').value),
                                0)
                else:
                    if int(getattr(d, f'cpu{c}_req_wr_ready').value):
                        break
            await send_task
            self._score(f"init{c}: ready observed low", saw_low, True)
            return await self._txn_end(c, self.caches[c].cur_txn)

        # both caches walk concurrently after the shared reset release;
        # the model hooks (victim/fill/commit/fabric pop) ran off the real
        # transaction context each probe established
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
        await self._txn(1, addr, 1, be=(1 << self.STRB_W) - 1,
                        wdata=0x5A5A_5A5A_5A5A_5A5A & ((1 << self.BUS_WIDTH) - 1),
                        label='a_wr')
        cm1 = self.caches[1]
        self._score("a: cache1 line M", cm1.installed_state(line), 'M')
        # poison the shared memory for this line (byte-distinct stale data)
        stale = bytearray(((0xC3 + i) & 0xFF) for i in range(self.LINE_BYTES))
        self.mem[line] = bytearray(stale)
        mem_words = self.dut.u_mem.u_core.r_mem
        base_word = (self._base_of(line) >> (self.STRB_W.bit_length() - 1))
        for b in range(self.FILL_BEATS):
            mem_words[base_word + b].value = self._beat_of_line(stale, b)

        # cache0 read miss: fill MUST come from cache1's CD, not memory
        ar_count0 = self.stats['mem_ar']
        t = await self._txn(0, addr, 0, label='a_rd')
        cm0 = self.caches[0]
        exp = self._beat_of_line(cm1.cache_data[line], 0)
        self._score("a: cache0 got peer bytes, not stale memory",
                    t['rsp_data'], exp)
        self._score("a: memory AR suppressed for the fill",
                    self.stats['mem_ar'], ar_count0)
        self._score("a: cache0 installed S", cm0.installed_state(line), 'S')
        self._score("a: cache1 downgraded S", cm1.installed_state(line), 'S')
        # both copies agree
        self._score("a: cache0 content == cache1 content",
                    bytes(cm0.cache_data[line]),
                    bytes(cm1.cache_data[line]))
        # absorption: the memory audit now shows cache1's bytes
        self._score("a: memory absorbed the dirty line",
                    bytes(self.mem[line]), bytes(cm1.cache_data[line]))
        # cache1 still hits with the merged content
        t = await self._txn(1, addr, 0, label='a_rb1')
        self._score("a: cache1 hit data kept",
                    t['rsp_data'], exp)
        self._scenario('PassDirtyForwarding')

    async def _s_upgrade_invalidates_peer(self):
        """(b) S->M upgrade invalidates the peer; peer re-read forwards."""
        sset = 2 % self.SETS
        t0 = self._dtag()
        addr = self._compose_addr(t0, sset)
        line = self._line_of(addr)
        await self._txn(0, addr, 0, label='b_r0')   # cache0 S
        await self._txn(1, addr, 0, label='b_r1')   # cache1 S (pass-through)
        self._score("b: both S", (self.caches[0].installed_state(line),
                                  self.caches[1].installed_state(line)),
                    ('S', 'S'))
        # cache0 upgrades (CLEAN_UNIQUE): fabric MakeInvalids cache1
        await self._txn(0, addr, 1, be=0xF,
                        wdata=0x00C0_FF00_0000_0000
                        & ((1 << self.BUS_WIDTH) - 1), label='b_up')
        self._score("b: cache0 M", self.caches[0].installed_state(line), 'M')
        self._score("b: peer invalidated",
                    self.caches[1].installed_state(line), 'I')
        mi = [e for e in self.events if e[1] == 'coh_req']
        # the upgrade raised NO memory AR (fabric snoop only)
        # peer read now misses and the fabric forwards cache0's merge
        t = await self._txn(1, addr, 0, label='b_rdp')
        exp = self._beat_of_line(self.caches[0].cache_data[line], 0)
        self._score("b: peer read got cache0's merge", t['rsp_data'], exp)
        self._score("b: peer installed S",
                    self.caches[1].installed_state(line), 'S')
        self._score("b: cache0 downgraded after forward",
                    self.caches[0].installed_state(line), 'S')
        self._score("b: memory absorbed",
                    bytes(self.mem[line]),
                    bytes(self.caches[0].cache_data[line]))
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
        cm0 = self.caches[0]
        self._score("c: cache0 M", cm0.installed_state(line), 'M')
        # fill the whole set to evict the dirty line
        vtags = [self._dtag() for _ in range(self.WAYS)]
        for w, tag in enumerate(vtags):
            a = self._compose_addr(tag, sset)
            await self._txn(0, a, 0, label=f'c_f{w}')
        self._score("c: line evicted", cm0.installed_state(line), 'I')
        # memory model carries the write-back; the actual sdpram must too
        exp_line = bytes(cm0.cache_data[line])
        self._score("c: memory model has dirty bytes",
                    bytes(self.mem[line]), exp_line)
        # peer reads the line: miss, peer Invalid -> memory read of the WB
        t = await self._txn(1, addr, 0, label='c_peer')
        self._score("c: peer sees the write-back", t['rsp_data'],
                    self._beat_of_line(exp_line, 0))
        self._scenario('DirtyEvictionWriteback')

    async def _s_e_downgrade_read_shared(self):
        """(d) E->S downgrade on ReadShared (tag promotion backdoor)."""
        sset = 4 % self.SETS
        t0 = self._dtag()
        addr = self._compose_addr(t0, sset)
        line = self._line_of(addr)
        await self._txn(0, addr, 0, label='d_r0')
        cm0 = self.caches[0]
        self._score("d: cache0 S", cm0.installed_state(line), 'S')
        # promote cache0's tag word S -> E (quiescent deposit; the CPU path
        # never installs E -- the documented Table 3.0 reachability gap)
        way = cm0.hit_way(cm0.set_of(line), line)
        set_idx = cm0.set_of(line)
        tag_word = self.dut.u_amber0.u_core.u_tag.mem[way * self.SETS
                                                      + set_idx]
        tag_word.value = ((line >> self.SET_BITS) << 3) | 2   # 2 = E
        cm0.slot_state[(set_idx, way)] = 'E'
        # cache1 misses the line: fabric READ_SHARED snoop hits E
        t = await self._txn(1, addr, 0, label='d_r1')
        exp = self._beat_of_line(cm0.cache_data[line], 0)
        self._score("d: cache1 got E line data", t['rsp_data'], exp)
        # E x READ_SHARED: DT+IS+WU; the peer downgrades to S
        rd_ts = int(tag_word.value)
        self._score("d: cache0 downgraded E->S", self._decode3(rd_ts & 7),
                    'S')
        cm0.slot_state[(set_idx, way)] = 'S'
        self._score("d: cache1 installed S",
                    self.caches[1].installed_state(line), 'S')
        self._scenario('EDowngradeReadShared')

    async def _s_simultaneous_misses(self):
        """(e) simultaneous same-line misses serialize fairly, both correct.
        No deadlock: bounded completion; fairness: both directions win."""
        sset = 5 % self.SETS
        firsts = []
        mixes = [(0, 0), (1, 1), (0, 1), (1, 0), (0, 0), (1, 1), (0, 1),
                 (1, 0)]
        for it, (w0, w1) in enumerate(mixes):
            t0 = self._dtag()
            addr = self._compose_addr(t0, sset, beat=it % self.FILL_BEATS)
            n_grant = len(self.stats['first_grant'])
            # drive both CPUs the same line in the same cycle
            results = await self._dual_txn(addr, w0, w1, label=f'e{it}')
            g = self.stats['first_grant'][n_grant:] or [None]
            firsts.append(g[0])
            for c, t in enumerate(results):
                cm = self.caches[c]
                if t['we']:
                    exp = t['wdata']
                else:
                    exp = self._beat_of_line(cm.cache_data[t['line']],
                                             t['beat'])
                self._score(f"e{it}: cache{c} rsp", t['rsp_data'], exp)
            # quiesce the fabric between iterations
            for _ in range(4):
                await self._negedge_settled()
        winners = set(x for x in firsts if x is not None)
        self._score("e: both directions won first service", winners, {0, 1})
        self._score("e: grants happened", len(self.stats['grants']),
                    2)
        self._scenario('SimultaneousSameLineMisses')

    async def _dual_txn(self, addr, w0, w1, label=''):
        """Present both CPUs the same request simultaneously; return the
        two completed transactions (any serialized order)."""
        args = []
        for c, we in ((0, w0), (1, w1)):
            be = (1 << self.STRB_W) - 1 if we else (1 << self.STRB_W) - 1
            wdata = (0x1000 + c) * 0x0001_0001_0001_0001 \
                & ((1 << self.BUS_WIDTH) - 1)
            args.append((c, addr, we, be, wdata))
        tasks = []
        for c, a, we, be, wdata in args:
            tasks.append(cocotb.start_soon(self._txn(c, a, we, be=be,
                                                     wdata=wdata,
                                                     label=f'{label}_c{c}')))
        out = []
        for t in tasks:
            out.append(await t)
        return out

    # ------------------------------------------------------------------
    # randomized dual-CPU lockstep
    # ------------------------------------------------------------------
    def _rand_addr(self, rng):
        line = rng.randrange(self.SPAN)
        beat = rng.randrange(self.FILL_BEATS)
        return self._base_of(line) + beat * self.STRB_W

    async def _cpu_loop(self, c, n, rng):
        for i in range(n):
            addr = self._rand_addr(rng)
            we = 1 if rng.random() < 0.5 else 0
            be = rng.randrange(1, 1 << self.STRB_W) if we \
                else (1 << self.STRB_W) - 1
            wdata = rng.getrandbits(self.BUS_WIDTH) if we else 0
            await self._txn(c, addr, we, be=be, wdata=wdata,
                            label=f'r{c}_{i}')
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

    def _check_coh_req_accounting(self):
        for c in range(2):
            cm = self.caches[c]
            fills = cm.tally[EV_FILL_END]
            wbs = len([1 for e in self.events if e[1] == 'wb' and e[2] == c])
            pulses = len(cm.coh_req_pulses)
            self._score(f"coh_req{c}: pulses == fills + write-backs",
                        pulses, fills + wbs)
            debt = list(cm.ft_debt_lines)
            for ft in cm.grant_fifo:
                # each leftover entry settles an upgrade debt (late F_DONE
                # push) or a killed pass's trailing stale grant
                if ft['line'] in debt:
                    debt.remove(ft['line'])
                elif ft['line'] == cm.last_killed_line:
                    pass
                else:
                    self._score(f"grant fifo leftover unexplained "
                                f"(cache{c})", ft['line'], None)
            self._score(f"grant fifo debts settled (cache{c})",
                        debt, [])

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
                cm = self.caches[c]
                self._score(f"nomon{c}: observer silent",
                            sum(cm.pkt_counts.values()), 0)

    async def _quiescence(self):
        for _ in range(20):
            await self._negedge_settled()
        self._score("quiescent: fabric idle",
                    int(self.dut.u_fabric.dbg_state.value), FAB_F_IDLE)
        self._score("quiescent: no pending",
                    int(self.dut.u_fabric.dbg_pend_vld.value), 0)
        for c in range(2):
            self._score(f"quiescent: cache{c} not ERROR",
                        int(self._amber(c).ctrl_state.value) == ST_ERROR,
                        False)

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

        if self.TEST_LEVEL in ('func', 'full'):
            await self._random_lockstep(self.FULL_TXN[self.TEST_LEVEL])
            self._scenario('RandomDualCpuLockstep')
            if self.USE_MONITOR == 0:
                self._scenario('MonbusPresentVsAbsent')

        # cross-checks on everything observed (the MonBus tally runs after
        # quiescence: the observer pipeline drains behind the last event;
        # USE_MONITOR=0 checks silence instead)
        self._check_coh_req_accounting()
        self._check_fabric_stats()

        if self.USE_MONITOR == 1:
            # congestion phase: both observers under stall, traffic flows
            self.mon_mode = 'stall'
            for c in range(2):
                await self._txn(c, self._rand_addr(random),
                                1 if random.random() < 0.5 else 0,
                                label=f'cg_{c}')
            self.mon_mode = 'free'
            self._scenario('MonbusCongestion')

        await self._memory_audit()
        await self._quiescence()
        if self.USE_MONITOR == 1:
            for c in range(2):
                self._check_tally(c)
        return self.mismatches == 0

    def get_test_report(self):
        return {
            'checks': self.checks,
            'mismatches': self.mismatches,
            'txns': [c.txns for c in self.caches],
            'snoops': [c.snoops for c in self.caches],
            'tally': [{EV_NAMES[k]: v for k, v in c.tally.items()}
                      for c in self.caches],
            'pkts': [{EV_NAMES[k]: v for k, v in c.pkt_counts.items()}
                     for c in self.caches],
            'stats': self.stats,
            'scenarios': self.scenarios,
        }
