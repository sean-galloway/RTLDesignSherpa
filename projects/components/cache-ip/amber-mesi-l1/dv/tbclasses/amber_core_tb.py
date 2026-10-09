"""
amber_core testbench

First end-to-end amber top integration (Task 9, MAS ch01 hierarchy):
amber_core composes all nine landed FUBs -- amber_cpu_frontend, amber_control
(with the pending_fill_bypass / victim leaves), amber_tag_array,
amber_data_array, amber_repl, amber_fill, amber_drain, amber_snoop_resp,
amber_monlite -- with no stubs and no harness: the DUT boundary IS the
core's external shape (CPU GAXI slave, fub_axi_* rd/wr master sides, ACE
snoop responder, MonBus, coh_req sideband). The memory side is closed with
the house CocoTBFramework AXI4 slave responders on the raw fub_axi_* pins
(shared MemoryModel -- the amber_core deliberately does not contain the
axi4_master_rd/wr transports; the amber_top rig wraps them later), the ACE
snoop port with the house snoop master, and the CPU side with the house
GAXI BFM pair.

What this suite pins (the INTEGRATION contract; the per-FUB contracts are
proven by the FUB suites):
  * init walk: cpu_req_wr_ready stays low until init_busy falls; a request
    presented mid-walk is held, never accepted early (a lookup before walk
    completion is illegal, MAS ch03 option 1). The TB model mirrors the
    walk: every slot Invalid until the walk completes.
  * first-hit latency: a cold access misses through the real AXI4 read
    path; the re-access hits in a constant, bounded number of cycles.
  * end-to-end data integrity: read data vs the MemoryModel through the
    real fill path, write merges, dirty write-backs landing in the
    MemoryModel through the real drain path.
  * oracle lockstep (Task 2 gem5-derived amber_fsm_oracle): the model is
    OBSERVATION-DRIVEN -- coherence effects land at the same observable
    state entries the DUT applies them at (victim select at MISS_VICTIM,
    the fill commit at FILL_WRITE, the write merge at the replayed
    HIT_WR), so a snoop granted at any cycle is scored against exactly the
    resolution the RTL used. Every snoop is scored at the GRANT cycle
    (hierarchical tap of the core-facing handshake): CRRESP bit-for-bit vs
    the oracle Table 3.0 decode, CD beat content vs the resolved golden
    line. Killed fills / upgrades replay through the model as second
    passes driven by the DUT's own re-observed miss states.
  * MonBus tally cross-check: the monlite packet stream counted per event
    class vs the counts derived from the model (the observer taps are
    wired at integration for the first time here); zero drops with
    monbus_ready held high; congestion phase exercises drop-and-count.

Golden models carried here (independent copies, kmap-TB rule: no shared
code with the DUT):
  memory-side line content   MemoryModel (the responders read/write it)
  cache line content         self.cache_data -- installed by fills at the
                             observed FILL_WRITE, merged by CPU writes at
                             the observed HIT_WR (D-4 merge on the replay)
  (set, way) -> line/state   self.tags / self.slot_state -- the INSTALLED
                             state view (first valid copy per line, the
                             port-B compare rule; duplicates matter: a
                             killed install leaves a dead {tag, I} slot
                             beside a live copy)
  per-line transient         self.obs -- OVERLAY ONLY (IS/IM/SM/IS_I/
                             M_I/SINK_WB_ACK), entered at the observed
                             victim select / fill launch, consumed at the
                             observed FILL_WRITE
  repl policy                LruModel / FifoModel -- victim-way parity

Levels (TEST_LEVEL):
  gate  -- InitWalk + FirstHitLatency + directed CPU sequence (miss/hit/
           upgrade/merge/dirty-eviction with memory audit) + directed
           snoop sequence (CRRESP + CD + post-snoop CPU re-verification)
  func  -- + RandomOracleLockstep (seeded random traffic, mid-miss snoops,
           responder profile switches), MonliteTallyCrossCheck,
           MonbusCongestion
  full  -- + 5k-transaction soak, snoops on most miss windows

Author: RTL Design Sherpa
Created: 2026-10-08
"""

import os
import random

import cocotb
from cocotb.triggers import RisingEdge, FallingEdge, Timer

from TBClasses.shared.tbbase import TBBase

from CocoTBFramework.components.shared.memory_model import MemoryModel
from CocoTBFramework.components.shared.flex_randomizer import FlexRandomizer
from CocoTBFramework.components.shared.field_config import FieldConfig
from CocoTBFramework.components.gaxi.gaxi_master import GAXIMaster
from CocoTBFramework.components.gaxi.gaxi_slave import GAXISlave
from CocoTBFramework.components.axi4.axi4_factories import (
    create_axi4_slave_rd,
    create_axi4_slave_wr,
)
from CocoTBFramework.components.ace.ace_factories import create_axi4ace_snoop_master
from CocoTBFramework.components.ace.ace_transaction import SnoopType

from projects.components.cache_ip.amber_mesi_l1.dv.golden.amber_fsm_oracle import (
    SNOOP_CODES,
    step as oracle_step,
)


# ctrl_state_t codes (amber_pkg) -- kept textual for log messages
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

# MonBus event codes (amber_pkg.amber_event_t)
EV_HIT, EV_MISS, EV_SNOOP, EV_EVICT, EV_TRANSITION, \
    EV_FILL_START, EV_FILL_END, EV_DRAIN_START, EV_DRAIN_END, \
    EV_DROPPED = range(0xA)
EV_NAMES = {EV_HIT: 'HIT', EV_MISS: 'MISS', EV_SNOOP: 'SNOOP',
            EV_EVICT: 'EVICT', EV_TRANSITION: 'TRANSITION',
            EV_FILL_START: 'FILL_START', EV_FILL_END: 'FILL_END',
            EV_DRAIN_START: 'DRAIN_START', EV_DRAIN_END: 'DRAIN_END',
            EV_DROPPED: 'DROPPED'}

# amber_ace_req_t encodings (amber_pkg): coherence sideband types
ACE_READ_SHARED, ACE_READ_UNIQUE, ACE_CLEAN_UNIQUE = 0, 1, 2
ACE_WRITE_BACK = 4

# oracle snoop name -> framework ACE snoop type (IHI0022 ACSNOOP encodings);
# the internal 3-bit tap encoding is just SNOOP_CODES inverted
SNOOP_FRAMEWORK = {
    'SNOOP_READ_ONCE': SnoopType.READ_ONCE,
    'SNOOP_READ_SHARED': SnoopType.READ_SHARED,
    'SNOOP_READ_UNIQUE': SnoopType.READ_UNIQUE,
    'SNOOP_CLEAN_SHARED': SnoopType.CLEAN_SHARED,
    'SNOOP_CLEAN_INVALID': SnoopType.CLEAN_INVALID,
    'SNOOP_MAKE_INVALID': SnoopType.MAKE_INVALID,
}
NAME_BY_CODE = {code: name for name, code in SNOOP_CODES.items()}

# amber_repl_t encodings this TB models
REPL_LRU, REPL_FIFO = 0, 2

# CRRESP bit 0 = DataTransfer (amber_pkg localparam)
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

    def hit(self, s, way):
        self.update(s, way)


class FifoModel:
    """Ring parity model: victim = ring head; an install overwrites the
    head slot and advances (amber_repl FIFO semantics; hits never reorder;
    exact because fills install into the victim way)."""

    def __init__(self, sets, ways):
        self.sets, self.ways = sets, ways
        self.ring = [[w for w in range(ways)] for _ in range(sets)]
        self.head = [0] * sets

    def victim(self, s):
        return self.ring[s][self.head[s]]

    def update(self, s, way):
        self.ring[s][self.head[s]] = way
        self.head[s] = (self.head[s] + 1) % self.ways

    def hit(self, s, way):
        pass   # hits do not reorder a FIFO (amber_repl FIFO semantics)


def _parse_packet(pkt):
    """monitor_common_pkg 128-bit layout (independent scored copy)."""
    return {
        'pkt_type': (pkt >> 124) & 0xF,
        'protocol': (pkt >> 105) & 0xF,
        'event_code': (pkt >> 97) & 0xFF,
        'agent_id': (pkt >> 72) & 0xFFFF,
        'unit_id': (pkt >> 64) & 0xFF,
        'data': pkt & ((1 << 64) - 1),
    }


class AmberCoreTB(TBBase):
    """Scores the amber_core integration against the oracle + content models."""

    FULL_TXN = {'gate': 0, 'func': 400, 'full': 5000}
    RSP_TIMEOUT_CYCLES = 3000

    # responder timing profiles (house FlexRandomizer shapes; same set as
    # the amber_fill/amber_drain unit suite)
    PROFILES = {
        'fast':   {'ready': ([(0, 0)], [1.0]),
                   'resp':  ([(0, 0)], [1.0])},
        'normal': {'ready': ([(0, 2), (3, 5)], [0.7, 0.3]),
                   'resp':  ([(0, 2), (3, 6)], [0.6, 0.4])},
        'slow':   {'ready': ([(1, 4), (5, 10)], [0.6, 0.4]),
                   'resp':  ([(2, 6), (7, 12)], [0.5, 0.5])},
    }

    def __init__(self, dut, **kwargs):
        super().__init__(dut)
        self.SEED = self.convert_to_int(os.environ.get('SEED', '12345'))
        self.TEST_LEVEL = os.environ.get('TEST_LEVEL', 'gate').lower()
        random.seed(self.SEED)

        # geometry (the grid varies all four; REPL_POLICY selects the model)
        self.SETS = int(os.environ.get('SETS', '128'))
        self.WAYS = int(os.environ.get('WAYS', '4'))
        self.ADDR_WIDTH = 32
        self.LINE_BYTES = int(os.environ.get('LINE_BYTES', '64'))
        self.BUS_WIDTH = int(os.environ.get('BUS_WIDTH', '64'))
        self.REPL_POLICY = int(os.environ.get('REPL_POLICY', '0'))
        self.STRB_W = self.BUS_WIDTH // 8
        self.FILL_BEATS = self.LINE_BYTES // self.STRB_W
        self.SET_BITS = (self.SETS - 1).bit_length()
        self.OFFSET_BITS = (self.LINE_BYTES - 1).bit_length()
        self.SET_MASK = self.SETS - 1
        self.LINE_MASK = (1 << (self.ADDR_WIDTH - self.OFFSET_BITS)) - 1
        self.CPU_REQ_W = self.ADDR_WIDTH + 1 + self.STRB_W + self.BUS_WIDTH

        # bounded working set: enough lines to force evictions at every
        # geometry AND enough tag-space for the directed scenarios
        # (MAX_TAG = SPAN/SETS - 1 must cover the ~WAYS+8 directed tags),
        # small enough to pre-fill and audit cheaply
        self.SPAN = min(max(self.SETS * 16, 64), 8192)
        assert self.SPAN >= (self.WAYS + 10) * self.SETS, \
            "SPAN too small for the directed tag budget"

        # golden models; the MemoryModel covers every address the directed
        # scenarios compose (tags shifted by the set/offset fields), not
        # just the pre-filled random working set
        self.memory_model = MemoryModel(
            num_lines=1 << 20,
            bytes_per_line=self.STRB_W,
            log=self.log,
        )
        self.cache_data = {}
        self.tags = {}
        self.slot_state = {}
        self.obs = {}            # transient overlay only (see docstring)
        self.repl = (LruModel(self.SETS, self.WAYS)
                     if self.REPL_POLICY == REPL_LRU
                     else FifoModel(self.SETS, self.WAYS))
        self.pend_line = None
        self.pend_eff = None

        # in-flight transaction context (the blocking pipeline allows one)
        self.cur_txn = None

        # observation log + scorekeeping
        self.events = []
        self.cyc = 0
        self.rsp_log = []
        self.checks = 0
        self.mismatches = 0
        self.txns = 0
        self.snoops = 0
        self.coh_req_count = 0
        self.scenarios = {}

        # expected MonBus tally vs received packet counts
        self.tally = {ev: 0 for ev in EV_NAMES}
        self.pkt_counts = {ev: 0 for ev in EV_NAMES}
        self._drop_reports = 0
        self.mon_mode = 'free'   # free / stall / random

        # snoop grant observations: the monitor records (and model-steps)
        # each grant; the driver scores the BFM result against it (snoops
        # are serialized, so the oldest outstanding grant is this snoop's)
        self.grant_log = []

        # directed-scenario tag allocator: tags map to lines inside the
        # pre-filled (initialized) memory span -- line = tag << SET_BITS | set
        self.MAX_TAG = (self.SPAN >> self.SET_BITS) - 1
        self._tag_next = 0

        self.log.info(f"AmberCoreTB sets={self.SETS} ways={self.WAYS} "
                      f"line={self.LINE_BYTES} bus={self.BUS_WIDTH} "
                      f"repl={self.REPL_POLICY} level={self.TEST_LEVEL} "
                      f"seed={self.SEED}")

    # ------------------------------------------------------------------
    # helpers
    # ------------------------------------------------------------------
    def _score(self, what, got, exp):
        self.checks += 1
        if got != exp:
            self.mismatches += 1
            if self.mismatches <= 30:
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
        # the landed control-suite idiom: builds the line-aligned BASE
        # ADDRESS directly (tag in its field, set in its field, zeros in
        # the offset); _line_of() recovers the line number
        line = (tag << (self.SET_BITS + self.OFFSET_BITS)) \
            | ((set_idx & self.SET_MASK) << self.OFFSET_BITS)
        return line \
            | ((beat & (self.FILL_BEATS - 1)) << (self.STRB_W.bit_length() - 1))

    def _dtag(self):
        """Next directed-scenario tag (maps inside the pre-filled span)."""
        self._tag_next += 1
        if self._tag_next > self.MAX_TAG:
            raise RuntimeError("directed scenario tag budget exhausted")
        return self._tag_next

    def _default_line(self, line):
        return bytes(((line + 0x11 * i) & 0xFF) for i in range(self.LINE_BYTES))

    def _mem_line(self, line):
        return bytes(self.memory_model.read(self._base_of(line),
                                            self.LINE_BYTES))

    def _beat_of_line(self, line_data, beat):
        lo = beat * self.STRB_W
        return int.from_bytes(bytes(line_data[lo:lo + self.STRB_W]), 'little')

    def _pack_req(self, addr, we, be, wdata):
        return ((addr & ((1 << self.ADDR_WIDTH) - 1))
                << (1 + self.STRB_W + self.BUS_WIDTH)) \
            | ((we & 1) << (self.STRB_W + self.BUS_WIDTH)) \
            | ((be & ((1 << self.STRB_W) - 1)) << self.BUS_WIDTH) \
            | (wdata & ((1 << self.BUS_WIDTH) - 1))

    def _hit_way(self, set_idx, line):
        """First way holding the tag in a VALID slot state -- mirrors the
        DUT hit compare (a snoop invalidate leaves the tag in place with
        state I; matching on the tag alone would return the dead slot)."""
        for w in range(self.WAYS):
            if (self.tags.get((set_idx, w)) == line
                    and self.slot_state.get((set_idx, w), 'I') != 'I'):
                return w
        return None

    def _slot_of(self, set_idx, line):
        """The way holding `line`'s tag in `set_idx` (valid or not)."""
        for w in range(self.WAYS):
            if self.tags.get((set_idx, w)) == line:
                return w
        return None

    # ------------------------------------------------------------------
    # line-state view: self.obs is a TRANSIENT OVERLAY (pending fills,
    # in-flight victims) only; the installed state of a line is derived
    # from the tag/slot arrays -- duplicates matter: a killed install
    # leaves a dead {tag, I} slot beside a live copy, and evicting the
    # dead slot must not invalidate the live line
    # ------------------------------------------------------------------
    def _installed_state(self, line):
        set_idx = self._set_of_line(line)
        for w in range(self.WAYS):
            if (self.tags.get((set_idx, w)) == line
                    and self.slot_state.get((set_idx, w), 'I') != 'I'):
                return self.slot_state[(set_idx, w)]
        return 'I'

    def _cur_state(self, line):
        st = self.obs.get(line)
        if st is not None:
            return st
        return self._installed_state(line)

    @staticmethod
    def _decode3(code):
        return {0: 'I', 1: 'S', 2: 'E', 3: 'M'}.get(code, f'RSV{code}')

    # ------------------------------------------------------------------
    # clock/reset/BFMs
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
        master_rand = soak_delay if self.TEST_LEVEL == 'full' else zero_delay

        self.master = GAXIMaster(
            dut=d, title='cpu_req', prefix='',
            clock=d.clk, field_config=req_fields,
            timeout_cycles=self.RSP_TIMEOUT_CYCLES,
            mode='skid', bus_name='cpu_req_wr', pkt_prefix='',
            multi_sig=False, randomizer=master_rand, log=self.log)
        self.slave = GAXISlave(
            dut=d, title='cpu_rsp', prefix='',
            clock=d.clk, field_config=rsp_fields,
            timeout_cycles=self.RSP_TIMEOUT_CYCLES,
            mode='skid', bus_name='cpu_rsp_rd', pkt_prefix='',
            multi_sig=False,
            randomizer=FlexRandomizer({'ready_delay': ([(0, 0)], [1])}),
            log=self.log)
        self.slave.add_callback(self._on_rsp)
        self.slave.set_ready_policy('always')

        # memory side: house AXI4 responders on the raw fub_axi_* pins
        self.rd_components = create_axi4_slave_rd(
            dut=d, clock=d.clk, prefix='fub_axi', log=self.log,
            id_width=8, addr_width=self.ADDR_WIDTH,
            data_width=self.BUS_WIDTH, user_width=1,
            memory_model=self.memory_model)
        self.ar_slave = self.rd_components['AR']
        self.r_master = self.rd_components['R']
        self.wr_components = create_axi4_slave_wr(
            dut=d, clock=d.clk, prefix='fub_axi', log=self.log,
            id_width=8, addr_width=self.ADDR_WIDTH,
            data_width=self.BUS_WIDTH, user_width=1,
            memory_model=self.memory_model)
        self.aw_slave = self.wr_components['AW']
        self.w_slave = self.wr_components['W']
        self.b_master = self.wr_components['B']

        # ACE snoop master on the snoop responder port
        self.snoop_master = create_axi4ace_snoop_master(
            dut=d, clock=d.clk, prefix='m_axi_', log=self.log,
            ifc_name='sn', addr_width=self.ADDR_WIDTH,
            data_width=self.BUS_WIDTH)['interface']

        # monbus
        d.mon_ready.value = 1

        # deterministic memory content across the working set
        for line in range(self.SPAN):
            self.memory_model.write(self._base_of(line),
                                    bytearray(self._default_line(line)))

        await self.assert_reset()
        cocotb.start_soon(self._monitor())
        cocotb.start_soon(self._monbus_ready_driver())
        await self.wait_clocks('clk', 3)
        await self.deassert_reset()
        self.set_profile('fast')

    async def assert_reset(self):
        self.dut.rst_n.value = 0

    async def deassert_reset(self):
        self.dut.rst_n.value = 1

    def set_profile(self, name):
        cfg = self.PROFILES[name]
        self.ar_slave.set_randomizer(FlexRandomizer({'ready_delay': cfg['ready']}))
        self.aw_slave.set_randomizer(FlexRandomizer({'ready_delay': cfg['ready']}))
        self.w_slave.set_randomizer(FlexRandomizer({'ready_delay': cfg['ready']}))
        self.r_master.set_randomizer(FlexRandomizer({'valid_delay': cfg['resp']}))
        self.b_master.set_randomizer(FlexRandomizer({'valid_delay': cfg['resp']}))

    def _on_rsp(self, packet):
        data = int(getattr(packet, 'fields', {}).get('data', 0))
        self.rsp_log.append((self.cyc, data))

    async def _negedge_settled(self):
        await FallingEdge(self.dut.clk)
        await Timer(500, units='ps')

    # ------------------------------------------------------------------
    # monitor: state transitions (model effects), accepts, grants, monbus
    # ------------------------------------------------------------------
    async def _monitor(self):
        d = self.dut
        prev_state = -1
        while True:
            await FallingEdge(d.clk)
            await Timer(100, units='ps')
            self.cyc += 1
            d.mon_time.value = self.cyc

            st = int(d.ctrl_state.value)
            if st != prev_state:
                self.events.append((self.cyc, 'state', st))
                self._on_state_entry(st)
                prev_state = st

            if int(d.cpu_req_wr_valid.value) and int(d.cpu_req_wr_ready.value):
                packed = int(d.cpu_req_wr_data.value)
                wdata = packed & ((1 << self.BUS_WIDTH) - 1)
                be = (packed >> self.BUS_WIDTH) & ((1 << self.STRB_W) - 1)
                we = (packed >> (self.BUS_WIDTH + self.STRB_W)) & 1
                addr = (packed >> (self.BUS_WIDTH + self.STRB_W + 1)) \
                    & ((1 << self.ADDR_WIDTH) - 1)
                self.events.append((self.cyc, 'accept',
                                    {'addr': addr, 'we': we, 'be': be,
                                     'wdata': wdata}))

            if int(d.coh_req_valid.value):
                self.coh_req_count += 1
                self.events.append((self.cyc, 'coh_req', {
                    'addr': int(d.coh_req_addr.value),
                    'type': int(d.coh_req_type.value)}))

            # snoop grant: model-step at the grant cycle -- the DUT state
            # sampled here is exactly the resolution the RTL used
            if int(d.u_snoop.ctrl_snoop_req.value) \
                    and int(d.u_control.ctrl_snoop_ready.value):
                self._on_snoop_grant(st)

            if int(d.mon_valid.value) and int(d.mon_ready.value):
                p = _parse_packet(int(d.mon_packet.value))
                self.pkt_counts[p['event_code']] += 1
                if p['event_code'] == EV_DROPPED:
                    self._drop_reports += 1

    # ------------------------------------------------------------------
    # observation-driven model: coherence effects land at the same
    # observable state entries the DUT applies them at
    # ------------------------------------------------------------------
    def _on_state_entry(self, st):
        txn = self.cur_txn
        if txn is None:
            return
        line = txn['line']
        if st == ST_MISS_VICTIM and not txn['victim_done']:
            txn['victim_done'] = True
            self._model_victim_select(txn)
        elif st == ST_MISS_FILL:
            # FILL_START fires per MISS_FILL ENTRY: a snoop detour leaves
            # and re-enters the state (MAS ch04 emit point is the entry)
            self.tally[EV_FILL_START] += 1
            if txn['fill_modeled']:
                return
            txn['fill_modeled'] = True
            # an upgrade reaches MISS_FILL with NO preceding MISS_VICTIM;
            # anything that passed MISS_VICTIM is a true miss (this also
            # covers a pre-launch-killed upgrade: the replayed LOOKUP saw
            # the invalidated line and took the miss path)
            upgrade_pass = not txn['victim_done'] or txn['victim'] is None
            txn['pass_upgrade'] = upgrade_pass
            self.obs[line] = 'SM' if upgrade_pass else \
                ('IS' if not txn['we'] else 'IM')
            # the victim's line is gone from this point (write-back
            # completed before the fill launched, or a clean victim's slot
            # is being overwritten): snoops answer Invalid (stale). The
            # overlay applies only when the victim slot held the line's
            # LAST VALID copy -- a dead duplicate slot says nothing about
            # a live copy elsewhere.
            vic = txn.get('victim')
            if vic and vic['line'] != line and vic.get('overlay'):
                self.obs[vic['line']] = 'I'
        elif st == ST_MISS_DRAIN:
            # DRAIN_START fires per MISS_DRAIN ENTRY (snoop detours
            # re-enter); the EVICT/DRAIN_END pair books at the select
            self.tally[EV_DRAIN_START] += 1
        elif st == ST_FILL_WRITE:
            # the fill commit: install {tag, state} exactly here, the
            # cycle the DUT writes the tag array
            self._model_pass_commit(txn)
        elif st == ST_HIT_RD:
            way = self._hit_way(txn['set_idx'], line)
            if way is not None:
                self.repl.hit(txn['set_idx'], way)
        elif st == ST_HIT_WR:
            # the write merge (D-4) lands with the hit service; E->M
            # promotion writes the tag here too (amber never installs E,
            # so pre is M in practice -- kept for completeness)
            self._model_merge(txn)

    def _model_merge(self, txn):
        line = txn['line']
        pre = self._installed_state(line)
        if txn['we']:
            if txn['be']:
                line_data = self.cache_data[line]
                lo = txn['beat'] * self.STRB_W
                for i in range(self.STRB_W):
                    if txn['be'] & (1 << i):
                        line_data[lo + i] = (txn['wdata'] >> (8 * i)) & 0xFF
            if pre == 'E':
                self.tally[EV_TRANSITION] += 1
                way = self._hit_way(txn['set_idx'], line)
                if way is not None:
                    self.slot_state[(txn['set_idx'], way)] = 'M'
        way = self._hit_way(txn['set_idx'], line)
        if way is not None:
            self.repl.hit(txn['set_idx'], way)

    def _model_victim_select(self, txn):
        """Predict the victim way from the repl model; book the eviction
        (victim-line transient, MISS/EVICT/DRAIN tallies)."""
        set_idx = txn['set_idx']
        way = self.repl.victim(set_idx)
        # victim-way parity with the DUT's repl engine: a divergence here
        # poisons every eviction prediction downstream
        self._score(f"{txn['label']}: victim way parity", way,
                    int(self.dut.u_repl.repl_victim_way.value))
        vline = self.tags.get((set_idx, way))
        vstate = self.slot_state.get((set_idx, way), 'I')
        dut_ts = int(self.dut.u_tag.mem[way * self.SETS + set_idx].value)
        dut_tag, dut_state = dut_ts >> 3, self._decode3(dut_ts & 7)
        # NB: the model's tags map (set, way) -> LINE NUMBER; the array
        # word is {tag, state} with tag = line >> SET_BITS
        exp_tag = (vline >> self.SET_BITS) if vline is not None else 0
        self._score(f"{txn['label']}: victim slot parity",
                    (exp_tag, vstate), (dut_tag, dut_state))
        # a same-tag victim slot is a killed-install duplicate (state I by
        # construction -- a valid copy would have hit); the pending line
        # owns the slot again, it is not an eviction
        if vline == txn['line']:
            txn['victim'] = {'way': way, 'line': vline, 'dirty': False,
                             'overlay': False}
            self.tally[EV_MISS] += 1
            return
        dirty = vstate == 'M'
        live = vstate in ('S', 'E', 'M')   # last-copy vs dead duplicate
        txn['victim'] = {'way': way, 'line': vline, 'dirty': dirty,
                         'overlay': live}
        self.tally[EV_MISS] += 1
        if dirty:
            # the depth-1 buffer owns the line until the WB ack; mid-drain
            # snoops compose through M_I/SINK_WB_ACK
            self.obs[vline] = 'M_I'
            self.tally[EV_EVICT] += 1
            self.tally[EV_DRAIN_END] += 1
        elif live:
            self.obs[vline] = 'I'

    def _model_pass_commit(self, txn):
        """The FILL_WRITE commit of the current pass: install {tag, state}
        at the victim way (upgrade: the hit way), consume the post-commit
        snoop effect, snapshot the fill data. A killed pass commits
        Invalid and the DUT's own re-observed miss states drive the next
        pass -- no model-side refetch exists."""
        line = txn['line']
        set_idx = txn['set_idx']
        pend = self.pend_eff if self.pend_line == line else None
        if self.pend_line == line:
            self.pend_line = None
            self.pend_eff = None
        if txn['pass_upgrade']:
            # the S slot stays installed during the upgrade; the commit
            # rewrites the HIT way -- the first VALID copy (a killed
            # install may leave a dead {tag, I} duplicate at an earlier
            # way; _slot_of would pick the corpse)
            way = self._hit_way(set_idx, line)
            if way is None:
                way = self._slot_of(set_idx, line)
            state = 'I' if txn['killed'] else 'M'
            if way is not None:
                self.slot_state[(set_idx, way)] = state
                self.repl.hit(set_idx, way)
            if not txn['killed']:
                # no cache_data re-snapshot: the upgrade only flips the
                # tag state S->M; the data array (and the model's
                # content) keep every merge already landed -- only the
                # replayed merge (observed HIT_WR) updates it
                pass
        else:
            transient = self.obs.get(line, 'IM')
            if transient == 'IS_I':
                committed = 'I'
            elif transient in ('IS', 'SM'):
                committed = pend or 'S'
            else:                       # IM installs M
                committed = pend or 'M'
            victim = txn['victim']
            way = victim['way']
            self.tags[(set_idx, way)] = line
            self.slot_state[(set_idx, way)] = committed
            self.cache_data[line] = bytearray(self._mem_line(line))
            self.repl.update(set_idx, way)
        self.obs.pop(line, None)
        vic = txn.get('victim')
        if vic and vic.get('overlay'):
            self.obs.pop(vic['line'], None)
        self.tally[EV_FILL_END] += 1
        self.tally[EV_TRANSITION] += 1
        # a killed pass (or a downgrade-pending commit) replays: the DUT
        # re-observes its own MISS_VICTIM / MISS_FILL; reopen the hooks
        # and clear the per-pass kill flag
        txn['victim_done'] = False
        txn['fill_modeled'] = False
        txn['victim'] = None
        txn['killed'] = False

    # ------------------------------------------------------------------
    # snoop model: oracle step at the grant cycle
    # ------------------------------------------------------------------
    def _on_snoop_grant(self, dut_state):
        d = self.dut
        line = self._line_of(int(d.u_snoop.ctrl_snoop_addr.value))
        name = NAME_BY_CODE[int(d.u_snoop.ctrl_snoop_type.value)]
        st = self._cur_state(line)
        fill = 'S' if st in ('IS', 'IS_I') else None
        pend = self.pend_eff if self.pend_line == line else None
        res = oracle_step(st, name, fill=fill, pending=pend)
        if res.pending is not None:
            self.pend_line, self.pend_eff = line, res.pending
        # expected CD content for DataTransfer responses
        exp_line = None
        if (res.crresp >> CRRESP_DT) & 1:
            if st in ('IS', 'IS_I', 'SM', 'IM'):
                # the pending fill serves its beats out of the data array
                # as they arrive (bypass) == memory-side content; a
                # Shared-domain install never transfers
                exp_line = self._mem_line(line)
            else:
                # installed line or the in-flight dirty victim: the array /
                # the victim buffer holds the (merged) cache content
                exp_line = bytes(self.cache_data.get(
                    line, bytearray(self.LINE_BYTES)))
        self.grant_log.append({'cyc': self.cyc, 'line': line, 'name': name,
                               'state': st, 'exp_crresp': res.crresp,
                               'exp_line': exp_line})
        self.tally[EV_SNOOP] += 1
        # installed-line state change: the service writes the tag on its
        # own port-A cycle (pending-line / victim answers never do); the
        # state lives in the slot arrays (first VALID copy, matching the
        # port-B compare) -- transient overlays keep the oracle result
        if st in ('S', 'E', 'M'):
            if res.next_state != st:
                self.tally[EV_TRANSITION] += 1
                set_idx = self._set_of_line(line)
                way = self._hit_way(set_idx, line)
                if way is not None:
                    self.slot_state[(set_idx, way)] = res.next_state
        else:
            self.obs[line] = res.next_state
        # kill bookkeeping: a snoop whose effect invalidates the pending
        # install (the pass commits Invalid and the pipeline re-fetches)
        txn = self.cur_txn
        if txn is not None and line == txn['line'] \
                and st in ('IS', 'IM', 'SM', 'IS_I'):
            if (st == 'SM' and res.next_state == 'IM') \
                    or (st in ('IS', 'IM') and res.pending == 'I') \
                    or (st == 'IS_I'):
                txn['killed'] = True

    async def _snoop(self, line, name, label=''):
        """Issue one snoop through the real ACE port; the monitor has
        already recorded (and model-stepped) the grant expectation."""
        n_grants = len(self.grant_log)
        result = await self.snoop_master.issue_snoop(
            self._base_of(line), SNOOP_FRAMEWORK[name])
        self.snoops += 1
        while len(self.grant_log) <= n_grants:
            await self._negedge_settled()
        exp = self.grant_log[n_grants]
        self._score(f"{label} crresp", result.crresp.value,
                    exp['exp_crresp'])
        if (exp['exp_crresp'] >> CRRESP_DT) & 1:
            self._score(f"{label} beat count", len(result.data),
                        self.FILL_BEATS)
            for b in range(min(len(result.data), self.FILL_BEATS)):
                self._score(f"{label} beat{b} data", result.data[b],
                            self._beat_of_line(exp['exp_line'], b))
        else:
            self._score(f"{label} no CD beats", len(result.data), 0)

    # ------------------------------------------------------------------
    # monbus driver
    # ------------------------------------------------------------------
    async def _monbus_ready_driver(self):
        d = self.dut
        while True:
            await FallingEdge(d.clk)
            if self.mon_mode == 'free':
                d.mon_ready.value = 1
            elif self.mon_mode == 'stall':
                d.mon_ready.value = 0
            else:  # random
                d.mon_ready.value = 1 if random.random() < 0.65 else 0

    # ------------------------------------------------------------------
    # transaction driver
    # ------------------------------------------------------------------
    async def _txn_begin(self, addr, we, be, wdata, label=''):
        line = self._line_of(addr)
        beat = (addr >> (self.STRB_W.bit_length() - 1)) & (self.FILL_BEATS - 1)
        # issue-time hint for the snoop plan only; the model follows the
        # DUT's observed states
        pre = self._cur_state(line)
        hint = oracle_step(pre, 'CPU_WR' if we else 'CPU_RD')
        txn = {'addr': addr, 'line': line, 'beat': beat, 'we': we, 'be': be,
               'wdata': wdata, 'label': label,
               'set_idx': self._set_of_line(line),
               'hit': hint.result == 'HIT',
               'upgrade': hint.req == 'CLEAN_UNIQUE',
               'pass_upgrade': False,
               'killed': False, 'victim': None,
               'victim_done': False, 'fill_modeled': False}
        self.cur_txn = txn
        txn['n_rsp'] = len(self.rsp_log)
        n_accept = len([1 for _, k, _ in self.events if k == 'accept'])
        pkt = self.master.create_packet(data=self._pack_req(addr, we, be, wdata))
        await self.master.send(pkt)
        for _ in range(self.RSP_TIMEOUT_CYCLES):
            accepts = [e for e in self.events if e[1] == 'accept']
            if len(accepts) >= n_accept + 1:
                break
            await self._negedge_settled()
        else:
            raise RuntimeError(f"{label}: request never accepted; state="
                               f"{int(self.dut.ctrl_state.value):#x}")
        txn['accept_cyc'] = accepts[-1][0]
        return txn

    async def _txn_end(self, txn):
        """Await the response; the model already committed at the observed
        FILL_WRITE / HIT_WR, so the response is scored against the final
        state."""
        n_rsp = txn['n_rsp']
        for _ in range(self.RSP_TIMEOUT_CYCLES):
            if len(self.rsp_log) >= n_rsp + 1:
                break
            await self._negedge_settled()
        else:
            raise RuntimeError(
                f"{txn['label']}: response timeout; state="
                f"{int(self.dut.ctrl_state.value):#x}")
        rsp_cyc, rsp_data = self.rsp_log[n_rsp]
        txn['rsp_cyc'] = rsp_cyc
        txn['rsp_data'] = rsp_data

        if txn['we']:
            exp = txn['wdata']
        else:
            exp = self._beat_of_line(self.cache_data[txn['line']],
                                     txn['beat'])
        self._score(f"{txn['label']} rsp data", rsp_data, exp)

        self.tally[EV_HIT] += 1
        self.txns += 1
        self.cur_txn = None
        return txn

    async def _txn(self, addr, we, be=None, wdata=None, label='',
                   snoops=()):
        if be is None:
            be = random.randrange(1, 1 << self.STRB_W) if we \
                else (1 << self.STRB_W) - 1
        if wdata is None:
            wdata = random.getrandbits(self.BUS_WIDTH) if we else 0
        txn = await self._txn_begin(addr, we, be, wdata, label)
        for snoop_line, snoop_name in snoops:
            await self._snoop(snoop_line, snoop_name,
                              label=f"{label}:{snoop_name}")
        return await self._txn_end(txn)

    # ------------------------------------------------------------------
    # scenario: init walk
    # ------------------------------------------------------------------
    async def _s_init_walk(self):
        d = self.dut
        cycles = 0
        saw_low = False
        # present a request mid-walk: the GAXI master holds valid until the
        # walk completes -- an early accept is the illegal-lookup bug
        send_task = cocotb.start_soon(self.master.send(
            self.master.create_packet(
                data=self._pack_req(self._compose_addr(0, 0), 0,
                                    (1 << self.STRB_W) - 1, 0))))
        while True:
            await self._negedge_settled()
            cycles += 1
            if cycles > self.SETS * 4 + 200:
                raise RuntimeError("init walk never completed")
            busy = int(d.init_busy.value)
            if busy:
                saw_low = True
                self._score("init: cpu_req_wr_ready low while init busy",
                            int(d.cpu_req_wr_ready.value), 0)
                self._score("init: no accept while init busy",
                            any(e[1] == 'accept' for e in self.events),
                            False)
            else:
                if int(d.cpu_req_wr_ready.value):
                    break
        await send_task   # the held request is accepted after the walk
        self._score("init: ready observed low during walk", saw_low, True)
        self._score("init: walk bounded", cycles <= self.SETS + 20, True)
        # fold the probe transaction into the models: it read a cold line
        # (a miss), installed it Shared at the predicted victim way; the
        # observed-state hooks stayed inert (cur_txn was None), so this is
        # a manual replay of the same bookkeeping
        n_rsp = len(self.rsp_log)
        for _ in range(self.RSP_TIMEOUT_CYCLES):
            if len(self.rsp_log) >= n_rsp + 1:
                break
            await self._negedge_settled()
        line = self._line_of(self._compose_addr(0, 0))
        set_idx = self._set_of_line(line)
        way = self.repl.victim(set_idx)
        self.tags[(set_idx, way)] = line
        self.slot_state[(set_idx, way)] = 'S'
        self.cache_data[line] = bytearray(self._mem_line(line))
        self.repl.update(set_idx, way)
        # the probe's observable events (monlite packets fired for real):
        # fold them into the expected tally so the cross-check stays exact
        self.tally[EV_HIT] += 1
        self.tally[EV_MISS] += 1
        self.tally[EV_FILL_START] += 1
        self.tally[EV_FILL_END] += 1
        self.tally[EV_TRANSITION] += 1
        self.txns += 1
        self.cur_txn = None
        self._scenario('InitWalk')

    # ------------------------------------------------------------------
    # scenario: first-hit latency
    # ------------------------------------------------------------------
    async def _s_first_hit_latency(self):
        addr = self._compose_addr(self._dtag(), 0)
        # cold: miss through the real fill path
        cold = await self._txn(addr, 0, label='lat_cold')
        miss_lat = cold['rsp_cyc'] - cold['accept_cyc']
        # warm: constant-latency hits
        lat0 = None
        for i in range(20):
            t = await self._txn(addr, 0, label=f'lat{i}')
            lat = t['rsp_cyc'] - t['accept_cyc']
            if lat0 is None:
                lat0 = lat
            self._score(f"lat{i}: hit latency constant", lat, lat0)
        self._score("hit latency bounded", 2 <= lat0 <= 12, True)
        self._score("cold access slower than a hit", miss_lat >= lat0 + 5,
                    True)
        self._scenario('FirstHitLatency')

    # ------------------------------------------------------------------
    # scenario: directed CPU sequence
    # ------------------------------------------------------------------
    async def _s_directed_sequence(self):
        sset = 1 % self.SETS
        t0 = self._dtag()
        base = self._compose_addr(t0, sset)
        # read miss -> S, fill data vs memory
        await self._txn(base, 0, label='d_miss')
        # read hit
        await self._txn(base + (1 % self.FILL_BEATS) * self.STRB_W, 0,
                        label='d_hit')
        # write hit on S: upgrade (CLEAN_UNIQUE, no fetch); rsp = wdata
        await self._txn(base, 1, be=0x5,
                        wdata=0xA5A5_0000_0000_0000
                        & ((1 << self.BUS_WIDTH) - 1),
                        label='d_upgr')
        # write hit on M: merge; read back the merged bytes
        await self._txn(base, 1, be=0x3, wdata=0x1234, label='d_whit')
        await self._txn(base, 0, label='d_rb')
        # dirty eviction: fill every way of the set dirty, then miss a new
        # line in the same set -- the evicted lines' write-backs must land
        # in the memory model
        vtags = [self._dtag() for _ in range(self.WAYS)]
        for w, tag in enumerate(vtags):
            a = self._compose_addr(tag, sset)
            await self._txn(a, 0, label=f'd_vr{w}')
            await self._txn(a, 1, be=(1 << self.STRB_W) - 1,
                            wdata=(0xD0 + w) * 0x0101_0101_0101_0101
                            & ((1 << self.BUS_WIDTH) - 1),
                            label=f'd_vw{w}')
        victims = {}
        for (s, w), line in self.tags.items():
            if s == sset and self.slot_state.get((s, w)) == 'M':
                victims[line] = bytes(self.cache_data[line])
        await self._txn(self._compose_addr(self._dtag(), sset), 0,
                        label='d_evict')
        for line, content in victims.items():
            if self._installed_state(line) != 'I':
                continue    # still installed; not evicted by d_evict
            self._score(f"dirty victim {line:#x} written back",
                        self._mem_line(line), content)
        self._scenario('DirectedSequence')

    # ------------------------------------------------------------------
    # scenario: directed snoop sequence
    # ------------------------------------------------------------------
    async def _s_snoop_sequence(self):
        sset = 2 % self.SETS
        # install an M line
        m_addr = self._compose_addr(self._dtag(), sset)
        m_line = self._line_of(m_addr)
        await self._txn(m_addr, 0, label='s_inst')
        await self._txn(m_addr, 1, be=(1 << self.STRB_W) - 1,
                        wdata=0x0BAD_0000_0000_0000
                        & ((1 << self.BUS_WIDTH) - 1), label='s_dirty')
        # READ_SHARED on M: DT+PD+IS, data out, downgrade to S
        await self._snoop(m_line, 'SNOOP_READ_SHARED', label='s_rs')
        self._score("s_rs: line downgraded", self._installed_state(m_line),
                    'S')
        t = await self._txn(m_addr, 0, label='s_rd_after')
        self._score("s_rs: CPU read still hits, content kept",
                    t['rsp_data'],
                    self._beat_of_line(self.cache_data[m_line], 0))
        # MAKE_INVALID on S: no data, invalidate
        await self._snoop(m_line, 'SNOOP_MAKE_INVALID', label='s_mi')
        self._score("s_mi: line invalidated",
                    self._installed_state(m_line), 'I')
        # CPU access re-fetches (miss again)
        pre_misses = self.tally[EV_MISS]
        await self._txn(m_addr, 0, label='s_refetch')
        self._score("s_mi: CPU read re-fetched", self.tally[EV_MISS],
                    pre_misses + 1)
        # READ_UNIQUE on I: no transfer
        await self._snoop(m_line, 'SNOOP_READ_UNIQUE', label='s_ru')
        self._scenario('SnoopSequence')

    # ------------------------------------------------------------------
    # randomized lockstep
    # ------------------------------------------------------------------
    def _rand_addr(self):
        line = random.randrange(self.SPAN)
        beat = random.randrange(self.FILL_BEATS)
        return self._base_of(line) + beat * self.STRB_W

    async def _rand_txn_with_snoops(self, i):
        addr = self._rand_addr()
        we = 1 if random.random() < 0.5 else 0
        be = random.randrange(0, 1 << self.STRB_W) if we \
            else (1 << self.STRB_W) - 1
        wdata = random.getrandbits(self.BUS_WIDTH) if we else 0
        label = f'r{i}'
        txn = await self._txn_begin(addr, we, be, wdata, label)

        # snoops raised while the miss machinery is in flight
        prob = 0.65 if self.TEST_LEVEL == 'full' else 0.35
        n_rsp = len(self.rsp_log)
        if random.random() < prob:
            cand = [random.randrange(self.SPAN)]
            # a pending-line snoop only makes sense on a true miss (an
            # upgrade window is a single cycle -- that kill corner is owned
            # by the amber_control suite)
            pre = self._cur_state(txn['line'])
            hint = oracle_step(pre, 'CPU_WR' if we else 'CPU_RD')
            if hint.result == 'MISS' and hint.req != 'CLEAN_UNIQUE':
                cand.append(txn['line'])
            for tline in cand[:2]:
                snoop = random.choice(list(SNOOP_CODES))
                # wait for a model context that pins the resolution the RTL
                # will use at the grant:
                #  - pending line: the transient entered at the OBSERVED
                #    fill launch (bypass semantics)
                #  - this txn's victim: the M_I transient at the OBSERVED
                #    victim select (the drain window), or stale I after
                #    the fill launched; never granted mid-gather
                #  - any other line: installed state, no wait
                # skip the snoop if the response arrives first (the
                # pipeline went back to IDLE: the window closed)
                skip = False
                if tline == txn['line']:
                    for _ in range(self.RSP_TIMEOUT_CYCLES):
                        if self._cur_state(tline) in ('IS', 'IM', 'IS_I',
                                                      'SM'):
                            break
                        if len(self.rsp_log) > n_rsp:
                            skip = True
                            break
                        await self._negedge_settled()
                    else:
                        skip = True
                elif txn.get('victim') is not None \
                        and tline == txn['victim']['line'] \
                        and not txn['fill_modeled']:
                    while self._cur_state(tline) not in ('M_I',
                                                         'SINK_WB_ACK') \
                            and not txn['fill_modeled']:
                        if len(self.rsp_log) > n_rsp:
                            skip = True
                            break
                        await self._negedge_settled()
                if not skip:
                    await self._snoop(tline, snoop,
                                      label=f"{label}:{snoop}")
        return await self._txn_end(txn)

    async def _random_lockstep(self, n, profile_switch=0.25):
        for i in range(n):
            if random.random() < profile_switch:
                self.set_profile(random.choice(list(self.PROFILES)))
            await self._rand_txn_with_snoops(i)
            if random.random() < 0.3:
                # occasional between-transaction snoop on a random line
                await self._snoop(random.randrange(self.SPAN),
                                  random.choice(list(SNOOP_CODES)),
                                  label=f'idle_sn{i}')
            for _ in range(random.randrange(2)):
                await self._negedge_settled()
        self.set_profile('fast')

    # ------------------------------------------------------------------
    # MonBus tally cross-check + congestion
    # ------------------------------------------------------------------
    def _check_tally(self):
        for ev in EV_NAMES:
            if ev == EV_DROPPED:
                continue
            self._score(f"monbus tally {EV_NAMES[ev]}",
                        self.pkt_counts[ev], self.tally[ev])
        self._score("monbus tally: no drop reports pre-congestion",
                    self._drop_reports, 0)
        self._score("monbus: live dropped_count zero pre-congestion",
                    int(self.dut.mon_dropped.value), 0)

    async def _s_monbus_congestion(self):
        self.mon_mode = 'stall'
        for i in range(8):
            await self._txn(self._rand_addr(),
                            1 if random.random() < 0.5 else 0,
                            label=f'cg{i}')
        # the observer never stalls the cache: all 8 transactions completed
        self.mon_mode = 'free'
        reports0 = self._drop_reports
        for _ in range(200):
            if self._drop_reports > reports0:
                break
            await self._negedge_settled()
        self._score("congestion: drop report re-emitted",
                    self._drop_reports > reports0, True)
        for _ in range(500):
            if int(self.dut.mon_dropped.value) == 0 \
                    and not int(self.dut.mon_valid.value):
                break
            await self._negedge_settled()
        self._score("congestion: dropped_count cleared",
                    int(self.dut.mon_dropped.value), 0)
        self._scenario('MonbusCongestion')

    # ------------------------------------------------------------------
    # coh_req sideband cross-check
    # ------------------------------------------------------------------
    def _check_coh_req(self):
        # coh_req pulses are the launch strobes (one per pass / per
        # drain), not the monlite state-ENTRY events: detour re-entries
        # fire the monlite again but never re-launch
        exp = self.tally[EV_FILL_END] + self.tally[EV_DRAIN_END]
        self._score("coh_req: one pulse per fill/drain launch",
                    self.coh_req_count, exp)
        for _, kind, p in self.events:
            if kind != 'coh_req':
                continue
            self._score("coh_req: line-aligned addr",
                        p['addr'] & (self.LINE_BYTES - 1), 0)
            self._score("coh_req: known type",
                        p['type'] in (ACE_READ_SHARED, ACE_READ_UNIQUE,
                                      ACE_CLEAN_UNIQUE, ACE_WRITE_BACK),
                        True)

    # ------------------------------------------------------------------
    # top-level run
    # ------------------------------------------------------------------
    async def run(self):
        await self._s_init_walk()
        await self._s_first_hit_latency()
        await self._s_directed_sequence()
        await self._s_snoop_sequence()

        if self.TEST_LEVEL in ('func', 'full'):
            await self._random_lockstep(self.FULL_TXN[self.TEST_LEVEL])
            self._scenario('RandomOracleLockstep')

        # cross-checks on everything observed so far
        self._check_tally()
        self._check_coh_req()
        self._scenario('MonliteTallyCrossCheck')

        if self.TEST_LEVEL in ('func', 'full'):
            await self._s_monbus_congestion()

        # quiescence: nothing dangling
        await self.wait_clocks('clk', 10)
        self._score("quiescent: no monbus valid at end",
                    int(self.dut.mon_valid.value), 0)
        self._score("quiescent: ctrl not in ERROR",
                    int(self.dut.ctrl_state.value) == ST_ERROR, False)
        return self.mismatches == 0

    def get_test_report(self):
        return {
            'checks': self.checks,
            'mismatches': self.mismatches,
            'txns': self.txns,
            'snoops': self.snoops,
            'tally': {EV_NAMES[k]: v for k, v in self.tally.items()},
            'pkts': {EV_NAMES[k]: v for k, v in self.pkt_counts.items()},
            'scenarios': self.scenarios,
        }
