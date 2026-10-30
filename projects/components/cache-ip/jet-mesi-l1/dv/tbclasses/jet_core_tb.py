"""
jet_top full-core testbench (Task 8)

The pair-rig top integration: jet_control + jet_mshr + jet_wb_buffer +
jet_rsp_seq composed with the REAL common-ip slice (l1_cpu_frontend,
l1_tag_array, l1_data_array, l1_repl, l1_fill, l1_drain, l1_snoop_resp,
l1_monlite) and the house axi4_master_*_monlite transports + monbus
arbiter.  The harness (dv/tb/jet_core_th.sv) is a pure structural
wrapper: the DUT boundary IS jet_top's external shape.  The memory side
is closed with the house AXI4 slave responders on m_axi_* (shared
MemoryModel), the CPU side with the house GAXI BFM pair, the ACE port
with the house snoop master.

Scoreboard shape (the Task-8 inheritance claim, re-based): jet is
lockup-free, so amber's per-transaction slice checks do not apply;
instead this TB keeps an EVENT-STREAM scoreboard, built on the
L1ControlTB machinery it inherits (geometry helpers, LruModel, the
gem5-derived oracle, the snoop tables, the BUG-001/002 pre-install-valid
eviction guard):

  * every CPU accept pushes an expected-response record (issue order);
    every response pops the head -- J4 tag-order release is checked by
    construction, read data = memory line + the byte-enable merges of
    every write accepted before the read (jet's merge-at-commit +
    read-capture-at-own-position rule makes exactly those visible);
  * every snoop grant resolves the line through the RTL's own match
    order (WB snarf > pending-fill bypass with PF_GUARD > in-flight
    upgrade at S > array with the stale-victim claimed-way rule) and is
    scored CRRESP-bit-for-bit plus CD-content against the oracle at that
    resolution -- timing-free coherence lockstep, unchanged semantics;
  * every commit tag write (install / pend / CU install) is scored
    against the entry model (state, tag, set, way) -- including the
    Task-8 killed-upgrade demote (a pre-grant invalidating snoop to the
    upgrade's line makes the CU commit install I, never resurrect M);
  * every drain retires the WB head to the MemoryModel, audited against
    the capture-time content snapshot (end-to-end writeback payload);
  * windowed timing properties: every alloc's fill launch lands within
    FILL_LAUNCH_WINDOW cycles (and never during a victim capture -- the
    MAS ch02/01 cap_busy contract, checked every cycle).

Golden models carried here (independent copies; kmap-TB rule):
  memory-side line content   MemoryModel (the AXI responders share it)
  cache line content         derived: mem line + pending-write list
  (set, way) -> line/state   tags / slot_state (installed view, fed by
                             the observed tag writes)
  per-entry transient        entries[] (alloc -> launch -> beats -> done
                             -> commit/retire), incl. pend_eff I-sticks
  writeback lines            wb[] capture-time content snapshots
  repl policy                per-policy parity model (jet_repl_models:
                             LruModel / FifoModel / RandReplModel), the
                             victim way pinned at every alloc

Levels (TEST_LEVEL):
  gate  -- InitWalk + directed CPU sequence (miss/hit/upgrade/merge/
           dirty-eviction + drain audit) + directed snoop sequence +
           KilledUpgrade + IllegalStateError (sticky CTRL_ERROR) +
           VictimClaimStall (w_victim_claimed as the SOLE stall cause) +
           CapBusyContract + ResponseTagOrder/WindowedFillStart pins
  func  -- + OracleLockstepSoak (random traffic + snoops + responder
           profile switches)
  full  -- + the ch06/02 FULL content: MSHR-saturating miss streams with
           concurrent hits+snoops, a merge storm onto one outstanding
           fill, set-oversubscription bursts into one set, the composed
           corner (MSHR-full + WB-full + snoop soak, dynamically), and
           the amber FULL soak depth (10k randomized oracle-lockstep
           transactions with interleaved snoops) re-run on jet

Author: RTL Design Sherpa
Created: 2026-10-29
"""

import os
import random
from collections import deque

import cocotb
from cocotb.triggers import FallingEdge, Timer

from CocoTBFramework.components.shared.memory_model import MemoryModel
from CocoTBFramework.components.shared.flex_randomizer import FlexRandomizer
from CocoTBFramework.components.shared.field_config import FieldConfig
from CocoTBFramework.components.gaxi.gaxi_master import GAXIMaster
from CocoTBFramework.components.gaxi.gaxi_slave import GAXISlave
from CocoTBFramework.components.axi4.axi4_factories import (
    create_axi4_slave_rd,
    create_axi4_slave_wr,
)
from CocoTBFramework.components.ace.ace_factories import (
    create_axi4ace_snoop_master,
)
from CocoTBFramework.components.ace.ace_transaction import SnoopType

from projects.components.cache_ip.common_ip.dv.tbclasses.l1_control_tb import (
    L1ControlTB,
    STATE_CODE,
)
from projects.components.cache_ip.common_ip.dv.golden.l1_fsm_oracle import (
    SNOOP_CODES,
    step as oracle_step,
)
from projects.components.cache_ip.jet_mesi_l1.dv.tbclasses.jet_repl_models import (
    REPL_LRU,
    REPL_NAMES,
    REPL_RANDOM,
    make_repl_model,
)

# jet_control classify stall reasons (rtl/fub/jet_control.sv localparams)
STALL_MSHR_FULL = 1
STALL_WB = 2            # wb_full_dirty_victim / drain race
STALL_SET_OVERSUB = 3   # set-full / upgrade-way / claim-aware victim
STALL_XCLASS = 4
STALL_TAG_FULL = 5
STALL_COMMIT = 6        # merge onto a fill-done entry
STALL_NAMES = {0: 'none', STALL_MSHR_FULL: 'mshr_full', STALL_WB: 'wb',
               STALL_SET_OVERSUB: 'set_oversub', STALL_XCLASS: 'xclass',
               STALL_TAG_FULL: 'tag_full', STALL_COMMIT: 'commit'}

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
CRRESP_DT = 0
CRRESP_NO_DT_MASK = 0b11000   # PF_GUARD: keep IS|WU, drop DT/PD/Err

# oracle snoop name -> framework ACE snoop type (IHI0022 ACSNOOP encodings)
SNOOP_FRAMEWORK = {
    'SNOOP_READ_ONCE': SnoopType.READ_ONCE,
    'SNOOP_READ_SHARED': SnoopType.READ_SHARED,
    'SNOOP_READ_UNIQUE': SnoopType.READ_UNIQUE,
    'SNOOP_CLEAN_SHARED': SnoopType.CLEAN_SHARED,
    'SNOOP_CLEAN_INVALID': SnoopType.CLEAN_INVALID,
    'SNOOP_MAKE_INVALID': SnoopType.MAKE_INVALID,
}
NAME_BY_CODE = {code: name for name, code in SNOOP_CODES.items()}


class JetCoreTB(L1ControlTB):
    """Event-stream oracle-lockstep scoreboard for jet_top."""

    FULL_TXN = {'gate': 0, 'func': 300, 'full': 10_000}
    RSP_TIMEOUT_CYCLES = 8000
    # windowed fill-launch property: generous smoke bound (one serialized
    # fill behind the engine + one victim capture + arbiter latency under
    # the slowest responder profile is far below this)
    FILL_LAUNCH_WINDOW = 128

    def __init__(self, dut, **kwargs):
        super().__init__(dut, **kwargs)
        # L1ControlTB pins the bus geometry (64-bit data / STRB_W=8);
        # keep the width name the top-level params use
        self.BUS_WIDTH = self.STRB_W * 8

        # the Task-12 grid knobs (the runner passes them; the harness
        # parameters carry them to the RTL)
        self.MSHR_COUNT = int(os.environ.get('MSHR_COUNT', '8'))
        self.VICTIM_DEPTH = int(os.environ.get('VICTIM_DEPTH', '2'))
        self.REPL_POLICY = int(os.environ.get('REPL_POLICY', '0'))
        # victim-way parity model per policy (update-at-alloc for all;
        # hits touch the policy only under LRU -- l1_repl's FIFO/RANDOM
        # branches ignore repl_hit, and the models mirror that)
        self.lru = make_repl_model(self.REPL_POLICY, self.SETS, self.WAYS)
        self._hit_updates_repl = (self.REPL_POLICY == REPL_LRU)

        # memory side shared with the AXI responders
        self.memory_model = MemoryModel(
            num_lines=1 << 20, bytes_per_line=self.STRB_W, log=self.log)

        # bounded working set (same shape as amber_core: evictions at the
        # grid geometry, cheap preload/audit); the preload covers the
        # directed scenarios' tag range too (they name lines up to
        # ~0x400 << SET_BITS at the default geometry)
        self.SPAN = min(max(self.SETS * 16, 64), 8192)
        self.PRELOAD_LINES = 1 << 17

        # event-stream model state
        self.pw = {}               # line -> [(beat, be, wdata)] accepted
        self.entries = {}          # line -> entry dict (pending fills)
        self.entry_by_idx = {}     # mshr idx -> line
        self.unlaunched = deque()  # alloc order (launch order == alloc)
        # fill-completion order: {'kind':'entry','e':...,'done':bool} /
        # {'kind':'cu','done':bool}
        self.launch_q = deque()
        self.upgr = {'valid': False, 'line': None, 'set': 0, 'way': 0,
                     'killed': False}
        self.wb = {}               # line -> content bytes (capture snapshot)
        self.wb_order = deque()    # WB drain order (oldest first)
        self.draining = None
        self.committing = None     # the launch_q head under C_INSTALL+

        # response bookkeeping (issue order in, release order out)
        self.rspq = deque()
        self.n_rsp = 0

        # snoop scoring: grant observations + expected effect tag writes
        self.grant_log = []
        self.exp_sn_tagwr = deque()

        # windowed-property stats + corner-exercise counters
        self.launch_waits = []
        self.launch_count = 0
        self.cu_launches = 0
        self.cap_busy_violations = 0
        self.kill_count = 0
        self.pf_grants = 0
        self.wb_grants = 0

        # Task-12 grid instrumentation (per-cycle, monitor-driven):
        #   stall_cycles[reason] -- lkup_stall_o cycles by J6 reason
        #   accept_log           -- per-accept class, in issue order
        #                           ('hit'/'merge'/'alloc'/'upgr'); the
        #                           cache_sim parity TB consumes it
        #   max_occupancy / max_wb -- lifetime peaks (the report)
        #   win_max_*            -- windowed peaks (scenarios reset them)
        #   corner_cycles        -- cycles at MSHR-full AND WB-full
        self.stall_cycles = {}
        self.accept_log = []
        self.merge_count = 0
        self.max_occupancy = 0
        self.max_wb = 0
        self.win_max_occupancy = 0
        self.win_max_wb = 0
        self.win_max_set_claims = 0
        self.corner_cycles = 0

        self.log.info(f"JetCoreTB sets={self.SETS} ways={self.WAYS} "
                      f"line={self.LINE_BYTES} bus={self.BUS_WIDTH} "
                      f"mshr={self.MSHR_COUNT} victim={self.VICTIM_DEPTH} "
                      f"repl={REPL_NAMES[self.REPL_POLICY]} "
                      f"level={self.TEST_LEVEL} seed={self.SEED}")

    # ------------------------------------------------------------------
    # model helpers
    # ------------------------------------------------------------------
    def _scenario(self, name):
        self.scenarios[name] = {'checks': self.checks,
                                'mismatches': self.mismatches}

    def _base_of(self, line):
        return (line & self.LINE_MASK) << self.OFFSET_BITS

    def _mem_line(self, line):
        return bytes(self.memory_model.read(self._base_of(line),
                                            self.LINE_BYTES))

    def _content(self, line):
        """Expected cache-resident line content: the memory image plus the
        byte-enable merges of every write accepted while the line has been
        resident (fill data is raw memory; writes merge at their hit /
        at the fill's commit, always in accept order)."""
        data = bytearray(self._mem_line(line))
        for beat, be, wdata in self.pw.get(line, []):
            lo = beat * self.STRB_W
            for i in range(self.STRB_W):
                if be & (1 << i):
                    data[lo + i] = (wdata >> (8 * i)) & 0xFF
        return bytes(data)

    def _claimed(self, set_idx, way):
        """A live MSHR entry claims (set, way): a tag hit there is the
        doomed victim's stale tag (the Invalid row, amber's rule)."""
        for e in self.entries.values():
            if e['set'] == set_idx and e['way'] == way:
                return True
        return False

    def _rand_addr(self):
        line = random.randrange(self.SPAN)
        beat = random.randrange(self.FILL_BEATS)
        return self._base_of(line) + beat * self.STRB_W

    # ------------------------------------------------------------------
    # clock/reset/BFMs
    # ------------------------------------------------------------------
    async def setup_clocks_and_reset(self, period_ns=10):
        await self.start_clock('aclk', freq=period_ns, units='ns')
        d = self.dut

        req_fields = FieldConfig.from_dict(
            field_dict={'data': {'bits': self.CPU_REQ_W_JET, 'default': 0}},
            lsb_first=True)
        rsp_fields = FieldConfig.from_dict(
            field_dict={'data': {'bits': self.BUS_WIDTH, 'default': 0}},
            lsb_first=True)

        master_rand = FlexRandomizer(
            {'valid_delay': ([(0, 0), (1, 2)], [7, 3])})
        self.master = GAXIMaster(
            dut=d, title='cpu_req', prefix='',
            clock=d.aclk, field_config=req_fields,
            timeout_cycles=self.RSP_TIMEOUT_CYCLES,
            mode='skid', bus_name='cpu_req_wr', pkt_prefix='',
            multi_sig=False, randomizer=master_rand, log=self.log)
        self.slave = GAXISlave(
            dut=d, title='cpu_rsp', prefix='',
            clock=d.aclk, field_config=rsp_fields,
            timeout_cycles=self.RSP_TIMEOUT_CYCLES,
            mode='skid', bus_name='cpu_rsp_rd', pkt_prefix='',
            multi_sig=False,
            randomizer=FlexRandomizer({'ready_delay': ([(0, 0)], [1])}),
            log=self.log)
        self.slave.set_ready_policy('always')

        # memory side: house AXI4 responders on the monlite-wrapped m_axi
        self.rd_components = create_axi4_slave_rd(
            dut=d, clock=d.aclk, prefix='m_axi', log=self.log,
            id_width=8, addr_width=self.ADDR_WIDTH,
            data_width=self.BUS_WIDTH, user_width=1,
            memory_model=self.memory_model)
        self.ar_slave = self.rd_components['AR']
        self.r_master = self.rd_components['R']
        self.wr_components = create_axi4_slave_wr(
            dut=d, clock=d.aclk, prefix='m_axi', log=self.log,
            id_width=8, addr_width=self.ADDR_WIDTH,
            data_width=self.BUS_WIDTH, user_width=1,
            memory_model=self.memory_model)
        self.aw_slave = self.wr_components['AW']
        self.w_slave = self.wr_components['W']
        self.b_master = self.wr_components['B']

        # ACE snoop master on the snoop responder port
        self.snoop_master = create_axi4ace_snoop_master(
            dut=d, clock=d.aclk, prefix='m_axi_', log=self.log,
            ifc_name='sn', addr_width=self.ADDR_WIDTH,
            data_width=self.BUS_WIDTH)['interface']

        d.mon_ready.value = 1

        # deterministic memory content: the whole reachable line space
        # (the random working set AND the directed-scenario tag range --
        # the responders share this model, so every fill sees it)
        for line in range(self.PRELOAD_LINES):
            self.memory_model.write(self._base_of(line),
                                    bytearray(self._default_line(line)))

        await self.assert_reset()
        cocotb.start_soon(self._monitor())
        await self.wait_clocks('aclk', 3)
        await self.deassert_reset()
        self.set_profile('fast')

    @property
    def CPU_REQ_W_JET(self):
        return self.ADDR_WIDTH + 1 + self.STRB_W + self.BUS_WIDTH

    async def assert_reset(self):
        self.dut.aresetn.value = 0

    async def deassert_reset(self):
        self.dut.aresetn.value = 1

    async def _negedge_settled(self):
        await FallingEdge(self.dut.aclk)
        await Timer(500, units='ps')

    def set_profile(self, name):
        # each profile: (rd_ready, rd_resp, wr_ready, wr_resp) -- the
        # fill side (AR/R) and the drain side (AW/W/B) separately, so the
        # corner scenarios can run fills fast and drains slow
        profiles = {
            'fast':   {'rd': ([(0, 0)], [1.0]), 'rresp': ([(0, 0)], [1.0]),
                       'wr': ([(0, 0)], [1.0]), 'bresp': ([(0, 0)], [1.0])},
            'normal': {'rd': ([(0, 2), (3, 5)], [0.7, 0.3]),
                       'rresp': ([(0, 2), (3, 6)], [0.6, 0.4]),
                       'wr': ([(0, 2), (3, 5)], [0.7, 0.3]),
                       'bresp': ([(0, 2), (3, 6)], [0.6, 0.4])},
            'slow':   {'rd': ([(1, 4), (5, 10)], [0.6, 0.4]),
                       'rresp': ([(2, 6), (7, 12)], [0.5, 0.5]),
                       'wr': ([(1, 4), (5, 10)], [0.6, 0.4]),
                       'bresp': ([(2, 6), (7, 12)], [0.5, 0.5])},
            # glacial: a fill stays in flight across a long directed
            # construction (the victim-claim hit walk, the merge storm's
            # list overflow) -- ~170-250 cycles per fill
            'glacial': {'rd': ([(2, 6), (8, 20)], [0.5, 0.5]),
                        'rresp': ([(5, 15), (20, 40)], [0.5, 0.5]),
                        'wr': ([(2, 6), (8, 20)], [0.5, 0.5]),
                        'bresp': ([(5, 15), (20, 40)], [0.5, 0.5])},
            # drainslow: fills fast, drains slow -- dirty-victim captures
            # outpace the drain engine, so the WB buffer fills
            'drainslow': {'rd': ([(0, 0)], [1.0]), 'rresp': ([(0, 0)], [1.0]),
                          'wr': ([(2, 6), (8, 20)], [0.5, 0.5]),
                          'bresp': ([(5, 15), (20, 40)], [0.5, 0.5])},
        }
        cfg = profiles[name]
        self.ar_slave.set_randomizer(FlexRandomizer({'ready_delay': cfg['rd']}))
        self.aw_slave.set_randomizer(FlexRandomizer({'ready_delay': cfg['wr']}))
        self.w_slave.set_randomizer(FlexRandomizer({'ready_delay': cfg['wr']}))
        self.r_master.set_randomizer(FlexRandomizer({'valid_delay': cfg['rresp']}))
        self.b_master.set_randomizer(FlexRandomizer({'valid_delay': cfg['bresp']}))

    # ------------------------------------------------------------------
    # the event-stream monitor: one pass per cycle, model updates in the
    # RTL's own visibility order (allocs are visible to a same-cycle
    # snoop grant -- the alloc-first rule; fill beats register at the
    # cycle's end, so a grant sees only prior beats -- PF_GUARD)
    # ------------------------------------------------------------------
    async def _monitor(self):
        d = self.dut
        u = d.u_top
        uc = u.u_control
        while True:
            await FallingEdge(d.aclk)
            await Timer(100, units='ps')
            self.cyc += 1
            d.i_mon_time.value = self.cyc

            init = int(u.init_busy.value)

            # 1. lookup-stage accept (lkup_valid & lkup_ready): the seq
            #    tag is granted here, so the issue order IS this order.
            #    (The GAXI handshake upstream only admits the request
            #    into the skid.)  Expected response + pending-write
            #    record + LRU hit update + upgrade-launch mark.
            if int(uc.lkup_valid_i.value) and int(uc.lkup_ready_o.value):
                addr = int(uc.lkup_addr_i.value)
                we = int(uc.lkup_we_i.value)
                be = int(uc.lkup_be_i.value)
                wdata = int(uc.lkup_wdata_i.value)
                line = self._line_of(addr)
                beat = (addr >> (self.STRB_W.bit_length() - 1)) \
                    & (self.FILL_BEATS - 1)
                # accept class (the cache_sim parity TB consumes the log;
                # the classes are mutually exclusive by construction)
                if int(uc.lkup_hit_o.value):
                    self.accept_log.append('hit')
                elif int(uc.lkup_upgrade_o.value):
                    self.accept_log.append('upgr')
                elif int(uc.lkup_merge_o.value):
                    self.accept_log.append('merge')
                    self.merge_count += 1
                else:
                    self.accept_log.append('alloc')
                if we:
                    self.pw.setdefault(line, []).append((beat, be, wdata))
                    exp = wdata
                else:
                    exp = self._beat_of_line(self._content(line), beat)
                self.rspq.append({'line': line, 'we': we, 'exp': exp,
                                  'cyc': self.cyc})
                # policy hit update (repl_hit fires at hit/upgrade
                # accepts; only LRU's state moves on a hit -- the
                # FIFO/RANDOM branches of l1_repl ignore repl_hit)
                if self._hit_updates_repl and int(uc.repl_hit_o.value):
                    self.lru.update(self._set_of_line(line),
                                    int(uc.repl_hit_way_o.value))
                if int(uc.lkup_upgrade_o.value):
                    self.upgr = {'valid': True, 'line': line,
                                 'set': self._set_of_line(line),
                                 'way': self._hit_way(
                                     self._set_of_line(line), line),
                                 'killed': False}

            # 2. MSHR alloc (before the snoop resolution: alloc-first
            #    same-cycle visibility)
            if int(uc.mshr_alloc_o.value) and int(uc.mshr_alloc_gnt_i.value):
                self._mon_alloc(uc)

            # 3. snoop grant: oracle resolution in the RTL's match order
            if int(u.u_snoop.ctrl_snoop_req.value) \
                    and int(uc.sn_ready_o.value):
                self._mon_snoop_grant(u, uc)

            # 3b. fill AR acceptance (the Task-9 pre-AR rule's progress
            #     input): the engine's outstanding AR belongs to the
            #     oldest un-done entry launch.  Observed AFTER the grant:
            #     a grant in the AR-handshake cycle still sees pre-AR
            #     (r_ar_done registers at the cycle's end).
            if int(d.m_axi_arvalid.value) and int(d.m_axi_arready.value):
                for item in self.launch_q:
                    if not item['done'] and item['kind'] == 'entry':
                        item['e']['ar'] = True
                        break

            # 4. fill beats (registered into beats_rcvd at the cycle's
            #    end -- after the grant resolution)
            if int(uc.fill_beat_valid_i.value):
                idx = int(uc.fill_beat_idx_i.value)
                num = int(uc.fill_beat_num_i.value)
                line = self.entry_by_idx.get(idx)
                if line is None:
                    self._score("fill beat on an unknown entry", idx, None)
                else:
                    e = self.entries[line]
                    e['beats'].add(num)
                    got = int(u.u_fill.fill_beat_data.value)
                    self._score(f"fill beat data line={line:#x} b{num}",
                                got, self._beat_of_line(
                                    self._mem_line(line), num))

            # 5. fill_done: oldest un-done launch completes; PassDirty
            if int(uc.fill_done_i.value):
                self._mon_fill_done(uc)

            # 6. fill launch accept: windowed property + the cap_busy
            #    contract (never during a capture, never on a dirty
            #    victim's alloc cycle)
            if int(uc.fill_start_o.value) and int(uc.fill_accept_i.value):
                if int(uc.cap_busy_o.value):
                    self.cap_busy_violations += 1
                    self._score("fill launch during a victim capture", 1, 0)
                if int(uc.mshr_alloc_o.value) \
                        and int(uc.mshr_alloc_wb_valid_o.value):
                    self.cap_busy_violations += 1
                    self._score("fill launch on a dirty-alloc cycle", 1, 0)
                cls = int(uc.fill_cls_o.value)
                if cls != JET_CLS_CU:
                    if not self.unlaunched:
                        self._score("fill launch with no pending alloc",
                                    cls, None)
                    else:
                        e = self.unlaunched.popleft()
                        e['launch_cyc'] = self.cyc
                        self.launch_waits.append(self.cyc - e['alloc_cyc'])
                        self.launch_count += 1
                        self._score(
                            f"windowed fill start line={e['line']:#x}",
                            self.cyc - e['alloc_cyc']
                            <= self.FILL_LAUNCH_WINDOW, True)
                        self.launch_q.append({'kind': 'entry', 'e': e,
                                              'done': False})
                else:
                    self.cu_launches += 1
                    self.launch_q.append({'kind': 'cu', 'done': False})

            # 7. tag writes: attribution by the commit/snoop FSM taps
            if int(uc.tag_a_wr_en_o.value):
                self._mon_tag_wr(uc, init)

            # 8. drains: head identity at the start, payload audit at done
            if int(uc.drain_start_o.value):
                if not self.wb_order:
                    self._score("drain_start with empty WB model", 1, 0)
                else:
                    self.draining = self.wb_order[0]
                    self._score("drain addr is the oldest WB line",
                                int(u.u_wb.drain_addr_o.value),
                                self._base_of(self.draining))
            if int(uc.drain_done_i.value):
                if self.draining is None:
                    self._score("drain_done with no drain in flight", 1, 0)
                else:
                    line = self.draining
                    # the W beats landed in the MemoryModel before the
                    # BRESP that produced this drain_done: the writeback
                    # payload round-trips through the real write path
                    self._score(f"drain payload line={line:#x}",
                                self._mem_line(line), self.wb[line])
                    del self.wb[line]
                    self.wb_order.popleft()
                    self.draining = None

            # 9. entry retire: claims free
            if int(uc.mshr_retire_o.value):
                idx = int(uc.mshr_retire_idx_o.value)
                line = self.entry_by_idx.pop(idx, None)
                if line is None:
                    self._score("retire of an unknown entry", idx, None)
                else:
                    self.entries.pop(line, None)
                if not self.launch_q or self.launch_q[0]['kind'] != 'entry':
                    self._score("retire while the commit head is not an "
                                "entry", 1, 0)
                else:
                    e = self.launch_q.popleft()['e']
                    self._score("retire matches the commit head",
                                line, e['line'])
                self.committing = None

            # 10. response release: pop the issue-order head (J4)
            if int(d.cpu_rsp_rd_valid.value) and int(d.cpu_rsp_rd_ready.value):
                got = int(d.cpu_rsp_rd_data.value)
                if not self.rspq:
                    self._score("unsolicited response", got, None)
                else:
                    req = self.rspq.popleft()
                    self._score(f"rsp data line={req['line']:#x} "
                                f"we={req['we']}", got, req['exp'])
                self.n_rsp += 1

            # 11. Task-12 grid instrumentation: occupancy/corner/stall
            occ = len(self.entries)
            wbocc = len(self.wb)
            if occ > self.max_occupancy:
                self.max_occupancy = occ
            if wbocc > self.max_wb:
                self.max_wb = wbocc
            if occ > self.win_max_occupancy:
                self.win_max_occupancy = occ
            if wbocc > self.win_max_wb:
                self.win_max_wb = wbocc
            if occ == self.MSHR_COUNT and wbocc == self.VICTIM_DEPTH:
                self.corner_cycles += 1
            if self.entries:
                set_claims = {}
                for e in self.entries.values():
                    set_claims[e['set']] = set_claims.get(e['set'], 0) + 1
                m = max(set_claims.values())
                if m > self.win_max_set_claims:
                    self.win_max_set_claims = m
            if int(uc.lkup_stall_o.value):
                r = int(uc.lkup_stall_reason_o.value)
                self.stall_cycles[r] = self.stall_cycles.get(r, 0) + 1

    # ------------------------------------------------------------------
    # monitor event handlers
    # ------------------------------------------------------------------
    def _mon_alloc(self, uc):
        line = int(uc.mshr_alloc_line_o.value) & self.LINE_MASK
        set_idx = int(uc.mshr_alloc_set_o.value)
        cls = int(uc.mshr_alloc_cls_o.value)
        way = int(uc.mshr_alloc_victim_way_o.value)
        wb_valid = int(uc.mshr_alloc_wb_valid_o.value)
        idx = int(uc.mshr_alloc_idx_i.value)

        # victim-way parity with the repl engine, then the update-at-alloc
        self._score(f"alloc victim way line={line:#x}", way,
                    self.lru.victim(set_idx))
        self.lru.update(set_idx, way)

        # the victim leaves the cache domain now (dirty: into the WB
        # buffer with a content snapshot; clean: silently).  The
        # BUG-001/002 pre-install-valid guard: only a VALID slot's line is
        # genuinely evicted -- a dead {tag, I} duplicate (a snoop
        # invalidate leaves the tag in place) says nothing about a live
        # copy elsewhere.
        vline = self.tags.get((set_idx, way))
        vstate = self.slot_state.get((set_idx, way), 'I')
        if vline is not None and vstate != 'I' and vline != line:
            self._score(f"alloc wb_valid line={line:#x}", wb_valid,
                        1 if vstate == 'M' else 0)
            if vstate == 'M':
                self.wb[vline] = self._content(vline)
                self.wb_order.append(vline)
            self.pw.pop(vline, None)

        e = {'line': line, 'set': set_idx, 'cls': cls, 'way': way,
             'idx': idx, 'pend': None, 'beats': set(), 'done': False,
             'pd': False, 'ar': False, 'alloc_cyc': self.cyc,
             'launch_cyc': None}
        self.entries[line] = e
        self.entry_by_idx[idx] = line
        self.unlaunched.append(e)

    def _mon_fill_done(self, uc):
        pd = int(uc.fill_pass_dirty_i.value)
        # the oldest un-done launch completes (in-order, single read ID)
        for c in self.launch_q:
            if not c['done']:
                c['done'] = True
                if c['kind'] == 'entry':
                    c['e']['done'] = True
                    c['e']['pd'] = pd
                return
        self._score("fill_done with no outstanding launch", 1, 0)

    def _mon_tag_wr(self, uc, init):
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
            head = self.launch_q[0] if self.launch_q else None
            if head is None or head['kind'] != 'entry':
                self._score("C_INSTALL with no entry at the commit head",
                            1, 0)
                return
            self._score("commit head is done", head['done'], True)
            e = head['e']
            exp_state = (AMBER_STATE_S
                         if e['cls'] == JET_CLS_RNSD and not e['pd']
                         else AMBER_STATE_M)
            self._score(f"install tag line={e['line']:#x}", line, e['line'])
            self._score(f"install set line={e['line']:#x}", set_idx,
                        e['set'])
            self._score(f"install way line={e['line']:#x}", way, e['way'])
            self._score(f"install state line={e['line']:#x}", state,
                        exp_state)
            # the eviction accounting happened at the ALLOC (the victim
            # leaves the cache domain then; pw popped there).  The slot's
            # tag/state cannot change between the alloc and this install
            # (a snoop hit on the claimed way is the stale-tag Invalid
            # row, no effect) -- so there is NOTHING to account here, and
            # re-popping by the slot's stale tag would clobber the
            # pending writes of a line RE-INCARNATED (re-filled) in the
            # alloc->commit window (the Task-12 drain-payload find).
            self.tags[(e['set'], e['way'])] = e['line']
            self.slot_state[(e['set'], e['way'])] = (
                'S' if exp_state == AMBER_STATE_S else 'M')
            self.committing = e
        elif cmt == C_PEND:
            e = self.committing
            if e is None:
                self._score("C_PEND with no committing entry", 1, 0)
                return
            exp = 'I' if e['pend'] == 'I' else 'S'
            self._score(f"pend effect line={e['line']:#x}", state,
                        STATE_CODE[exp])
            self.slot_state[(e['set'], e['way'])] = exp
            if exp == 'I':
                # the killed fill: merged write data never lands
                self.pw.pop(e['line'], None)
        elif cmt == C_CU_INSTALL:
            u = self.upgr
            if not u['valid']:
                self._score("CU install with no in-flight upgrade", 1, 0)
                return
            exp = AMBER_STATE_I if u['killed'] else AMBER_STATE_M
            self._score(f"CU install tag line={u['line']:#x}", line,
                        u['line'])
            self._score(f"CU install way line={u['line']:#x}", way,
                        u['way'])
            # the Task-8 killed-upgrade pin: demote to I, never
            # resurrect M
            self._score(f"CU install state line={u['line']:#x} "
                        f"(killed={u['killed']})", state, exp)
            self.slot_state[(u['set'], way)] = (
                'I' if u['killed'] else 'M')
            if u['killed']:
                self.pw.pop(u['line'], None)
            self.upgr = {'valid': False, 'line': None, 'set': 0, 'way': 0,
                         'killed': False}
            if self.launch_q and self.launch_q[0]['kind'] == 'cu':
                self.launch_q.popleft()
            else:
                self._score("CU install but the commit head is not CU",
                            1, 0)
        elif sn == SN_EFFECT:
            # the deferred snoop effect on an array hit
            if not self.exp_sn_tagwr:
                self._score("unanticipated snoop-effect tag write", 1, 0)
                return
            exp = self.exp_sn_tagwr.popleft()
            self._score(f"snoop effect line={exp['line']:#x}", line,
                        exp['line'])
            self._score(f"snoop effect way line={exp['line']:#x}", way,
                        exp['way'])
            self._score(f"snoop effect state line={exp['line']:#x}",
                        state, STATE_CODE[exp['next']])
            self.slot_state[(exp['set'], way)] = exp['next']
            if exp['next'] == 'I':
                self.pw.pop(exp['line'], None)
        else:
            self._score("unattributed tag write "
                        f"(line={line:#x} state={state})", 1, 0)

    def _mon_snoop_grant(self, u, uc):
        addr = int(uc.sn_addr_i.value)
        line = self._line_of(addr)
        name = NAME_BY_CODE[int(uc.sn_type_i.value)]
        got_crresp = int(uc.sn_crresp_o.value)

        cd = None
        if line in self.wb:
            # WB snarf: the buffer owns the line until the WB ack --
            # answered at M (SINK_WB_ACK), drain still completes
            res = oracle_step('M', name)
            self.wb_grants += 1
            if (res.crresp >> CRRESP_DT) & 1:
                cd = self.wb[line]
        elif line in self.entries:
            e = self.entries[line]
            if not e['ar']:
                # the Task-9 pre-AR rule (the amber BUG-002 analog): the
                # entry's fill AR has not been accepted, so the fill's
                # data necessarily post-dates this snoop -- the answer is
                # the Invalid row with no effect and no data (jet has no
                # replay path; a pend_eff here would drop a write fill's
                # merge at the commit)
                res = oracle_step('I', name)
            else:
                # pending-fill bypass at the post-fill state, PF_GUARDed
                self.pf_grants += 1
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
                # pend_eff with I-sticks
                if e['pend'] != 'I':
                    if res.next_state == 'IS_I':
                        e['pend'] = 'I'
                    else:
                        e['pend'] = res.pending
                res = res._replace(crresp=crresp)
                if (crresp >> CRRESP_DT) & 1:
                    # the fill data (merges land at the commit, after)
                    cd = self._mem_line(line)
        elif self.upgr['valid'] and line == self.upgr['line']:
            # the in-flight upgrade's line: legitimately resident S until
            # the CU commit lands; the effect writes the tag (array hit)
            res = oracle_step('S', name)
            if res.next_state != 'S':
                self.exp_sn_tagwr.append({
                    'line': line, 'set': self.upgr['set'],
                    'way': self.upgr['way'], 'next': res.next_state})
                if res.next_state == 'I':
                    self.upgr['killed'] = True
                    self.kill_count += 1
        else:
            set_idx = self._set_of_line(line)
            way = self._hit_way(set_idx, line)
            ref = 'I'
            if way is not None and not self._claimed(set_idx, way):
                ref = self.slot_state.get((set_idx, way), 'I')
            res = oracle_step(ref, name)
            if (res.crresp >> CRRESP_DT) & 1:
                cd = self._content(line)
            if ref != 'I' and res.next_state != ref:
                self.exp_sn_tagwr.append({
                    'line': line, 'set': set_idx, 'way': way,
                    'next': res.next_state})

        self.grant_log.append({'cyc': self.cyc, 'line': line, 'name': name,
                               'exp_crresp': res.crresp, 'cd': cd})
        # the grant-cycle CRRESP is combinational on the probes: score it
        # right here (the driver re-scores the BFM's captured value)
        self._score(f"snoop {name} line={line:#x} crresp (grant)",
                    got_crresp, res.crresp)

    # ------------------------------------------------------------------
    # drivers
    # ------------------------------------------------------------------
    def _pack_req(self, addr, we, be, wdata):
        return ((addr & ((1 << self.ADDR_WIDTH) - 1))
                << (1 + self.STRB_W + self.BUS_WIDTH)) \
            | ((we & 1) << (self.STRB_W + self.BUS_WIDTH)) \
            | ((be & ((1 << self.STRB_W) - 1)) << self.BUS_WIDTH) \
            | (wdata & ((1 << self.BUS_WIDTH) - 1))

    async def _send(self, addr, we, be=None, wdata=None, label=''):
        """Issue one request; returns its response ordinal (accept order).
        The monitor scores the accept and (later) the release."""
        if be is None:
            be = random.randrange(1, 1 << self.STRB_W) if we \
                else (1 << self.STRB_W) - 1
        if wdata is None:
            wdata = random.getrandbits(self.BUS_WIDTH) if we else 0
        n = self.txns
        pkt = self.master.create_packet(data=self._pack_req(addr, we, be,
                                                            wdata))
        await self.master.send(pkt)
        self.txns += 1
        return n

    async def _await_rsp(self, n, label=''):
        for _ in range(self.RSP_TIMEOUT_CYCLES):
            if self.n_rsp > n:
                return
            await self._negedge_settled()
        raise RuntimeError(f"{label}: response {n} timeout; "
                           f"n_rsp={self.n_rsp} ctrl_state="
                           f"{int(self.dut.ctrl_state.value):#x}")

    async def _txn(self, addr, we, be=None, wdata=None, label=''):
        n = await self._send(addr, we, be, wdata, label)
        await self._await_rsp(n, label)

    async def _await_all_responses(self, label='drain'):
        if self.txns:
            await self._await_rsp(self.txns - 1, label)
        for _ in range(20):
            await self._negedge_settled()
        self._score(f"{label}: all responses released",
                    len(self.rspq), 0)

    async def _snoop(self, line, name, label=''):
        """Issue one snoop through the real ACE port; the monitor recorded
        (and scored) the grant-cycle expectation."""
        n = len(self.grant_log)
        result = await self.snoop_master.issue_snoop(
            self._base_of(line), SNOOP_FRAMEWORK[name])
        self.snoops += 1
        for _ in range(self.RSP_TIMEOUT_CYCLES):
            if len(self.grant_log) > n:
                break
            await self._negedge_settled()
        else:
            raise RuntimeError(f"{label}: snoop grant never observed")
        exp = self.grant_log[n]
        self._score(f"{label} crresp (bfm)", int(result.crresp.value),
                    exp['exp_crresp'])
        if (exp['exp_crresp'] >> CRRESP_DT) & 1:
            self._score(f"{label} beat count", len(result.data),
                        self.FILL_BEATS)
            for b in range(min(len(result.data), self.FILL_BEATS)):
                self._score(f"{label} beat{b} data", result.data[b],
                            self._beat_of_line(exp['cd'], b))
        else:
            self._score(f"{label} no CD beats", len(result.data), 0)

    # ------------------------------------------------------------------
    # scenarios
    # ------------------------------------------------------------------
    async def _s_init_walk(self):
        d = self.dut
        # present a request mid-walk: the GAXI master holds valid until
        # the D-3 walk completes; the request skid may absorb it, but the
        # lookup stage must never accept it early (a lookup before walk
        # completion is illegal, MAS ch03 option 1)
        send_task = cocotb.start_soon(self._send(
            self._compose_addr(0, 0), 0, label='init_probe'))
        cycles = 0
        saw_busy = False
        while True:
            await self._negedge_settled()
            cycles += 1
            if cycles > self.SETS * 4 + 200:
                raise RuntimeError("init walk never completed")
            if int(d.init_busy.value):
                saw_busy = True
                self._score("init: no lookup-stage accept during the walk",
                            int(d.u_top.u_control.lkup_valid_i.value)
                            & int(d.u_top.u_control.lkup_ready_o.value), 0)
            else:
                break
        self._score("init: walk observed", saw_busy, True)
        self._score("init: walk bounded", cycles <= self.SETS + 20, True)
        await send_task
        await self._await_rsp(0, 'init_probe')
        self._scenario('InitWalk')

    async def _s_hit_sequence(self):
        s0 = 0
        a1 = lambda beat=0: self._compose_addr(0x10, s0, beat)
        a2 = lambda beat=0: self._compose_addr(0x11, s0, beat)

        await self._txn(a1(), 0, label='hit:miss_rd')           # I -> S
        await self._txn(a1(), 0, label='hit:rd_S')
        await self._txn(a1(3), 0, label='hit:rd_S_b3')
        await self._txn(a1(), 1, be=0x0F, wdata=0x1122334455667788,
                        label='hit:upgrade_S')                  # S -> M (CU)
        await self._txn(a1(), 1, be=0xFF, wdata=0xDEADBEEFCAFEF00D,
                        label='hit:wr_M')
        await self._txn(a1(), 0, label='hit:rd_M')
        await self._txn(a2(), 0, label='hit:miss_rd_2')
        await self._txn(a2(), 0, label='hit:rd_S_2')
        await self._txn(a1(), 0, label='hit:rd_M_keep')
        self._scenario('HitSequence')

    async def _s_miss_sequence(self):
        sc = self.SETS - 1
        for i in range(self.WAYS):
            await self._txn(self._compose_addr(0x30 + i, sc), 0,
                            label=f'miss_clean:fill[{i}]')
        await self._txn(self._compose_addr(0x38, sc), 0,
                        label='miss_clean:evict')

        sd = self.SETS // 2
        await self._txn(self._compose_addr(0x40, sd), 1,
                        label='miss_dirty:wr_miss')             # I -> M
        for i in range(1, self.WAYS):
            await self._txn(self._compose_addr(0x40 + i, sd), 0,
                            label=f'miss_dirty:fill[{i}]')
        await self._txn(self._compose_addr(0x48, sd), 0,
                        label='miss_dirty:evict')               # dirty evict
        await self._txn(self._compose_addr(0x40, sd), 0,
                        label='miss_dirty:refetch')  # WB payload round-trip

        se = (self.SETS // 4) * 3
        await self._txn(self._compose_addr(0x50, se, 2), 1, be=0x3C,
                        wdata=0xAABBCCDDEEFF0011,
                        label='miss_dirty:wr_miss_be')
        await self._txn(self._compose_addr(0x50, se, 2), 0,
                        label='miss_dirty:rd_back_be')
        self._scenario('MissSequence')

    async def _s_be_zero_write(self):
        sz = self.SETS // 8
        az = self._compose_addr(0x68, sz)
        await self._txn(az, 1, be=0x00, wdata=0x0123456789ABCDEF,
                        label='be0:wr_miss')
        await self._txn(az, 1, be=0x00, wdata=0xFEDCBA9876543210,
                        label='be0:wr_hit')
        await self._txn(az, 0, label='be0:rd_back')
        self._scenario('BeZeroWrite')

    async def _s_snoop_sequence(self):
        sset = 2 % self.SETS
        m_addr = self._compose_addr(0x20, sset)
        m_line = self._line_of(m_addr)
        await self._txn(m_addr, 0, label='s_inst')
        await self._txn(m_addr, 1, be=(1 << self.STRB_W) - 1,
                        wdata=0x0BAD_0000_0000_0000, label='s_dirty')
        # READ_SHARED on M: DT+PD+IS, dirty data out, downgrade to S
        await self._snoop(m_line, 'SNOOP_READ_SHARED', label='s_rs')
        self._score("s_rs: line downgraded",
                    self.slot_state.get((sset, self._hit_way(sset, m_line))),
                    'S')
        await self._txn(m_addr, 0, label='s_rd_after')
        # MAKE_INVALID on S: no data, invalidate; CPU access re-fetches
        await self._snoop(m_line, 'SNOOP_MAKE_INVALID', label='s_mi')
        await self._txn(m_addr, 0, label='s_refetch')
        # READ_UNIQUE on I: no transfer
        await self._snoop(m_line, 'SNOOP_READ_UNIQUE', label='s_ru')
        self._scenario('SnoopSequence')

    async def _s_snoop_pending_fill(self):
        # the pending-fill bypass with PF_GUARD: a snoop for the in-flight
        # fill's line answers at the post-fill state; DataTransfer only
        # once every beat has landed
        sp = 5
        self.set_profile('slow')
        pf0 = self.pf_grants
        line_x = self._line_of(self._compose_addr(0x70, sp))
        n = await self._send(self._compose_addr(0x70, sp), 1,
                             wdata=0x1122334455667788, label='pf:wr_miss')
        # let the fill's AR land, then snoop mid-flight (beats < full) --
        # a pre-AR snoop is the Invalid row (no bypass resolution), so the
        # pin needs the AR observed first (the fixed-wait version missed
        # the window at the tiny geometry under RANDOM)
        for _ in range(self.RSP_TIMEOUT_CYCLES):
            e = self.entries.get(line_x)
            if e is not None and e['ar']:
                break
            await self._negedge_settled()
        else:
            raise RuntimeError("pf: the write-miss fill never launched")
        await self._snoop(line_x, 'SNOOP_READ_SHARED', label='pf:rs_mid')
        await self._snoop(line_x, 'SNOOP_READ_UNIQUE', label='pf:ru_mid')
        await self._await_rsp(n, 'pf:rsp')
        self.set_profile('fast')
        self._score("pf: bypass resolutions exercised",
                    self.pf_grants > pf0, True)
        self._scenario('SnoopPendingFill')

    async def _s_pend_armed_downgrade_ro(self):
        """BUG-004 (the Task-12 grid find): an in-flight WRITE-miss fill
        takes READ_SHARED (arms pend_eff DOWNGRADE_S) then READ_ONCE.
        The effect's next state chains against the ARMED S -- RO is an
        S-fixed-point -- so the fill commits S with the store merged.
        The pre-fix RTL resolved RO against the original post-fill M,
        armed INVALIDATE_I, and silently dropped the store.  The
        lockstep pend-effect tap pins every arm; the post-commit slot
        state and the readback pin the outcome (a dropped store refetches
        stale memory)."""
        sp = 6 % self.SETS
        addr = self._compose_addr(0x88, sp)
        line_x = self._line_of(addr)
        self.set_profile('slow')
        n = await self._send(addr, 1, be=(1 << self.STRB_W) - 1,
                             wdata=0xB004_D0A6_0000_0000 | sp,
                             label='b4:wr_miss')
        # wait for the fill's AR (a pre-AR snoop is the Invalid row with
        # no effect -- the corner needs the pending-fill bypass), then:
        # RS arms DOWNGRADE_S; RO must leave the armed downgrade alone
        for _ in range(self.RSP_TIMEOUT_CYCLES):
            e = self.entries.get(line_x)
            if e is not None and e['ar']:
                break
            await self._negedge_settled()
        else:
            raise RuntimeError("b4: the write-miss fill never launched")
        await self._snoop(line_x, 'SNOOP_READ_SHARED', label='b4:rs')
        await self._snoop(line_x, 'SNOOP_READ_ONCE', label='b4:ro')
        await self._await_rsp(n, 'b4:rsp')
        self.set_profile('fast')
        self._score("b4: fill committed the armed downgrade (S, not I)",
                    self._slot_state_of(line_x), 'S')
        # the store survived: the read hits S and returns the merged data
        await self._txn(addr, 0, label='b4:readback')
        self._score("b4: readback hits (no refetch)",
                    self.accept_log[-1], 'hit')
        self._scenario('PendArmedDowngradeRO')

    async def _s_victim_claim_stall(self):
        """The Task-6-review deferred pin: w_victim_claimed (the
        claim-aware victim check) as the SOLE stall cause.  One live claim
        in a set; read hits to the other ways walk the LRU victim back
        onto the claimed way; then a true miss into the set stalls
        set_oversubscribed with every other contributor provably absent
        (mshr_set_full / mshr_full / WB-full / capture / WB-race /
        upgrade-way all scored low, from the ports + the model).  The
        stall releases when the conflicting entry's commit retires (the
        documented release), and the miss then allocates.

        LRU-only construction: only LRU lets hits reorder the victim onto
        the claim (FIFO ignores hits, RANDOM's draw is hit-independent --
        those policies reach the same stall organically in the soak)."""
        if self.REPL_POLICY != REPL_LRU:
            self.log.info("VictimClaimStall: LRU-only construction "
                          "(hit reordering); skipped for policy "
                          f"{REPL_NAMES[self.REPL_POLICY]}")
            return
        uc = self.dut.u_top.u_control
        s = 3 % self.SETS
        tag0 = 0xA0
        # one resident line per way but one (the claim takes the last)
        for i in range(self.WAYS - 1):
            await self._txn(self._compose_addr(tag0 + i, s), 0,
                            label=f'vc:fill[{i}]')
        # the one claim: a fresh read miss, held in flight by glacial
        # fills (the hit walk must land inside the fill window)
        self.set_profile('glacial')
        line_a = self._line_of(self._compose_addr(tag0 + self.WAYS - 1, s))
        n_a = await self._send(self._compose_addr(tag0 + self.WAYS - 1, s),
                               0, label='vc:claim')
        for _ in range(self.RSP_TIMEOUT_CYCLES):
            if line_a in self.entries:
                break
            await self._negedge_settled()
        else:
            raise RuntimeError("vc: the claim's alloc was never observed")
        claim_way = self.entries[line_a]['way']
        # hits to the other ways walk the victim onto the claim (each hit
        # makes its way MRU; the claim way -- MRU from its own alloc --
        # sinks one rank per hit, WAYS-1 hits at most).  The hits are
        # SEND-ONLY: J4 releases every response in issue order, so an
        # awaited hit would serialize behind the claim's (glacial) fill;
        # the policy update the walk needs happens at the lookup ACCEPT
        # (observed via the accept log), and the responses are collected
        # at the end.
        hit_ns = []
        for _ in range(self.WAYS):
            v = self.lru.victim(s)
            if v == claim_way:
                break
            vline = self.tags.get((s, v))
            self._score("vc: hit target is a valid unclaimed line",
                        vline is not None
                        and self.slot_state.get((s, v), 'I') != 'I'
                        and not self._claimed(s, v), True)
            if vline is None:
                break
            al0 = len(self.accept_log)
            hit_ns.append(await self._send(self._base_of(vline), 0,
                                           label='vc:hit'))
            # the walk's next step reads the model victim AFTER this
            # hit's accept landed (the skid may hold the request a cycle
            # past the GAXI handshake)
            for _ in range(200):
                if len(self.accept_log) > al0:
                    break
                await self._negedge_settled()
            else:
                raise RuntimeError("vc: walk hit never accepted")
            self._score("vc: walk access was a hit",
                        self.accept_log[-1], 'hit')
        self._score("vc: hits walked the victim onto the claimed way",
                    self.lru.victim(s), claim_way)
        self._score("vc: exactly one live claim in the set",
                    sum(1 for e in self.entries.values()
                        if e['set'] == s), 1)
        # the miss that observes the claim-aware stall
        line_b = self._line_of(self._compose_addr(tag0 + self.WAYS, s))
        stall_cycles = 0
        send_task = cocotb.start_soon(self._send(
            self._compose_addr(tag0 + self.WAYS, s), 0,
            label='vc:stall_miss'))
        # the window runs until the miss's ALLOC is observed (the lookup
        # accept -- the GAXI skid may absorb the request earlier, so the
        # send task completing is not the accept)
        for _ in range(self.RSP_TIMEOUT_CYCLES):
            await self._negedge_settled()
            if int(uc.lkup_stall_o.value) and int(uc.lkup_valid_i.value):
                self._score("vc: stall reason is set_oversubscribed",
                            int(uc.lkup_stall_reason_o.value),
                            STALL_SET_OVERSUB)
                # the sole-cause proof: every other contributor to the
                # classify is provably absent, so the stall IS
                # w_victim_claimed
                self._score("vc: not mshr_set_full",
                            int(uc.mshr_set_full_i.value), 0)
                self._score("vc: not mshr_full",
                            int(uc.mshr_full_i.value), 0)
                self._score("vc: WB not full",
                            int(uc.wb_full_i.value), 0)
                self._score("vc: no capture streaming",
                            int(uc.cap_busy_o.value), 0)
                self._score("vc: request line not in the WB (no "
                            "drain race)", line_b in self.wb, False)
                self._score("vc: no upgrade blocks the victim way",
                            self.upgr['valid']
                            and self.upgr['set'] == s
                            and self.upgr['way'] == self.lru.victim(s),
                            False)
                stall_cycles += 1
            if line_b in self.entries:
                break
        else:
            raise RuntimeError("vc: the stalling miss never allocated")
        n_b = await send_task
        self._score("vc: claim-aware stall observed", stall_cycles > 0,
                    True)
        await self._await_rsp(n_a, 'vc:claim_rsp')
        await self._await_rsp(n_b, 'vc:miss_rsp')
        self.set_profile('fast')
        self.log.info(f"VictimClaimStall: {stall_cycles} stall cycles, "
                      f"sole cause w_victim_claimed")
        self._scenario('VictimClaimStall')

    async def _s_killed_upgrade(self):
        """The Task-8 coherence corner: a pre-grant invalidating snoop to
        the in-flight upgrade's line.  The snoop writes I to the tag; the
        CU commit must DEMOTE its install to I (never resurrect M).  The
        commit-handler score is the pin; this scenario drives the corner
        and checks it was actually exercised."""
        su = min(15, self.SETS - 1)
        line_a = self._line_of(self._compose_addr(0x78, su))
        await self._txn(self._compose_addr(0x78, su), 0,
                        label='ku:rd_a')                        # A -> S
        kills0 = self.kill_count
        cu0 = self.cu_launches
        self.set_profile('slow')   # stretch the CU's AR/R window
        n = await self._send(self._compose_addr(0x78, su), 1, be=0xFF,
                             wdata=0x13579BDF2468ACE0, label='ku:upgrade')
        # wait for the CU launch, then snoop the line before the CU's
        # (slow) response completes
        for _ in range(self.RSP_TIMEOUT_CYCLES):
            if self.cu_launches > cu0:
                break
            await self._negedge_settled()
        else:
            raise RuntimeError("ku: upgrade launch never observed")
        await self._snoop(line_a, 'SNOOP_MAKE_INVALID', label='ku:mi')
        await self._await_rsp(n, 'ku:rsp')
        self.set_profile('fast')
        self._score("ku: the corner was exercised (kill recorded)",
                    self.kill_count > kills0, True)
        self._score("ku: line ends Invalid",
                    self._slot_state_of(line_a), 'I')
        # a later read misses and re-fetches from memory
        await self._txn(self._compose_addr(0x78, su), 0, label='ku:refetch')
        self._scenario('KilledUpgrade')

    def _slot_state_of(self, line):
        set_idx = self._set_of_line(line)
        for w in range(self.WAYS):
            if self.tags.get((set_idx, w)) == line:
                return self.slot_state.get((set_idx, w), 'I')
        return 'I'

    async def _s_illegal_state(self):
        """Sticky CTRL_ERROR (MAS ch02/01): corrupt the commit FSM state
        register with a reserved encoding; the pipeline must latch ERROR,
        dead-stop accepts, and only reset exits."""
        d = self.dut
        await self._txn(self._compose_addr(0x60, 1), 0, label='err:pre')
        await self._await_all_responses('err:quiesce')
        d.u_top.u_control.r_cmt_state.value = 0x9   # reserved encoding
        for _ in range(4):
            await self._negedge_settled()
        self._score("error: CTRL_ERROR sticky",
                    int(d.ctrl_state.value), AMBER_CTRL_ERROR)
        self._score("error: accepts dead-stopped",
                    int(d.cpu_req_wr_ready.value), 0)
        for _ in range(6):
            await self._negedge_settled()
        self._score("error: still sticky",
                    int(d.ctrl_state.value), AMBER_CTRL_ERROR)
        # reset is the only exit; the cache re-initializes and serves
        await self.assert_reset()
        await self.wait_clocks('aclk', 5)
        await self.deassert_reset()
        self._reset_jet_models()
        await self._s_init_walk_recover()
        await self._txn(self._compose_addr(0x61, 1), 0,
                        label='err:post_recover')
        self._scenario('IllegalStateError')

    def _reset_jet_models(self):
        """Reset-side golden state: arrays/repl/engines reset; the memory
        side survives (it is the DRAM)."""
        self.tags = {}
        self.slot_state = {}
        self.pw = {}
        self.entries = {}
        self.entry_by_idx = {}
        self.unlaunched = deque()
        self.launch_q = deque()
        self.upgr = {'valid': False, 'line': None, 'set': 0, 'way': 0,
                     'killed': False}
        self.wb = {}
        self.wb_order = deque()
        self.draining = None
        self.committing = None
        self.rspq = deque()
        self.exp_sn_tagwr = deque()
        self.lru = make_repl_model(self.REPL_POLICY, self.SETS, self.WAYS)

    async def _s_init_walk_recover(self):
        """Post-reset init walk: wait it out (no probe this time)."""
        d = self.dut
        for _ in range(self.SETS * 4 + 200):
            await self._negedge_settled()
            if not int(d.init_busy.value):
                return
        raise RuntimeError("post-reset init walk never completed")

    async def _s_response_tag_order(self):
        """Interleaved hits/misses/merges: a read miss (slow fill), a hit
        to a resident line behind it, a merge onto the fill -- releases
        must come back in issue order (J4; the FIFO pop scores every
        release against the issue-order head, so any re-order corrupts
        the data check; this scenario pins that the mix itself ran)."""
        st = 3
        await self._txn(self._compose_addr(0x91, st), 0,
                        label='ord:resident')                   # resident S
        self.set_profile('slow')
        n0 = await self._send(self._compose_addr(0x90, st), 0,
                              label='ord:miss_a')               # slow miss
        n1 = await self._send(self._compose_addr(0x91, st), 0,
                              label='ord:hit_b')                # hit behind
        n2 = await self._send(self._compose_addr(0x90, st, 1), 0,
                              label='ord:merge_c')              # merge on A
        await self._await_rsp(n2, 'ord:rsp_c')
        self.set_profile('fast')
        self._score("ord: responses in issue order",
                    (n0, n1, n2), (n0, n0 + 1, n0 + 2))
        self._score("ord: launches happened", self.launch_count > 0, True)
        self._scenario('ResponseTagOrder')

    async def _s_windowed_fill_start(self):
        mx = max(self.launch_waits) if self.launch_waits else 0
        self._score("windowed fill start: max wait within bound",
                    mx <= self.FILL_LAUNCH_WINDOW, True)
        self._score("windowed fill start: launches observed",
                    self.launch_count >= self.WAYS + 4, True)
        self._score("cap_busy contract: no launch during a capture",
                    self.cap_busy_violations, 0)
        self.log.info(f"WindowedFillStart: {self.launch_count} launches, "
                      f"max wait {mx}")
        self._scenario('WindowedFillStart')

    # ------------------------------------------------------------------
    # FULL content (MAS ch06/02: beyond amber's soak)
    # ------------------------------------------------------------------
    def _reset_window_stats(self):
        self.win_max_occupancy = 0
        self.win_max_wb = 0
        self.win_max_set_claims = 0

    async def _s_mshr_saturation(self):
        """MSHR-pressure miss stream with concurrent hits + snoops
        (ch06/02).  The lookup allocates at most one entry per
        fill-launch window (the launch register waits for the
        single-outstanding fill engine), so the file's sustainable
        occupancy is the engine pipeline (one filling + one
        launch-pending entry) plus the done-not-retired backlog the
        commit pacer allows -- the stream below adds merge pressure on
        every other line (a deep commit list lags the fill engine) to
        maximize the backlog.  The file fills to MSHR_COUNT literally at
        the K=2 corner (and the overflow miss observes the mshr_full
        stall there); at the wider cells the engine-paced plateau
        (>= 3 live entries sustained over the stream) is the pin -- the
        wider file is burst headroom by design (single-outstanding
        l1_fill, unchanged from amber).
        """
        u = self.dut.u_top
        uc = u.u_control
        K = self.MSHR_COUNT
        tag0 = 0x100
        self._reset_window_stats()
        # resident hit lines (fast fills, awaited) in a set the stream
        # reaches last (tiny geometry: K == SETS covers every set -- one
        # claim in the hit set is still < WAYS, so the hits stay hits
        # unless the claim evicts one, which the monitor scores either
        # way)
        hit_set = self.SETS - 1
        hit_addrs = []
        for i in range(2):
            a = self._compose_addr(tag0 + 0x40 + i, hit_set)
            await self._txn(a, 0, label=f'sat:resident[{i}]')
            hit_addrs.append(a)

        # merge pressure only where the tag ring (RSP_DEPTH = K+2) can
        # hold it: at K=2 the ring is 4 deep and a heavy line alone would
        # fill it before the file does
        n_merge = 0 if K <= 2 else 3
        self.set_profile('fast')
        ns = []
        stall0 = self.stall_cycles.get(STALL_MSHR_FULL, 0)
        n_lines = 2 * K + 4
        for i in range(n_lines):
            set_i = i % self.SETS
            ns.append(await self._send(
                self._compose_addr(tag0 + i, set_i), 0, label=f'sat:m{i}'))
            if n_merge and i % 2 == 0:
                # merge pressure on the in-flight fill: the deep commit
                # list lags the fill engine, building the backlog
                for j in range(n_merge):
                    ns.append(await self._send(
                        self._compose_addr(tag0 + i, set_i,
                                           (j + 1) % self.FILL_BEATS),
                        0, label=f'sat:m{i}g{j}'))
            if i == n_lines // 2:
                # concurrent hit + snoop mid-stream (hit-under-miss),
                # send-only: J4 releases its response behind the fills'
                ns.append(await self._send(hit_addrs[0], 0,
                                           label='sat:hit_mid'))
                await self._snoop(self._line_of(hit_addrs[1]),
                                  'SNOOP_READ_SHARED', label='sat:sn_mid')
        # the RTL occupancy gauge tracks the model through the stream (the
        # gauge's r_valid clear and the model's retire pop straddle one
        # posedge at a retire boundary, so allow a few cycles to converge)
        occ_match = False
        for _ in range(4):
            await self._negedge_settled()
            if int(u.u_mshr.occupancy_o) == len(self.entries):
                occ_match = True
                break
        self._score("sat: RTL occupancy == model", occ_match, True)
        self._score("sat: occupancy reached the sustainable plateau",
                    self.win_max_occupancy >= min(K, 3), True)
        # the overflow miss: at the K=2 corner the file fills and the
        # stall is mshr_full; wider cells absorb the stream without
        # backpressure (the finding IS the plateau -- the file's depth
        # past the engine pipeline is burst headroom)
        ov_task = cocotb.start_soon(self._send(
            self._compose_addr(tag0 + n_lines, n_lines % self.SETS), 0,
            label='sat:overflow'))
        # a snoop to a live entry's line while the overflow waits
        live = list(self.entries.keys())
        if live:
            await self._snoop(live[0], 'SNOOP_READ_SHARED',
                              label='sat:sn_pend')
        n_ov = await ov_task
        if K <= 2:
            self._score("sat: file filled to MSHR_COUNT",
                        self.win_max_occupancy, K)
            self._score("sat: mshr_full stall observed under the "
                        "overflow",
                        self.stall_cycles.get(STALL_MSHR_FULL, 0) > stall0,
                        True)
        # concurrent hit while the file drains
        ns.append(await self._send(hit_addrs[1], 0, label='sat:hit_late'))
        await self._await_rsp(ns[-1], 'sat:stream')
        await self._await_rsp(n_ov, 'sat:overflow_rsp')
        self._scenario('MshrSaturation')

    async def _s_merge_storm(self):
        """Merge storm (ch06/02): repeated aliases onto one outstanding
        fill.  An RU fill (write miss) is held in flight by slow
        responders; a storm of reads+writes to the same line rides the
        merge list to capacity (the merge-list-full stall reports
        mshr_full), the fill completing mid-storm freezes the list (the
        commit_in_progress stall), and the post-commit aliases hit.
        Every response is scored by the event stream (a read observes
        exactly the writes that precede it)."""
        sm = 9 % self.SETS
        t0 = 0x180
        line_x = self._line_of(self._compose_addr(t0, sm))
        full_be = (1 << self.STRB_W) - 1
        self._reset_window_stats()
        # glacial fills: the storm must overflow the merge list while the
        # fill is still in flight (the list holds MSHR_COUNT requesters)
        self.set_profile('glacial')
        n0 = await self._send(self._compose_addr(t0, sm), 1, be=full_be,
                              wdata=0x5150_5A5A_A5A5_0F0F,
                              label='mgs:alloc')
        for _ in range(self.RSP_TIMEOUT_CYCLES):
            if line_x in self.entries:
                break
            await self._negedge_settled()
        else:
            raise RuntimeError("mgs: the storm fill never allocated")
        depth = 2 * self.MSHR_COUNT + 2
        stall_mshr0 = self.stall_cycles.get(STALL_MSHR_FULL, 0)
        stall_commit0 = self.stall_cycles.get(STALL_COMMIT, 0)
        merges0 = self.merge_count
        ns = []
        for i in range(depth):
            we = 1 if (i % 3 == 2) else 0
            ns.append(await self._send(
                self._compose_addr(t0, sm, i % self.FILL_BEATS), we,
                label=f'mgs:m{i}'))
        self.set_profile('fast')
        await self._await_rsp(n0, 'mgs:alloc_rsp')
        await self._await_rsp(ns[-1], 'mgs:tail')
        self._score("mgs: merges observed", self.merge_count > merges0,
                    True)
        self._score("mgs: merge-list-full stall observed (mshr_full)",
                    self.stall_cycles.get(STALL_MSHR_FULL, 0)
                    > stall_mshr0, True)
        self._score("mgs: commit-in-progress stall observed",
                    self.stall_cycles.get(STALL_COMMIT, 0)
                    > stall_commit0, True)
        self._scenario('MergeStorm')

    async def _s_set_oversubscription(self):
        """Set-oversubscription burst (ch06/02): a burst of misses into
        ONE set fills its way claims; the next miss stalls
        set_oversubscribed (or mshr_full when the file is the smaller
        resource) until a commit frees a claim.  The pin: per-set live
        claims peak at min(WAYS, MSHR_COUNT) -- reached exactly at the
        min<=2 cells (the claim window is one fill+commit) and floored
        at 3 elsewhere.

        The v4 construction (the window is L_commit0 > 2 fast fill
        times, because the overflow miss allocates at fill_done(2) and
        claim 0 frees at commit-0 retire):
          1. scrub the set (clean residents: a dirty victim's capture
             would pace the burst with WB stalls),
          2. GLACIAL profile; send the miss PAIR first (entry 1's launch
             pends behind fill 0 -- the single-outstanding engine paces
             the later allocs, so the pair must not sit behind merge
             sends), then the merge writes onto line 0 (they all land in
             the glacial fill window; the per-entry merge list caps at
             MSHR_COUNT),
          3. FAST profile: fill 0's remaining beats hurry, commit 0 runs
             with a full merge list (merge slots yield to fill 1's
             streaming beats), fills 1..N stream back-to-back, the
             overflow misses alloc two fill-times later with claims 0..3
             still live -> the stall fires.
        At K=4/WAYS=4 the window is unreachable by construction (the
        merge cap K bounds commit-0's lag at ~19 cycles against the
        ~26-cycle requirement; the plateau finding already moves the
        MSHR-full property to the unit TB + the formal K=2 corner), so
        the stall pin there is the claim floor only -- recorded in the
        testplan/dv-matrix."""
        so = 13 % self.SETS
        K = self.MSHR_COUNT
        target = min(self.WAYS, K)
        self._reset_window_stats()
        exp_stall = (STALL_SET_OVERSUB if K > self.WAYS
                     else STALL_MSHR_FULL)
        stall0 = self.stall_cycles.get(exp_stall, 0)
        stalls_snapshot = dict(self.stall_cycles)
        # 1. scrub the set: install WAYS clean (read-fill) lines, evicting
        #    any dirty residents left by earlier scenarios
        for i in range(self.WAYS):
            await self._txn(self._compose_addr(0x140 + i, so), 0,
                            label=f'ovb:scrub{i}')
        # 2. the pair, then the deep merge list on line 0, all inside
        #    fill 0's glacial window
        self.set_profile('glacial')
        n_merge = min(K - 1, 2 * self.FILL_BEATS - 1)
        ns = []
        for i in range(2):
            ns.append(await self._send(self._compose_addr(0x1C0 + i, so),
                                       1, label=f'ovb:{i}'))
        for j in range(n_merge):
            ns.append(await self._send(
                self._compose_addr(0x1C0, so, (j + 1) % self.FILL_BEATS),
                1, label=f'ovb:0g{j}'))
        # 3. the burst: fill 0 hurries to done, commit 0 lags on the full
        #    merge list while fills 1..N stream
        self.set_profile('fast')
        for i in range(2, self.WAYS + 2):
            ns.append(await self._send(self._compose_addr(0x1C0 + i, so),
                                       1, label=f'ovb:{i}'))
        await self._await_rsp(ns[-1], 'ovb:tail')
        delta = {STALL_NAMES.get(k, k):
                 v - stalls_snapshot.get(k, 0)
                 for k, v in self.stall_cycles.items()
                 if v - stalls_snapshot.get(k, 0)}
        self.log.info(f"ovb: win_max_set_claims={self.win_max_set_claims} "
                      f"stall deltas={delta}")
        floor = target if target <= 2 else 3
        # RANDOM: the LFSR victim pick does not advance during a stall, so
        # an overflow miss whose draw lands on a claimed way stalls until
        # THAT way's commit retires -- the burst serializes behind the
        # commits and claims never pile past the pair (the set_oversub
        # stall itself fires richly: a random pick on a claimed way with
        # just 2 live claims).  The pile floor is an LRU/FIFO property.
        if self.REPL_POLICY == REPL_RANDOM:
            floor = min(floor, 2)
        self._score("ovb: per-set claims reached the pressure floor",
                    self.win_max_set_claims >= floor, True)
        if target <= 2:
            self._score("ovb: per-set claims peaked at the smaller "
                        "resource", self.win_max_set_claims, target)
        # the stall pin where the window is constructible (the docstring:
        # K=4/WAYS=4 is the unreachable cell)
        stall_constructible = not (self.WAYS >= 4 and K == 4)
        if stall_constructible:
            self._score(f"ovb: {STALL_NAMES[exp_stall]} stall observed",
                        self.stall_cycles.get(exp_stall, 0) > stall0, True)
        else:
            self.log.info("ovb: K=4/WAYS=4 -- the stall window is not "
                          "constructible (merge-cap-bounded commit lag "
                          "< 2 fill times); the floor pin stands, the "
                          "stall is pinned at the K=2/WAYS=2 cells + the "
                          "unit TB + the formal K=2 corner")
        self._scenario('SetOversubscription')

    async def _s_composed_corner(self):
        """The composed corner, reached dynamically (ch06/02): MSHR
        pressure AND WB-full with snoops soaking through -- the dynamic
        complement of the formal proof (ch05/01).  Slow responders
        stretch fills and drains; a write-biased miss stream over a
        tight set window makes dirty-victim captures outpace the drain
        engine (the WB fills to VICTIM_DEPTH) while the miss stream
        drives the MSHR file to its engine-paced plateau (the file fills
        literally at the K=2 corner); snoops rotate across WB lines
        (snarf), pending entries (bypass), and the arrays.  The monitor
        counts the cycles at full occupancy AND full WB (the corner is
        asserted as simultaneous at K=2; at wider files the plateau +
        WB-full peaks plus the snoop soak are the pin)."""
        rng = random.Random((self.SEED << 8) | 0xC0)
        self._reset_window_stats()
        self.set_profile('drainslow')
        corner0 = self.corner_cycles
        sn0 = self.snoops
        set_window = max(2, min(self.SETS, 2 * self.WAYS))
        budget = 30 * (self.MSHR_COUNT + self.VICTIM_DEPTH) + 200
        tag0 = 0x200
        pending = []
        it = 0
        while it < budget:
            a = self._compose_addr(tag0 + (it % 0x180),
                                   rng.randrange(set_window))
            n = await self._send(a, 1 if rng.random() < 0.6 else 0,
                                 label=f'cc:{it}')
            pending.append(n)
            it += 1
            if it % 4 == 3:
                if self.wb and rng.random() < 0.4:
                    tgt = rng.choice(list(self.wb.keys()))
                elif self.entries and rng.random() < 0.5:
                    tgt = rng.choice(list(self.entries.keys()))
                else:
                    tgt = rng.randrange(self.SPAN)
                await self._snoop(tgt, rng.choice(list(SNOOP_CODES)),
                                  label=f'cc:sn{it}')
            while len(pending) > self.MSHR_COUNT:
                await self._await_rsp(pending.pop(0), 'cc:pace')
            if (self.win_max_occupancy >= min(self.MSHR_COUNT, 3)
                    and self.win_max_wb >= self.VICTIM_DEPTH
                    and (self.MSHR_COUNT > 2 or self.corner_cycles > corner0)
                    and self.snoops - sn0 >= 6):
                break
        self.set_profile('fast')
        for n in pending:
            await self._await_rsp(n, 'cc:tail')
        self._score("cc: MSHR pressure reached the plateau",
                    self.win_max_occupancy >= min(self.MSHR_COUNT, 3),
                    True)
        self._score("cc: WB-full reached", self.win_max_wb,
                    self.VICTIM_DEPTH)
        if self.MSHR_COUNT <= 2:
            self._score("cc: composed corner observed (MSHR-full AND "
                        "WB-full)", self.corner_cycles > corner0, True)
        self._score("cc: snoop soak during the corner",
                    self.snoops - sn0 >= 6, True)
        self.log.info(f"ComposedCorner: {it} iterations, "
                      f"{self.corner_cycles - corner0} corner cycles, "
                      f"{self.snoops - sn0} snoops")
        self._scenario('ComposedCorner')

    # ------------------------------------------------------------------
    # randomized oracle lockstep soak
    # ------------------------------------------------------------------
    async def _random_soak(self, n):
        for i in range(n):
            if random.random() < 0.25:
                self.set_profile(random.choice(
                    ['fast', 'normal', 'slow']))
            await self._send(self._rand_addr(),
                             1 if random.random() < 0.5 else 0,
                             label=f'r{i}')
            if random.random() < 0.35:
                # snoop a random line -- biased toward lines this txn
                # touches (pending-fill / upgrade windows)
                line = random.randrange(self.SPAN)
                if random.random() < 0.4 and self.entries:
                    line = random.choice(list(self.entries.keys()))
                await self._snoop(line,
                                  random.choice(list(SNOOP_CODES)),
                                  label=f'r{i}:sn')
            for _ in range(random.randrange(2)):
                await self._negedge_settled()
        self.set_profile('fast')
        await self._await_all_responses('soak')
        self._scenario('OracleLockstepSoak')

    # ------------------------------------------------------------------
    # quiescence + report
    # ------------------------------------------------------------------
    async def _quiesce(self):
        await self._await_all_responses('final')
        # let the last eviction's drain / commit retire land (the response
        # releases ahead of the WB drain completing)
        for _ in range(self.RSP_TIMEOUT_CYCLES):
            if not self.wb and not self.entries and not self.upgr['valid']:
                break
            await self._negedge_settled()
        self._score("quiescent: no pending snoop effects",
                    len(self.exp_sn_tagwr), 0)
        self._score("quiescent: WB drained", len(self.wb), 0)
        self._score("quiescent: no live MSHR entries", len(self.entries), 0)
        self._score("quiescent: no in-flight upgrade",
                    self.upgr['valid'], False)
        self._score("quiescent: ctrl not in ERROR",
                    int(self.dut.ctrl_state.value) == AMBER_CTRL_ERROR,
                    False)

    async def run(self):
        await self._s_init_walk()
        await self._s_hit_sequence()
        await self._s_miss_sequence()
        await self._s_be_zero_write()
        await self._s_snoop_sequence()
        await self._s_snoop_pending_fill()
        await self._s_pend_armed_downgrade_ro()
        await self._s_victim_claim_stall()
        await self._s_killed_upgrade()
        await self._s_response_tag_order()
        await self._s_windowed_fill_start()
        await self._s_illegal_state()

        if self.TEST_LEVEL == 'full':
            # the ch06/02 FULL content beyond amber's soak
            await self._s_mshr_saturation()
            await self._s_merge_storm()
            await self._s_set_oversubscription()
            await self._s_composed_corner()

        if self.TEST_LEVEL in ('func', 'full'):
            # the amber FULL suite re-run on jet unchanged: 10k
            # transactions of randomized oracle lockstep with the
            # interleaved snoop soak
            await self._random_soak(self.FULL_TXN[self.TEST_LEVEL])

        await self._quiesce()
        return self.mismatches == 0

    def get_test_report(self):
        return {
            'checks': self.checks,
            'mismatches': self.mismatches,
            'txns': self.txns,
            'snoops': self.snoops,
            'launches': self.launch_count,
            'max_launch_wait': max(self.launch_waits)
                               if self.launch_waits else 0,
            'mshr_count': self.MSHR_COUNT,
            'victim_depth': self.VICTIM_DEPTH,
            'repl_policy': REPL_NAMES[self.REPL_POLICY],
            'max_occupancy': self.max_occupancy,
            'max_wb': self.max_wb,
            'corner_cycles': self.corner_cycles,
            'merges': self.merge_count,
            'stall_cycles': {STALL_NAMES.get(k, k): v
                             for k, v in self.stall_cycles.items()},
            'scenarios': self.scenarios,
        }
