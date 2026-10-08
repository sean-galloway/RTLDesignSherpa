"""
amber_snoop_resp testbench -- ACE-level closed loop with the real control

Task 7 integration: the DUT is the harness amber_snoop_resp_th (REAL
amber_control + landed amber_tag_array/amber_data_array/amber_repl + REAL
amber_snoop_resp on the house axi4ace_snoop_slave transport). The
cocotb-framework AXI4ACESnoopMaster drives the m_axi_* ACE pins; a frontend
stub and fill/drain timing stubs (D-12: timing only, never protocol) keep
random CPU traffic flowing on port A while snoops land on the ACE pins -- both
ports live. The evolving line-state model (mem / cache_data / line_state /
tags / slot_state / lru, inherited from the control TB) is the scoreboard:
every snoop response is decoded at the model's reference state and every CPU
transaction is scored against the oracle lockstep.

Reuse: this class extends AmberControlTB (dv/tbclasses/amber_control_tb.py)
for the partner stubs, the every-cycle monitors, the tap-event stream and the
golden models -- the control suite keeps testing the raw-pin directed paths
via test_amber_control.py; this TB drives every snoop through the ACE
boundary and scores the adapter end to end.

Scenarios:
  table30_directed (gate)   one snoop per reachable HAS Table 3.0 cell (24);
                            M/S seeded by real CPU transactions, E through the
                            TB tag-array backdoor (the CPU path never
                            installs E -- MAS ch02 install states are S/M; the
                            backdoor keeps the E rows covered at this level),
                            I left untouched
  pool soak (func/full)     64-line pool, randomized snoops over the evolving
                            model, refill = the CPU re-acquiring the line
                            (read -> S, write -> M, backdoor -> E), directed
                            zero-gap same-line pairs, mid-soak idle reset with
                            model reset (the init walk re-invalidates the
                            arrays; the stub-era model-survives-reset fiction
                            is gone)
  SnoopVictimLineDuringGather (func/full)   T5-review composition: the ACE
                            snoop for the dirty VICTIM line is raised during
                            the multi-cycle gather, stalls (never granted in
                            a MISS_VICTIM cycle), grants at MISS_DRAIN and is
                            served from the staged buffer -- both halves
                            pinned separately before, composed here
  real_control_loop (func/full)   NEW: randomized snoops against an amber
                            simultaneously serving random CPU traffic. The
                            loop issues a random request, fires 0..2 snoops
                            while the miss/fill/drain machinery is in flight
                            (pending line -> pending-fill-bypass reference,
                            dirty victim -> staged-buffer reference, clean
                            victim -> stale-entry rule, other lines ->
                            installed state), then scores the whole slice.
                            The mid-transaction snoop effects (post-commit
                            pend) are applied by the concurrent-aware slice
                            scorer, mirroring pend_vld_q.

Compliance: ACEComplianceChecker per transaction -- check_crresp_validity,
check_cr_order (CR in issue order = CR-after-CDLAST per the one-outstanding
contract), check_cd_order with the expected beat count (CDLAST placement).

Levels: gate = directed cells (fast profile); func/full = the soak + loop
under gaxi_backpressure / gaxi_stress. Counts below.

Author: RTL Design Sherpa
Created: 2026-10-06 (closed-loop rewrite 2026-10-08, Task 7)
"""

import os
import random

import cocotb
from cocotb.triggers import FallingEdge, Timer

from CocoTBFramework.components.ace.ace_interfaces import AXI4ACESnoopMaster
from CocoTBFramework.components.ace.ace_transaction import SnoopType
from CocoTBFramework.components.ace.ace_compliance_checker import ACEComplianceChecker
from CocoTBFramework.components.shared.flex_randomizer import FlexRandomizer
from TBClasses.amba.amba_random_configs import GAXI_RANDOMIZER_CONFIGS

from projects.components.cache_ip.amber_mesi_l1.dv.golden.amber_fsm_oracle import (
    SNOOPS as ORACLE_SNOOPS,
    step as oracle_step,
)
from projects.components.cache_ip.amber_mesi_l1.dv.tbclasses.amber_control_tb import (
    AmberControlTB,
    STATE_CODE,
    ACE_READ_SHARED,
    ACE_READ_UNIQUE,
    ACE_CLEAN_UNIQUE,
    ORACLE_REQ_TO_ACE,
    CRRESP_DT,
    ST_IDLE,
    ST_MISS_VICTIM,
    ST_MISS_DRAIN,
)


# oracle snoop name -> framework SnoopType (ACSNOOP[3:0] encoding)
FRAMEWORK_SNOOPS = {
    'SNOOP_READ_SHARED':   SnoopType.READ_SHARED,
    'SNOOP_READ_ONCE':     SnoopType.READ_ONCE,
    'SNOOP_READ_UNIQUE':   SnoopType.READ_UNIQUE,
    'SNOOP_CLEAN_SHARED':  SnoopType.CLEAN_SHARED,
    'SNOOP_CLEAN_INVALID': SnoopType.CLEAN_INVALID,
    'SNOOP_MAKE_INVALID':  SnoopType.MAKE_INVALID,
}


class AmberSnoopRespTB(AmberControlTB):
    """Closed-loop snoop-responder TB: real control + arrays + repl in the
    ACE response path, with random CPU traffic on the second port."""

    # (profile, snoop count for the pool soak, control-stub era semantics kept)
    LEVELS = {
        'gate': ('fast', 0),
        'func': ('gaxi_backpressure', 600),
        'full': ('gaxi_stress', 6000),
    }

    # real_control_loop iterations per level
    LOOP_TXN = {'gate': 0, 'func': 120, 'full': 1200}

    def __init__(self, dut, **kwargs):
        # the snoop-responder geometry grid varies the bus/line width; the
        # control/array geometry stays at the pkg default (the control suite
        # owns the SETS/WAYS axis). NOTE: AmberControlTB.__init__ hardcodes
        # LINE_BYTES/STRB_W/FILL_BEATS at the pkg default (its grid varies
        # SETS/WAYS only) -- read the environment into locals FIRST and
        # restore the responder geometry AFTER super().__init__ runs.
        os.environ.setdefault('SETS', '128')
        os.environ.setdefault('WAYS', '4')
        addr_w = self.convert_to_int(os.environ.get('ADDR_WIDTH', '32'))
        data_w = self.convert_to_int(os.environ.get('DATA_WIDTH', '64'))
        line_b = self.convert_to_int(os.environ.get('LINE_BYTES', '64'))

        super().__init__(dut)

        self.ADDR_WIDTH = addr_w
        self.DATA_WIDTH = data_w
        self.LINE_BYTES = line_b
        self.STRB_W = self.DATA_WIDTH // 8
        self.FILL_BEATS = self.LINE_BYTES // self.STRB_W
        self.OFFSET_BITS = (self.LINE_BYTES - 1).bit_length()
        self.BEAT_BITS = (self.FILL_BEATS - 1).bit_length()
        self.LINE_MASK = (1 << (self.ADDR_WIDTH - self.OFFSET_BITS)) - 1
        self.drain_latency = self.FILL_BEATS + 2

        self.master = AXI4ACESnoopMaster(
            dut=dut, clock=dut.clk, prefix='m_axi_', log=self.log,
            data_width=self.DATA_WIDTH, addr_width=self.ADDR_WIDTH)
        self.ace_checker = ACEComplianceChecker(log=self.log)
        self._ace_seq = 0
        self._cd_seq = 0
        # grant-tap bookkeeping: the monitor stamps every snoop grant; the
        # issuer records the count before issuing and resolves its grant
        # cycle post-hoc (grants are totally ordered == issue order)
        self._gnt_count = 0
        self._cd_idx = 0
        # in-flight transaction metadata, published by _real_control_loop and
        # consulted by the mid-transaction snoop classification
        self.cur_txn = None

        self.profile, self.n_snoops = self.LEVELS.get(
            self.TEST_LEVEL, self.LEVELS['gate'])
        # House pattern (pumice_axi_bfm): amba_random_configs GAXI profiles
        # per channel -- ac is the producer side (valid_delay), cr/cd are
        # consumed by the master BFM (ready_delay).
        chan_cfg = GAXI_RANDOMIZER_CONFIGS[self.profile]
        self.master.ac_channel.set_randomizer(FlexRandomizer(chan_cfg['master']))
        self.master.cr_channel.set_randomizer(FlexRandomizer(chan_cfg['slave']))
        self.master.cd_channel.set_randomizer(FlexRandomizer(chan_cfg['slave']))
        # mid-transaction snoops must grant inside the pending-fill / drain
        # windows (a handful of cycles); the level profiles' AC valid_delay
        # (up to 50 cycles under gaxi_backpressure) would land the grant
        # past the install and change the case the DUT answers. Drive the
        # AC side promptly for those; CR/CD keep the full level
        # backpressure. Quiescent snoops keep the level AC profile.
        self._ac_rand_level = FlexRandomizer(chan_cfg['master'])
        self._ac_rand_fast = FlexRandomizer(
            GAXI_RANDOMIZER_CONFIGS['fast']['master'])
        self._cd_rand_level = FlexRandomizer(chan_cfg['slave'])
        self._cd_rand_fast = FlexRandomizer(
            GAXI_RANDOMIZER_CONFIGS['fast']['slave'])
        self.log.info(f"AmberSnoopRespTB level={self.TEST_LEVEL} profile={self.profile} "
                      f"data_width={self.DATA_WIDTH} line_bytes={self.LINE_BYTES} "
                      f"fill_beats={self.FILL_BEATS} sets={self.SETS} ways={self.WAYS} "
                      f"seed={self.SEED}")

    # ------------------------------------------------------------------
    # clock/reset/monitor
    # ------------------------------------------------------------------
    async def _check_init(self):
        """Width-safe override of the control TB's init-walk check: the
        stray request's be/wdata literals are sized to this geometry
        (STRB_W=4 at the 32-bit bus grid)."""
        d = self.dut
        self._reset_models()
        init_writes = []
        cycles = 0
        stray_left = 3
        d.req_addr.value = self._compose_addr(0x77, 1)
        d.req_we.value = 1
        d.req_be.value = (1 << self.STRB_W) - 1
        d.req_wdata.value = 0x5A5A5A5A5A5A5A5A & ((1 << self.DATA_WIDTH) - 1)
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
                    any(k == 'state' and p == 2 for _, k, p in
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
        d.tb_tag_wr_en.value = 0
        d.tb_tag_wr_way_onehot.value = 0
        d.tb_tag_wr_set.value = 0
        d.tb_tag_wr_tag_state.value = 0
        d.tag_b_set.value = 0
        # NOTE: no snoop_req/snoop_type/snoop_addr/cd_ready_in drives -- in
        # the closed loop those are observation taps of the harness, not TB
        # inputs. All snoops enter through the ACE master.
        await self.assert_reset()
        cocotb.start_soon(self._monitor())
        cocotb.start_soon(self._fill_stub())
        cocotb.start_soon(self._drain_stub())
        cocotb.start_soon(self._victim_way_tracker())
        cocotb.start_soon(self._pf_invariant())
        cocotb.start_soon(self._victim_invariant())
        await self.wait_clocks('clk', 3)
        await self.deassert_reset()

    async def _monitor(self):
        """Tap-event stream: the control TB's monitor plus sn_gnt stamping
        (snoop_req && snoop_ready) and the CD beat counter the pf invariant
        reads (inv_cd_beat is maintained here, every cycle)."""
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
                if int(d.ctrl_data_wr_en.value):
                    kind = 'ctrl_wr'
                elif self._suppress_fill_wr:
                    kind = 'bd_wr'
                else:
                    kind = 'fill_wr'
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
            if int(d.snoop_req.value) and int(d.snoop_ready.value):
                self.events.append((self.cyc, 'sn_gnt', st))
                self._gnt_count += 1
            # CD beat bookkeeping for the pf invariant: inv_cd_beat is the
            # index of the beat PRESENTED this cycle (handshakes completed
            # before it) -- the invariant reads it after this pass, so the
            # increment for a handshake seen now applies next cycle.
            self.inv_cd_beat = self._cd_idx
            if int(d.ctrl_cdvalid.value) and int(d.ctrl_cdready.value):
                self._cd_idx += 1
            elif not int(d.ctrl_cdvalid.value):
                self._cd_idx = 0

    # ------------------------------------------------------------------
    # line-state seeding on the closed loop
    # ------------------------------------------------------------------
    async def _backdoor_tag_write(self, set_idx, way, line, state_name, label):
        """TB tag-array backdoor: install {line, state} at (set, way). Used
        only for E seeding (the CPU path never installs E) and only from
        quiescent points -- the harness mux gives the backdoor the write
        port, so a collision with control would be TB misuse."""
        d = self.dut
        await self._negedge_settled()
        self._score(f"{label}: backdoor quiescent (FSM idle)",
                    int(d.ctrl_state.value), ST_IDLE)
        self._score(f"{label}: backdoor quiescent (no snoop open)",
                    int(d.snoop_req.value), 0)
        tag = (line >> self.SET_BITS) \
            & ((1 << (self.ADDR_WIDTH - self.SET_BITS - self.OFFSET_BITS)) - 1)
        d.tb_tag_wr_en.value = 1
        d.tb_tag_wr_way_onehot.value = 1 << way
        d.tb_tag_wr_set.value = set_idx
        d.tb_tag_wr_tag_state.value = (tag << 3) | STATE_CODE[state_name]
        await self._negedge()
        d.tb_tag_wr_en.value = 0

    def _retire_line_at(self, set_idx, way, line):
        """Slot-replacement accounting: the way's old line is retired
        (line_state -> I) only when no OTHER live copy of it remains --
        stale {tag, I} duplicates are benign and the live copy at another
        way survives the slot overwrite on both sides. Call BEFORE the
        way's tags/slot_state are overwritten."""
        for w in range(self.WAYS):
            if w != way and self.tags.get((set_idx, w)) == line \
                    and self.slot_state.get((set_idx, w), 'I') != 'I':
                return
        self.line_state[line] = 'I'
        self.cache_data.pop(line, None)

    def _backdoor_install_model(self, line, state_name, set_idx, way, data):
        """Model side of the backdoor install: the slot's old line is gone
        (dropped without writeback -- a seeding device, not a coherence
        event; both sides forget the bytes consistently)."""
        old = self.tags.get((set_idx, way))
        if old is not None and old != line:
            self._retire_line_at(set_idx, way, old)
        self.tags[(set_idx, way)] = line
        self.slot_state[(set_idx, way)] = state_name
        self.line_state[line] = state_name
        self.cache_data[line] = bytearray(data)

    async def _seed_line_state(self, addr, state, label='seed'):
        """Install `state` at `addr` through the REAL datapath: M via a CPU
        write (miss+merge or hit/upgrade), S via a CPU read, E via the
        backdoor, I by leaving the untouched line alone. Every seeding
        transaction is scored by the inherited _txn machinery."""
        line = self._line_of(addr)
        cur = self.line_state.get(line, 'I')
        if state == 'I':
            self._score(f"{label}: I seed over an absent line", cur, 'I')
            return
        if state == 'M':
            await self._txn(addr, 1, label=f"{label}:seed_M")
        elif state == 'S':
            await self._txn(addr, 0, label=f"{label}:seed_S")
        else:  # 'E'
            set_idx = self._set_of_line(line)
            way = self.lru.victim(set_idx)
            data = bytes(random.randrange(256) for _ in range(self.LINE_BYTES))
            beats = [self._beat_of_line(data, b) for b in range(self.FILL_BEATS)]
            await self._backdoor_data_write(set_idx, way, beats)
            await self._backdoor_tag_write(set_idx, way, line, 'E',
                                           label=f"{label}:seed_E")
            self._backdoor_install_model(line, 'E', set_idx, way, data)
        self._score(f"{label}: seeded {state}",
                    self.line_state.get(line, 'I'), state)

    # ------------------------------------------------------------------
    # the ACE snoop issuer + scorer
    # ------------------------------------------------------------------
    def _gnt_cyc(self, gnt_idx):
        """Cycle of the gnt_idx-th sn_gnt tap event (grants are totally
        ordered, matching issue order)."""
        n = -1
        for cyc, kind, _ in self.events:
            if kind == 'sn_gnt':
                n += 1
                if n == gnt_idx:
                    return cyc
        return None

    async def _ace_snoop(self, line, snoop, label, ref=None, exp_line=None,
                         grant_lo=None, grant_hi=None):
        """Issue one snoop through the ACE master and score the response.

        ref:       the reference state the DUT must decode at (default: the
                   model's installed state; the callers pass the resolved
                   reference for the in-flight cases).
        exp_line:  expected CD beat content (default: the model line).
        grant_lo/hi: optional grant-window assertion (event cycles); the
                   composition/loop scenarios pin where the grant may land.
        """
        if ref is None:
            ref = self.line_state.get(line, 'I')
        res = oracle_step(ref, snoop)
        exp_crresp = res.crresp
        if exp_line is None and (exp_crresp >> CRRESP_DT) & 1:
            exp_line = bytes(self.cache_data.get(
                line, bytearray(self.LINE_BYTES)))
        addr = (line & self.LINE_MASK) << self.OFFSET_BITS

        gnt_idx = self._gnt_count
        self.inv_sn_open = True
        self.inv_sn_line = line
        self.inv_sn_name = snoop
        try:
            result = await self.master.issue_snoop(
                addr, FRAMEWORK_SNOOPS[snoop])
        finally:
            self.inv_sn_open = False
        cr = result.crresp

        # CRRESP, bit by bit (IHI0022 order; the oracle value is the pkg
        # Table 3.0 decode, pkg-pinned against this oracle by the kmap TBs)
        self._score(f"{label} crresp.dt", int(cr.data_transfer),
                    (exp_crresp >> 0) & 1)
        self._score(f"{label} crresp.err", int(cr.error), 0)
        self._score(f"{label} crresp.pd", int(cr.pass_dirty),
                    (exp_crresp >> 2) & 1)
        self._score(f"{label} crresp.is", int(cr.is_shared),
                    (exp_crresp >> 3) & 1)
        self._score(f"{label} crresp.wu", int(cr.was_unique),
                    (exp_crresp >> 4) & 1)

        # CD beats
        if (exp_crresp >> CRRESP_DT) & 1:
            self._score(f"{label} exp_line known", exp_line is not None, True)
            self._score(f"{label} cd beat count", len(result.data),
                        self.FILL_BEATS)
            self.ace_checker.set_expected_cd_beats(self.FILL_BEATS)
            for i, got in enumerate(result.data):
                self._score(f"{label} cd[{i}]", got,
                            self._beat_of_line(exp_line, i))
                # the framework checker numbers CD sequences among
                # data-carrying responses only (a non-DT snoop contributes
                # no beats and does not advance its CD counter)
                self.ace_checker.check_cd_order(
                    self._cd_seq, i == self.FILL_BEATS - 1, addr,
                    FRAMEWORK_SNOOPS[snoop])
            self._cd_seq += 1
        else:
            self._score(f"{label} cd empty", len(result.data), 0)

        # framework compliance
        self.ace_checker.check_cr_order(self._ace_seq, addr,
                                        FRAMEWORK_SNOOPS[snoop])
        self.ace_checker.check_crresp_validity(cr, FRAMEWORK_SNOOPS[snoop],
                                               addr)
        self._ace_seq += 1

        # optional grant-window assertion
        if grant_lo is not None:
            gc = self._gnt_cyc(gnt_idx)
            self._score(f"{label} grant observed", gc is not None, True)
            if gc is not None:
                self._score(f"{label} grant >= lo", gc >= grant_lo, True)
                if grant_hi is not None:
                    self._score(f"{label} grant < hi", gc < grant_hi, True)
        self.snoops += 1
        return res

    def _apply_snoop_effect(self, line, ref, res, label):
        """Apply a completed snoop's next-state to the model (installed-line
        case). A state change shows up as a tag write the RTL applies to the
        way its port-B lookup found -- the first valid matching copy, the
        same rule _hit_way uses -- so the per-way slot model follows."""
        nxt = res.next_state
        if nxt == ref:
            return
        set_idx = self._set_of_line(line)
        way = self._hit_way(set_idx, line)
        self.line_state[line] = nxt
        if way is not None:
            self.slot_state[(set_idx, way)] = nxt
        if nxt == 'I':
            self.cache_data.pop(line, None)

    def _free_set(self, used):
        """First set index outside `used` (the TB's directed scenarios run
        against pool-soaked state; their victim sequences need sets the
        pool never touched)."""
        return next(s for s in range(self.SETS) if s not in used)

    # ------------------------------------------------------------------
    # gate: one snoop per reachable Table 3.0 cell
    # ------------------------------------------------------------------
    async def _table30_directed(self):
        i = 0
        for st in ['M', 'E', 'S', 'I']:
            for sn in ORACLE_SNOOPS:
                addr = 0x1000 + i * self.LINE_BYTES
                i += 1
                label = f"t30[{st},{sn.replace('SNOOP_', '')}]"
                await self._seed_line_state(addr, st, label=label)
                line = self._line_of(addr)
                res = await self._ace_snoop(line, sn, label)
                self._apply_snoop_effect(line, st, res, label)
        self.log.info("table30_directed done (24 cells)")

    # ------------------------------------------------------------------
    # gate: pin the HIT_WR promotion one-hot (found + fixed by this task)
    # ------------------------------------------------------------------
    async def _e_write_hit_promotes(self):
        """EWriteHitPromotes: the Task 7 closed loop found the landed
        amber_control driving HIT_WR's E->M promotion with an all-zeros
        way one-hot (a silent drop -- E never occurs without a backdoor,
        so the control suite could not see it). Pin: backdoor-seed E,
        CPU write hit, then verify the tag array actually holds M (readback)
        and a snoop decodes at M with the merged data."""
        se = self._free_set({(0x1000 >> self.OFFSET_BITS) + i
                             & self.SET_MASK for i in range(24)})
        addr = self._compose_addr(0xF0, se)
        line = self._line_of(addr)
        await self._seed_line_state(addr, 'E', label='ewh:seed')
        wdata = random.getrandbits(self.STRB_W * 8)
        await self._txn(addr, 1, be=(1 << self.STRB_W) - 1, wdata=wdata,
                        label='ewh:wr_hit')
        # functional proof: the promotion landed in the tag array
        d = self.dut
        await self._negedge_settled()
        d.tag_b_set.value = se
        await Timer(1, units='ns')
        tsw = (self.ADDR_WIDTH - self.SET_BITS - self.OFFSET_BITS) + 3
        found_m = False
        ts = int(d.tag_b_tag_state.value)
        for w in range(self.WAYS):
            if ((ts >> (w * tsw)) & 0x7) == STATE_CODE['M']:
                found_m = True
        self._score("ewh: promoted to M in the tag array", found_m, True)
        self._score("ewh: model state M", self.line_state.get(line), 'M')
        # and the coherence view agrees: a snoop decodes at M with the
        # merged content
        res = await self._ace_snoop(line, 'SNOOP_READ_SHARED', 'ewh:rs')
        self._score("ewh: snoop next S", res.next_state, 'S')
        self._score("ewh: merged data visible",
                    bytes(self.cache_data[line][0:self.STRB_W]),
                    wdata.to_bytes(self.STRB_W, 'little'))
        self._apply_snoop_effect(line, 'M', res, 'ewh')
        self.log.info("EWriteHitPromotes directed done")

    # ------------------------------------------------------------------
    # func/full: pool soak over the evolving model
    # ------------------------------------------------------------------
    async def _midsoak_reset(self, label):
        """Idle-phase reset recovery: quiescence checked on the taps, reset
        pulse, init walk verified (the inherited _check_init resets the
        cache-side models -- the memory side survives, it is the DRAM)."""
        d = self.dut
        await self._negedge_settled()
        self._score(f"{label}: quiescent (FSM idle)",
                    int(d.ctrl_state.value), ST_IDLE)
        self._score(f"{label}: no snoop open", int(d.snoop_req.value), 0)
        await self.assert_reset()
        await self.wait_clocks('clk', 5)
        await self.deassert_reset()
        await self._check_init()

    async def _pool_soak(self):
        pool = [0x2000 + i * self.LINE_BYTES for i in range(64)]
        for a in pool:
            await self._seed_line_state(a, random.choice(['I', 'S', 'E', 'M']),
                                        label='pool_seed')
        # Directed: zero-gap pairs across transactions. The AC skid exists so
        # the master can present the next snoop while the current response
        # is still sequencing -- issue zero-gap pairs and same-line pairs
        # with no idle between them.
        for addr in pool[:8]:
            line = self._line_of(addr)
            await self._seed_line_state(addr, 'M', label='pool_pair')
            for sn in ('SNOOP_READ_SHARED', 'SNOOP_READ_SHARED',
                       'SNOOP_CLEAN_SHARED'):
                res = await self._ace_snoop(line, sn, f"pair({sn[6:]})")
                self._apply_snoop_effect(line, self.line_state.get(line, 'I'),
                                         res, f"pair({sn[6:]})")
        self.scenarios['pipelining_zero_gap'] = True
        # randomized soak with refills; idle-phase reset at the halfway mark
        for n in range(self.n_snoops):
            addr = random.choice(pool)
            line = self._line_of(addr)
            if self.line_state.get(line, 'I') == 'I' \
                    and random.random() < 0.5:
                await self._seed_line_state(
                    addr, random.choice(['S', 'E', 'M']), label='pool_refill')
            res = await self._ace_snoop(line, random.choice(ORACLE_SNOOPS),
                                        f"soak[{n}]")
            self._apply_snoop_effect(line, self.line_state.get(line, 'I'),
                                     res, f"soak[{n}]")
            if n == self.n_snoops // 2:
                await self._midsoak_reset('reset_recovery')
                self.scenarios['reset_recovery'] = True
            if n % 1000 == 0:
                self.mark_progress(f"pool soak {n}/{self.n_snoops}")
        self.log.info(f"pool soak done ({self.n_snoops} snoops)")

    # ------------------------------------------------------------------
    # T5-review composition: snoop for the VICTIM line raised during the
    # gather -- stall -> grant at MISS_DRAIN -> buffer service, one scenario
    # ------------------------------------------------------------------
    async def _snoop_victim_during_gather(self):
        # a set the pool never touched (the pool maps to different set
        # ranges per geometry); the composition's victim sequence assumes
        # the svg lines are the set's only residents
        pool_sets = {((0x2000 >> self.OFFSET_BITS) + i) & self.SET_MASK
                     for i in range(64)}
        sg = self._free_set(pool_sets)
        line_v = self._line_of(self._compose_addr(0xE0, sg))
        await self._txn(self._compose_addr(0xE0, sg), 1, wdata=0x600DC0DE,
                        label='svg:wr_v')                    # V -> M
        for i in range(1, self.WAYS):
            await self._txn(self._compose_addr(0xE0 + i, sg), 0,
                            label=f'svg:fill[{i}]')
        # widen the drain window so the raised-during-gather snoop is
        # deterministically served from the buffer (the same discipline as
        # the control TB's SnoopHitsVictimBypass)
        saved_latency = self.drain_latency
        self.drain_latency = self.FILL_BEATS + 16
        accept = await self._req_issue(self._compose_addr(0xE4, sg), 0,
                                       (1 << self.STRB_W) - 1, 0,
                                       'svg:evict_miss')
        # raise the snoop DURING the gather (before the victim_load tap);
        # it must stall through every MISS_VICTIM cycle and grant at
        # MISS_DRAIN after the victim_load strobe. Prompt AC keeps the
        # grant inside the (widened) drain window.
        gnt_idx = self._gnt_count
        self.master.ac_channel.set_randomizer(self._ac_rand_fast)
        self.master.cd_channel.set_randomizer(self._cd_rand_fast)
        task = cocotb.start_soon(self._ace_snoop(
            line_v, 'SNOOP_READ_UNIQUE', 'svg:ru',
            ref='M', exp_line=bytes(self.cache_data[line_v]),
            grant_lo=accept + 1))
        res = await task
        self.master.ac_channel.set_randomizer(self._ac_rand_level)
        self.master.cd_channel.set_randomizer(self._cd_rand_level)
        # restore only now: the drain stub captured the widened latency at
        # drain_start, and restoring earlier could race its read
        self.drain_latency = saved_latency
        gc = self._gnt_cyc(gnt_idx)
        # grant-window analysis on the event stream: no grant inside any
        # MISS_VICTIM window after the accept; the grant sits in a
        # MISS_DRAIN window that opened after the victim_load strobe
        self._score("svg: grant observed", gc is not None, True)
        if gc is not None:
            in_mv = self._grant_inside_state(accept, gc, ST_MISS_VICTIM)
            self._score("svg: stalled through every gather cycle",
                        in_mv, False)
            self._score("svg: granted in MISS_DRAIN",
                        self._state_at(gc), ST_MISS_DRAIN)
            vl = [c for c, k, p in self.events if k == 'victim_load'
                  and self._line_of(p['addr']) == line_v and c < gc]
            self._score("svg: victim_load preceded the grant", len(vl) > 0,
                        True)
        # the evicting transaction completes normally (slice scoring)
        accept, rsp_cyc, rsp_data = await self._req_await_rsp(accept,
                                                              'svg:rsp')
        sl = self._slice(accept, rsp_cyc)
        line_new = self._line_of(self._compose_addr(0xE4, sg))
        set_idx = self._set_of_line(line_new)
        res_txn = oracle_step(self.line_state.get(line_new, 'I'), 'CPU_RD')
        self._score_slice(self._compose_addr(0xE4, sg), line_new, set_idx,
                          0, 0, (1 << self.STRB_W) - 1, 0, res_txn, rsp_data,
                          sl, 'svg')
        self.txns += 1
        self._score("svg: victim retired to memory",
                    bytes(self._mem_line(line_v)),
                    bytes(self.cache_data.get(
                        line_v, bytearray(self.LINE_BYTES))))
        # re-fetch the drained line: the writeback payload must come back
        await self._txn(self._compose_addr(0xE0, sg), 0, label='svg:refetch')
        self._score("svg: refetch returns the drained data",
                    self.line_state.get(line_v), 'S')
        self.log.info("SnoopVictimLineDuringGather directed done")

    def _state_at(self, cyc):
        st = None
        for c, k, p in self.events:
            if k == 'state' and c <= cyc:
                st = p
            elif c > cyc:
                break
        return st

    def _grant_inside_state(self, since_cyc, grant_cyc, state):
        """True if any sn_gnt in (since_cyc, grant_cyc) falls inside a
        window of `state` (entry inclusive, exit exclusive)."""
        entry = None
        for c, k, p in self.events:
            if c <= since_cyc or c >= grant_cyc:
                if k == 'state' and c >= grant_cyc:
                    break
                continue
            if k == 'state':
                if p == state:
                    entry = c
                elif entry is not None:
                    entry = None
            elif k == 'sn_gnt' and entry is not None:
                return True
        return False

    # ------------------------------------------------------------------
    # NEW scenario: randomized snoops against an amber simultaneously
    # serving random CPU traffic -- both ports live
    # ------------------------------------------------------------------
    async def _real_control_loop(self):
        n = self.LOOP_TXN[self.TEST_LEVEL]
        pool_tags = 3 * self.WAYS
        seen_lines = []
        for i in range(n):
            s = random.randrange(self.SETS)
            t = random.randrange(pool_tags)
            # LINE INDEX (the model dictionaries key on _line_of); the
            # request byte address adds the beat offset below
            line = (t << self.SET_BITS) | s
            seen_lines.append(line)
            beat = random.randrange(self.FILL_BEATS)
            addr = (line << self.OFFSET_BITS) \
                | (beat << (self.STRB_W.bit_length() - 1))
            we = 1 if random.random() < 0.55 else 0
            be = random.randrange(1, 1 << self.STRB_W) if we \
                else (1 << self.STRB_W) - 1
            wdata = random.getrandbits(self.STRB_W * 8) if we else 0
            label = f'loop[{i}]'

            # oracle prediction + in-flight metadata (single-driver model:
            # nothing mutates the models between here and _req_issue)
            st = self.line_state.get(line, 'I')
            res = oracle_step(st, 'CPU_WR' if we else 'CPU_RD')
            miss = res.result == 'MISS'
            upgr = res.req == 'CLEAN_UNIQUE'
            set_idx = self._set_of_line(line)
            victim_way = self.lru.victim(set_idx) \
                if (miss and not upgr) else None
            victim_line = self.tags.get((set_idx, victim_way)) \
                if victim_way is not None else None
            victim_dirty = victim_line is not None and self.slot_state.get(
                (set_idx, victim_way), 'I') == 'M'
            # the victim slot can hold a stale {tag, I} copy of the TXN line
            # itself (an earlier life): no victim exists then -- a snoop to
            # that line mid-fill is the pending-fill case, not the victim
            victim_is_txn = victim_line is not None and victim_line == line
            if victim_is_txn:
                victim_line, victim_dirty = None, False

            # mid-transaction snoop plan, decided up front (model-side rolls
            # only). A window-sensitive snoop (pf / vic) MUST be first: its
            # grant lands at the request phase, before any response
            # backpressure, but only if it is issued promptly -- a second
            # slot is reserved for the timing-insensitive other-line case.
            # At most one of each. A planned dirty-victim snoop widens this
            # iteration's drain so the grant deterministically lands inside
            # the drain window (the drain stub samples the latency at
            # drain_start).
            roll = random.random()
            plan = []
            if miss and not upgr and (victim_line is None or roll < 0.5):
                plan.append('pf')
            elif victim_line is not None and roll < 0.8:
                plan.append('vic')
            if plan:
                if random.random() < 0.45:
                    plan.append('oth')
            elif random.random() < 0.35:
                plan.append('oth')
            wide_drain = 'vic' in plan and victim_dirty
            saved_latency = self.drain_latency
            if wide_drain:
                self.drain_latency = self.FILL_BEATS + 16

            self.cur_txn = {
                'line': line, 'we': we, 'be': be, 'wdata': wdata,
                'beat': beat, 'miss': miss, 'upgr': upgr,
                'cls': ORACLE_REQ_TO_ACE.get(res.req),
                'victim': victim_line, 'victim_dirty': victim_dirty,
                'victim_way': victim_way,
                'post_fill': 'S' if res.req == 'READ_SHARED' else 'M',
                'pend': None,
            }
            self._tap_pos = len(self.events)

            accept = await self._req_issue(addr, we, be, wdata, label)

            # mid-transaction snoops: prompt AC + CD so each grant and every
            # beat lands in its intended window (pf beats must complete
            # before the post-install merge rewrites the fill way; the
            # staged buffer holds regardless). CR keeps the level
            # backpressure -- the CR-after-CDLAST stall stress stays on the
            # mid-transaction responses.
            if plan:
                self.master.ac_channel.set_randomizer(self._ac_rand_fast)
                self.master.cd_channel.set_randomizer(self._ac_rand_fast)

            for j, target in enumerate(plan):
                sn = random.choice(ORACLE_SNOOPS)
                if target == 'pf':
                    # pending-line snoop: fire after the fill launches so
                    # the grant lands in the pf window; the bypass answers
                    # at the ORIGINAL post-fill state (the repeat-snoop
                    # semantics are pinned by the control TB's
                    # ImStepPendingClearCorner)
                    await self._wait_tap(
                        'fill_start',
                        pred=lambda p: (p['addr'] >> self.OFFSET_BITS)
                        == line)
                    fill_cyc = self.cyc
                    res_sn = await self._ace_snoop(
                        line, sn, f'{label}.pf{j}',
                        ref=self.cur_txn['post_fill'],
                        exp_line=bytes(self._mem_line(line)),
                        grant_lo=fill_cyc + 1)
                    self._arm_pend(res_sn)
                elif target == 'vic':
                    if victim_dirty:
                        # staged-buffer service: fire inside the drain
                        # window, answered at M with the staged line
                        await self._wait_tap(
                            'victim_load',
                            pred=lambda p: self._line_of(p['addr'])
                            == victim_line)
                        await self._wait_tap('drain_start')
                        ds_cyc = self.cyc
                        await self._ace_snoop(
                            victim_line, sn, f'{label}.vic{j}', ref='M',
                            exp_line=bytes(self.cache_data[victim_line]),
                            grant_lo=ds_cyc)
                        # the buffer owns the line until the WB ack; the
                        # model retires it through the transaction machinery
                    else:
                        # clean victim: its tag survives at the victim slot
                        # until the install, and the stale-entry rule answers
                        # Invalid, no transfer -- BUT only when the line's
                        # LIVE copy is the victim-slot one. A stale {tag, I}
                        # duplicate of the victim line can sit at the victim
                        # way while the live copy occupies another way; the
                        # port-B lookup then finds the live copy first and
                        # the snoop is answered from the installed state.
                        await self._wait_tap(
                            'fill_start',
                            pred=lambda p: (p['addr'] >> self.OFFSET_BITS)
                            == line)
                        vset = self._set_of_line(victim_line)
                        live_way = self._hit_way(vset, victim_line)
                        if live_way == self.cur_txn['victim_way']:
                            res_sn = await self._ace_snoop(
                                victim_line, sn, f'{label}.stale{j}', ref='I')
                            # the local copy is being overwritten by the
                            # fill: the tag no longer describes a live line
                            self.line_state[victim_line] = 'I'
                            self.cache_data.pop(victim_line, None)
                        else:
                            res_sn = await self._ace_snoop(
                                victim_line, sn, f'{label}.stale{j}')
                            self._apply_snoop_effect(
                                victim_line,
                                self.line_state.get(victim_line, 'I'),
                                res_sn, f'{label}.stale{j}')
                    if wide_drain:
                        # the stub captured the widened latency at
                        # drain_start; restore only now
                        self.drain_latency = saved_latency
                else:
                    # other-line snoop: installed state, stable across the
                    # whole window (single driver; installs and evictions
                    # touch the txn line / victim slot only)
                    other = self._pick_other_line(line, victim_line,
                                                  seen_lines)
                    if other is None:
                        continue
                    res_sn = await self._ace_snoop(other, sn,
                                                   f'{label}.oth{j}')
                    self._apply_snoop_effect(
                        other, self.line_state.get(other, 'I'), res_sn,
                        f'{label}.oth{j}')
            if wide_drain and self.drain_latency != saved_latency:
                self.drain_latency = saved_latency
            if plan:
                self.master.ac_channel.set_randomizer(self._ac_rand_level)
                self.master.cd_channel.set_randomizer(self._cd_rand_level)

            accept, rsp_cyc, rsp_data = await self._req_await_rsp(accept,
                                                                  label)
            sl = self._slice(accept, rsp_cyc)
            self._score_slice_loop(addr, line, set_idx, beat, we, be, wdata,
                                   res, rsp_data, sl, label)
            self.txns += 1
            self.cur_txn = None
            if i % 100 == 0:
                self.mark_progress(f"real_control_loop {i}/{n}")

        # quiescent tail: back-to-back snoops while the pipeline idles
        for _ in range(min(n, 32)):
            line = random.choice(seen_lines)
            res_sn = await self._ace_snoop(line, random.choice(ORACLE_SNOOPS),
                                           f'loop_tail{line:#x}')
            self._apply_snoop_effect(line, self.line_state.get(line, 'I'),
                                     res_sn, 'loop_tail')
        self.log.info(f"real_control_loop done ({n} transactions, "
                      f"{self.snoops} ACE snoops total)")

    def _pick_other_line(self, line, victim_line, seen_lines):
        """A line whose state is stable for the whole in-flight window:
        installed (model-tracked), not the txn line, not the victim slot;
        falls back to a guaranteed-absent fresh line (an I-line snoop is
        still a full ACE transaction: CR 0, no CD)."""
        cands = [l for l in dict.fromkeys(seen_lines)
                 if l != line and l != victim_line
                 and self.line_state.get(l, 'I') != 'I']
        if cands:
            return random.choice(cands)
        # a guaranteed-absent fresh line (index form); an I-line snoop is
        # still a full ACE transaction: CR 0, no CD
        fresh = (random.randrange(1, 1 << 8) << self.SET_BITS) \
            | random.randrange(self.SETS)
        return fresh if fresh != line and fresh != victim_line else None

    def _arm_pend(self, res_sn):
        """Mirror pend_vld_q: a mid-fill snoop arms a post-commit effect
        only when it changes the resolved reference state; an invalidation
        sticks, a downgrade arms only over no effect."""
        txn = self.cur_txn
        if txn is None:
            return
        ref = txn['post_fill']
        nxt = res_sn.next_state
        if nxt == ref:
            return
        if nxt == 'I':
            txn['pend'] = 'I'
        elif txn['pend'] is None:
            txn['pend'] = 'S'

    # ------------------------------------------------------------------
    # concurrent-aware transaction slice scorer
    # ------------------------------------------------------------------
    def _score_slice_loop(self, addr, line, set_idx, beat, we, be, wdata,
                          res, rsp_data, sl, label):
        """The _real_control_loop transaction scorer. Same discipline as
        the control TB's _score_slice, generalized: fills are attributed by
        address (a killed pending line re-fetches -> a second fill), the
        first install admits the snoop's post-commit pend, and events that
        belong to mid-transaction snoops on other lines update the models
        without being scored as this transaction's machinery."""
        states = [p for _, k, p in sl if k == 'state']
        upgrade = res.req == 'CLEAN_UNIQUE'
        miss = res.result == 'MISS'

        self._score(f"{label} LOOKUP entered", 2 in states, True)
        rsp_evts = [p for _, k, p in sl if k == 'rsp']
        self._score(f"{label} exactly one response", len(rsp_evts), 1)
        if we:
            exp_rsp = wdata
        elif res.result == 'MISS':
            exp_rsp = self._beat_of_line(self._mem_line(line), beat)
        else:
            # read hit: the cached line (merges included)
            exp_rsp = self._beat_of_line(
                bytes(self.cache_data.get(line, bytearray(self.LINE_BYTES))),
                beat)
        self._score(f"{label} rsp data", rsp_data, exp_rsp)
        if not miss:
            self._score(f"{label} hit service state",
                        (4 if we else 3) in states, True)
        else:
            self._score(f"{label} FILL_WRITE entered", 8 in states, True)
            self._score(f"{label} REPLAY entered", 9 in states, True)
            self._score(f"{label} replay hit state",
                        (4 if we else 3) in states, True)

        # expected fill class sequence: first from the oracle miss request;
        # a post-commit state that does not satisfy the replayed request
        # produces another fill (pend-killed pending line / killed upgrade)
        exp_classes = []
        committed = None
        if miss:
            exp_classes.append(ORACLE_REQ_TO_ACE[res.req])
            committed = self.cur_txn['pend'] or \
                ('S' if res.req == 'READ_SHARED' else 'M')
            r1 = oracle_step(committed, 'CPU_WR' if we else 'CPU_RD')
            if r1.result == 'MISS':
                exp_classes.append(ORACLE_REQ_TO_ACE[r1.req])
                committed = 'S' if r1.req == 'READ_SHARED' else 'M'
        fills = [p for _, k, p in sl if k == 'fill_start'
                 and (p['addr'] >> self.OFFSET_BITS) == line]
        self._score(f"{label} fill classes", [p['class'] for p in fills],
                    exp_classes)

        # chronological replay with per-launch victim prediction (the model
        # lru/slot_state are the same ones the DUT's repl/array hold);
        # foreign events (mid-txn snoops on other lines) update the models
        # without being scored as this transaction's machinery
        STATE_DECODE = {0: 'I', 1: 'S', 2: 'E', 3: 'M'}
        pend = self.cur_txn['pend']
        pending_victim = None
        install_i = 0
        n_ctrl_wr = 0
        for cyc, kind, p in sl:
            if kind == 'repl_req':
                # a victim select for a true-fill miss launch (upgrades go
                # straight to MISS_FILL)
                if miss and not upgrade:
                    self._score(f"{label} victim way", p['victim_way'],
                                self.lru.victim(set_idx))
            elif kind == 'victim_load':
                vline = self._line_of(p['addr'])
                exp_data = int.from_bytes(bytes(self.cache_data[vline]),
                                          'little')
                self._score(f"{label} victim data", p['data'], exp_data)
                pending_victim = (vline, bytes(self.cache_data[vline]))
            elif kind == 'drain_done':
                if pending_victim is not None:
                    vline, vdata = pending_victim
                    self.mem[vline] = bytearray(vdata)
                    pending_victim = None
            elif kind == 'fill_start':
                if p['class'] != ACE_CLEAN_UNIQUE:
                    self.cache_data[line] = bytearray(self._mem_line(line))
            elif kind == 'fill_wr':
                b = p['addr'] & (self.FILL_BEATS - 1)
                self._score(f"{label} fill beat data", p['data'],
                            self._beat_of_line(self.cache_data[line], b))
            elif kind == 'ctrl_wr':
                n_ctrl_wr += 1
                lo = beat * self.STRB_W
                for i in range(self.STRB_W):
                    if be & (1 << i):
                        self.cache_data[line][lo + i] = (wdata >> (8 * i)) \
                            & 0xFF
            elif kind == 'tag_wr':
                wr_set = p['set']
                wr_state = p['tag_state'] & 0x7
                wr_tag = p['tag_state'] >> 3
                if wr_set == set_idx and wr_tag == (line >> self.SET_BITS):
                    # this transaction's own write
                    if not miss:
                        # hit-write promotion (E/S -> M); a hit read never
                        # writes the tag
                        self._score(f"{label} hit promotion state", wr_state,
                                    STATE_CODE['M'])
                        way = p['way_oh'].bit_length() - 1
                        self.slot_state[(set_idx, way)] = 'M'
                        self.line_state[line] = 'M'
                    elif upgrade:
                        self._score(f"{label} upgrade install state",
                                    wr_state, STATE_CODE['M'])
                        way = p['way_oh'].bit_length() - 1
                        self.slot_state[(set_idx, way)] = 'M'
                        self.line_state[line] = 'M'
                    else:
                        exp_st = (pend if install_i == 0 and pend else
                                  ('S' if fills[min(install_i,
                                                    len(fills) - 1)]['class']
                                   == ACE_READ_SHARED else 'M'))
                        self._score(f"{label} install state[{install_i}]",
                                    wr_state, STATE_CODE[exp_st])
                        way = p['way_oh'].bit_length() - 1
                        old = self.tags.get((set_idx, way))
                        if old is not None and old != line:
                            self._retire_line_at(set_idx, way, old)
                        self.tags[(set_idx, way)] = line
                        self.slot_state[(set_idx, way)] = exp_st
                        self.line_state[line] = exp_st
                        install_i += 1
                else:
                    # a mid-txn snoop's downgrade/invalidate on another
                    # line: apply the model side (the write lands on the
                    # live copy, so no last-copy retirement is needed)
                    fline = (wr_tag << self.SET_BITS) | wr_set
                    fway = p['way_oh'].bit_length() - 1
                    dec = STATE_DECODE.get(wr_state, 'I')
                    self.tags[(wr_set, fway)] = fline
                    self.slot_state[(wr_set, fway)] = dec
                    self.line_state[fline] = dec
                    if dec == 'I':
                        self.cache_data.pop(fline, None)
            elif kind == 'repl_update':
                self.lru.update(set_idx, p['way'])
            elif kind == 'repl_hit':
                way = self._hit_way(set_idx, line)
                if way is not None:
                    self.lru.update(set_idx, way)

        if miss:
            self._score(f"{label} write merge count", n_ctrl_wr,
                        1 if we else 0)
        if committed is not None:
            self.line_state[line] = committed

    # ------------------------------------------------------------------
    async def run(self) -> bool:
        await self._check_init()
        self.scenarios['InitWalk'] = True
        if self.TEST_LEVEL == 'gate':
            await self._table30_directed()
            self.scenarios['table30_directed'] = True
            await self._e_write_hit_promotes()
            self.scenarios['EWriteHitPromotes'] = True
        else:
            await self._pool_soak()
            self.scenarios['backpressure_response' if self.TEST_LEVEL == 'func'
                            else 'stress_soak'] = True
            await self._snoop_victim_during_gather()
            self.scenarios['SnoopVictimLineDuringGather'] = True
            await self._real_control_loop()
            self.scenarios['real_control_loop'] = True
        self.scenarios['data_integrity'] = True
        self.scenarios['crresp_bit_order'] = True
        rep = self.ace_checker.get_compliance_report()
        self._score("ACE compliance violations", rep['total_violations'], 0)
        return self.mismatches == 0

    def get_test_report(self):
        rep = super().get_test_report()
        rep['ace_seq'] = self._ace_seq
        rep['ace_violations'] = len(self.ace_checker.violations)
        return rep
