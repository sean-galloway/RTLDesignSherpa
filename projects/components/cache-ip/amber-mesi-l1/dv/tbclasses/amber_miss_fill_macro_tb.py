"""
amber_miss_fill_macro testbench -- macro suite 2: the miss/fill path group

Task 9.5 macro composition: the DUT is the wrapper
amber_miss_fill_macro_test -- REAL amber_control (with the
pending_fill_bypass leaf) + landed tag/data/repl arrays + REAL amber_fill
on its house axi4_master_rd transport, memory side closed by the house
AXI4 slave responder on the wrapper's m_axi AR/R pins. Drain/victim stay
timing stubs (D-12); snoops enter on the control-facing pins.

The class reuses the landed control TB machinery (AmberControlTB: golden
models, every-cycle monitors, the oracle lockstep scorer, the mid-fill
snoop scenario suite) and makes the golden memory write-through into the
responder MemoryModel, so the REAL fill reads exactly the bytes the model
scores against. The partner-stub fill model (_fill_stub / fillbeat pins)
is retired: fill_done / fill_beat_* are engine outputs now.

Macro-specific pins (what the stub could not check):
  * FillOrchestration (gate): the first read miss drives the real AR
    channel -- araddr/arlen/arsize/arburst observed at m_axi, R beats
    gathered through the engine into the data array, response data vs
    the MemoryModel;
  * UpgradeNoFetchEngine (gate): a CLEAN_UNIQUE upgrade raises NO AR
    transaction at all (the stub suppressed beats by construction; the
    engine must not issue one);
  * KilledFillRefetch (func): the inherited snoop-killed-fill scenarios
    (ImStepPendingClearCorner, UpgradeKilledByInvalidatingSnoop) now
    re-issue a REAL AR burst for the re-fetch;
  * the inherited mid-fill snoop suite (SnoopPendingFillBypass,
    SnoopPendingReadSharedFill, ...) services snoops against beats
    arriving on the real R channel.

Levels (TEST_LEVEL):
  gate  -- InitWalk + FillOrchestration + UpgradeNoFetchEngine
  func  -- + MissSequence + the mid-fill snoop suite + killed-fill
           re-fetch pins + randomized lockstep soak (with idle snoops)
  full  -- deeper soak (sign-off scale)

Author: RTL Design Sherpa
Created: 2026-10-08
"""

import cocotb

from CocoTBFramework.components.shared.memory_model import MemoryModel
from CocoTBFramework.components.shared.flex_randomizer import FlexRandomizer
from CocoTBFramework.components.axi4.axi4_factories import (
    create_axi4_slave_rd,
)

from projects.components.cache_ip.amber_mesi_l1.dv.golden.amber_fsm_oracle import (
    step as oracle_step,
)
from projects.components.cache_ip.amber_mesi_l1.dv.tbclasses.amber_control_tb import (
    AmberControlTB,
    ACE_CLEAN_UNIQUE,
    ACE_READ_UNIQUE,
    STATE_CODE,
)

AXBURST_INCR = 0b01


class _WriteThroughMem(dict):
    """Golden memory dict that writes through to the responder
    MemoryModel on every assignment: the responder's R channel reads the
    same bytes the model scores against, so drain-side retirements (the
    stub-era self.mem update) and lazy default-line installs reach the
    REAL fill path. Base-address function injected by the TB (line ->
    byte address)."""

    def __init__(self, mm, base_of):
        super().__init__()
        self._mm = mm
        self._base_of = base_of

    def __setitem__(self, line, data):
        super().__setitem__(line, data)
        self._mm.write(self._base_of(line), bytearray(data))


class AmberMissFillMacroTB(AmberControlTB):
    """Miss/fill macro: real fill engine + transport in the loop."""

    FULL_TXN = {'gate': 0, 'func': 2500, 'full': 10_000}

    # responder timing profiles (the fill/drain unit suite's set)
    PROFILES = {
        'fast':   {'ready': ([(0, 0)], [1.0]),
                   'resp':  ([(0, 0)], [1.0])},
        'normal': {'ready': ([(0, 2), (3, 5)], [0.7, 0.3]),
                   'resp':  ([(0, 2), (3, 6)], [0.6, 0.4])},
        'slow':   {'ready': ([(1, 4), (5, 10)], [0.6, 0.4]),
                   'resp':  ([(2, 6), (7, 12)], [0.5, 0.5])},
    }

    def __init__(self, dut, **kwargs):
        super().__init__(dut, **kwargs)

        # memory side: the house AXI4 read responder closes the wrapper's
        # m_axi AR/R pins; the golden model writes through to it
        self.memory_model = MemoryModel(
            num_lines=1 << 20,
            bytes_per_line=self.STRB_W,
            log=self.log,
        )
        self.mem = _WriteThroughMem(self.memory_model,
                                    lambda line: (line & self.LINE_MASK)
                                    << self.OFFSET_BITS)
        rd = create_axi4_slave_rd(
            dut=dut, clock=dut.clk, prefix='m_axi', log=self.log,
            id_width=8, addr_width=self.ADDR_WIDTH,
            data_width=self.STRB_W * 8, user_width=1,
            memory_model=self.memory_model)
        self.ar_slave = rd['AR']
        self.r_master = rd['R']
        self.set_profile('fast')
        self.log.info("AmberMissFillMacroTB: miss/fill group with the real "
                      "fill engine + axi4_master_rd in the loop")

    # ------------------------------------------------------------------
    # golden memory: reads lazily install the deterministic default on
    # BOTH sides (the dict insert writes through to the MemoryModel).
    # The install must happen BEFORE the request is issued -- the real
    # engine reads the MemoryModel at AR time, while the model-side
    # fill_start replay would otherwise install it too late.
    # ------------------------------------------------------------------
    def _mem_line(self, line):
        if line not in self.mem:
            self.mem[line] = bytearray(self._default_line(line))
        return self.mem[line]

    async def _req_issue(self, addr, we, be, wdata, label=''):
        self._mem_line(self._line_of(addr))
        return await super()._req_issue(addr, we, be, wdata, label)

    def set_profile(self, name):
        cfg = self.PROFILES[name]
        self.ar_slave.set_randomizer(FlexRandomizer({'ready_delay': cfg['ready']}))
        self.r_master.set_randomizer(FlexRandomizer({'valid_delay': cfg['resp']}))

    # ------------------------------------------------------------------
    # setup: the fill is REAL -- no fill_done/beat drives, no fill stub;
    # the drain stub stays (drain is group 3's engine)
    # ------------------------------------------------------------------
    async def setup_clocks_and_reset(self, period_ns=10):
        await self.start_clock('clk', freq=period_ns, units='ns')
        d = self.dut
        d.req_valid.value = 0
        d.req_addr.value = 0
        d.req_we.value = 0
        d.req_be.value = 0
        d.req_wdata.value = 0
        d.drain_done.value = 0
        d.snoop_req.value = 0
        d.snoop_type.value = 0
        d.snoop_addr.value = 0
        d.cd_ready_in.value = 0
        d.tag_b_set.value = 0
        await self.assert_reset()
        cocotb.start_soon(self._monitor())
        cocotb.start_soon(self._monitor_ar())
        cocotb.start_soon(self._drain_stub())
        cocotb.start_soon(self._victim_invariant())
        cocotb.start_soon(self._pf_invariant())
        await self.wait_clocks('clk', 3)
        await self.deassert_reset()

    # ------------------------------------------------------------------
    # monitor: AR handshake stamps (orchestration scoring)
    # ------------------------------------------------------------------
    async def _monitor_ar(self):
        d = self.dut
        while True:
            await self._negedge_settled()
            if int(d.m_axi_arvalid.value) and int(d.m_axi_arready.value):
                self.events.append((self.cyc, 'ar', {
                    'addr': int(d.m_axi_araddr.value),
                    'len': int(d.m_axi_arlen.value),
                    'size': int(d.m_axi_arsize.value),
                    'burst': int(d.m_axi_arburst.value),
                }))

    # ------------------------------------------------------------------
    # gate pin: the first read miss drives the REAL AR channel
    # ------------------------------------------------------------------
    async def _fill_orchestration(self):
        so = 4 % self.SETS
        addr = self._compose_addr(0x20, so)
        line = self._line_of(addr)
        # install the deterministic default line in the model/memory
        exp_line = bytes(self._mem_line(line))

        self._tap_pos = len(self.events)
        tap0 = self._tap_pos
        accept = await self._req_issue(addr, 0, (1 << self.STRB_W) - 1, 0,
                                       'orc:rd_miss')
        await self._wait_tap('fill_done')
        sl = [e for e in self.events[tap0:] if e[0] > accept]
        ars = [p for _, k, p in sl if k == 'ar']
        self._score("orc: exactly one AR burst", len(ars), 1)
        if ars:
            self._score("orc: AR line-aligned",
                        ars[0]['addr'] & (self.LINE_BYTES - 1), 0)
            self._score("orc: AR addr is the fill line",
                        ars[0]['addr'] >> self.OFFSET_BITS, line)
            self._score("orc: AR len", ars[0]['len'], self.FILL_BEATS - 1)
            self._score("orc: AR size", ars[0]['size'],
                        self.STRB_W.bit_length() - 1)
            self._score("orc: AR burst INCR", ars[0]['burst'], AXBURST_INCR)

        accept, rsp_cyc, rsp_data = await self._req_await_rsp(accept,
                                                              'orc:rsp')
        sl = self._slice(accept, rsp_cyc)
        n_beats = sum(1 for _, k, _ in sl if k == 'fill_wr')
        self._score("orc: beats gathered", n_beats, self.FILL_BEATS)
        self._score("orc: rsp = memory beat",
                    rsp_data, self._beat_of_line(exp_line, 0))
        # the transaction scorer owns the model replay + machinery checks
        set_idx = self._set_of_line(line)
        res = oracle_step('I', 'CPU_RD')
        self._score_slice(addr, line, set_idx, 0, 0,
                          (1 << self.STRB_W) - 1, 0, res, rsp_data, sl,
                          'orc')
        self.txns += 1
        self.log.info("FillOrchestration directed done (real AR/R burst)")

    # ------------------------------------------------------------------
    # gate pin: an upgrade raises NO AR transaction at all
    # ------------------------------------------------------------------
    async def _upgrade_no_fetch_engine(self):
        su = 6 % self.SETS
        addr = self._compose_addr(0x21, su)
        wdata = 0x0BADC0DE0DDC0DE0 & ((1 << (self.STRB_W * 8)) - 1)
        await self._txn(addr, 0, label='unf:rd')            # -> S
        ar_start = self._count_ar()
        accept = await self._req_issue(addr, 1,
                                       (1 << self.STRB_W) - 1, wdata,
                                       'unf:upgrade')
        accept, rsp_cyc, rsp_data = await self._req_await_rsp(accept,
                                                              'unf:rsp')
        await self._negedge_settled()
        ar_during = self._count_ar() - ar_start
        self._score("unf: CLEAN_UNIQUE issued no AR", ar_during, 0)
        sl = self._slice(accept, rsp_cyc)
        fills = [p for _, k, p in sl if k == 'fill_start']
        self._score("unf: one upgrade fill", len(fills), 1)
        self._score("unf: upgrade class", fills[0]['class'],
                    ACE_CLEAN_UNIQUE)
        line = self._line_of(addr)
        set_idx = self._set_of_line(line)
        res = oracle_step('S', 'CPU_WR')
        self._score_slice(addr, line, set_idx, 0, 1,
                          (1 << self.STRB_W) - 1, wdata,
                          res, rsp_data, sl, 'unf')
        self.txns += 1
        self.log.info("UpgradeNoFetchEngine directed done (no AR raised)")

    def _count_ar(self):
        return sum(1 for _, k, _ in self.events if k == 'ar')

    # ------------------------------------------------------------------
    # func pin: killed-fill re-fetch against the REAL engine. An
    # invalidating snoop (READ_UNIQUE) mid-fill kills the pending write
    # miss: the commit installs Invalid, the replayed write re-observes
    # the miss and the REAL fill re-issues a second AR burst (READ_UNIQUE
    # again) -- the re-orchestration the timing stub never performed.
    # (The invalidation-STICKS nuance of the control suite's
    # ImStepPendingClearCorner needs both follow-on snoops inside one
    # fill window; the real engine's done latency makes that window an
    # artifact, so that pin stays with the control suite and the
    # coherence macro's real_control_loop, which exercises it with
    # prompt-AC snoops.)
    # ------------------------------------------------------------------
    async def _killed_fill_refetch(self):
        sc = 13 % self.SETS
        line_x = self._line_of(self._compose_addr(0x76, sc))
        wdata = 0xA5A5A5A55A5A5A5A & ((1 << (self.STRB_W * 8)) - 1)
        accept, _ = await self._start_miss(self._compose_addr(0x76, sc), 1,
                                           wdata=wdata, label='kfr:wr_miss',
                                           wait_beats=1)
        ar_before = self._count_ar()
        await self._snoop(line_x, 'SNOOP_READ_UNIQUE', 'kfr:ru', exp_ref='M',
                          exp_line=bytes(self._mem_line(line_x)))
        accept, rsp_cyc, rsp_data = await self._req_await_rsp(accept,
                                                              'kfr:rsp')
        sl = self._slice(accept, rsp_cyc)
        fills = [p for _, k, p in sl if k == 'fill_start']
        self._score("kfr: two fills (fetch + re-fetch)", len(fills), 2)
        self._score("kfr: both fills READ_UNIQUE",
                    [p['class'] for p in fills],
                    [ACE_READ_UNIQUE, ACE_READ_UNIQUE])
        self._score("kfr: second AR burst re-issued",
                    self._count_ar() - ar_before, 1)
        second = next(i for i, e in enumerate(sl)
                      if e[1] == 'fill_start' and e[2] is fills[1])
        wr1 = self._tag_wr_for(sl[:second], line_x)
        wr2 = self._tag_wr_for(sl[second:], line_x)
        self._score("kfr: killed fill commits I", wr1['tag_state'] & 0x7,
                    STATE_CODE['I'])
        self._score("kfr: re-fetch installs M", wr2['tag_state'] & 0x7,
                    STATE_CODE['M'])
        self._score("kfr: rsp data", rsp_data, wdata)
        self._replay_models(sl, sc, line_x, merge_be=(1 << self.STRB_W) - 1,
                            merge_wdata=wdata, label='kfr')
        self.log.info("KilledFillRefetch directed done (real re-issued AR)")

    # ------------------------------------------------------------------
    async def run(self) -> bool:
        await self._check_init()
        self.scenarios['InitWalk'] = True
        self.scenarios['StrayReqInInit'] = True
        await self._fill_orchestration()
        self.scenarios['FillOrchestration'] = True
        await self._upgrade_no_fetch_engine()
        self.scenarios['UpgradeNoFetchEngine'] = True
        if self.TEST_LEVEL in ('func', 'full'):
            await self._miss_sequence()
            self.scenarios['MissSequence'] = True
            # mid-fill snoop service + killed-fill re-fetch: the
            # inherited Task 4 suite, now against the real R channel.
            # The igl scenario drives req_valid directly (bypassing
            # _req_issue), so install its lines in the memory model
            # here -- the real fill reads the responder's model at AR
            # time, there is no stub to source beats from the golden
            # dict behind the DUT's back.
            igl_si = 12
            self._mem_line(self._line_of(self._compose_addr(0x7D, igl_si)))
            self._mem_line(self._line_of(self._compose_addr(0x7E, igl_si)))
            await self._snoop_pending_fill()
            self.scenarios['SnoopPendingFillBypass'] = True
            await self._snoop_pending_read_shared_fill()
            self.scenarios['SnoopPendingReadSharedFill'] = True
            await self._idle_grant_back_to_lookup()
            self.scenarios['IdleGrantBackToLookup'] = True
            await self._snoop_post_commit()
            self.scenarios['SnoopPostCommitApplies'] = True
            await self._snoop_other_line_mid_fill()
            self.scenarios['SnoopOtherLineMidFill'] = True
            await self._killed_fill_refetch()
            self.scenarios['KilledFillRefetch'] = True
            await self._upgrade_snoop_suite()
            self.scenarios['UpgradeNoBypassArm'] = True
            self.scenarios['UpgradeKilledByInvalidatingSnoop'] = True
            # randomized soak with idle snoops (the control suite's FULL
            # stream, at the macro's level-scaled count)
            await self._full_random()
            self.scenarios['FullRandomLockstep'] = True
            self.scenarios['IdleSnoopSoak'] = True
        return self.mismatches == 0
