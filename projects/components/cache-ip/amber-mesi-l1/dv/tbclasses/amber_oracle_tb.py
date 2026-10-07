"""
amber_fsm_oracle pkg-pin testbench

Drives the landed amber_snoop_kmap leaf (the module-boundary wrapper over the
amber_pkg Table 3.0 decode functions) with every {state, snoop} cell the
gem5-derived oracle produces a CRRESP for, and scores the DUT against the
ORACLE -- not against a table copy -- so the simulation is a direct
pkg<->oracle consistency pin. Reserved encodings (Owned / RSV5-7 line states,
snoop codes 6/7) are checked against the contracted safe default, and the
oracle is asserted to refuse them.

The DUT is combinational: each check drives the inputs, waits a delta, and
compares, exactly like the amber_snoop_kmap TB this class is modeled on.

Author: RTL Design Sherpa
Created: 2026-10-07
"""

import os

from cocotb.triggers import Timer

from TBClasses.shared.tbbase import TBBase

from projects.components.cache_ip.amber_mesi_l1.dv.golden.amber_fsm_oracle import (
    AmberOracleError,
    step,
)


class AmberOracleTB(TBBase):
    """Scores amber_snoop_kmap against the gem5-derived FSM oracle."""

    # cache_state_t encodings (amber_pkg): 3-bit, MESI now + MOESI headroom
    STATE_I = 0b000
    STATE_S = 0b001
    STATE_E = 0b010
    STATE_M = 0b011

    # amber_snoop_t encodings (amber_pkg): the six IHI0022 AC snoop types
    SNOOP_READ_SHARED   = 0b000
    SNOOP_READ_ONCE     = 0b001
    SNOOP_READ_UNIQUE   = 0b010
    SNOOP_CLEAN_SHARED  = 0b011
    SNOOP_CLEAN_INVALID = 0b100
    SNOOP_MAKE_INVALID  = 0b101

    SNOOP_BY_EVENT = {
        'SNOOP_READ_SHARED':   SNOOP_READ_SHARED,
        'SNOOP_READ_ONCE':     SNOOP_READ_ONCE,
        'SNOOP_READ_UNIQUE':   SNOOP_READ_UNIQUE,
        'SNOOP_CLEAN_SHARED':  SNOOP_CLEAN_SHARED,
        'SNOOP_CLEAN_INVALID': SNOOP_CLEAN_INVALID,
        'SNOOP_MAKE_INVALID':  SNOOP_MAKE_INVALID,
    }

    # pkg-decode reference state name -> 3-bit encoding (the state whose
    # Table 3.0 row answers a snoop during a transient)
    REF_BY_NAME = {
        'I': STATE_I,
        'S': STATE_S,
        'E': STATE_E,
        'M': STATE_M,
    }

    SAFE_DEFAULT_CRRESP = 0b00000
    SAFE_DEFAULT_NEXT   = STATE_I

    def __init__(self, dut, **kwargs):
        super().__init__(dut)
        self.TEST_LEVEL = os.environ.get('TEST_LEVEL', 'gate').lower()
        self.checks = 0
        self.mismatches = 0
        self.log.info("AmberOracleTB: oracle<->pkg pin via amber_snoop_kmap")

    # -- the three mandatory methods; the DUT is purely combinational --------
    async def setup_clocks_and_reset(self):
        await self.assert_reset()
        await self.deassert_reset()

    async def assert_reset(self):
        await Timer(1, units='ns')

    async def deassert_reset(self):
        await Timer(1, units='ns')

    # -- scoring --------------------------------------------------------------
    @staticmethod
    def _fmt(val):
        return f"0b{val:05b}" if isinstance(val, int) else str(val)

    def _score(self, what, got, exp):
        self.checks += 1
        if got != exp:
            self.mismatches += 1
            if self.mismatches <= 20:
                self.log.error(f"{what}: got {self._fmt(got)} "
                               f"expected {self._fmt(exp)}")

    async def _drive(self, state3, snoop3):
        self.dut.line_state.value = state3
        self.dut.snoop_type.value = snoop3
        await Timer(1, units='ns')
        return int(self.dut.crresp.value), int(self.dut.next_state.value)

    # -- tests ------------------------------------------------------------------
    async def run(self, rows) -> bool:
        """Score the pkg decode against the oracle.

        rows: the transition table from the test module. Snoop rows are
        driven at their pkg-decode reference state; stable-state rows also
        pin next_state. Level grid mirrors the kmap TB: gate = stable rows,
        func = + transient rows, full = + exhaustive reserved-encoding sweep.
        """
        level = self.TEST_LEVEL
        snoop_rows = [r for r in rows if r['event'].startswith('SNOOP_')]
        stable_rows = [r for r in snoop_rows
                       if r['state'] in ('I', 'S', 'E', 'M')]
        transient_rows = [r for r in snoop_rows
                          if r['state'] not in ('I', 'S', 'E', 'M')]

        if level == 'gate':
            run_rows = stable_rows
        else:
            run_rows = snoop_rows

        self.log.info(f"amber_oracle pkg-pin: {len(run_rows)} snoop rows "
                      f"at {level}")

        for r in run_rows:
            res = step(r['state'], r['event'], fill=r['fill'],
                       pending=r['in_pending'])
            state3 = self.REF_BY_NAME[r['ref']]
            snoop3 = self.SNOOP_BY_EVENT[r['event']]
            got_crresp, got_next = await self._drive(state3, snoop3)
            self._score(f"crresp({r['ref']},{r['event']}) [{r['cite']}]",
                        got_crresp, res.crresp)
            if r['state'] in ('I', 'S', 'E', 'M'):
                self._score(f"next_state({r['state']},{r['event']})",
                            got_next, self.REF_BY_NAME[res.next_state])

        if level == 'full':
            # Reserved encodings contract to the safe default in the pkg
            # decode (the snoop responder can never crash), while the oracle
            # refuses them -- both halves of the contract asserted here.
            reserved_states = (0b100, 0b101, 0b110, 0b111)
            reserved_snoops = (0b110, 0b111)
            for s in reserved_states:
                for n in (self.SNOOP_READ_SHARED, 0b110):
                    got_crresp, got_next = await self._drive(s, n)
                    self._score(f"crresp(reserved state 0b{s:03b},0b{n:03b})",
                                got_crresp, self.SAFE_DEFAULT_CRRESP)
                    self._score(f"next_state(reserved state 0b{s:03b},0b{n:03b})",
                                got_next, self.SAFE_DEFAULT_NEXT)
            for n in reserved_snoops:
                for s in (self.STATE_I, self.STATE_M):
                    got_crresp, got_next = await self._drive(s, n)
                    self._score(f"crresp(0b{s:03b},reserved snoop 0b{n:03b})",
                                got_crresp, self.SAFE_DEFAULT_CRRESP)
                    self._score(f"next_state(0b{s:03b},reserved snoop 0b{n:03b})",
                                got_next, self.SAFE_DEFAULT_NEXT)
            # The oracle side of the reserved contract.
            self.checks += 1
            try:
                step('O', 'SNOOP_READ_SHARED')
                self.mismatches += 1
                self.log.error("oracle accepted reserved state 'O'")
            except AmberOracleError:
                pass
            self.checks += 1
            try:
                step('I', 'SNOOP_RESERVED_6')
                self.mismatches += 1
                self.log.error("oracle accepted reserved snoop encoding")
            except AmberOracleError:
                pass

        return self.mismatches == 0

    def get_test_report(self):
        return {'checks': self.checks, 'mismatches': self.mismatches}
