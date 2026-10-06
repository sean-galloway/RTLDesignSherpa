"""
amber_snoop_kmap testbench

Combinational decode of {line_state, snoop_type} -> {crresp, next_state}
per the amber HAS Table 3.0 MESI snoop matrix. The DUT has no clock and no
reset: each check drives the inputs, waits a delta, and compares.

Golden model: this TB carries an independent copy of HAS Table 3.0 -- the
amber MESI interpretation of the cocotb-framework 1.2.0 ACE BFM default
handler, cross-checked against the gem5 Ruby MESI_Two_Level transient tables
(amber PRD D9). The model is deliberately NOT imported from anywhere near the
RTL or the kmap workbook generator: a test that shares code with the DUT can
never fail for the right reason.

Author: RTL Design Sherpa
Created: 2026-10-06
"""

import os

from cocotb.triggers import Timer

from TBClasses.shared.tbbase import TBBase


class AmberSnoopKmapTB(TBBase):
    """Scores amber_snoop_kmap against the HAS Table 3.0 truth table."""

    # cache_state_t encodings (amber_pkg): 3-bit, MESI now + MOESI headroom
    STATE_I = 0b000
    STATE_S = 0b001
    STATE_E = 0b010
    STATE_M = 0b011
    STATE_O = 0b100          # reserved in v1.0 (MOESI headroom, D6)

    # amber_snoop_t encodings (amber_pkg): the six IHI0022 AC snoop types.
    # CleanUnique / MakeUnique are master transactions, not snoops, and never
    # appear here (HAS Table 3.0 note).
    SNOOP_READ_SHARED   = 0b000
    SNOOP_READ_ONCE     = 0b001
    SNOOP_READ_UNIQUE   = 0b010
    SNOOP_CLEAN_SHARED  = 0b011
    SNOOP_CLEAN_INVALID = 0b100
    SNOOP_MAKE_INVALID  = 0b101

    CRRESP_W = 5
    NEXT_W = 3

    def __init__(self, dut, **kwargs):
        super().__init__(dut)
        self.TEST_LEVEL = os.environ.get('TEST_LEVEL', 'gate').lower()
        self.checks = 0
        self.mismatches = 0
        self.log.info("AmberSnoopKmapTB: HAS Table 3.0 decode")

    # -- the three mandatory methods; the DUT is purely combinational --------
    async def setup_clocks_and_reset(self):
        await self.assert_reset()
        await self.deassert_reset()

    async def assert_reset(self):
        await Timer(1, units='ns')

    async def deassert_reset(self):
        await Timer(1, units='ns')

    # -- golden model: HAS Table 3.0, CRRESP = (DT, Err, PD, IS, WU) ---------
    # One row per reachable {state, snoop} cell. Reserved cells -- Owned (not
    # implemented in v1.0) and snoop codes 6/7 (not IHI0022 encodings) -- are
    # contracted to the safe default (no transfer, next = Invalid), which is
    # also how the kmap workbook marks those cells don't-care.
    def model(self, state, snoop):
        if state == self.STATE_M:
            if snoop in (self.SNOOP_READ_SHARED, self.SNOOP_CLEAN_SHARED,
                         self.SNOOP_CLEAN_INVALID):
                return (1, 0, 1, 1, 0), self.STATE_I if snoop == self.SNOOP_CLEAN_INVALID else self.STATE_S
            if snoop in (self.SNOOP_READ_ONCE, self.SNOOP_READ_UNIQUE):
                return (1, 0, 1, 0, 0), self.STATE_I
            if snoop == self.SNOOP_MAKE_INVALID:
                return (0, 0, 0, 0, 0), self.STATE_I
        elif state == self.STATE_E:
            if snoop in (self.SNOOP_READ_SHARED, self.SNOOP_READ_ONCE):
                return (1, 0, 0, 1, 1), self.STATE_S
            if snoop == self.SNOOP_READ_UNIQUE:
                return (1, 0, 0, 0, 1), self.STATE_I
            if snoop == self.SNOOP_CLEAN_SHARED:
                return (0, 0, 0, 1, 1), self.STATE_E
            if snoop in (self.SNOOP_CLEAN_INVALID, self.SNOOP_MAKE_INVALID):
                return (0, 0, 0, 0, 0), self.STATE_I
        elif state == self.STATE_S:
            if snoop in (self.SNOOP_READ_SHARED, self.SNOOP_READ_ONCE):
                return (0, 0, 0, 1, 0), self.STATE_S
            if snoop == self.SNOOP_CLEAN_SHARED:
                return (0, 0, 0, 0, 0), self.STATE_S
            if snoop in (self.SNOOP_READ_UNIQUE, self.SNOOP_CLEAN_INVALID,
                         self.SNOOP_MAKE_INVALID):
                return (0, 0, 0, 0, 0), self.STATE_I
        return (0, 0, 0, 0, 0), self.STATE_I

    # -- scoring --------------------------------------------------------------
    def _score(self, what, got, exp):
        self.checks += 1
        if got != exp:
            self.mismatches += 1
            if self.mismatches <= 20:
                self.log.error(f"{what}: got 0b{got:0{self.CRRESP_W}b} "
                               f"expected 0b{exp:0{self.CRRESP_W}b}")

    async def _check_cell(self, state, snoop):
        exp_crresp, exp_next = self.model(state, snoop)
        exp_crresp_int = 0
        for bit in exp_crresp:
            exp_crresp_int = (exp_crresp_int << 1) | bit
        self.dut.line_state.value = state
        self.dut.snoop_type.value = snoop
        await Timer(1, units='ns')
        self._score(f"crresp(state=0b{state:03b},snoop=0b{snoop:03b})",
                    int(self.dut.crresp.value), exp_crresp_int)
        self._score(f"next_state(state=0b{state:03b},snoop=0b{snoop:03b})",
                    int(self.dut.next_state.value), exp_next)

    # -- tests ------------------------------------------------------------------
    async def run(self) -> bool:
        states = [self.STATE_I, self.STATE_S, self.STATE_E, self.STATE_M]
        snoops = [self.SNOOP_READ_SHARED, self.SNOOP_READ_ONCE,
                  self.SNOOP_READ_UNIQUE, self.SNOOP_CLEAN_SHARED,
                  self.SNOOP_CLEAN_INVALID, self.SNOOP_MAKE_INVALID]
        level = self.TEST_LEVEL

        if level == 'gate':
            cells = [(s, n) for s in states for n in snoops]
        elif level == 'func':
            cells = [(s, n) for s in states for n in snoops]
            cells += [(s, n) for s in states for n in (0b110, 0b111)]
            cells += [(self.STATE_O, n) for n in snoops]
        else:  # full: exhaustive over the whole 3-bit x 3-bit space
            cells = [(s, n) for s in range(8) for n in range(8)]

        self.log.info(f"amber_snoop_kmap: {len(cells)} cells at {level}")
        for s, n in cells:
            await self._check_cell(s, n)
        return self.mismatches == 0

    def get_test_report(self):
        return {'checks': self.checks, 'mismatches': self.mismatches}
