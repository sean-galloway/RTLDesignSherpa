"""
GF(2^m) arithmetic testbench

One TB class for the three combinational GF blocks -- gf_mul, gf_mul_const and
gf_inv. The DUTs have no clock and no reset: each check drives the operand
ports, waits a delta, and compares against the golden model.

Golden model: reedsolo (MIT, PyPI). gf_mult_noLUT(x, y, prim, 2**m) is the
reference product for ANY m and primitive polynomial, so the TB never carries a
GF table of its own (area CLAUDE.md rule). The inverse is checked as a product:
a * inv(a) must be 1 in the same model.

Author: RTL Design Sherpa
Created: 2026-09-30
"""

import os
import random

from cocotb.triggers import Timer

import reedsolo

from TBClasses.shared.tbbase import TBBase


class GFTB(TBBase):
    """Drives one GF block and scores it against reedsolo."""

    # operand pairs per level for the variable multiplier; the const multiplier
    # and the inverse are exhaustive over a at every level (<= 4096 operands).
    MUL_SAMPLES = {'gate': 512, 'func': 8192, 'full': 65536}

    def __init__(self, dut, **kwargs):
        super().__init__(dut)
        self.SEED = self.convert_to_int(os.environ.get('SEED', '12345'))
        self.TEST_LEVEL = os.environ.get('TEST_LEVEL', 'gate').lower()
        if self.TEST_LEVEL not in self.MUL_SAMPLES:
            self.log.warning(f"Invalid TEST_LEVEL '{self.TEST_LEVEL}', using 'gate'")
            self.TEST_LEVEL = 'gate'
        self.M = self.convert_to_int(os.environ.get('SYMBOL_WIDTH', '8'))
        self.PRIM = int(os.environ.get('PRIM_POLY', '0x11D'), 0)   # hex or decimal
        self.CONST = self.convert_to_int(os.environ.get('CONST', '2'))
        self.Q = 1 << self.M
        random.seed(self.SEED)
        self.checks = 0
        self.mismatches = 0
        self.log.info(f"GFTB m={self.M} prim=0x{self.PRIM:X} level={self.TEST_LEVEL} "
                      f"seed={self.SEED}")

    # -- the three mandatory methods; nothing to clock or reset -----------------
    async def setup_clocks_and_reset(self):
        await self.assert_reset()
        await self.deassert_reset()

    async def assert_reset(self):
        await Timer(1, units='ns')

    async def deassert_reset(self):
        await Timer(1, units='ns')

    # -- golden model ----------------------------------------------------------
    def gold_mul(self, a: int, b: int) -> int:
        return reedsolo.gf_mult_noLUT(a, b, prim=self.PRIM, field_charac_full=self.Q)

    # -- scoring ---------------------------------------------------------------
    def _score(self, what: str, got: int, exp: int) -> bool:
        self.checks += 1
        if got != exp:
            self.mismatches += 1
            if self.mismatches <= 20:
                self.log.error(f"{what}: got 0x{got:X} expected 0x{exp:X}")
            return False
        return True

    def _operands(self):
        """Corner values plus random samples per level, or exhaustive at full
        when the field is small enough to make that cheap."""
        corners = {0, 1, 2, self.Q - 1, self.Q - 2, self.Q >> 1, (self.Q >> 1) - 1}
        n = self.MUL_SAMPLES[self.TEST_LEVEL]
        if self.TEST_LEVEL == 'full' and self.Q * self.Q <= n:
            return [(a, b) for a in range(self.Q) for b in range(self.Q)]
        pairs = [(a, b) for a in corners for b in corners]
        pairs += [(random.randrange(self.Q), random.randrange(self.Q)) for _ in range(n)]
        return pairs

    # -- tests ------------------------------------------------------------------
    async def run_mul(self) -> bool:
        pairs = self._operands()
        self.log.info(f"gf_mul: {len(pairs)} operand pairs")
        for a, b in pairs:
            self.dut.i_a.value = a
            self.dut.i_b.value = b
            await Timer(1, units='ns')
            self._score(f"mul({a:#x},{b:#x})", int(self.dut.ow_p.value), self.gold_mul(a, b))
        return self.mismatches == 0

    async def run_mul_const(self) -> bool:
        self.log.info(f"gf_mul_const: CONST=0x{self.CONST:X}, exhaustive over {self.Q} operands")
        for a in range(self.Q):
            self.dut.i_a.value = a
            await Timer(1, units='ns')
            self._score(f"mul_const({a:#x})", int(self.dut.ow_p.value),
                        self.gold_mul(a, self.CONST))
        return self.mismatches == 0

    async def run_inv(self) -> bool:
        self.log.info(f"gf_inv: exhaustive over {self.Q} operands")
        for a in range(self.Q):
            self.dut.i_a.value = a
            await Timer(1, units='ns')
            inv = int(self.dut.ow_inv.value)
            zero = int(self.dut.ow_zero.value)
            if a == 0:
                self._score("inv(0)", inv, 0)
                self._score("zero(0)", zero, 1)
            else:
                self._score(f"zero({a:#x})", zero, 0)
                # the inverse is right iff a * inv == 1 in the golden model
                self._score(f"a*inv({a:#x})", self.gold_mul(a, inv), 1)
        return self.mismatches == 0

    def get_test_report(self):
        return {'checks': self.checks, 'mismatches': self.mismatches}
