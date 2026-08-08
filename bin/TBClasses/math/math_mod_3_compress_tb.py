# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway
#
# Module: MathMod3CompressTB
# Purpose: Testbench for math_mod_3_compress
# Subsystem: framework
#
# Extracted from val/math/test_math_mod_3_compress.py, which had no TB class
# ([[tb-structure]]).

import os

from cocotb.triggers import Timer

from TBClasses.shared.tbbase import TBBase


class MathMod3CompressTB(TBBase):
    """Testbench for math_mod_3_compress: rem_out == d_in % 3.

    The DUT is purely combinational -- d_in in, rem_out out, no clock and no
    reset -- so the contract lifecycle methods are honest no-ops rather than
    invented ceremony. They exist because every TB implements them
    (/GLOBAL_REQUIREMENTS.md 2.2), and a caller that drives the standard
    sequence gets correct behaviour here instead of a base-class stub that
    silently does nothing.
    """

    STRIDE = {'gate': 64, 'func': 8, 'full': 1}

    def __init__(self, dut):
        super().__init__(dut)
        self.TEST_LEVEL = os.environ.get('TEST_LEVEL', 'gate').lower()
        if self.TEST_LEVEL not in ('gate', 'func', 'full'):
            self.TEST_LEVEL = 'gate'
        self.stride = self.STRIDE[self.TEST_LEVEL]
        self.log.info(f"MathMod3CompressTB: TEST_LEVEL={self.TEST_LEVEL}, "
                      f"stride={self.stride}")

    async def assert_reset(self):
        """No reset: this DUT is combinational."""
        return

    async def deassert_reset(self):
        """No reset: this DUT is combinational."""
        return

    async def setup_clocks_and_reset(self):
        """No clock or reset to set up; the input starts at a known value."""
        self.dut.d_in.value = 0
        await Timer(1, units="ns")

    async def sweep(self):
        """Check rem_out == d_in % 3 across the 16-bit space at this depth.

        full is exhaustive (65536); func samples every 8th value and gate every
        64th. A strided sweep still exercises every carry-save path -- what it
        gives up is exhaustiveness, which is what the level knob is for.
        """
        for d in range(0, 1 << 16, self.stride):
            self.dut.d_in.value = d
            await Timer(1, units="ns")
            got = int(self.dut.rem_out.value)
            exp = d % 3
            assert got == exp, f"d_in={d}: rem_out={got}, expected {exp}"
        self.log.info(f"math_mod_3_compress: {(1 << 16) // self.stride} values checked")
