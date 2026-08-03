# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway
#
# Module: DaddaMultiplierTB
# Purpose: Testbench for math_multiplier_dadda_4to2
# Subsystem: framework
#
# Extracted from val/math/test_math_multiplier_dadda_4to2.py so the runner holds only the parameter grid and the
# cocotb_test.run() call ([[tb-structure]]).

import os
import random
from TBClasses.shared.tbbase import TBBase


class DaddaMultiplierTB(TBBase):
    """Testbench for Dadda 4:2 multiplier.

    Works with the interface:
    - i_multiplier: N-bit input
    - i_multiplicand: N-bit input
    - ow_product: 2N-bit output
    """

    def __init__(self, dut):
        """Initialize the testbench with design under test."""
        TBBase.__init__(self, dut)
        self.N = self.convert_to_int(os.environ.get('PARAM_N', '8'))
        self.max_val = 2**self.N
        self.mask = self.max_val - 1
        self.product_mask = (2**(2*self.N)) - 1
        self.test_level = os.environ.get('TEST_LEVEL', 'gate').lower()
        self.seed = self.convert_to_int(os.environ.get('SEED', '12345'))

        random.seed(self.seed)

        self.test_count = 0
        self.pass_count = 0
        self.fail_count = 0

        self.log.info(f"Testing Dadda 4:2 Multiplier with N={self.N}")

    def print_settings(self):
        """Print testbench settings."""
        self.log.info(f"Dadda 4:2 Multiplier Testbench Settings:")
        self.log.info(f"  Width (N): {self.N}")
        self.log.info(f"  Test Level: {self.test_level}")
        self.log.info(f"  Seed: {self.seed}")

    def clear_interface(self):
        """Clear the DUT interface."""
        self.dut.i_multiplier.value = 0
        self.dut.i_multiplicand.value = 0

    async def test_single_mult(self, a: int, b: int) -> bool:
        """Test a single multiplication operation."""
        self.dut.i_multiplier.value = a
        self.dut.i_multiplicand.value = b

        await self.wait_time(1, 'ns')

        product = int(self.dut.ow_product.value)
        expected = (a * b) & self.product_mask

        self.test_count += 1

        if product == expected:
            self.pass_count += 1
            return True
        else:
            self.fail_count += 1
            self.log.error(f"FAIL: a=0x{a:02X}, b=0x{b:02X}")
            self.log.error(f"  Expected: product=0x{expected:04X}")
            self.log.error(f"  Actual:   product=0x{product:04X}")
            return False

    async def run_comprehensive_tests(self):
        """Run comprehensive test suite based on test level."""
        test_level = self.test_level.lower()

        if test_level == 'gate':
            num_random = 20
        elif test_level == 'func':
            num_random = 100
        else:  # full
            num_random = 1000

        # Edge case tests
        self.log.info("Testing edge cases...")
        edge_cases = [
            (0, 0),
            (0, 1),
            (1, 0),
            (1, 1),
            (self.mask, 0),
            (0, self.mask),
            (self.mask, 1),
            (1, self.mask),
            (self.mask, self.mask),
            (0x80, 0x80),  # 1.0 * 1.0 for BF16 mantissa
            (0xFF, 0xFF),  # Max * Max
            (0x55, 0xAA),  # Alternating bits
            (0xAA, 0x55),
        ]

        for a, b in edge_cases:
            passed = await self.test_single_mult(a, b)
            if not passed:
                assert False, f"Edge case failed: a=0x{a:02X}, b=0x{b:02X}"

        self.log.info(f"Edge cases: {self.pass_count}/{self.test_count} passed")

        # Exhaustive test for small multipliers (if test level allows)
        if test_level == 'full' and self.N <= 8:
            self.log.info(f"Running exhaustive test ({self.max_val}x{self.max_val} = {self.max_val**2} cases)...")
            for a in range(self.max_val):
                for b in range(self.max_val):
                    passed = await self.test_single_mult(a, b)
                    if not passed:
                        assert False, f"Exhaustive test failed: a=0x{a:02X}, b=0x{b:02X}"
                if a % max(1, self.max_val // 10) == 0:
                    self.log.info(f"Exhaustive progress: {a}/{self.max_val}")
        else:
            # Random tests
            self.log.info(f"Running {num_random} random tests...")
            for i in range(num_random):
                a = random.randint(0, self.mask)
                b = random.randint(0, self.mask)
                passed = await self.test_single_mult(a, b)
                if not passed:
                    assert False, f"Random test {i} failed"

                if i % max(1, num_random // 10) == 0:
                    self.log.info(f"Progress: {i}/{num_random}")

        self.log.info(f"Final: {self.pass_count}/{self.test_count} passed, {self.fail_count} failed")
        assert self.fail_count == 0, f"Test failures: {self.fail_count}"
