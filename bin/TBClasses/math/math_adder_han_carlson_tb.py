# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway
#
# Module: HanCarlsonAdderTB
# Purpose: Testbench for math_adder_han_carlson
# Subsystem: framework
#
# Extracted from val/math/test_math_adder_han_carlson.py so the runner holds only the parameter grid and the
# cocotb_test.run() call ([[tb-structure]]).

import os
import random
from TBClasses.shared.tbbase import TBBase


class HanCarlsonAdderTB(TBBase):
    """Testbench for Han-Carlson prefix adder.

    Works with the interface:
    - i_a, i_b: N-bit inputs
    - i_cin: Carry input
    - ow_sum: N-bit sum output
    - ow_cout: Carry output
    """

    def __init__(self, dut):
        """Initialize the testbench with design under test."""
        TBBase.__init__(self, dut)
        self.N = self.convert_to_int(os.environ.get('PARAM_N', '16'))
        self.max_val = 2**self.N
        self.mask = self.max_val - 1
        self.test_level = os.environ.get('TEST_LEVEL', 'gate').lower()
        self.seed = self.convert_to_int(os.environ.get('SEED', '12345'))

        random.seed(self.seed)

        self.test_count = 0
        self.pass_count = 0
        self.fail_count = 0

        self.log.info(f"Testing Han-Carlson Adder with N={self.N}")

    def print_settings(self):
        """Print testbench settings."""
        self.log.info(f"Han-Carlson Adder Testbench Settings:")
        self.log.info(f"  Width (N): {self.N}")
        self.log.info(f"  Test Level: {self.test_level}")
        self.log.info(f"  Seed: {self.seed}")

    def clear_interface(self):
        """Clear the DUT interface."""
        self.dut.i_a.value = 0
        self.dut.i_b.value = 0
        self.dut.i_cin.value = 0

    async def test_single_add(self, a: int, b: int, cin: int) -> bool:
        """Test a single addition operation."""
        self.dut.i_a.value = a
        self.dut.i_b.value = b
        self.dut.i_cin.value = cin

        await self.wait_time(1, 'ns')

        ow_sum = int(self.dut.ow_sum.value)
        ow_cout = int(self.dut.ow_cout.value)

        # Calculate expected
        full_sum = a + b + cin
        expected_sum = full_sum & self.mask
        expected_cout = 1 if full_sum >= self.max_val else 0

        self.test_count += 1

        if ow_sum == expected_sum and ow_cout == expected_cout:
            self.pass_count += 1
            return True
        else:
            self.fail_count += 1
            self.log.error(f"FAIL: a=0x{a:X}, b=0x{b:X}, cin={cin}")
            self.log.error(f"  Expected: sum=0x{expected_sum:X}, cout={expected_cout}")
            self.log.error(f"  Actual:   sum=0x{ow_sum:X}, cout={ow_cout}")
            return False

    async def run_comprehensive_tests(self):
        """Run comprehensive test suite based on test level."""
        test_level = self.test_level.lower()

        if test_level == 'gate':
            num_random = 10
        elif test_level == 'func':
            num_random = 500
        elif test_level == 'full':
            num_random = 1000
        else:
            # Unknown level must not silently run the DEEPEST suite (the old
            # else did exactly that); fall back to func and say so.
            self.log.warning(f"Unknown test_level '{test_level}', using func")
            num_random = 500

        # Edge case tests
        self.log.info("Testing edge cases...")
        edge_cases = [
            (0, 0, 0),
            (0, 0, 1),
            (self.mask, 0, 0),
            (self.mask, 0, 1),
            (0, self.mask, 0),
            (0, self.mask, 1),
            (self.mask, self.mask, 0),
            (self.mask, self.mask, 1),
            (self.mask // 2, self.mask // 2, 0),
            (self.mask // 2, self.mask // 2 + 1, 0),
        ]

        for a, b, cin in edge_cases:
            passed = await self.test_single_add(a, b, cin)
            if not passed:
                assert False, f"Edge case failed: a=0x{a:X}, b=0x{b:X}, cin={cin}"

        self.log.info(f"Edge cases: {self.pass_count}/{self.test_count} passed")

        # Random tests
        self.log.info(f"Running {num_random} random tests...")
        for i in range(num_random):
            a = random.randint(0, self.mask)
            b = random.randint(0, self.mask)
            cin = random.randint(0, 1)
            passed = await self.test_single_add(a, b, cin)
            if not passed:
                assert False, f"Random test {i} failed"

            if i % max(1, num_random // 10) == 0:
                self.log.info(f"Progress: {i}/{num_random}")

        self.log.info(f"Final: {self.pass_count}/{self.test_count} passed, {self.fail_count} failed")
        assert self.fail_count == 0, f"Test failures: {self.fail_count}"
