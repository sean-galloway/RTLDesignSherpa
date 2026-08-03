# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway
#
# Module: AddSubTB
# Purpose: Testbench for math_addsub_full_nbit
# Subsystem: framework
#
# Extracted from val/math/test_math_addsub_full_nbit.py so the runner holds only the parameter grid and the
# cocotb_test.run() call ([[tb-structure]]).

import os
import random
import itertools
from TBClasses.shared.tbbase import TBBase


class AddSubTB(TBBase):
    """Testbench for adder/subtractor modules."""

    def __init__(self, dut):
        """Initialize the testbench with design under test.

        Args:
            dut: The cocotb design under test object
        """
        TBBase.__init__(self, dut)
        self.N = self.convert_to_int(os.environ.get('PARAM_N', '1'))
        self.max_val = 2**self.N
        self.mask = self.max_val - 1
        self.test_level = os.environ.get('TEST_LEVEL', 'gate').lower()
        self.seed = self.convert_to_int(os.environ.get('SEED', '12345'))

        # Initialize the random generator
        random.seed(self.seed)

        # Track test statistics
        self.test_count = 0
        self.pass_count = 0
        self.fail_count = 0

        # Get DUT type
        self.dut_type = os.environ.get('DUT', 'unknown')
        self.log.info(f"Testing {self.dut_type} with N={self.N}")

    def clear_interface(self):
        """Clear the DUT interface by setting all inputs to 0."""
        self.dut.i_a.value = 0
        self.dut.i_b.value = 0
        self.dut.i_c.value = 0

    def print_settings(self):
        """Print the current testbench settings."""
        self.log.info('-------------------------------------------')
        self.log.info('Add/Sub Testbench Settings:')
        self.log.info(f'    DUT:   {self.dut_type}')
        self.log.info(f'    N:     {self.N}')
        self.log.info(f'    Mask:  0x{self.mask:X}')
        self.log.info(f'    Seed:  {self.seed}')
        self.log.info(f'    Level: {self.test_level}')
        self.log.info('-------------------------------------------')

    async def main_loop(self, count=256):
        """Main test loop for adder/subtractor.

        Tests all combinations of inputs up to max_val or randomly samples
        if max_val is larger than count.

        Args:
            count: Number of test vectors to generate if random sampling
        """
        self.log.info(f"Starting main test loop with count={count}")

        # Determine if we need to test all possible values or random sampling
        if self.max_val < count:
            self.log.info(f"Testing all {self.max_val} possible values")
            a_list = list(range(self.max_val))
            b_list = list(range(self.max_val))
        else:
            self.log.info(f"Random sampling with {count} test vectors")
            a_list = [random.randint(0, self.mask) for _ in range(count)]
            b_list = [random.randint(0, self.mask) for _ in range(count)]

        # Test both addition and subtraction modes
        c_list = [0, 1]  # 0 for addition, 1 for subtraction

        total_tests = len(a_list) * len(b_list) * len(c_list)
        self.log.info(f"Will run {total_tests} total test cases")

        # Test the adder/subtractor
        for test_idx, (a, b, cin) in enumerate(itertools.product(a_list, b_list, c_list)):
            # Log progress periodically
            if test_idx % max(1, total_tests // 10) == 0:
                self.log.info(f"Progress: {test_idx}/{total_tests} tests completed")

            # Apply test inputs
            self.dut.i_a.value = a
            self.dut.i_b.value = b
            self.dut.i_c.value = cin

            # Wait for a simulation time to ensure values propagate
            await self.wait_time(2, 'ns')

            # Check if the operation is addition or subtraction
            if cin == 0:  # Addition
                expected_sum = (a + b) & self.mask
                expected_c = 1 if (a + b) >= self.max_val else 0
            else:  # Subtraction
                expected_sum = (a - b) & self.mask
                expected_c = 0 if a < b else 1  # borrow vs. no borrow

            # Get actual outputs
            actual_sum = int(self.dut.ow_sum.value)
            actual_c = int(self.dut.ow_carry.value)

            msg = f'{a=} {b=} {cin=} {expected_sum=} {actual_sum=}'
            self.log.debug(msg)

            # Verify results
            if (actual_sum != expected_sum) or (actual_c != expected_c):
                self.log.error(f"Test failed for inputs: a={a}, b={b}, cin={cin} (mode={'subtraction' if cin else 'addition'})")
                self.log.error(f"  Expected: sum={expected_sum}, carry/borrow={expected_c}")
                self.log.error(f"  Actual: sum={actual_sum}, carry/borrow={actual_c}")

                # For debugging, also print binary
                self.log.error("  Binary comparison:")
                self.log.error(f"    a      = {bin(a)[2:].zfill(self.N)}")
                self.log.error(f"    b      = {bin(b)[2:].zfill(self.N)}")
                self.log.error(f"    mode   = {'subtraction' if cin else 'addition'}")
                self.log.error(f"    exp_sum= {bin(expected_sum)[2:].zfill(self.N)}")
                self.log.error(f"    act_sum= {bin(actual_sum)[2:].zfill(self.N)}")

                self.fail_count += 1
                assert False, f"Add/Sub test failed for inputs a={a}, b={b}, cin={cin}"
            else:
                self.pass_count += 1

            self.test_count += 1

        # Print test summary
        self.log.info(f"Test Summary: {self.pass_count}/{self.test_count} passed, {self.fail_count} failed")
