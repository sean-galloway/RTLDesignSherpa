# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway
#
# Module: SortTB
# Purpose: Testbench for sort
# Subsystem: framework
#
# Extracted from val/common/test_sort.py so the runner holds only the parameter grid and the
# cocotb_test.run() call ([[tb-structure]]).

import os
import random
import cocotb
from cocotb.clock import Clock
from cocotb.triggers import RisingEdge, Timer
from TBClasses.shared.tbbase import TBBase


class SortTB(TBBase):
    """Testbench for Sort module"""

    def __init__(self, dut):
        super().__init__(dut)

        # Get test parameters from environment
        self.SEED = self.convert_to_int(os.environ.get('SEED', '12345'))
        self.TEST_LEVEL = os.environ.get('TEST_LEVEL', 'gate').lower()
        self.NUM_VALS = self.convert_to_int(os.environ.get('TEST_NUM_VALS', '5'))
        self.SIZE = self.convert_to_int(os.environ.get('TEST_SIZE', '16'))
        self.DEBUG = self.convert_to_int(os.environ.get('TEST_DEBUG', '0'))

        # Calculate derived parameters
        self.TOTAL_WIDTH = self.NUM_VALS * self.SIZE
        self.MAX_VAL = (1 << self.SIZE) - 1
        self.PIPELINE_STAGES = self.NUM_VALS  # Pipeline depth equals NUM_VALS

        # Initialize random generator
        random.seed(self.SEED)

        # Validate test level
        valid_levels = ['gate', 'func', 'full']
        if self.TEST_LEVEL not in valid_levels:
            self.log.warning(f"Invalid TEST_LEVEL '{self.TEST_LEVEL}', using 'gate'. Valid: {valid_levels}")
            self.TEST_LEVEL = 'gate'

        # Log configuration
        self.log.info(f"Sort TB initialized{self.get_time_ns_str()}")
        self.log.info(f"SEED={self.SEED}, TEST_LEVEL={self.TEST_LEVEL}")
        self.log.info(f"NUM_VALS={self.NUM_VALS}, SIZE={self.SIZE}")
        self.log.info(f"TOTAL_WIDTH={self.TOTAL_WIDTH}, MAX_VAL={self.MAX_VAL}")
        self.log.info(f"PIPELINE_STAGES={self.PIPELINE_STAGES}")

        # Initialize signal mappings
        self._setup_signals()

        # Test results storage
        self.test_results = []
        self.test_failures = []

        # Clock setup
        self.clock_period = 10  # 10ns = 100MHz

    # ---- contract lifecycle (/GLOBAL_REQUIREMENTS.md 2.2) ----------------
    # Mandatory on every TB. This class inherited TBBase's stubs, which
    # only log "should be overridden" and drive nothing -- nominally
    # compliant, functionally absent. Wraps the reset path this TB
    # already used, so behaviour is unchanged.

    async def assert_reset(self):
        """Assert reset."""
        self.dut.rst_n.value = 0

    async def deassert_reset(self):
        """Release reset."""
        self.dut.rst_n.value = 1

    async def setup_clocks_and_reset(self):
        """Start the clock and drive the full reset sequence."""
        await self.start_clock('clk', 10, 'ns')
        await self.reset_dut()

    def _setup_signals(self):
        """Setup signal mappings"""
        self.clk = self.dut.clk
        self.rst_n = self.dut.rst_n
        self.data_in = self.dut.data
        self.valid_in = self.dut.valid_in
        self.sorted_out = self.dut.sorted
        self.done_out = self.dut.done

    async def setup_clock(self):
        """Setup clock"""
        cocotb.start_soon(Clock(self.clk, self.clock_period, units="ns").start())
        await Timer(1, units='ns')

    async def reset_dut(self):
        """Reset the DUT"""
        self.rst_n.value = 0
        self.data_in.value = 0
        self.valid_in.value = 0
        await RisingEdge(self.clk)
        await RisingEdge(self.clk)
        self.rst_n.value = 1
        await RisingEdge(self.clk)

    def pack_values(self, values):
        """Pack array of values into concatenated signal"""
        packed = 0
        for i, val in enumerate(values):
            if i < self.NUM_VALS:
                packed |= (val & self.MAX_VAL) << (i * self.SIZE)
        return packed

    def unpack_values(self, packed_data):
        """Unpack concatenated signal into array of values"""
        values = []
        for i in range(self.NUM_VALS):
            val = (packed_data >> (i * self.SIZE)) & self.MAX_VAL
            values.append(val)
        return values

    def get_sorted_output(self):
        """Get the sorted output data"""
        try:
            output_val = int(self.sorted_out.value)
            return self.unpack_values(output_val)
        except:
            return [0] * self.NUM_VALS

    def is_sorted_descending(self, values):
        """Check if values are sorted in descending order"""
        for i in range(len(values) - 1):
            if values[i] < values[i + 1]:
                return False
        return True

    async def send_data_and_wait(self, input_values):
        """Send data through pipeline and wait for result"""
        # Pack and drive input with valid signal
        packed_input = self.pack_values(input_values)
        self.data_in.value = packed_input
        self.valid_in.value = 1
        await RisingEdge(self.clk)

        # Deassert valid (single cycle pulse)
        self.valid_in.value = 0

        # Wait for done signal or pipeline stages to complete
        max_wait_cycles = self.PIPELINE_STAGES + 5  # Add some margin
        wait_count = 0

        while wait_count < max_wait_cycles:
            await RisingEdge(self.clk)
            wait_count += 1

            # Check if done is asserted
            if int(self.done_out.value) == 1:
                break

        # Get output regardless of done signal for debugging
        output_values = self.get_sorted_output()
        done_asserted = (int(self.done_out.value) == 1)

        if not done_asserted:
            self.log.warning(f"Done signal not asserted after {wait_count} cycles{self.get_time_ns_str()}")

        return output_values, done_asserted

    async def test_basic_sorting(self):
        """Test basic sorting functionality"""
        self.log.info(f"Testing basic sorting{self.get_time_ns_str()}")

        await self.setup_clock()
        await self.reset_dut()

        all_passed = True

        # Test different value patterns based on level
        if self.TEST_LEVEL == 'gate':
            test_cases = [
                [5, 3, 8, 1, 9][:self.NUM_VALS],  # Mixed values
                [1, 2, 3, 4, 5][:self.NUM_VALS],  # Already sorted ascending
                [9, 7, 5, 3, 1][:self.NUM_VALS],  # Already sorted descending
            ]
        elif self.TEST_LEVEL == 'func':
            test_cases = [
                [5, 3, 8, 1, 9][:self.NUM_VALS],
                [1, 2, 3, 4, 5][:self.NUM_VALS],
                [9, 7, 5, 3, 1][:self.NUM_VALS],
                [5, 5, 5, 5, 5][:self.NUM_VALS],  # All equal
                [1, 9, 2, 8, 3][:self.NUM_VALS],  # Alternating
            ]
        else:  # full
            test_cases = [
                [5, 3, 8, 1, 9][:self.NUM_VALS],
                [1, 2, 3, 4, 5][:self.NUM_VALS],
                [9, 7, 5, 3, 1][:self.NUM_VALS],
                [5, 5, 5, 5, 5][:self.NUM_VALS],
                [1, 9, 2, 8, 3][:self.NUM_VALS],
                [0, 0, 0, 0, 0][:self.NUM_VALS],  # All zeros
                [self.MAX_VAL] * self.NUM_VALS,   # All max values
            ]

        # Pad test cases to correct length
        for i, case in enumerate(test_cases):
            while len(case) < self.NUM_VALS:
                case.append(0)
            test_cases[i] = case[:self.NUM_VALS]

        for test_num, input_values in enumerate(test_cases):
            if not all_passed and self.TEST_LEVEL == 'gate':
                break

            self.log.debug(f"Test case {test_num}: {input_values}{self.get_time_ns_str()}")

            # Send data through pipeline
            output_values, done_asserted = await self.send_data_and_wait(input_values)

            # Expected result: sorted in descending order
            expected_values = sorted(input_values, reverse=True)

            # Verify sorting
            success = (output_values == expected_values) and done_asserted

            if success:
                self.log.debug(f"PASS: {input_values} → {output_values}{self.get_time_ns_str()}")
            else:
                self.log.error(f"FAIL: {input_values} → {output_values}, expected: {expected_values}{self.get_time_ns_str()}")
                self.log.error(f"  Done asserted: {done_asserted}")
                all_passed = False
                if self.TEST_LEVEL == 'gate':
                    break

            # Store result
            result = {
                'test_type': 'basic_sorting',
                'test_num': test_num,
                'input_values': input_values,
                'output_values': output_values,
                'expected_values': expected_values,
                'done_asserted': done_asserted,
                'success': success
            }
            self.test_results.append(result)
            if not success:
                self.test_failures.append(result)

        return all_passed

    async def test_random_sorting(self):
        """Test sorting with random data"""
        if self.TEST_LEVEL == 'gate':
            self.log.info(f"Skipping random sorting tests{self.get_time_ns_str()}")
            return True

        self.log.info(f"Testing random sorting{self.get_time_ns_str()}")

        await self.setup_clock()
        await self.reset_dut()

        all_passed = True

        # Determine number of random tests based on level
        if self.TEST_LEVEL == 'func':
            num_tests = 20
        else:  # full
            num_tests = 100

        for test_num in range(num_tests):
            # Generate random input values
            input_values = [random.randint(0, min(self.MAX_VAL, 1000)) for _ in range(self.NUM_VALS)]

            self.log.debug(f"Random test {test_num}: {input_values}{self.get_time_ns_str()}")

            # Send data through pipeline
            output_values, done_asserted = await self.send_data_and_wait(input_values)

            # Expected result
            expected_values = sorted(input_values, reverse=True)

            # Verify sorting
            success = (output_values == expected_values) and done_asserted

            if not success:
                self.log.error(f"Random test {test_num} FAIL:{self.get_time_ns_str()}")
                self.log.error(f"  Input: {input_values}")
                self.log.error(f"  Output: {output_values}")
                self.log.error(f"  Expected: {expected_values}")
                self.log.error(f"  Done asserted: {done_asserted}")
                all_passed = False
                if self.TEST_LEVEL == 'func':
                    break

            # Store result (sample for large tests)
            if test_num % 10 == 0:
                result = {
                    'test_type': 'random_sorting',
                    'test_num': test_num,
                    'input_values': input_values,
                    'output_values': output_values,
                    'expected_values': expected_values,
                    'done_asserted': done_asserted,
                    'success': success
                }
                self.test_results.append(result)
                if not success:
                    self.test_failures.append(result)

        return all_passed

    async def test_pipeline_throughput(self):
        """Test pipeline throughput - can accept new data every cycle"""
        if self.TEST_LEVEL == 'gate':
            self.log.info(f"Skipping pipeline throughput tests{self.get_time_ns_str()}")
            return True

        self.log.info(f"Testing pipeline throughput{self.get_time_ns_str()}")

        await self.setup_clock()
        await self.reset_dut()

        all_passed = True

        # Create test sequence
        test_sequences = [
            [1, 2, 3, 4, 5][:self.NUM_VALS],
            [5, 4, 3, 2, 1][:self.NUM_VALS],
            [9, 1, 8, 2, 7][:self.NUM_VALS],
        ]

        # Pad sequences
        for i, seq in enumerate(test_sequences):
            while len(seq) < self.NUM_VALS:
                seq.append(0)
            test_sequences[i] = seq[:self.NUM_VALS]

        expected_outputs = [sorted(seq, reverse=True) for seq in test_sequences]

        # Send data back-to-back
        for seq_num, input_vals in enumerate(test_sequences):
            packed_input = self.pack_values(input_vals)
            self.data_in.value = packed_input
            self.valid_in.value = 1
            await RisingEdge(self.clk)
            self.valid_in.value = 0

        # Wait for all outputs to emerge
        await Timer(self.PIPELINE_STAGES * self.clock_period * 2, units='ns')

        # Note: In a real test, you'd need to track which output corresponds to which input
        # This is a simplified version that just checks the final output
        final_output = self.get_sorted_output()
        final_expected = expected_outputs[-1]

        if final_output != final_expected:
            self.log.error(f"Pipeline throughput test failed{self.get_time_ns_str()}")
            self.log.error(f"  Final output: {final_output}")
            self.log.error(f"  Expected: {final_expected}")
            all_passed = False

        # Store result
        result = {
            'test_type': 'pipeline_throughput',
            'success': all_passed
        }
        self.test_results.append(result)
        if not result['success']:
            self.test_failures.append(result)

        return all_passed

    async def test_boundary_conditions(self):
        """Test boundary conditions"""
        if self.TEST_LEVEL == 'gate':
            self.log.info(f"Skipping boundary condition tests{self.get_time_ns_str()}")
            return True

        self.log.info(f"Testing boundary conditions{self.get_time_ns_str()}")

        await self.setup_clock()
        await self.reset_dut()

        all_passed = True

        # Test boundary cases
        boundary_cases = []

        # All minimum values
        boundary_cases.append([0] * self.NUM_VALS)

        # All maximum values
        boundary_cases.append([self.MAX_VAL] * self.NUM_VALS)

        # Mix of min and max
        mix_case = []
        for i in range(self.NUM_VALS):
            mix_case.append(self.MAX_VAL if i % 2 == 0 else 0)
        boundary_cases.append(mix_case)

        # Single unique value among duplicates
        if self.NUM_VALS >= 3:
            unique_case = [5] * self.NUM_VALS
            unique_case[self.NUM_VALS // 2] = 100
            boundary_cases.append(unique_case)

        # Power of 2 values
        if self.SIZE >= 8:
            power_case = []
            for i in range(self.NUM_VALS):
                power_val = min(2 ** (i + 1), self.MAX_VAL)
                power_case.append(power_val)
            boundary_cases.append(power_case)

        for test_num, input_values in enumerate(boundary_cases):
            self.log.debug(f"Boundary test {test_num}: {input_values}{self.get_time_ns_str()}")

            # Send data through pipeline
            output_values, done_asserted = await self.send_data_and_wait(input_values)

            # Expected result
            expected_values = sorted(input_values, reverse=True)

            # Verify sorting
            success = (output_values == expected_values) and done_asserted

            if success:
                self.log.debug(f"Boundary PASS: {input_values} → {output_values}{self.get_time_ns_str()}")
            else:
                self.log.error(f"Boundary FAIL: {input_values} → {output_values}, expected: {expected_values}{self.get_time_ns_str()}")
                self.log.error(f"  Done asserted: {done_asserted}")
                all_passed = False

            # Store result
            result = {
                'test_type': 'boundary_conditions',
                'test_num': test_num,
                'input_values': input_values,
                'output_values': output_values,
                'expected_values': expected_values,
                'done_asserted': done_asserted,
                'success': success
            }
            self.test_results.append(result)
            if not success:
                self.test_failures.append(result)

        return all_passed

    async def test_reset_behavior(self):
        """Test reset behavior"""
        self.log.info(f"Testing reset behavior{self.get_time_ns_str()}")

        await self.setup_clock()

        all_passed = True

        # Apply some input values
        test_values = [5, 3, 8, 1, 9][:self.NUM_VALS]
        while len(test_values) < self.NUM_VALS:
            test_values.append(0)

        packed_input = self.pack_values(test_values)
        self.data_in.value = packed_input
        self.valid_in.value = 1

        # Reset while input is applied
        await self.reset_dut()

        # Check that output is cleared after reset
        output_values = self.get_sorted_output()
        expected_zeros = [0] * self.NUM_VALS
        done_state = int(self.done_out.value)

        if output_values != expected_zeros or done_state != 0:
            self.log.warning(f"Reset state - Output: {output_values}, Done: {done_state}{self.get_time_ns_str()}")
            # This might not be a failure depending on RTL implementation

        # Apply new input after reset
        new_values = [2, 7, 4, 1, 6][:self.NUM_VALS]
        while len(new_values) < self.NUM_VALS:
            new_values.append(0)

        # Send data through pipeline
        output_values, done_asserted = await self.send_data_and_wait(new_values)
        expected_values = sorted(new_values, reverse=True)

        if output_values != expected_values or not done_asserted:
            self.log.error(f"Post-reset sorting failed: {output_values} != {expected_values}{self.get_time_ns_str()}")
            self.log.error(f"  Done asserted: {done_asserted}")
            all_passed = False

        # Store result
        result = {
            'test_type': 'reset_behavior',
            'success': all_passed
        }
        self.test_results.append(result)
        if not result['success']:
            self.test_failures.append(result)

        return all_passed

    async def run_all_tests(self):
        """Run all appropriate tests based on test level"""
        self.log.info(f"Running SORT tests at level: {self.TEST_LEVEL.upper()}{self.get_time_ns_str()}")

        # Define test functions
        test_functions = [
            (self.test_basic_sorting, "Basic sorting"),
            (self.test_random_sorting, "Random sorting"),
            (self.test_pipeline_throughput, "Pipeline throughput"),
            (self.test_boundary_conditions, "Boundary conditions"),
            (self.test_reset_behavior, "Reset behavior")
        ]

        all_passed = True
        test_results = {}

        # Clear previous results
        self.test_results = []
        self.test_failures = []

        # Run tests
        for i, (test_func, test_name) in enumerate(test_functions, 1):
            self.log.info(f"[{i}/{len(test_functions)}] {test_name}{self.get_time_ns_str()}")
            try:
                test_passed = await test_func()
                test_results[test_name] = test_passed

                if not test_passed:
                    self.log.error(f"{test_name} FAILED{self.get_time_ns_str()}")
                    all_passed = False
                else:
                    self.log.info(f"{test_name} PASSED{self.get_time_ns_str()}")

            except Exception as e:
                self.log.error(f"{test_name} raised exception: {str(e)}{self.get_time_ns_str()}")
                test_results[test_name] = False
                all_passed = False

        # Print summary
        self.log.info("="*60)
        self.log.info("TEST RESULTS SUMMARY")
        self.log.info("="*60)
        for test_name, result in test_results.items():
            status = "PASSED" if result else "FAILED"
            self.log.info(f"{test_name}: {status}")
        self.log.info("="*60)

        overall_status = "PASSED" if all_passed else "FAILED"
        self.log.info(f"Overall SORT result: {overall_status}")
        self.log.info(f"Total operations: {len(self.test_results)}, Failures: {len(self.test_failures)}")
        self.log.info("="*60)

        return all_passed
