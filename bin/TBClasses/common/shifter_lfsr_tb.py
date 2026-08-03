# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway
#
# Module: ShifterLFSRTB
# Purpose: Testbench for shifter_lfsr
# Subsystem: framework
#
# Extracted from val/common/test_shifter_lfsr.py so the runner holds only the parameter grid and the
# cocotb_test.run() call ([[tb-structure]]).

import os
import random
from TBClasses.shared.tbbase import TBBase


class ShifterLFSRTB(TBBase):
    """
    Testbench for the LFSR Shifter module
    Features:
    - Verify LFSR sequence generation
    - Test seed loading
    - Verify cycle detection
    - Test with different widths and tap configurations
    """

    def __init__(self, dut):
        """Initialize the testbench with the DUT"""
        super().__init__(dut)

        # Get test parameters from environment variables
        self.SEED = self.convert_to_int(os.environ.get('SEED', '12345'))
        self.TEST_LEVEL = os.environ.get('TEST_LEVEL', 'gate').lower()
        self.WIDTH = self.convert_to_int(os.environ.get('TEST_WIDTH', '8'))
        self.TAP_INDEX_WIDTH = self.convert_to_int(os.environ.get('TEST_TAP_INDEX_WIDTH', '12'))
        self.TAP_COUNT = self.convert_to_int(os.environ.get('TEST_TAP_COUNT', '4'))

        # Calculate maximum data value based on width
        self.MAX_DATA = (1 << self.WIDTH) - 1

        # Initialize random generator
        random.seed(self.SEED)

        # Extract DUT signals
        self.clk = self.dut.clk
        self.rst_n = self.dut.rst_n
        self.enable = self.dut.enable
        self.seed_load = self.dut.seed_load
        self.seed_data = self.dut.seed_data
        self.taps = self.dut.taps
        self.lfsr_out = self.dut.lfsr_out
        self.lfsr_done = self.dut.lfsr_done

        # Log configuration
        self.log.info("LFSR Shifter TB initialized")
        self.log.info(f"SEED={self.SEED}")
        self.log.info(f"TEST_LEVEL={self.TEST_LEVEL}")
        self.log.info(f"WIDTH={self.WIDTH}")
        self.log.info(f"TAP_INDEX_WIDTH={self.TAP_INDEX_WIDTH}")
        self.log.info(f"TAP_COUNT={self.TAP_COUNT}")

        # Test results storage
        self.test_results = []

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

    async def reset_dut(self):
        """Reset the DUT"""
        self.log.debug(f'Starting reset_dut{self.get_time_ns_str()}')

        # Initialize inputs
        self.enable.value = 0
        self.seed_load.value = 0
        self.seed_data.value = 0

        # Set up default taps
        self.set_taps([self.WIDTH, self.WIDTH//2, 2, 1])

        # Apply reset
        self.rst_n.value = 0
        await self.wait_clocks('clk', 5)
        self.rst_n.value = 1
        await self.wait_clocks('clk', 10)

        self.log.debug('Ending reset_dut')

    def set_taps(self, tap_values):
        """
        Set the tap values for the LFSR

        Args:
            tap_values: List of tap values
        """
        # Ensure we have the right number of taps
        taps = tap_values[:self.TAP_COUNT]
        # Pad with zeros if needed
        taps += [0] * (self.TAP_COUNT - len(taps))

        # Concatenate tap positions into a single value
        tap_value = 0
        for i, tap in enumerate(taps):
            # Make sure tap value fits in TAP_INDEX_WIDTH bits
            tap = min(tap, (1 << self.TAP_INDEX_WIDTH) - 1)
            tap_value |= tap << (i * self.TAP_INDEX_WIDTH)

        self.taps.value = tap_value

        self.log.info(f"Set taps to: {taps}{self.get_time_ns_str()}")

    async def load_seed(self, seed_value):
        """
        Load a seed value into the LFSR

        Args:
            seed_value: Seed value to load
        """
        seed_value &= self.MAX_DATA

        self.log.info(f"Loading seed: 0x{seed_value:x}{self.get_time_ns_str()}")

        # Enable seed loading
        self.seed_load.value = 1
        self.seed_data.value = seed_value
        self.enable.value = 1

        # Wait a cycle
        await self.wait_clocks('clk', 1)

        # Disable seed loading
        self.seed_load.value = 0

        # Wait a cycle
        # await self.wait_clocks('clk', 2)

    async def run_lfsr(self, cycles, verify_sequence=True, expected_sequence=None):
        """
        Run the LFSR for a number of cycles

        Args:
            cycles: Number of cycles to run
            verify_sequence: Whether to verify the LFSR sequence
            expected_sequence: Expected LFSR sequence (if None, use reference model)

        Returns:
            Dict with test results
        """
        # Initialize result dict
        result = {
            'cycles': cycles,
            'lfsr_values': [],
            'done_detected': False,
            'done_at_cycle': None,
            'expected_values': expected_sequence or [],
            'all_match': True
        }

        # Enable the LFSR
        self.enable.value = 1

        # Run for the specified number of cycles
        for i in range(cycles):
            # Wait for clock edge
            await self.wait_clocks('clk', 1)

            # Read outputs
            await self.wait_falling_clocks('clk', 1)
            lfsr_value = int(self.lfsr_out.value)
            done_bit = int(self.lfsr_done.value)

            # Store results
            result['lfsr_values'].append(lfsr_value)

            # Check if done bit is set
            if done_bit and not result['done_detected']:
                result['done_detected'] = True
                result['done_at_cycle'] = i
                self.log.info(f"LFSR cycle detected at cycle {i}{self.get_time_ns_str()}")

            # Log LFSR value
            self.log.debug(f"Cycle {i}: LFSR=0x{lfsr_value:x}, Done={done_bit}{self.get_time_ns_str()}")

        # Verify sequence if requested
        if verify_sequence and expected_sequence:
            min_len = min(len(result['lfsr_values']), len(expected_sequence))
            for i in range(min_len):
                if result['lfsr_values'][i] != expected_sequence[i]:
                    result['all_match'] = False
                    self.log.error(f"LFSR mismatch at cycle {i}: " +
                                    f"expected=0x{expected_sequence[i]:x}, " +
                                    f"actual=0x{result['lfsr_values'][i]:x}{self.get_time_ns_str()}")

            if result['all_match']:
                self.log.info(f"LFSR sequence verified successfully{self.get_time_ns_str()}")

        # Disable the LFSR
        self.enable.value = 0

        # Store result
        self.test_results.append(result)

        return result

    def simulate_xnor_lfsr(self, seed, taps, cycles):
        """
        Simulate an LFSR in software to match the RTL implementation

        Args:
            seed: Seed value
            taps: List of tap values
            cycles: Number of cycles to simulate

        Returns:
            List of LFSR values
        """
        # Initialize values
        r_lfsr = seed & self.MAX_DATA
        results = []

        # Create tap mask based on the tap values
        # Note: In RTL, taps are 1-indexed (so tap 8 means bit 7)
        tap_mask = 0
        for tap in taps:
            if tap > 0 and tap <= self.WIDTH:
                tap_mask |= 1 << (tap - 1)

        # Apply the first shift that happens after seed load
        # Calculate feedback using the seed
        tapped_bits = r_lfsr & tap_mask

        # Count the set bits to determine parity
        xor_result = 0
        for i in range(self.WIDTH):
            if (tapped_bits >> i) & 1:
                xor_result ^= 1

        # XNOR logic - feedback is 1 if even parity (or 0 set bits), otherwise 0
        w_feedback = 1 if xor_result == 0 else 0

        # Shift left and add feedback bit (matches r_lfsr <= {r_lfsr[WIDTH-2:0], w_feedback})
        r_lfsr = ((r_lfsr << 1) | w_feedback) & self.MAX_DATA

        # Run simulation for the requested cycles
        for _ in range(cycles):
            # Add current LFSR value to results
            results.append(r_lfsr)

            # Calculate feedback for next cycle
            tapped_bits = r_lfsr & tap_mask

            # Calculate parity of tapped bits
            xor_result = 0
            for i in range(self.WIDTH):
                if (tapped_bits >> i) & 1:
                    xor_result ^= 1

            # XNOR feedback
            w_feedback = 1 if xor_result == 0 else 0

            # Shift left and add feedback bit
            r_lfsr = ((r_lfsr << 1) | w_feedback) & self.MAX_DATA

        return results

    async def test_basic_operation(self):
        """
        Test basic LFSR operation

        Returns:
            True if all tests passed
        """
        self.log.info("Testing basic LFSR operation")

        # Reset DUT
        await self.reset_dut()

        # Set standard taps for the width
        if self.WIDTH == 8:
            taps = [8, 6, 5, 4]
        elif self.WIDTH == 16:
            taps = [16, 15, 13, 4]
        elif self.WIDTH == 32:
            taps = [32, 22, 2, 1]
        else:
            taps = [self.WIDTH, self.WIDTH//2, 2, 1]

        self.set_taps(taps)

        # Load a seed value
        seed = 0x01  # Common test seed
        await self.load_seed(seed)

        # Generate expected sequence using software model
        num_cycles = 20 if self.TEST_LEVEL == 'gate' else 50
        expected_sequence = self.simulate_xnor_lfsr(seed, taps, num_cycles)

        # Run the LFSR
        result = await self.run_lfsr(num_cycles, True, expected_sequence)

        return result['all_match']

    async def test_seed_loading(self):
        """
        Test seed loading functionality

        Returns:
            True if all tests passed
        """
        self.log.info("Testing seed loading functionality")

        # Reset DUT
        await self.reset_dut()

        # Set standard taps for the width
        self.set_taps([self.WIDTH, self.WIDTH//2, 2, 1])

        # Test different seed values
        seeds = [
            0x01,  # Minimal
            0xAA & self.MAX_DATA,  # Alternating pattern
            0xFF & self.MAX_DATA,  # All ones
            (1 << (self.WIDTH - 1)) & self.MAX_DATA,  # MSB only
        ]

        all_passed = True

        for seed in seeds:
            self.log.info(f"Testing seed: 0x{seed:x}{self.get_time_ns_str()}")

            # Load the seed
            await self.load_seed(seed)

            # Run for a few cycles
            cycles = 5
            expected_sequence = self.simulate_xnor_lfsr(seed, [self.WIDTH, self.WIDTH//2, 2, 1], cycles)
            result = await self.run_lfsr(cycles, True, expected_sequence)

            if not result['all_match']:
                all_passed = False
                if self.TEST_LEVEL == 'gate':
                    break

        return all_passed

    async def test_cycle_detection(self):
        """
        Test LFSR cycle detection

        Returns:
            True if all tests passed
        """
        self.log.info("Testing LFSR cycle detection")

        # Reset DUT
        await self.reset_dut()

        # Set standard taps for the width
        taps = [self.WIDTH, self.WIDTH//2, 2, 1]
        self.set_taps(taps)

        # Use a known seed value
        seed = 0x01
        await self.load_seed(seed)

        # Run for a longer time to see if cycle is detected
        # For full testing, we'd need to run 2^WIDTH-1 cycles,
        # but that's impractical for larger widths
        max_cycles = {
            'gate': 32,
            'func': min(256, 2**self.WIDTH - 1),
            'full': min(1024, 2**self.WIDTH - 1)
        }

        cycles = max_cycles[self.TEST_LEVEL]

        # Run the LFSR
        result = await self.run_lfsr(cycles, False)

        # Check if we've seen any repeated values
        values_seen = set()
        first_repeat = None

        for i, value in enumerate(result['lfsr_values']):
            if value in values_seen:
                first_repeat = i
                break
            values_seen.add(value)

        # Check if we detected the cycle
        if first_repeat is not None:
            cycle_length = first_repeat
            self.log.info(f"First value repeat at cycle {first_repeat} (cycle length: {cycle_length}){self.get_time_ns_str()}")

            # The done bit should have been set by then
            cycle_detected = result['done_detected']

            if not cycle_detected:
                self.log.error("LFSR cycle not detected via done bit")
                return False

            # Compare detected cycle with actual repeat
            if abs(result['done_at_cycle'] - first_repeat) > 1:  # Allow 1 cycle difference for HW/SW sync
                self.log.error(f"Cycle detection mismatch: detected at {result['done_at_cycle']}, " +
                                f"but first repeat at {first_repeat}{self.get_time_ns_str()}")
                return False

            self.log.info(f"Cycle detection test passed{self.get_time_ns_str()}")
        else:
            # We didn't run enough cycles to see a repeat
            self.log.warning(f"No repeats detected in {cycles} cycles{self.get_time_ns_str()}")

        return True

    async def test_different_taps(self):
        """
        Test LFSR with different tap configurations

        Returns:
            True if all tests passed
        """
        if self.TEST_LEVEL == 'gate':
            self.log.info("Skipping tap configuration tests in gate mode")
            return True

        self.log.info("Testing different tap configurations")

        # Define some standard tap configurations for different widths
        tap_configs = {
            4: [[4, 3, 0, 0]],
            8: [[8, 6, 5, 4], [8, 6, 5, 1]],
            16: [[16, 15, 13, 4], [16, 14, 13, 11]],
            32: [[32, 22, 2, 1], [32, 30, 26, 25]]
        }

        # Default to some reasonable taps for other widths
        if self.WIDTH not in tap_configs:
            tap_configs[self.WIDTH] = [[self.WIDTH, self.WIDTH//2, 2, 1]]

        # Select tap configurations based on test level
        if self.TEST_LEVEL == 'func':
            tap_configs[self.WIDTH] = tap_configs[self.WIDTH][:1]  # Use only first config

        all_passed = True

        for taps in tap_configs[self.WIDTH]:
            self.log.info(f"Testing taps: {taps}{self.get_time_ns_str()}")

            # Reset DUT
            await self.reset_dut()

            # Set taps
            self.set_taps(taps)

            # Load a seed
            seed = 0x01
            await self.load_seed(seed)

            # Run for a few cycles
            cycles = 10
            expected_sequence = self.simulate_xnor_lfsr(seed, taps, cycles)
            result = await self.run_lfsr(cycles, True, expected_sequence)

            if not result['all_match']:
                all_passed = False
                if self.TEST_LEVEL == 'func':
                    break

        return all_passed

    async def run_all_tests(self):
        """
        Run all tests according to the test level

        Returns:
            True if all tests passed
        """
        self.log.info(f"Running all tests at level: {self.TEST_LEVEL}{self.get_time_ns_str()}")

        all_passed = True

        # 1. Basic operation test
        self.log.info(f"1. Testing basic LFSR operation{self.get_time_ns_str()}")
        basic_passed = await self.test_basic_operation()
        if not basic_passed:
            self.log.error("Basic operation test failed")
            all_passed = False
            if self.TEST_LEVEL == 'gate':
                return all_passed

        # 2. Seed loading test
        self.log.info(f"2. Testing seed loading functionality{self.get_time_ns_str()}")
        seed_passed = await self.test_seed_loading()
        if not seed_passed:
            self.log.error("Seed loading test failed")
            all_passed = False
            if self.TEST_LEVEL == 'gate':
                return all_passed

        # 3. Cycle detection test
        self.log.info(f"3. Testing cycle detection{self.get_time_ns_str()}")
        cycle_passed = await self.test_cycle_detection()
        if not cycle_passed:
            self.log.error("Cycle detection test failed")
            all_passed = False
            if self.TEST_LEVEL == 'gate':
                return all_passed

        # 4. Different taps test (func and full only)
        if self.TEST_LEVEL != 'gate':
            self.log.info(f"4. Testing different tap configurations{self.get_time_ns_str()}")
            taps_passed = await self.test_different_taps()
            if not taps_passed:
                self.log.error("Tap configuration test failed")
                all_passed = False

        # Print summary
        self.print_summary()

        return all_passed

    def print_summary(self):
        """Print summary of test results"""
        total_tests = len(self.test_results)
        passed_tests = sum(bool(r.get('all_match', True))
                        for r in self.test_results)

        self.log.info("="*50)
        self.log.info(f"Test Summary: {passed_tests}/{total_tests} tests passed")
        self.log.info("="*50)

        # Print detailed results based on test level
        if self.TEST_LEVEL != 'gate' and passed_tests < total_tests:
            self.log.info("Failed tests:")
            for i, result in enumerate(self.test_results):
                if not result.get('all_match', True):
                    self.log.info(f"Test {i+1}:")
                    self.log.info(f"  Cycles: {result['cycles']}")
                    self.log.info(f"  Done detected: {result['done_detected']}")
                    if result['done_detected']:
                        self.log.info(f"  Done at cycle: {result['done_at_cycle']}")
                    # Print the first few mismatches
                    mismatches = []
                    if 'expected_values' in result and len(result['expected_values']) > 0:
                        for j, (actual, expected) in enumerate(zip(result['lfsr_values'], result['expected_values'])):
                            if actual != expected:
                                mismatches.append((j, actual, expected))
                                if len(mismatches) >= 5:  # Limit to first 5 mismatches
                                    break
                    if mismatches:
                        self.log.info("  First mismatches:")
                        for cycle, actual, expected in mismatches:
                            self.log.info(f"    Cycle {cycle}: expected=0x{expected:x}, actual=0x{actual:x}")
