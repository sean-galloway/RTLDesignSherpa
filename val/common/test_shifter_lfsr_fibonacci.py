# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: ShifterLFSRFibonacciConfig
# Purpose: Configuration class for Fibonacci LFSR Shifter tests
#
# Documentation: PRD.md
# Subsystem: tests
#
# Author: sean galloway
# Created: 2025-10-18

import os
import sys
import random

import pytest
import cocotb
from cocotb_test.simulator import run


# Add repo root to path for CocoTBFramework imports
repo_root = os.path.abspath(os.path.join(os.path.dirname(__file__), '../..'))
if os.path.join(repo_root, 'bin') not in sys.path:
    sys.path.insert(0, os.path.join(repo_root, 'bin'))

from CocoTBFramework.tbclasses.shared.tbbase import TBBase
from CocoTBFramework.tbclasses.shared.filelist_utils import get_sources_from_filelist
from CocoTBFramework.tbclasses.shared.utilities import get_paths, create_view_cmd


class ShifterLFSRFibonacciConfig:
    """Configuration class for Fibonacci LFSR Shifter tests"""
    def __init__(self, name, width=8, tap_index_width=12, tap_count=4, tap_values=None):
        """
        Initialize the test configuration

        Args:
            name: Configuration name
            width: LFSR width
            tap_index_width: Width of tap indices
            tap_count: Number of taps
            tap_values: List of tap values (if None, default taps will be used)
        """
        self.name = name
        self.width = width
        self.tap_index_width = tap_index_width
        self.tap_count = tap_count

        # Default taps if not provided
        if tap_values is None:
            if width == 8:
                # Build tap values based on tap_count
                if tap_count == 1:
                    self.tap_values = [8]
                elif tap_count == 2:
                    self.tap_values = [8, 6]
                elif tap_count == 3:
                    self.tap_values = [8, 6, 5]
                else:
                    self.tap_values = [8, 6, 5, 4]  # Standard taps for 8-bit LFSR
            elif width == 16:
                # Build tap values based on tap_count
                if tap_count == 1:
                    self.tap_values = [16]
                elif tap_count == 2:
                    self.tap_values = [16, 15]
                elif tap_count == 3:
                    self.tap_values = [16, 15, 13]
                else:
                    self.tap_values = [16, 15, 13, 4]  # Standard taps for 16-bit LFSR
            elif width == 32:
                # Build tap values based on tap_count
                if tap_count == 1:
                    self.tap_values = [32]
                elif tap_count == 2:
                    self.tap_values = [32, 22]
                elif tap_count == 3:
                    self.tap_values = [32, 22, 2]
                else:
                    self.tap_values = [32, 22, 2, 1]  # Standard taps for 32-bit LFSR
            elif width == 64:
                # Build tap values based on tap_count
                if tap_count == 1:
                    self.tap_values = [64]
                elif tap_count == 2:
                    self.tap_values = [64, 63]
                elif tap_count == 3:
                    self.tap_values = [64, 63, 61]
                else:
                    self.tap_values = [64, 63, 61, 60]  # Standard taps for 64-bit LFSR
            elif width == 96:
                # Build tap values based on tap_count
                if tap_count == 1:
                    self.tap_values = [96]
                elif tap_count == 2:
                    self.tap_values = [96, 94]
                elif tap_count == 3:
                    self.tap_values = [96, 94, 49]
                else:
                    self.tap_values = [96, 94, 49, 47]  # Standard taps for 96-bit LFSR
            elif width == 128:
                # Build tap values based on tap_count
                if tap_count == 1:
                    self.tap_values = [128]
                elif tap_count == 2:
                    self.tap_values = [128, 126]
                elif tap_count == 3:
                    self.tap_values = [128, 126, 101]
                else:
                    self.tap_values = [128, 126, 101, 99]  # Standard taps for 128-bit LFSR
            else:
                # For other widths, use some reasonable defaults based on tap_count
                self.tap_values = []
                if tap_count >= 1:
                    self.tap_values.append(width)
                if tap_count >= 2:
                    self.tap_values.append(width//2)
                if tap_count >= 3:
                    self.tap_values.append(2)
                if tap_count >= 4:
                    self.tap_values.append(1)
                # Pad with zeros if needed
                while len(self.tap_values) < tap_count:
                    self.tap_values.append(0)
        else:
            # Use provided tap values, but ensure we have exactly tap_count values
            self.tap_values = tap_values[:tap_count]
            # Pad with zeros if needed
            while len(self.tap_values) < tap_count:
                self.tap_values.append(0)


class ShifterLFSRFibonacciTB(TBBase):
    """
    Testbench for the Fibonacci LFSR Shifter module
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
        self.TEST_LEVEL = os.environ.get('TEST_LEVEL', 'basic')
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
        self.log.info("Fibonacci LFSR Shifter TB initialized")
        self.log.info(f"SEED={self.SEED}")
        self.log.info(f"TEST_LEVEL={self.TEST_LEVEL}")
        self.log.info(f"WIDTH={self.WIDTH}")
        self.log.info(f"TAP_INDEX_WIDTH={self.TAP_INDEX_WIDTH}")
        self.log.info(f"TAP_COUNT={self.TAP_COUNT}")

        # Test results storage
        self.test_results = []

    async def reset_dut(self):
        """Reset the DUT"""
        self.log.debug(f'Starting reset_dut{self.get_time_ns_str()}')

        # Initialize inputs
        self.enable.value = 0
        self.seed_load.value = 0
        self.seed_data.value = 0

        # Set up default taps based on TAP_COUNT
        default_taps = []
        if self.TAP_COUNT >= 1:
            default_taps.append(self.WIDTH)  # First tap is always WIDTH
        if self.TAP_COUNT >= 2:
            default_taps.append(self.WIDTH // 2)  # Second tap is WIDTH/2
        if self.TAP_COUNT >= 3:
            default_taps.append(2)  # Third tap is 2
        if self.TAP_COUNT >= 4:
            default_taps.append(1)  # Fourth tap is 1

        # Pad with zeros if needed
        while len(default_taps) < self.TAP_COUNT:
            default_taps.append(0)

        # Make sure we only use the specified number of taps
        default_taps = default_taps[:self.TAP_COUNT]

        self.set_taps(default_taps)

        # Apply reset
        self.rst_n.value = 0
        await self.wait_clocks('clk', 5)
        self.rst_n.value = 1
        await self.wait_clocks('clk', 10)

        self.log.debug(f'Ending reset_dut{self.get_time_ns_str()}')

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
            tap_value |= (tap & ((1 << self.TAP_INDEX_WIDTH) - 1)) << (i * self.TAP_INDEX_WIDTH)

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
        await self.wait_clocks('clk', 1)

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
            self.log.debug(f"Cycle {i}: LFSR=0x{lfsr_value:x}, Done={done_bit}")

        # Verify sequence if requested
        if verify_sequence and expected_sequence:
            min_len = min(len(result['lfsr_values']), len(expected_sequence))
            for i in range(min_len):
                if result['lfsr_values'][i] != expected_sequence[i]:
                    result['all_match'] = False
                    self.log.error(f"LFSR mismatch at cycle {i}: " +
                                    f"expected=0x{expected_sequence[i]:x}, " +
                                    f"actual=0x{result['lfsr_values'][i]:x}" +
                                    f"{self.get_time_ns_str()}")

            if result['all_match']:
                self.log.info(f"LFSR sequence verified successfully{self.get_time_ns_str()}")

        # Disable the LFSR
        self.enable.value = 0

        # Store result
        self.test_results.append(result)

        return result

    def simulate_xor_lfsr(self, seed, taps, cycles):
        """
        Simulate a Fibonacci LFSR (XOR-based) in software to match hardware behavior
        """
        # Initialize with the seed
        lfsr = seed & self.MAX_DATA
        width = self.WIDTH
        all_results = []

        # Ensure we're using the correct number of taps
        taps = taps[:self.TAP_COUNT]

        # Prepare tap mask with only the non-zero, valid taps
        tap_mask = 0
        for tap in taps:
            if tap > 0 and tap <= width:
                tap_mask |= 1 << (tap - 1)

        # Run simulation for cycles+1 cycles (one extra cycle)
        for _ in range(cycles + 1):
            # Calculate feedback from current LFSR value
            feedback = 0
            tapped_bits = lfsr & tap_mask

            # Calculate XOR of all tapped bits
            for i in range(width):
                if (tapped_bits >> i) & 1:
                    feedback ^= 1

            # Right shift with feedback into MSB
            lfsr = ((lfsr >> 1) | (feedback << (width - 1))) & self.MAX_DATA
            all_results.append(lfsr)

        # Drop the first calculated value to match hardware behavior
        return all_results[1:]

    def get_standard_taps_for_width(self):
        """
        Get standard taps for the current WIDTH and TAP_COUNT
        """
        # Standard taps for different widths, respecting TAP_COUNT
        taps = []

        if self.WIDTH == 8:
            if self.TAP_COUNT >= 1:
                taps.append(8)
            if self.TAP_COUNT >= 2:
                taps.append(6)
            if self.TAP_COUNT >= 3:
                taps.append(5)
            if self.TAP_COUNT >= 4:
                taps.append(4)
        elif self.WIDTH == 16:
            if self.TAP_COUNT >= 1:
                taps.append(16)
            if self.TAP_COUNT >= 2:
                taps.append(15)
            if self.TAP_COUNT >= 3:
                taps.append(13)
            if self.TAP_COUNT >= 4:
                taps.append(4)
        elif self.WIDTH == 32:
            if self.TAP_COUNT >= 1:
                taps.append(32)
            if self.TAP_COUNT >= 2:
                taps.append(22)
            if self.TAP_COUNT >= 3:
                taps.append(2)
            if self.TAP_COUNT >= 4:
                taps.append(1)
        else:
            # For other widths
            if self.TAP_COUNT >= 1:
                taps.append(self.WIDTH)
            if self.TAP_COUNT >= 2:
                taps.append(self.WIDTH // 2)
            if self.TAP_COUNT >= 3:
                taps.append(2)
            if self.TAP_COUNT >= 4:
                taps.append(1)

        # Pad with zeros if needed
        while len(taps) < self.TAP_COUNT:
            taps.append(0)

        # Make sure we only use the specified number of taps
        return taps[:self.TAP_COUNT]

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
        taps = self.get_standard_taps_for_width()
        self.set_taps(taps)

        # Use a seed that interacts with tap positions
        # For TAP_COUNT >= 1, this will always have MSB set
        seed = (1 << (self.WIDTH - 1)) & self.MAX_DATA
        await self.load_seed(seed)

        # Generate expected sequence using software model
        num_cycles = 20 if self.TEST_LEVEL == 'basic' else 50
        expected_sequence = self.simulate_xor_lfsr(seed, taps, num_cycles)

        # Run the LFSR
        result = await self.run_lfsr(num_cycles, True, expected_sequence)

        return result['all_match']

    async def test_seed_loading(self):
        """
        Test seed loading functionality

        Returns:
            True if all tests passed
        """
        self.log.info(f"Testing seed loading functionality{self.get_time_ns_str()}")

        # Reset DUT
        await self.reset_dut()

        # Set standard taps for the width
        taps = self.get_standard_taps_for_width()
        self.set_taps(taps)

        # Test different seed values - ensure they interact with at least one tap
        seeds = [
            (1 << (self.WIDTH - 1)) & self.MAX_DATA,  # MSB only - interacts with highest tap
            0xAA & self.MAX_DATA,  # Alternating pattern
            0xFF & self.MAX_DATA,  # All ones
            ((1 << (self.WIDTH - 1)) | (1 << (self.WIDTH - 4))) & self.MAX_DATA,  # MSB and another tap bit set
        ]

        all_passed = True

        for seed in seeds:
            self.log.info(f"Testing seed: 0x{seed:x}{self.get_time_ns_str()}")

            # Load the seed
            await self.load_seed(seed)

            # Run for a few cycles
            cycles = 5
            expected_sequence = self.simulate_xor_lfsr(seed, taps, cycles)
            result = await self.run_lfsr(cycles, True, expected_sequence)

            if not result['all_match']:
                all_passed = False
                if self.TEST_LEVEL == 'basic':
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
        taps = self.get_standard_taps_for_width()
        self.set_taps(taps)

        # Use a seed that interacts with tap positions
        seed = (1 << (self.WIDTH - 1)) & self.MAX_DATA  # MSB set
        await self.load_seed(seed)

        # Run for a longer time to see if cycle is detected
        # For full testing, we'd need to run 2^WIDTH-1 cycles,
        # but that's impractical for larger widths
        max_cycles = {
            'basic': 32,
            'medium': min(256, 2**self.WIDTH - 1),
            'full': min(1024, 2**self.WIDTH - 1)
        }

        cycles = max_cycles[self.TEST_LEVEL]

        # Run the LFSR
        result = await self.run_lfsr(cycles, False)

        # Check if we've seen any repeated values
        values_seen = set()
        first_repeat = None

        # Check if we've seen the seed value again (excluding the first time)
        seed_reappearances = []
        for i, value in enumerate(result['lfsr_values']):
            if value == seed and i > 0:  # Skip initial detection
                seed_reappearances.append(i)
                break

        # Use the first seed reappearance rather than the first repeat
        first_repeat = seed_reappearances[0] if seed_reappearances else None

        # Check if we detected the cycle
        if first_repeat is not None:
            cycle_length = first_repeat
            self.log.info(f"First value repeat at cycle {first_repeat} (cycle length: {cycle_length})")

            # The done bit should have been set by then
            cycle_detected = result['done_detected']

            if not cycle_detected:
                self.log.error("LFSR cycle not detected via done bit")
                return False

            # Compare detected cycle with actual repeat
            if abs(result['done_at_cycle'] - first_repeat) > 1:  # Allow 1 cycle difference for HW/SW sync
                self.log.error(f"Cycle detection mismatch: detected at {result['done_at_cycle']}, " +
                                f"but first repeat at {first_repeat}" +
                                f"{self.get_time_ns_str()}")
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
        if self.TEST_LEVEL == 'basic':
            self.log.info("Skipping tap configuration tests in basic mode")
            return True

        self.log.info("Testing different tap configurations")

        # Define tap configurations based on WIDTH and TAP_COUNT
        tap_configs = {
            4: {
                2: [[4, 3]],
                4: [[4, 3, 2, 1]]
            },
            8: {
                2: [[8, 6]],
                4: [[8, 6, 5, 4], [8, 6, 5, 1]]
            },
            16: {
                2: [[16, 15]],
                4: [[16, 15, 13, 4], [16, 14, 13, 11]]
            },
            32: {
                2: [[32, 22]],
                4: [[32, 22, 2, 1], [32, 30, 26, 25]]
            }
        }

        # Default to some reasonable taps for other widths based on TAP_COUNT
        if self.WIDTH not in tap_configs or self.TAP_COUNT not in tap_configs.get(self.WIDTH, {}):
            tap_configs[self.WIDTH] = {
                self.TAP_COUNT: [[self.WIDTH] + [max(1, self.WIDTH // (i+1)) for i in range(1, self.TAP_COUNT)]]
            }

        # Select the appropriate configurations for this WIDTH and TAP_COUNT
        configs_for_test = tap_configs.get(self.WIDTH, {}).get(self.TAP_COUNT, [[self.WIDTH, self.WIDTH//2]])

        # Select tap configurations based on test level
        if self.TEST_LEVEL == 'medium':
            configs_for_test = configs_for_test[:1]  # Use only first config

        all_passed = True

        for taps in configs_for_test:
            # Make sure we're using exactly TAP_COUNT taps
            taps = taps[:self.TAP_COUNT]
            if len(taps) < self.TAP_COUNT:
                # Pad with zeros if needed
                taps += [0] * (self.TAP_COUNT - len(taps))

            self.log.info(f"Testing taps: {taps}")

            # Reset DUT
            await self.reset_dut()

            # Set taps
            self.set_taps(taps)

            # Load a seed that interacts with the highest tap
            seed = (1 << (taps[0] - 1)) & self.MAX_DATA
            await self.load_seed(seed)

            # Run for a few cycles
            cycles = 10
            expected_sequence = self.simulate_xor_lfsr(seed, taps, cycles)
            result = await self.run_lfsr(cycles, True, expected_sequence)

            if not result['all_match']:
                all_passed = False
                if self.TEST_LEVEL == 'medium':
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
        self.log.info("1. Testing basic LFSR operation")
        basic_passed = await self.test_basic_operation()
        if not basic_passed:
            self.log.error("Basic operation test failed")
            all_passed = False
            if self.TEST_LEVEL == 'basic':
                return all_passed

        # 2. Seed loading test
        self.log.info("2. Testing seed loading functionality")
        seed_passed = await self.test_seed_loading()
        if not seed_passed:
            self.log.error("Seed loading test failed")
            all_passed = False
            if self.TEST_LEVEL == 'basic':
                return all_passed

        # 3. Cycle detection test
        self.log.info("3. Testing cycle detection")
        cycle_passed = await self.test_cycle_detection()
        if not cycle_passed:
            self.log.error("Cycle detection test failed")
            all_passed = False
            if self.TEST_LEVEL == 'basic':
                return all_passed

        # 4. Different taps test (medium and full only)
        if self.TEST_LEVEL != 'basic':
            self.log.info("4. Testing different tap configurations")
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
        if self.TEST_LEVEL != 'basic' and passed_tests < total_tests:
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


@cocotb.test(timeout_time=5000, timeout_unit="us")
async def comprehensive_test(dut):
    """Run a comprehensive test suite according to the specified test level."""
    # Initialize the testbench
    tb = ShifterLFSRFibonacciTB(dut)

    # Start clock with configured period
    await tb.start_clock('clk', 10, 'ns')

    # Run all tests
    passed = await tb.run_all_tests()

    # Verify test result
    assert passed, f"Comprehensive test failed at level {tb.TEST_LEVEL}"


def generate_test_params():
    """
    Generate test parameters based on REG_LEVEL.

    REG_LEVEL=GATE: 2 tests (8-bit, basic+medium)
    REG_LEVEL=FUNC: 6 tests (8-bit all levels, plus 16, 32, 64-bit) - default
    REG_LEVEL=FULL: 11 tests (all widths including 4, 96, 128-bit + tap configs)

    Returns:
        List of dicts with WIDTH, TAP_INDEX_WIDTH, TAP_COUNT, test_level
    """
    import os
    reg_level = os.environ.get('REG_LEVEL', 'FUNC').upper()

    if reg_level == 'GATE':
        return [
            {'WIDTH': 8, 'TAP_INDEX_WIDTH': 12, 'TAP_COUNT': 4, 'test_level': 'basic'},
            {'WIDTH': 8, 'TAP_INDEX_WIDTH': 12, 'TAP_COUNT': 4, 'test_level': 'medium'},
        ]
    elif reg_level == 'FUNC':
        return [
            {'WIDTH':  8, 'TAP_INDEX_WIDTH': 12, 'TAP_COUNT': 4, 'test_level': 'basic'},
            {'WIDTH':  8, 'TAP_INDEX_WIDTH': 12, 'TAP_COUNT': 4, 'test_level': 'medium'},
            {'WIDTH':  8, 'TAP_INDEX_WIDTH': 12, 'TAP_COUNT': 4, 'test_level': 'full'},
            {'WIDTH': 16, 'TAP_INDEX_WIDTH': 12, 'TAP_COUNT': 4, 'test_level': 'medium'},
            {'WIDTH': 32, 'TAP_INDEX_WIDTH': 12, 'TAP_COUNT': 4, 'test_level': 'medium'},
            {'WIDTH': 64, 'TAP_INDEX_WIDTH': 12, 'TAP_COUNT': 4, 'test_level': 'medium'},
        ]
    else:  # FULL
        return [
            {'WIDTH':  8, 'TAP_INDEX_WIDTH': 12, 'TAP_COUNT': 4, 'test_level': 'basic'},
            {'WIDTH':  8, 'TAP_INDEX_WIDTH': 12, 'TAP_COUNT': 4, 'test_level': 'medium'},
            {'WIDTH':  8, 'TAP_INDEX_WIDTH': 12, 'TAP_COUNT': 4, 'test_level': 'full'},
            {'WIDTH':  4, 'TAP_INDEX_WIDTH': 12, 'TAP_COUNT': 4, 'test_level': 'medium'},
            {'WIDTH': 16, 'TAP_INDEX_WIDTH': 12, 'TAP_COUNT': 4, 'test_level': 'medium'},
            {'WIDTH': 32, 'TAP_INDEX_WIDTH': 12, 'TAP_COUNT': 4, 'test_level': 'medium'},
            {'WIDTH': 64, 'TAP_INDEX_WIDTH': 12, 'TAP_COUNT': 4, 'test_level': 'medium'},
            {'WIDTH': 96, 'TAP_INDEX_WIDTH': 12, 'TAP_COUNT': 4, 'test_level': 'medium'},
            {'WIDTH': 128, 'TAP_INDEX_WIDTH': 12, 'TAP_COUNT': 4, 'test_level': 'medium'},
            # Different tap configurations
            {'WIDTH':  8, 'TAP_INDEX_WIDTH':  8, 'TAP_COUNT': 2, 'test_level': 'medium'},
            {'WIDTH':  8, 'TAP_INDEX_WIDTH': 16, 'TAP_COUNT': 6, 'test_level': 'medium'},
        ]


@pytest.mark.parametrize("params", generate_test_params())
def test_shifter_lfsr_fibonacci(request, params):
    """Run the test with pytest and configurable parameters"""
    # Get all of the directory and module information
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({'rtl_cmn': 'rtl/common', 'rtl_amba_includes': 'rtl/amba/includes'})

    dut_name = "shifter_lfsr_fibonacci"
    toplevel = dut_name

    # Get verilog sources and includes from filelist
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path='rtl/common/filelists/shifter_lfsr_fibonacci.f'
    )

    # Create a human-readable test identifier
    t_width = params['WIDTH']
    t_tiw = params['TAP_INDEX_WIDTH']
    t_tc = params['TAP_COUNT']
    t_name = params['test_level']
    test_name_plus_params = f"test_{dut_name}_W{t_width}_TIW{t_tiw}_TC{t_tc}_{t_name}"

    # Handle pytest-xdist parallel execution
    worker_id = os.environ.get('PYTEST_XDIST_WORKER', '')
    if worker_id:
        test_name_plus_params = f"{test_name_plus_params}_{worker_id}"

    log_path = os.path.join(log_dir, f'{test_name_plus_params}.log')

    # Use it in the simbuild path
    sim_build = os.path.join(tests_dir, 'local_sim_build', test_name_plus_params)

    # Make sim_build directory
    os.makedirs(sim_build, exist_ok=True)

    # Get the logs and results into one area
    os.makedirs(log_dir, exist_ok=True)
    results_path = os.path.join(log_dir, f'results_{test_name_plus_params}.xml')
    # RTL parameters
    parameters = {
        'WIDTH': params['WIDTH'],
        'TAP_INDEX_WIDTH': params['TAP_INDEX_WIDTH'],
        'TAP_COUNT': params['TAP_COUNT']
    }

    # Prepare environment variables
    seed = random.randint(0, 100000)
    extra_env = {
        'TRACE_FILE': f"{sim_build}/dump.vcd",
        'VERILATOR_TRACE': '1',  # Enable tracing
        'DUT': dut_name,
        'LOG_PATH': log_path,
        'COCOTB_LOG_LEVEL': 'INFO',
        'COCOTB_RESULTS_FILE': results_path,
        'SEED': str(0x414347),  # str(seed),
        'TEST_LEVEL': params['test_level'],
        'TEST_WIDTH': str(params['WIDTH']),
        'TEST_TAP_INDEX_WIDTH': str(params['TAP_INDEX_WIDTH']),
        'TEST_TAP_COUNT': str(params['TAP_COUNT'])
    }

    # Calculate timeout based on test complexity
    complexity_factor = 1.0
    # sourcery skip: no-conditionals-in-tests
    if params['test_level'] == 'medium':
        complexity_factor = 2.0
    elif params['test_level'] == 'full':
        complexity_factor = 5.0
    timeout_factor = complexity_factor * 50
    extra_env['COCOTB_TIMEOUT_MULTIPLIER'] = str(timeout_factor)


    # VCD waveform generation support via WAVES environment variable
    # Trace compilation always enabled (minimal overhead)
    # Set WAVES=1 to enable VCD dumping for debugging
    compile_args = [
        "--trace",
        "--trace-structs",
        "--trace-depth", "99",
    ]
    sim_args = [
        "--trace",  # VCD waveform format
        "--trace-structs",
        "--trace-depth", "99",
    ]

    plusargs = [
        "--trace",
    ]

    cmd_filename = create_view_cmd(log_dir, log_path, sim_build, module, test_name_plus_params)

    # Conditionally set COCOTB_TRACE_FILE for VCD generation
    if bool(int(os.environ.get('WAVES', '0'))):
        extra_env['COCOTB_TRACE_FILE'] = os.path.join(sim_build, 'dump.vcd')

    try:
        run(
            python_search=[tests_dir],  # where to search for all the python test files
            verilog_sources=verilog_sources,
            includes=includes,
            toplevel=toplevel,
            module=module,
            parameters=parameters,
            sim_build=sim_build,
            extra_env=extra_env,
            waves=False,  # VCD controlled by compile_args, not cocotb-test
            keep_files=True,
            compile_args=compile_args,
            sim_args=sim_args,
            plusargs=plusargs,
        )
    except Exception as e:
        # If the test fails, make sure logs are preserved
        print(f"Test failed: {str(e)}")
        print(f"Logs preserved at: {log_path}")
        print(f"To view the Waveforms run this command: {cmd_filename}")
        raise  # Re-raise exception to indicate failure
