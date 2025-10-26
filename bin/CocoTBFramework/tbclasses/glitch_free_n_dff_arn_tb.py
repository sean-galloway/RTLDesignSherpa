# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: GlitchFreeNDffArnTB
# Purpose: Testbench for glitch_free_n_dff_arn module
#
# Documentation: bin/CocoTBFramework/README.md
# Subsystem: framework
#
# Author: sean galloway
# Created: 2025-10-18

"""
Testbench for glitch_free_n_dff_arn module

The glitch_free_n_dff_arn implements a parameterized N-stage synchronizer for
safe clock domain crossing (CDC). It uses multiple flip-flops in series to
reduce the probability of metastability propagation.

Key Features Tested:
- Synchronization delay matches FLOP_COUNT parameter
- Data propagation through all stages
- Reset behavior
- Multiple data widths (1, 4, 8, 16, 32 bits)
- Multiple stage counts (2, 3, 4, 5 stages)

Author: RTL Design Sherpa Project
"""

import cocotb
from cocotb.triggers import RisingEdge, Timer
from CocoTBFramework.tbclasses.shared.tbbase import TBBase
import os
import random


class GlitchFreeNDffArnTB(TBBase):
    """Testbench for glitch_free_n_dff_arn synchronizer"""

    def __init__(self, dut):
        super().__init__(dut)

        # Get parameters from environment
        self.FLOP_COUNT = self.convert_to_int(os.environ.get('PARAM_FLOP_COUNT', '3'))
        self.WIDTH = self.convert_to_int(os.environ.get('PARAM_WIDTH', '4'))

        self.log.info(f"Glitch-Free N-DFF TB initialized: FLOP_COUNT={self.FLOP_COUNT}, WIDTH={self.WIDTH}")

    async def setup_clocks_and_reset(self):
        """Setup clocks and reset"""
        await self.start_clock('clk', freq=10, units='ns')

        # Initialize inputs
        self.dut.d.value = 0

        # Reset sequence
        await self.assert_reset()
        await self.wait_clocks('clk', 5)
        await self.deassert_reset()
        await self.wait_clocks('clk', 3)

    async def assert_reset(self):
        """Assert reset signal"""
        self.dut.rst_n.value = 0

    async def deassert_reset(self):
        """Deassert reset signal"""
        self.dut.rst_n.value = 1

    async def test_propagation_delay(self):
        """Test that data takes exactly FLOP_COUNT cycles to propagate"""
        self.log.info("=== Test: Propagation Delay ===")

        all_passed = True
        test_values = [
            0x1 & ((1 << self.WIDTH) - 1),  # Simple non-zero pattern
            (1 << self.WIDTH) - 1,  # All ones
            0xA & ((1 << self.WIDTH) - 1),  # Alternating pattern
            random.randint(1, (1 << self.WIDTH) - 1)  # Random non-zero
        ]

        for test_val in test_values:
            # Clear synchronizer first with known value (0)
            self.dut.d.value = 0
            await self.wait_clocks('clk', self.FLOP_COUNT + 2)

            # Drive test value and wait for it to be sampled on next rising edge
            self.dut.d.value = test_val
            await RisingEdge(self.dut.clk)  # Value sampled into r_q_array[0]

            # Wait FLOP_COUNT-1 more clock edges for propagation through pipeline
            for _ in range(self.FLOP_COUNT - 1):
                await RisingEdge(self.dut.clk)

            # Now check output immediately (combinational from r_q_array[FLOP_COUNT-1])
            await Timer(1, units='ns')  # Small delay for combinational output
            final_output = int(self.dut.q.value)
            if final_output != test_val:
                self.log.error(f"  FAIL: Expected 0x{test_val:X}, got 0x{final_output:X} after {self.FLOP_COUNT} cycles")
                all_passed = False
            else:
                self.log.debug(f"  PASS: 0x{test_val:X} propagated in {self.FLOP_COUNT} cycles")

        if all_passed:
            self.log.info(f"✓ Propagation delay test passed ({self.FLOP_COUNT} cycles)")

        return all_passed

    async def test_continuous_data(self):
        """Test continuous changing data stream"""
        self.log.info("=== Test: Continuous Data Stream ===")

        all_passed = True
        num_values = self.FLOP_COUNT + 10  # Send enough values to fill pipeline + extras
        values_sent = []

        # Send stream of random values
        for _ in range(num_values):
            val = random.randint(0, (1 << self.WIDTH) - 1)
            values_sent.append(val)
            self.dut.d.value = val
            await RisingEdge(self.dut.clk)

        # Wait for last value to propagate through pipeline (FLOP_COUNT-1 more edges)
        for _ in range(self.FLOP_COUNT - 1):
            await RisingEdge(self.dut.clk)

        # Check output immediately
        await Timer(1, units='ns')
        final_output = int(self.dut.q.value)
        # The output should show the last value sent (values_sent[-1])
        # because we waited FLOP_COUNT cycles total from when it was sampled
        expected_val = values_sent[-1]

        if final_output != expected_val:
            self.log.error(f"  FAIL: Expected 0x{expected_val:X} (sent {self.FLOP_COUNT} cycles ago), got 0x{final_output:X}")
            all_passed = False
        else:
            self.log.debug(f"  PASS: Continuous stream handled correctly (output=0x{final_output:X})")

        if all_passed:
            self.log.info("✓ Continuous data test passed")

        return all_passed

    async def test_reset_behavior(self):
        """Test reset clears all stages"""
        self.log.info("=== Test: Reset Behavior ===")

        all_passed = True

        # Load synchronizer with non-zero data
        test_val = (1 << self.WIDTH) - 1  # All ones
        self.dut.d.value = test_val
        await self.wait_clocks('clk', self.FLOP_COUNT + 2)

        # Verify data propagated
        if int(self.dut.q.value) != test_val:
            self.log.error("  FAIL: Test setup - data didn't propagate")
            return False

        # Assert reset
        await self.assert_reset()
        await RisingEdge(self.dut.clk)

        # Allow time for combinational output to settle
        await Timer(1, units='ns')

        # Output should be zero immediately after reset
        reset_output = int(self.dut.q.value)
        if reset_output != 0:
            self.log.error(f"  FAIL: Output should be 0 after reset, got 0x{reset_output:X}")
            all_passed = False
        else:
            self.log.debug(f"  PASS: Reset cleared output to 0")

        # Deassert reset
        await self.deassert_reset()
        await self.wait_clocks('clk', 2)

        if all_passed:
            self.log.info("✓ Reset behavior test passed")

        return all_passed

    async def test_all_bit_patterns(self):
        """Test all possible bit patterns (small widths only)"""
        if self.WIDTH > 8:
            self.log.info("=== Test: All Bit Patterns (skipped for WIDTH > 8) ===")
            return True

        self.log.info(f"=== Test: All {2**self.WIDTH} Bit Patterns ===")

        all_passed = True
        for pattern in range(2**self.WIDTH):
            # Drive pattern
            self.dut.d.value = pattern
            await RisingEdge(self.dut.clk)

            # Wait for propagation
            await self.wait_clocks('clk', self.FLOP_COUNT)

            # Check output
            output = int(self.dut.q.value)
            if output != pattern:
                self.log.error(f"  FAIL: Pattern 0x{pattern:X} → 0x{output:X}")
                all_passed = False

        if all_passed:
            self.log.info(f"✓ All {2**self.WIDTH} patterns passed")

        return all_passed

    async def test_data_stability(self):
        """Test that stable input produces stable output"""
        self.log.info("=== Test: Data Stability ===")

        all_passed = True
        test_val = random.randint(0, (1 << self.WIDTH) - 1)

        # Drive stable value
        self.dut.d.value = test_val
        await self.wait_clocks('clk', self.FLOP_COUNT + 5)

        # Output should remain stable
        for _ in range(10):
            await RisingEdge(self.dut.clk)
            output = int(self.dut.q.value)
            if output != test_val:
                self.log.error(f"  FAIL: Output changed unexpectedly to 0x{output:X}")
                all_passed = False
                break

        if all_passed:
            self.log.debug(f"  PASS: Output stable at 0x{test_val:X}")
            self.log.info("✓ Data stability test passed")

        return all_passed

    async def run_all_tests(self):
        """Run all test scenarios"""
        results = []

        # Test 1: Propagation delay
        passed = await self.test_propagation_delay()
        results.append(("Propagation Delay", passed))

        # Test 2: Continuous data stream
        passed = await self.test_continuous_data()
        results.append(("Continuous Data Stream", passed))

        # Test 3: Reset behavior
        passed = await self.test_reset_behavior()
        results.append(("Reset Behavior", passed))

        # Test 4: All bit patterns (small widths)
        passed = await self.test_all_bit_patterns()
        results.append(("All Bit Patterns", passed))

        # Test 5: Data stability
        passed = await self.test_data_stability()
        results.append(("Data Stability", passed))

        # Summary
        self.log.info("=" * 60)
        self.log.info("Test Summary:")
        for name, passed in results:
            status = "✓ PASSED" if passed else "✗ FAILED"
            self.log.info(f"  {name}: {status}")
        self.log.info("=" * 60)

        return all(result[1] for result in results)
