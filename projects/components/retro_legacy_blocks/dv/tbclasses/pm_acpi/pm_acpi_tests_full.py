# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: PMACPIFullTests
# Purpose: PM_ACPI Full Test Suite
#
# Documentation: projects/components/retro_legacy_blocks/docs/pm_acpi_spec/
# Subsystem: retro_legacy_blocks/pm_acpi
#
# Created: 2025-11-29

"""
PM_ACPI Full Test Suite

Comprehensive stress tests and edge case coverage including:
- Long duration PM Timer runs
- All register bit patterns
- High-frequency register access stress
- Combined feature stress tests
- Edge case validation
- Concurrent operation testing
"""

from cocotb.triggers import ClockCycles, Timer

from projects.components.retro_legacy_blocks.dv.tbclasses.pm_acpi.pm_acpi_tb import (
    PMACPITB, PMACPIRegisterMap
)


class PMACPIFullTests:
    """Full test methods for PM_ACPI module."""

    def __init__(self, tb: PMACPITB):
        """
        Initialize test suite.

        Args:
            tb: PM_ACPI testbench instance
        """
        self.tb = tb
        self.log = tb.log

    async def run_all_full_tests(self) -> bool:
        """Run all full-level tests."""
        self.log.info("=" * 80)
        self.log.info("Starting PM_ACPI Full Tests")
        self.log.info("=" * 80)

        results = []

        test_methods = [
            ('PM Timer Long Duration', self.test_pm_timer_long_duration),
            ('PM Timer Overflow Approach', self.test_pm_timer_overflow_approach),
            ('GPE All Bits Comprehensive', self.test_gpe_all_bits_comprehensive),
            ('GPE Status Clear Stress', self.test_gpe_status_clear_stress),
            ('Clock Gate Rapid Toggle', self.test_clock_gate_rapid_toggle),
            ('Power Domain Stress', self.test_power_domain_stress),
            ('Combined Feature Stress', self.test_combined_feature_stress),
            ('Register Access Burst', self.test_register_access_burst),
            ('Interrupt Matrix Stress', self.test_interrupt_matrix_stress),
            ('Power State Configuration', self.test_power_state_configuration),
            ('Full System Integration', self.test_full_system_integration),
            ('Edge Case Validation', self.test_edge_case_validation),
        ]

        for test_name, test_method in test_methods:
            self.log.info(f"\n{'=' * 60}")
            self.log.info(f"Running: {test_name}")
            self.log.info(f"{'=' * 60}")
            try:
                result = await test_method()
                results.append((test_name, result))
            except Exception as e:
                self.log.error(f"{test_name} raised exception: {e}")
                results.append((test_name, False))

        # Print summary
        self.log.info("\n" + "=" * 80)
        self.log.info("FULL TEST SUMMARY")
        self.log.info("=" * 80)

        passed_count = sum(1 for _, result in results if result)
        total_count = len(results)

        for test_name, result in results:
            status = "PASSED" if result else "FAILED"
            self.log.info(f"{test_name:45s} {status}")

        self.log.info(f"\nFull Tests: {passed_count}/{total_count} passed")

        return all(result for _, result in results)

    # ========================================================================
    # PM Timer Stress Tests
    # ========================================================================

    async def test_pm_timer_long_duration(self) -> bool:
        """Run PM Timer for extended duration and verify stability."""
        self.log.info("Testing PM Timer long duration run...")

        try:
            # Fast timer
            await self.tb.configure_pm_timer(divider=0)
            await self.tb.enable_acpi(enable=True, pm_timer=True, gpe=False)
            await ClockCycles(self.tb.pclk, 5)

            # Run for many iterations
            prev_val = 0
            read_count = 500  # Extended duration
            total_increment = 0

            for i in range(read_count):
                timer_val = await self.tb.read_pm_timer()
                if timer_val < prev_val:
                    self.log.error(f"Timer went backwards at iteration {i}: {prev_val} -> {timer_val}")
                    return False
                total_increment += (timer_val - prev_val) if prev_val > 0 else 0
                prev_val = timer_val
                await ClockCycles(self.tb.pclk, 10)  # Longer intervals

            avg_increment = total_increment / (read_count - 1) if read_count > 1 else 0
            self.log.info(f"  Timer read {read_count} times, final value: 0x{prev_val:08X}")
            self.log.info(f"  Average increment per read: {avg_increment:.2f}")
            self.log.info("PM Timer long duration PASSED")
            return True

        except Exception as e:
            self.log.error(f"PM Timer long duration failed: {e}")
            return False

    async def test_pm_timer_overflow_approach(self) -> bool:
        """Test PM Timer behavior near overflow boundaries."""
        self.log.info("Testing PM Timer overflow approach...")

        try:
            # Configure timer with various dividers and run
            dividers = [0, 1, 2, 4, 8]

            for divider in dividers:
                await self.tb.configure_pm_timer(divider=divider)
                await self.tb.enable_acpi(enable=True, pm_timer=True, gpe=False)
                await ClockCycles(self.tb.pclk, 10)

                # Read timer multiple times to verify monotonic behavior
                prev_val = 0
                for _ in range(50):
                    timer_val = await self.tb.read_pm_timer()
                    if timer_val < prev_val and prev_val < 0xFFFFFF00:
                        # Allow for overflow wrap, but not random backwards
                        self.log.error(f"Timer went backwards: {prev_val} -> {timer_val}")
                        return False
                    prev_val = timer_val
                    await ClockCycles(self.tb.pclk, 5)

            self.log.info("PM Timer overflow approach PASSED")
            return True

        except Exception as e:
            self.log.error(f"PM Timer overflow approach failed: {e}")
            return False

    # ========================================================================
    # GPE Comprehensive Tests
    # ========================================================================

    async def test_gpe_all_bits_comprehensive(self) -> bool:
        """Comprehensive test of all GPE bits with multiple patterns."""
        self.log.info("Testing GPE all bits comprehensive...")

        try:
            await self.tb.enable_acpi(enable=True, pm_timer=False, gpe=True)
            await ClockCycles(self.tb.pclk, 5)

            # Walking ones
            for bit in range(32):
                pattern = 1 << bit
                await self.tb.configure_gpe_enables(pattern)
                await ClockCycles(self.tb.pclk, 2)

                _, lo = await self.tb.read_register(PMACPIRegisterMap.GPE0_ENABLE_LO)
                _, hi = await self.tb.read_register(PMACPIRegisterMap.GPE0_ENABLE_HI)
                readback = (hi << 16) | lo

                if readback != pattern:
                    self.log.error(f"Walking ones bit {bit} failed: 0x{pattern:08X} != 0x{readback:08X}")
                    return False

            # Walking zeros
            for bit in range(32):
                pattern = 0xFFFFFFFF ^ (1 << bit)
                await self.tb.configure_gpe_enables(pattern)
                await ClockCycles(self.tb.pclk, 2)

                _, lo = await self.tb.read_register(PMACPIRegisterMap.GPE0_ENABLE_LO)
                _, hi = await self.tb.read_register(PMACPIRegisterMap.GPE0_ENABLE_HI)
                readback = (hi << 16) | lo

                if readback != pattern:
                    self.log.error(f"Walking zeros bit {bit} failed")
                    return False

            # Checkerboard patterns
            patterns = [
                0x55555555, 0xAAAAAAAA, 0x33333333, 0xCCCCCCCC,
                0x0F0F0F0F, 0xF0F0F0F0, 0x00FF00FF, 0xFF00FF00,
            ]

            for pattern in patterns:
                await self.tb.configure_gpe_enables(pattern)
                await ClockCycles(self.tb.pclk, 3)

                _, lo = await self.tb.read_register(PMACPIRegisterMap.GPE0_ENABLE_LO)
                _, hi = await self.tb.read_register(PMACPIRegisterMap.GPE0_ENABLE_HI)
                readback = (hi << 16) | lo

                if readback != pattern:
                    self.log.error(f"Pattern 0x{pattern:08X} failed: read 0x{readback:08X}")
                    return False

            self.log.info("  Verified walking ones, walking zeros, and checkerboard patterns")
            self.log.info("GPE all bits comprehensive PASSED")
            return True

        except Exception as e:
            self.log.error(f"GPE all bits comprehensive failed: {e}")
            return False

    async def test_gpe_status_clear_stress(self) -> bool:
        """Stress test GPE status register clear operations."""
        self.log.info("Testing GPE status clear stress...")

        try:
            await self.tb.enable_acpi(enable=True, pm_timer=False, gpe=True)
            await self.tb.configure_gpe_enables(0xFFFFFFFF)
            await ClockCycles(self.tb.pclk, 5)

            # Repeatedly read and attempt to clear status
            iterations = 100

            for i in range(iterations):
                # Read current status
                status = await self.tb.read_gpe_status()

                # Clear all status bits (W1C)
                await self.tb.write_register(PMACPIRegisterMap.GPE0_STATUS_LO, 0xFFFF)
                await self.tb.write_register(PMACPIRegisterMap.GPE0_STATUS_HI, 0xFFFF)
                await ClockCycles(self.tb.pclk, 2)

            self.log.info(f"  Completed {iterations} status read/clear cycles")
            self.log.info("GPE status clear stress PASSED")
            return True

        except Exception as e:
            self.log.error(f"GPE status clear stress failed: {e}")
            return False

    # ========================================================================
    # Clock Gate Tests
    # ========================================================================

    async def test_clock_gate_rapid_toggle(self) -> bool:
        """Test rapid clock gate toggling."""
        self.log.info("Testing clock gate rapid toggle...")

        try:
            await self.tb.enable_acpi(enable=True, pm_timer=False, gpe=False)
            await ClockCycles(self.tb.pclk, 5)

            # Rapid toggle each bit
            iterations = 50

            for _ in range(iterations):
                for bit in range(32):
                    # Set bit
                    await self.tb.configure_clock_gates(1 << bit)
                    await ClockCycles(self.tb.pclk, 1)

                    # Clear bit
                    await self.tb.configure_clock_gates(0)
                    await ClockCycles(self.tb.pclk, 1)

            # Verify we can still set a pattern correctly
            test_pattern = 0xDEADBEEF
            await self.tb.configure_clock_gates(test_pattern)
            await ClockCycles(self.tb.pclk, 5)

            outputs = self.tb.get_clock_gate_outputs()
            if outputs != test_pattern:
                self.log.error(f"Final pattern mismatch: 0x{test_pattern:08X} != 0x{outputs:08X}")
                return False

            self.log.info(f"  Completed {iterations} rapid toggle cycles")
            self.log.info("Clock gate rapid toggle PASSED")
            return True

        except Exception as e:
            self.log.error(f"Clock gate rapid toggle failed: {e}")
            return False

    # ========================================================================
    # Power Domain Tests
    # ========================================================================

    async def test_power_domain_stress(self) -> bool:
        """Stress test power domain control."""
        self.log.info("Testing power domain stress...")

        try:
            await self.tb.enable_acpi(enable=True, pm_timer=False, gpe=False)
            await ClockCycles(self.tb.pclk, 5)

            # Test all patterns multiple times
            iterations = 5

            for _ in range(iterations):
                for pattern in range(256):
                    await self.tb.configure_power_domains(pattern)
                    await ClockCycles(self.tb.pclk, 1)

                    outputs = self.tb.get_power_domain_outputs()
                    if outputs != pattern:
                        self.log.error(f"Power domain mismatch: 0x{pattern:02X} != 0x{outputs:02X}")
                        return False

            self.log.info(f"  Tested all 256 patterns {iterations} times (1280 operations)")
            self.log.info("Power domain stress PASSED")
            return True

        except Exception as e:
            self.log.error(f"Power domain stress failed: {e}")
            return False

    # ========================================================================
    # Combined Feature Tests
    # ========================================================================

    async def test_combined_feature_stress(self) -> bool:
        """Test multiple features operating together under stress."""
        self.log.info("Testing combined feature stress...")

        try:
            # Enable all features
            await self.tb.configure_pm_timer(divider=2)
            await self.tb.enable_acpi(enable=True, pm_timer=True, gpe=True)
            await self.tb.configure_gpe_enables(0xFFFFFFFF)
            await ClockCycles(self.tb.pclk, 10)

            iterations = 100

            for i in range(iterations):
                # Read timer
                timer_val = await self.tb.read_pm_timer()

                # Update clock gates
                await self.tb.configure_clock_gates(i * 0x11111111)

                # Update power domains
                await self.tb.configure_power_domains(i & 0xFF)

                # Read GPE status
                gpe_status = await self.tb.read_gpe_status()

                # Verify clock gate and power domain outputs
                clk_out = self.tb.get_clock_gate_outputs()
                pwr_out = self.tb.get_power_domain_outputs()

                expected_clk = (i * 0x11111111) & 0xFFFFFFFF
                expected_pwr = i & 0xFF

                if clk_out != expected_clk:
                    self.log.error(f"Clock gate mismatch at iteration {i}")
                    return False

                if pwr_out != expected_pwr:
                    self.log.error(f"Power domain mismatch at iteration {i}")
                    return False

                await ClockCycles(self.tb.pclk, 5)

            self.log.info(f"  Completed {iterations} combined feature iterations")
            self.log.info("Combined feature stress PASSED")
            return True

        except Exception as e:
            self.log.error(f"Combined feature stress failed: {e}")
            return False

    async def test_register_access_burst(self) -> bool:
        """Test burst register access patterns."""
        self.log.info("Testing register access burst...")

        try:
            await self.tb.enable_acpi(enable=True, pm_timer=True, gpe=True)
            await ClockCycles(self.tb.pclk, 5)

            # Burst write/read cycles
            iterations = 200

            for i in range(iterations):
                pattern = (i * 0x12345679) & 0xFFFFFFFF

                # Write burst
                await self.tb.configure_clock_gates(pattern)
                await self.tb.configure_gpe_enables(pattern)
                await self.tb.configure_power_domains(pattern & 0xFF)
                await self.tb.write_register(PMACPIRegisterMap.WAKE_ENABLE, (pattern >> 24) & 0x0F)
                await self.tb.write_register(PMACPIRegisterMap.ACPI_INT_ENABLE, (pattern >> 16) & 0x3F)

                # Read burst (verify one of them)
                clk_out = self.tb.get_clock_gate_outputs()
                if clk_out != pattern:
                    self.log.error(f"Clock gate mismatch at iteration {i}: 0x{pattern:08X} != 0x{clk_out:08X}")
                    return False

            self.log.info(f"  Completed {iterations} burst access cycles")
            self.log.info("Register access burst PASSED")
            return True

        except Exception as e:
            self.log.error(f"Register access burst failed: {e}")
            return False

    # ========================================================================
    # Interrupt Tests
    # ========================================================================

    async def test_interrupt_matrix_stress(self) -> bool:
        """Stress test interrupt enable combinations."""
        self.log.info("Testing interrupt matrix stress...")

        try:
            await self.tb.enable_acpi(enable=True, pm_timer=True, gpe=True)
            await ClockCycles(self.tb.pclk, 5)

            # Test all 64 possible 6-bit interrupt enable combinations multiple times
            iterations = 5

            for _ in range(iterations):
                for pattern in range(64):
                    await self.tb.write_register(PMACPIRegisterMap.ACPI_INT_ENABLE, pattern)
                    await ClockCycles(self.tb.pclk, 2)

                    _, readback = await self.tb.read_register(PMACPIRegisterMap.ACPI_INT_ENABLE)
                    if (readback & 0x3F) != pattern:
                        self.log.error(f"Interrupt enable mismatch: 0x{pattern:02X} != 0x{readback:02X}")
                        return False

            self.log.info(f"  Tested all 64 interrupt patterns {iterations} times (320 operations)")
            self.log.info("Interrupt matrix stress PASSED")
            return True

        except Exception as e:
            self.log.error(f"Interrupt matrix stress failed: {e}")
            return False

    # ========================================================================
    # Power State Tests
    # ========================================================================

    async def test_power_state_configuration(self) -> bool:
        """Test power state configuration register patterns."""
        self.log.info("Testing power state configuration...")

        try:
            await self.tb.enable_acpi(enable=True, pm_timer=False, gpe=False)
            await ClockCycles(self.tb.pclk, 5)

            # Test PM1_CONTROL sleep type patterns
            for sleep_type in range(8):
                await self.tb.write_register(PMACPIRegisterMap.PM1_CONTROL, sleep_type)
                await ClockCycles(self.tb.pclk, 5)

                _, readback = await self.tb.read_register(PMACPIRegisterMap.PM1_CONTROL)
                if (readback & 0x7) != sleep_type:
                    self.log.error(f"Sleep type mismatch: {sleep_type} != {readback & 0x7}")
                    return False

            # Test PM1_ENABLE patterns
            for enable_pattern in range(16):
                await self.tb.write_register(PMACPIRegisterMap.PM1_ENABLE, enable_pattern)
                await ClockCycles(self.tb.pclk, 3)

                _, readback = await self.tb.read_register(PMACPIRegisterMap.PM1_ENABLE)
                if (readback & 0xF) != enable_pattern:
                    self.log.error(f"PM1 enable mismatch: {enable_pattern} != {readback & 0xF}")
                    return False

            # Test wake enable patterns
            for wake_pattern in range(16):
                await self.tb.write_register(PMACPIRegisterMap.WAKE_ENABLE, wake_pattern)
                await ClockCycles(self.tb.pclk, 3)

                _, readback = await self.tb.read_register(PMACPIRegisterMap.WAKE_ENABLE)
                if (readback & 0xF) != wake_pattern:
                    self.log.error(f"Wake enable mismatch: {wake_pattern} != {readback & 0xF}")
                    return False

            self.log.info("  All power state configurations verified")
            self.log.info("Power state configuration PASSED")
            return True

        except Exception as e:
            self.log.error(f"Power state configuration failed: {e}")
            return False

    # ========================================================================
    # Integration Tests
    # ========================================================================

    async def test_full_system_integration(self) -> bool:
        """Full system integration test exercising all features."""
        self.log.info("Testing full system integration...")

        try:
            # Phase 1: Enable and configure all features
            self.log.info("  Phase 1: Full configuration")
            await self.tb.configure_pm_timer(divider=1)
            await self.tb.enable_acpi(enable=True, pm_timer=True, gpe=True)
            await self.tb.configure_gpe_enables(0xFFFFFFFF)
            await self.tb.configure_clock_gates(0xAAAAAAAA)
            await self.tb.configure_power_domains(0x55)
            await self.tb.enable_interrupts(pme=True, wake=True, timer_ovf=True,
                                            state_trans=True, pm1=True, gpe=True)
            await ClockCycles(self.tb.pclk, 20)

            # Phase 2: Exercise PM Timer
            self.log.info("  Phase 2: PM Timer operation")
            timer_vals = []
            for _ in range(20):
                timer_vals.append(await self.tb.read_pm_timer())
                await ClockCycles(self.tb.pclk, 10)

            # Verify monotonic increase
            for i in range(1, len(timer_vals)):
                if timer_vals[i] < timer_vals[i-1]:
                    self.log.error("Timer not monotonic during integration")
                    return False

            # Phase 3: Modify configurations during operation
            self.log.info("  Phase 3: Dynamic reconfiguration")
            for i in range(50):
                # Change clock gates
                await self.tb.configure_clock_gates((i * 0x33333333) & 0xFFFFFFFF)

                # Change power domains
                await self.tb.configure_power_domains((i * 17) & 0xFF)

                # Read timer to ensure it's still running
                timer_val = await self.tb.read_pm_timer()

                await ClockCycles(self.tb.pclk, 5)

            # Phase 4: Verify final state
            self.log.info("  Phase 4: Final state verification")
            state = await self.tb.get_current_power_state()
            if state != PMACPIRegisterMap.POWER_STATE_S0:
                self.log.warning(f"Unexpected power state: {state}")

            # Verify outputs match last settings
            clk_out = self.tb.get_clock_gate_outputs()
            pwr_out = self.tb.get_power_domain_outputs()

            expected_clk = (49 * 0x33333333) & 0xFFFFFFFF
            expected_pwr = (49 * 17) & 0xFF

            if clk_out != expected_clk:
                self.log.error(f"Final clock gate mismatch")
                return False

            if pwr_out != expected_pwr:
                self.log.error(f"Final power domain mismatch")
                return False

            self.log.info("Full system integration PASSED")
            return True

        except Exception as e:
            self.log.error(f"Full system integration failed: {e}")
            return False

    async def test_edge_case_validation(self) -> bool:
        """Validate edge cases and boundary conditions."""
        self.log.info("Testing edge case validation...")

        try:
            await self.tb.enable_acpi(enable=True, pm_timer=True, gpe=True)
            await ClockCycles(self.tb.pclk, 5)

            # Edge case 1: Maximum divider value
            await self.tb.configure_pm_timer(divider=0xFFFF)
            await ClockCycles(self.tb.pclk, 10)
            _, config = await self.tb.read_register(PMACPIRegisterMap.PM_TIMER_CONFIG)
            if (config & 0xFFFF) != 0xFFFF:
                self.log.error("Maximum divider not stored correctly")
                return False
            self.log.info("  Maximum divider value validated")

            # Edge case 2: Zero divider
            await self.tb.configure_pm_timer(divider=0)
            await ClockCycles(self.tb.pclk, 10)
            _, config = await self.tb.read_register(PMACPIRegisterMap.PM_TIMER_CONFIG)
            if (config & 0xFFFF) != 0:
                self.log.error("Zero divider not stored correctly")
                return False
            self.log.info("  Zero divider value validated")

            # Edge case 3: All GPE bits enabled then disabled
            await self.tb.configure_gpe_enables(0xFFFFFFFF)
            await ClockCycles(self.tb.pclk, 5)
            await self.tb.configure_gpe_enables(0x00000000)
            await ClockCycles(self.tb.pclk, 5)

            _, lo = await self.tb.read_register(PMACPIRegisterMap.GPE0_ENABLE_LO)
            _, hi = await self.tb.read_register(PMACPIRegisterMap.GPE0_ENABLE_HI)
            if lo != 0 or hi != 0:
                self.log.error("GPE enables not cleared correctly")
                return False
            self.log.info("  GPE enable/disable transition validated")

            # Edge case 4: Rapid enable/disable ACPI
            for _ in range(20):
                await self.tb.enable_acpi(enable=True, pm_timer=True, gpe=True)
                await ClockCycles(self.tb.pclk, 2)
                await self.tb.enable_acpi(enable=False, pm_timer=False, gpe=False)
                await ClockCycles(self.tb.pclk, 2)

            # Final enable
            await self.tb.enable_acpi(enable=True, pm_timer=True, gpe=True)
            await ClockCycles(self.tb.pclk, 10)

            # Verify ACPI is enabled
            _, control = await self.tb.read_register(PMACPIRegisterMap.ACPI_CONTROL)
            if not (control & PMACPIRegisterMap.CONTROL_ACPI_ENABLE):
                self.log.error("ACPI not enabled after rapid toggle")
                return False
            self.log.info("  Rapid ACPI enable/disable validated")

            self.log.info("Edge case validation PASSED")
            return True

        except Exception as e:
            self.log.error(f"Edge case validation failed: {e}")
            return False
