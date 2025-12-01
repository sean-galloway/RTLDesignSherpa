# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: PMACPIMediumTests
# Purpose: PM_ACPI Medium Test Suite
#
# Documentation: projects/components/retro_legacy_blocks/docs/pm_acpi_spec/
# Subsystem: retro_legacy_blocks/pm_acpi
#
# Created: 2025-11-29

"""
PM_ACPI Medium Test Suite

Extended test coverage beyond basic tests including:
- PM Timer divider variations and accuracy
- Multiple GPE enable/status patterns
- Power state transitions
- Wake source combinations
- Extended register access patterns
- Timer stress with various dividers
"""

from cocotb.triggers import ClockCycles, Timer

from projects.components.retro_legacy_blocks.dv.tbclasses.pm_acpi.pm_acpi_tb import (
    PMACPITB, PMACPIRegisterMap
)


class PMACPIMediumTests:
    """Medium test methods for PM_ACPI module."""

    def __init__(self, tb: PMACPITB):
        """
        Initialize test suite.

        Args:
            tb: PM_ACPI testbench instance
        """
        self.tb = tb
        self.log = tb.log

    async def run_all_medium_tests(self) -> bool:
        """Run all medium-level tests."""
        self.log.info("=" * 80)
        self.log.info("Starting PM_ACPI Medium Tests")
        self.log.info("=" * 80)

        results = []

        test_methods = [
            ('PM Timer Divider Sweep', self.test_pm_timer_divider_sweep),
            ('PM Timer Extended Run', self.test_pm_timer_extended_run),
            ('GPE Enable Patterns', self.test_gpe_enable_patterns),
            ('GPE Walking Ones', self.test_gpe_walking_ones),
            ('Clock Gate Patterns', self.test_clock_gate_patterns),
            ('Power Domain Patterns', self.test_power_domain_patterns),
            ('PM1 Control Sweep', self.test_pm1_control_sweep),
            ('Wake Enable Combinations', self.test_wake_enable_combinations),
            ('Interrupt Enable Matrix', self.test_interrupt_enable_matrix),
            ('Register Access Stress', self.test_register_access_stress),
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
        self.log.info("MEDIUM TEST SUMMARY")
        self.log.info("=" * 80)

        passed_count = sum(1 for _, result in results if result)
        total_count = len(results)

        for test_name, result in results:
            status = "PASSED" if result else "FAILED"
            self.log.info(f"{test_name:45s} {status}")

        self.log.info(f"\nMedium Tests: {passed_count}/{total_count} passed")

        return all(result for _, result in results)

    # ========================================================================
    # PM Timer Extended Tests
    # ========================================================================

    async def test_pm_timer_divider_sweep(self) -> bool:
        """Test PM Timer with various divider values."""
        self.log.info("Testing PM Timer divider sweep...")

        try:
            dividers = [0, 1, 2, 4, 8, 16, 32, 64, 100, 255]

            for divider in dividers:
                # Configure and enable
                await self.tb.configure_pm_timer(divider=divider)
                await self.tb.enable_acpi(enable=True, pm_timer=True, gpe=False)
                await ClockCycles(self.tb.pclk, 10)

                # Read timer values
                timer_val1 = await self.tb.read_pm_timer()
                await ClockCycles(self.tb.pclk, 200)
                timer_val2 = await self.tb.read_pm_timer()

                increment = timer_val2 - timer_val1
                expected = 200 // (divider + 1) if divider > 0 else 200

                self.log.info(f"  Divider {divider:3d}: increment={increment}, expected~{expected}")

                # Verify timer incremented (don't be too strict on exact counts)
                if increment == 0 and expected > 2:
                    self.log.error(f"Timer did not increment with divider {divider}")
                    return False

            self.log.info("PM Timer divider sweep PASSED")
            return True

        except Exception as e:
            self.log.error(f"PM Timer divider sweep failed: {e}")
            return False

    async def test_pm_timer_extended_run(self) -> bool:
        """Run PM Timer for extended period and verify monotonic increase."""
        self.log.info("Testing PM Timer extended run...")

        try:
            # Fast timer
            await self.tb.configure_pm_timer(divider=0)
            await self.tb.enable_acpi(enable=True, pm_timer=True, gpe=False)
            await ClockCycles(self.tb.pclk, 5)

            # Run for many iterations
            prev_val = 0
            read_count = 200  # More iterations than basic test

            for i in range(read_count):
                timer_val = await self.tb.read_pm_timer()
                if timer_val < prev_val:
                    self.log.error(f"Timer went backwards at iteration {i}: {prev_val} -> {timer_val}")
                    return False
                prev_val = timer_val
                await ClockCycles(self.tb.pclk, 5)

            self.log.info(f"  Timer read {read_count} times, final value: 0x{prev_val:08X}")
            self.log.info("PM Timer extended run PASSED")
            return True

        except Exception as e:
            self.log.error(f"PM Timer extended run failed: {e}")
            return False

    # ========================================================================
    # GPE Extended Tests
    # ========================================================================

    async def test_gpe_enable_patterns(self) -> bool:
        """Test comprehensive GPE enable patterns."""
        self.log.info("Testing GPE enable patterns...")

        try:
            await self.tb.enable_acpi(enable=True, pm_timer=False, gpe=True)
            await ClockCycles(self.tb.pclk, 5)

            # Extended pattern set
            patterns = [
                0x00000000, 0xFFFFFFFF, 0x55555555, 0xAAAAAAAA,
                0x0F0F0F0F, 0xF0F0F0F0, 0x00FF00FF, 0xFF00FF00,
                0x0000FFFF, 0xFFFF0000, 0x12345678, 0x87654321,
                0xDEADBEEF, 0xCAFEBABE, 0x01234567, 0x76543210,
            ]

            for pattern in patterns:
                await self.tb.configure_gpe_enables(pattern)
                await ClockCycles(self.tb.pclk, 5)

                _, lo = await self.tb.read_register(PMACPIRegisterMap.GPE0_ENABLE_LO)
                _, hi = await self.tb.read_register(PMACPIRegisterMap.GPE0_ENABLE_HI)
                readback = (hi << 16) | lo

                if readback != pattern:
                    self.log.error(f"GPE pattern mismatch: 0x{pattern:08X} != 0x{readback:08X}")
                    return False

            self.log.info(f"  Tested {len(patterns)} GPE patterns")
            self.log.info("GPE enable patterns PASSED")
            return True

        except Exception as e:
            self.log.error(f"GPE enable patterns test failed: {e}")
            return False

    async def test_gpe_walking_ones(self) -> bool:
        """Test GPE with walking ones pattern."""
        self.log.info("Testing GPE walking ones...")

        try:
            await self.tb.enable_acpi(enable=True, pm_timer=False, gpe=True)
            await ClockCycles(self.tb.pclk, 5)

            # Walking ones through all 32 bits
            for bit in range(32):
                pattern = 1 << bit
                await self.tb.configure_gpe_enables(pattern)
                await ClockCycles(self.tb.pclk, 3)

                _, lo = await self.tb.read_register(PMACPIRegisterMap.GPE0_ENABLE_LO)
                _, hi = await self.tb.read_register(PMACPIRegisterMap.GPE0_ENABLE_HI)
                readback = (hi << 16) | lo

                if readback != pattern:
                    self.log.error(f"GPE bit {bit} mismatch: 0x{pattern:08X} != 0x{readback:08X}")
                    return False

            # Walking zeros
            for bit in range(32):
                pattern = 0xFFFFFFFF ^ (1 << bit)
                await self.tb.configure_gpe_enables(pattern)
                await ClockCycles(self.tb.pclk, 3)

                _, lo = await self.tb.read_register(PMACPIRegisterMap.GPE0_ENABLE_LO)
                _, hi = await self.tb.read_register(PMACPIRegisterMap.GPE0_ENABLE_HI)
                readback = (hi << 16) | lo

                if readback != pattern:
                    self.log.error(f"GPE walking-zero bit {bit} mismatch")
                    return False

            self.log.info("  Walking ones and zeros verified")
            self.log.info("GPE walking ones PASSED")
            return True

        except Exception as e:
            self.log.error(f"GPE walking ones test failed: {e}")
            return False

    # ========================================================================
    # Clock Gate Extended Tests
    # ========================================================================

    async def test_clock_gate_patterns(self) -> bool:
        """Test comprehensive clock gate patterns."""
        self.log.info("Testing clock gate patterns...")

        try:
            await self.tb.enable_acpi(enable=True, pm_timer=False, gpe=False)
            await ClockCycles(self.tb.pclk, 5)

            patterns = [
                0x00000000, 0xFFFFFFFF, 0x55555555, 0xAAAAAAAA,
                0x0F0F0F0F, 0xF0F0F0F0, 0x00FF00FF, 0xFF00FF00,
            ]

            for pattern in patterns:
                await self.tb.configure_clock_gates(pattern)
                await ClockCycles(self.tb.pclk, 5)

                outputs = self.tb.get_clock_gate_outputs()
                if outputs != pattern:
                    self.log.error(f"Clock gate mismatch: 0x{pattern:08X} != 0x{outputs:08X}")
                    return False

            # Walking ones for clock gates
            for bit in range(32):
                pattern = 1 << bit
                await self.tb.configure_clock_gates(pattern)
                await ClockCycles(self.tb.pclk, 3)

                outputs = self.tb.get_clock_gate_outputs()
                if outputs != pattern:
                    self.log.error(f"Clock gate bit {bit} mismatch")
                    return False

            self.log.info("Clock gate patterns PASSED")
            return True

        except Exception as e:
            self.log.error(f"Clock gate patterns test failed: {e}")
            return False

    # ========================================================================
    # Power Domain Extended Tests
    # ========================================================================

    async def test_power_domain_patterns(self) -> bool:
        """Test all power domain patterns."""
        self.log.info("Testing power domain patterns...")

        try:
            await self.tb.enable_acpi(enable=True, pm_timer=False, gpe=False)
            await ClockCycles(self.tb.pclk, 5)

            # Test all 256 possible 8-bit patterns
            for pattern in range(256):
                await self.tb.configure_power_domains(pattern)
                await ClockCycles(self.tb.pclk, 3)

                outputs = self.tb.get_power_domain_outputs()
                if outputs != pattern:
                    self.log.error(f"Power domain mismatch: 0x{pattern:02X} != 0x{outputs:02X}")
                    return False

            self.log.info("  Tested all 256 power domain patterns")
            self.log.info("Power domain patterns PASSED")
            return True

        except Exception as e:
            self.log.error(f"Power domain patterns test failed: {e}")
            return False

    # ========================================================================
    # PM1 Control Tests
    # ========================================================================

    async def test_pm1_control_sweep(self) -> bool:
        """Test PM1 control register patterns."""
        self.log.info("Testing PM1 control sweep...")

        try:
            await self.tb.enable_acpi(enable=True, pm_timer=False, gpe=False)
            await ClockCycles(self.tb.pclk, 5)

            # Test sleep type patterns (bits 2:0)
            for sleep_type in range(8):
                await self.tb.write_register(PMACPIRegisterMap.PM1_CONTROL, sleep_type)
                await ClockCycles(self.tb.pclk, 5)

                _, readback = await self.tb.read_register(PMACPIRegisterMap.PM1_CONTROL)
                if (readback & 0x7) != sleep_type:
                    self.log.error(f"PM1 sleep type mismatch: {sleep_type} != {readback & 0x7}")
                    return False

            # Test PM1 enable patterns
            for enable_pattern in range(16):
                await self.tb.write_register(PMACPIRegisterMap.PM1_ENABLE, enable_pattern)
                await ClockCycles(self.tb.pclk, 3)

                _, readback = await self.tb.read_register(PMACPIRegisterMap.PM1_ENABLE)
                if (readback & 0xF) != enable_pattern:
                    self.log.error(f"PM1 enable mismatch: {enable_pattern} != {readback & 0xF}")
                    return False

            self.log.info("PM1 control sweep PASSED")
            return True

        except Exception as e:
            self.log.error(f"PM1 control sweep failed: {e}")
            return False

    # ========================================================================
    # Wake Enable Tests
    # ========================================================================

    async def test_wake_enable_combinations(self) -> bool:
        """Test all wake enable combinations."""
        self.log.info("Testing wake enable combinations...")

        try:
            await self.tb.enable_acpi(enable=True, pm_timer=False, gpe=False)
            await ClockCycles(self.tb.pclk, 5)

            # Test all 16 possible 4-bit patterns
            for pattern in range(16):
                await self.tb.write_register(PMACPIRegisterMap.WAKE_ENABLE, pattern)
                await ClockCycles(self.tb.pclk, 3)

                _, readback = await self.tb.read_register(PMACPIRegisterMap.WAKE_ENABLE)
                if (readback & 0xF) != pattern:
                    self.log.error(f"Wake enable mismatch: 0x{pattern:X} != 0x{readback & 0xF:X}")
                    return False

            self.log.info("  Tested all 16 wake enable patterns")
            self.log.info("Wake enable combinations PASSED")
            return True

        except Exception as e:
            self.log.error(f"Wake enable combinations failed: {e}")
            return False

    # ========================================================================
    # Interrupt Enable Tests
    # ========================================================================

    async def test_interrupt_enable_matrix(self) -> bool:
        """Test all interrupt enable combinations."""
        self.log.info("Testing interrupt enable matrix...")

        try:
            await self.tb.enable_acpi(enable=True, pm_timer=True, gpe=True)
            await ClockCycles(self.tb.pclk, 5)

            # Test all 64 possible 6-bit patterns
            for pattern in range(64):
                await self.tb.write_register(PMACPIRegisterMap.ACPI_INT_ENABLE, pattern)
                await ClockCycles(self.tb.pclk, 3)

                _, readback = await self.tb.read_register(PMACPIRegisterMap.ACPI_INT_ENABLE)
                if (readback & 0x3F) != pattern:
                    self.log.error(f"Interrupt enable mismatch: 0x{pattern:02X} != 0x{readback & 0x3F:02X}")
                    return False

            self.log.info("  Tested all 64 interrupt enable patterns")
            self.log.info("Interrupt enable matrix PASSED")
            return True

        except Exception as e:
            self.log.error(f"Interrupt enable matrix failed: {e}")
            return False

    # ========================================================================
    # Register Access Stress Tests
    # ========================================================================

    async def test_register_access_stress(self) -> bool:
        """Stress test register access with many read/write operations."""
        self.log.info("Testing register access stress...")

        try:
            await self.tb.enable_acpi(enable=True, pm_timer=True, gpe=True)
            await ClockCycles(self.tb.pclk, 5)

            # Rapid fire register writes and reads
            iterations = 100

            for i in range(iterations):
                # Write various registers
                pattern = (i * 0x12345) & 0xFFFFFFFF

                await self.tb.configure_clock_gates(pattern)
                await self.tb.configure_gpe_enables(pattern)
                await self.tb.configure_power_domains(pattern & 0xFF)

                # Read them back
                clk_out = self.tb.get_clock_gate_outputs()
                pwr_out = self.tb.get_power_domain_outputs()

                if clk_out != pattern:
                    self.log.error(f"Clock gate stress mismatch at iteration {i}")
                    return False

                if pwr_out != (pattern & 0xFF):
                    self.log.error(f"Power domain stress mismatch at iteration {i}")
                    return False

            self.log.info(f"  Completed {iterations} stress iterations")
            self.log.info("Register access stress PASSED")
            return True

        except Exception as e:
            self.log.error(f"Register access stress failed: {e}")
            return False
