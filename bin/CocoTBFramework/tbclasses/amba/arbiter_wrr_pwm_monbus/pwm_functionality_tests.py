"""
PWM Functionality Tests

This module contains focused tests for PWM generation, timing accuracy,
duty cycle verification, and PWM-arbiter interaction.
"""

import asyncio
from typing import Dict, Any, List
from cocotb.triggers import RisingEdge, ClockCycles

from .test_helper_classes import (
    RequestPattern
)


class PWMFunctionalityTests:
    """
    Test class focused on PWM functionality and timing
    """

    def __init__(self, components):
        self.components = components
        self.dut = components.dut
        self.log = components.log
        self.params = components.params

        # Simple PWM controller for direct control
        self.pwm_controller = SimplePWMController(self.dut, self.log)

        # Test results tracking
        self.test_results = {
            'total_tests': 0,
            'passed_tests': 0,
            'failed_tests': [],
            'success': False
        }

    async def run_tests(self) -> Dict[str, Any]:
        """Run all PWM functionality tests"""
        self.log.info("Starting PWM Functionality Tests")

        tests = self._get_tests_for_level()

        for test_name, test_func in tests:
            self.test_results['total_tests'] += 1

            try:
                self.log.info(f"Running {test_name}")
                success = await test_func()

                if success:
                    self.test_results['passed_tests'] += 1
                    self.log.info(f"✓ {test_name} PASSED")
                else:
                    self.test_results['failed_tests'].append(test_name)
                    self.log.error(f"✗ {test_name} FAILED")

            except Exception as e:
                self.test_results['failed_tests'].append(test_name)
                self.log.error(f"✗ {test_name} ERROR: {str(e)}")

        self.test_results['success'] = len(self.test_results['failed_tests']) == 0

        self.log.info(f"PWM Functionality Tests Complete: "
                     f"{self.test_results['passed_tests']}/{self.test_results['total_tests']} passed")

        return self.test_results

    def _get_tests_for_level(self) -> List[tuple]:
        """Get tests based on test level"""
        basic_tests = [
            ("test_pwm_basic_operation", self.test_pwm_basic_operation),
            ("test_pwm_duty_cycle_accuracy", self.test_pwm_duty_cycle_accuracy),
        ]

        medium_tests = basic_tests + [
            ("test_pwm_period_variations", self.test_pwm_period_variations),
            ("test_pwm_repeat_functionality", self.test_pwm_repeat_functionality),
            ("test_pwm_arbiter_blocking", self.test_pwm_arbiter_blocking),
        ]

        full_tests = medium_tests + [
            ("test_pwm_duty_cycle_sweep", self.test_pwm_duty_cycle_sweep),
            ("test_pwm_edge_cases", self.test_pwm_edge_cases),
            ("test_pwm_stress_scenarios", self.test_pwm_stress_scenarios),
        ]

        level_map = {
            'basic': basic_tests,
            'medium': medium_tests,
            'full': full_tests
        }

        return level_map[self.params['test_level'].value]

    # ==========================================================================
    # BASIC TESTS
    # ==========================================================================

    async def test_pwm_basic_operation(self) -> bool:
        """Test basic PWM start/stop operation"""
        self.log.debug("Testing basic PWM operation")

        # Test simple PWM cycle
        duty = 4
        period = 8

        success = await self.pwm_controller.run_pwm_cycle(duty, period, repeat_count=1)

        if not success:
            self.log.error("Basic PWM cycle failed to complete")
            return False

        # Verify PWM output went back to 0
        if self.dut.pwm_out.value != 0:
            self.log.error("PWM output did not return to 0 after completion")
            return False

        return True

    async def test_pwm_duty_cycle_accuracy(self) -> bool:
        """Test PWM duty cycle timing accuracy"""
        self.log.debug("Testing PWM duty cycle accuracy")

        duty = 3
        period = 8

        # Start PWM
        await self.pwm_controller.configure_pwm(duty, period, repeat_count=1)
        await self.pwm_controller.start_pwm()

        # Monitor PWM output for one complete period
        high_cycles = 0
        low_cycles = 0
        total_cycles = 0

        for cycle in range(period):
            await RisingEdge(self.dut.clk)
            total_cycles += 1

            if self.dut.pwm_out.value == 1:
                high_cycles += 1
            else:
                low_cycles += 1

        # Wait for completion
        await self.pwm_controller.wait_pwm_complete(timeout_cycles=50)

        # Verify duty cycle accuracy
        expected_high = duty
        expected_low = period - duty

        if high_cycles != expected_high:
            self.log.error(f"PWM high cycles incorrect: expected {expected_high}, got {high_cycles}")
            return False

        if low_cycles != expected_low:
            self.log.error(f"PWM low cycles incorrect: expected {expected_low}, got {low_cycles}")
            return False

        self.log.debug(f"PWM timing verified: {high_cycles} high, {low_cycles} low cycles")
        return True

    # ==========================================================================
    # MEDIUM TESTS
    # ==========================================================================

    async def test_pwm_period_variations(self) -> bool:
        """Test PWM with various period configurations"""
        self.log.debug("Testing PWM period variations")

        periods = [4, 6, 8, 10, 12]
        duty_percent = 50  # 50% duty cycle

        for period in periods:
            duty = max(1, period // 2)  # 50% duty cycle

            self.log.debug(f"Testing period {period} with duty {duty}")

            success = await self.pwm_controller.run_pwm_cycle(duty, period, repeat_count=1)

            if not success:
                self.log.error(f"PWM failed with period {period}")
                return False

        return True

    async def test_pwm_repeat_functionality(self) -> bool:
        """Test PWM repeat count functionality"""
        self.log.debug("Testing PWM repeat functionality")

        duty = 2
        period = 4
        repeat_count = 3

        # Start PWM with repeat
        await self.pwm_controller.configure_pwm(duty, period, repeat_count)
        await self.pwm_controller.start_pwm()

        # Monitor for expected duration
        expected_total_cycles = period * repeat_count
        cycle_count = 0
        pwm_high_count = 0

        for _ in range(expected_total_cycles + 5):  # Add buffer
            await RisingEdge(self.dut.clk)
            cycle_count += 1

            if self.dut.pwm_out.value == 1:
                pwm_high_count += 1

            # Check if completed early
            if self.dut.cfg_sts_pwm_done.value == 1:
                break

        # Verify repeat functionality
        expected_high_cycles = duty * repeat_count

        if abs(pwm_high_count - expected_high_cycles) > 1:  # Allow 1 cycle tolerance
            self.log.error(f"PWM repeat count incorrect: expected ~{expected_high_cycles} high cycles, "
                         f"got {pwm_high_count}")
            return False

        return True

    async def test_pwm_arbiter_blocking(self) -> bool:
        """Test that PWM properly blocks arbiter grants"""
        self.log.debug("Testing PWM arbiter blocking")

        # Set up continuous requests
        self.dut.req.value = (1 << self.params['clients']) - 1  # All clients request

        # Start PWM with significant high time
        duty = 6
        period = 8

        await self.pwm_controller.configure_pwm(duty, period, repeat_count=1)
        await self.pwm_controller.start_pwm()

        # Monitor for grants during PWM high period
        grants_during_high = 0
        grants_during_low = 0

        for cycle in range(period):
            await RisingEdge(self.dut.clk)

            pwm_state = bool(self.dut.pwm_out.value)
            grant_active = bool(self.dut.gnt_valid.value)

            if pwm_state and grant_active:
                grants_during_high += 1
                self.log.warning(f"Grant active during PWM high at cycle {cycle}")

            if not pwm_state and grant_active:
                grants_during_low += 1

        # Wait for PWM completion
        await self.pwm_controller.wait_pwm_complete(timeout_cycles=50)

        # Verify blocking behavior
        if grants_during_high > 0:
            self.log.error(f"Grants occurred during PWM high: {grants_during_high}")
            return False

        if grants_during_low == 0:
            self.log.warning("No grants during PWM low period - may indicate other issues")

        self.log.debug(f"PWM blocking verified: {grants_during_low} grants during low, "
                      f"{grants_during_high} during high")
        return True

    async def test_pwm_with_minimal_monitoring(self) -> bool:
        """Test PWM functionality with minimal monitoring packets"""
        self.log.debug("Testing PWM with minimal monitoring")

        # Disable all monitoring to focus on PWM functionality
        await self.components.disable_all_monitoring_packets()

        # Test basic PWM cycle
        duty = 4
        period = 8
        success = await self.pwm_controller.run_pwm_cycle(duty, period, repeat_count=1)

        if not success:
            self.log.error("PWM cycle failed with monitoring disabled")
            return False

        # Verify no monitoring packets were generated
        packets = self.components.monbus_slave.get_received_packets()
        if len(packets) > 0:
            self.log.error(f"Unexpected {len(packets)} monitoring packets with all monitoring disabled")
            return False

        self.log.debug("PWM functionality verified with monitoring disabled")
        return True

    # ==========================================================================
    # FULL TESTS
    # ==========================================================================

    async def test_pwm_duty_cycle_sweep(self) -> bool:
        """Test comprehensive duty cycle sweep"""
        self.log.debug("Testing PWM duty cycle sweep")

        period = 8
        duty_cycles = list(range(1, period))  # 1 to 7

        results = {}

        for duty in duty_cycles:
            self.log.debug(f"Testing duty cycle {duty}/{period} ({duty/period*100:.1f}%)")

            success = await self.pwm_controller.run_pwm_cycle(duty, period, repeat_count=1)
            results[duty] = success

            if not success:
                self.log.error(f"Duty cycle {duty}/{period} failed")
                return False

        self.log.debug(f"Duty cycle sweep completed: {len(results)} configurations tested")
        return True

    async def test_pwm_edge_cases(self) -> bool:
        """Test PWM edge cases"""
        self.log.debug("Testing PWM edge cases")

        edge_cases = [
            {"duty": 1, "period": 8, "name": "minimum_duty"},
            {"duty": 7, "period": 8, "name": "maximum_duty"},
            {"duty": 1, "period": 2, "name": "minimum_period"},
            {"duty": 8, "period": 8, "name": "100_percent_duty"},
        ]

        for case in edge_cases:
            self.log.debug(f"Testing edge case: {case['name']}")

            success = await self.pwm_controller.run_pwm_cycle(
                case["duty"], case["period"], repeat_count=1
            )

            if not success:
                self.log.error(f"Edge case {case['name']} failed")
                return False

        return True

    async def test_pwm_stress_scenarios(self) -> bool:
        """Test PWM under stress conditions"""
        self.log.debug("Testing PWM stress scenarios")

        # Rapid PWM cycles
        for i in range(5):
            duty = 2 + (i % 3)  # Vary duty: 2, 3, 4, 2, 3
            period = 6 + (i % 2)  # Vary period: 6, 7, 6, 7, 6

            success = await self.pwm_controller.run_pwm_cycle(duty, period, repeat_count=1)

            if not success:
                self.log.error(f"Stress scenario {i+1} failed: duty={duty}, period={period}")
                return False

        # Test with arbiter activity
        self.dut.req.value = (1 << self.params['clients']) - 1

        # Run PWM while arbiter is busy
        success = await self.pwm_controller.run_pwm_cycle(4, 8, repeat_count=2)

        if not success:
            self.log.error("PWM failed under arbiter stress")
            return False

        return True


class SimplePWMController:
    """Simple PWM controller for direct testing"""

    def __init__(self, dut, log):
        self.dut = dut
        self.log = log

    async def configure_pwm(self, duty: int, period: int, repeat_count: int = 1):
        """Configure PWM parameters"""
        self.dut.cfg_pwm_duty.value = duty
        self.dut.cfg_pwm_period.value = period
        self.dut.cfg_pwm_repeat_count.value = repeat_count
        await RisingEdge(self.dut.clk)

    async def start_pwm(self):
        """Start PWM operation"""
        self.dut.cfg_pwm_start.value = 1
        await RisingEdge(self.dut.clk)
        self.dut.cfg_pwm_start.value = 0

    async def wait_pwm_complete(self, timeout_cycles: int = 1000):
        """Wait for PWM completion"""
        for _ in range(timeout_cycles):
            await RisingEdge(self.dut.clk)
            if self.dut.cfg_sts_pwm_done.value == 1:
                return True
        return False

    async def run_pwm_cycle(self, duty: int, period: int, repeat_count: int = 1):
        """Run a complete PWM cycle"""
        await self.configure_pwm(duty, period, repeat_count)
        await self.start_pwm()

        # Wait for expected duration plus buffer
        expected_cycles = period * repeat_count
        await ClockCycles(self.dut.clk, expected_cycles + 10)

        return await self.wait_pwm_complete(timeout_cycles=50)
