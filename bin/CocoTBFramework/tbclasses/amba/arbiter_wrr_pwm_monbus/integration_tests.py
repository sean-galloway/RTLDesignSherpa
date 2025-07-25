"""
Integration Tests

This module contains focused tests for component integration, system-level scenarios,
and comprehensive end-to-end validation of the combined Arbiter+PWM+MonBus system.
"""

import asyncio
from typing import Dict, Any, List
from cocotb.triggers import RisingEdge, ClockCycles

from .test_helper_classes import (
    RequestPattern, get_standard_test_scenarios, TestScenario
)
from CocoTBFramework.tbclasses.monbus import (
    ProtocolType, PktType, AXIErrorCode, AXIThresholdCode, AXIPerformanceCode,
    analyze_fairness, analyze_timing_patterns
)


class IntegrationTests:
    """
    Test class focused on system integration and end-to-end scenarios
    """

    def __init__(self, components):
        self.components = components
        self.dut = components.dut
        self.log = components.log
        self.params = components.params

        # Integration-specific PWM controller
        self.pwm_controller = IntegrationPWMController(self.dut, self.log)

        # Test results tracking
        self.test_results = {
            'total_tests': 0,
            'passed_tests': 0,
            'failed_tests': [],
            'success': False
        }

    async def run_tests(self) -> Dict[str, Any]:
        """Run all integration tests"""
        self.log.info("Starting Integration Tests")

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

        self.log.info(f"Integration Tests Complete: "
                     f"{self.test_results['passed_tests']}/{self.test_results['total_tests']} passed")

        return self.test_results

    def _get_tests_for_level(self) -> List[tuple]:
        """Get tests based on test level"""
        basic_tests = [
            ("test_arbiter_pwm_basic_integration", self.test_arbiter_pwm_basic_integration),
            ("test_monbus_arbiter_integration", self.test_monbus_arbiter_integration),
        ]

        medium_tests = basic_tests + [
            ("test_pwm_monbus_integration", self.test_pwm_monbus_integration),
            ("test_full_system_scenarios", self.test_full_system_scenarios),
            ("test_stress_integration", self.test_stress_integration),
        ]

        full_tests = medium_tests + [
            ("test_comprehensive_system_validation", self.test_comprehensive_system_validation),
            ("test_scenario_runner_integration", self.test_scenario_runner_integration),
            ("test_end_to_end_monitoring", self.test_end_to_end_monitoring),
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

    async def test_arbiter_pwm_basic_integration(self) -> bool:
        """Test basic integration between arbiter and PWM"""
        self.log.debug("Testing arbiter-PWM basic integration")

        # Start with all clients requesting
        self.dut.req.value = (1 << self.params['clients']) - 1

        # Configure and start PWM
        duty = 4
        period = 8
        await self.pwm_controller.configure_pwm(duty, period, repeat_count=1)
        await self.pwm_controller.start_pwm()

        # Monitor the interaction
        grants_during_high = 0
        grants_during_low = 0
        pwm_high_cycles = 0
        pwm_low_cycles = 0

        for cycle in range(period + 5):  # Monitor complete period + buffer
            await RisingEdge(self.dut.clk)

            pwm_state = bool(self.dut.pwm_out.value)
            grant_active = bool(self.dut.gnt_valid.value)

            if pwm_state:
                pwm_high_cycles += 1
                if grant_active:
                    grants_during_high += 1
            else:
                pwm_low_cycles += 1
                if grant_active:
                    grants_during_low += 1

        # Wait for PWM completion
        await self.pwm_controller.wait_pwm_complete(timeout_cycles=50)

        # Validate integration
        if grants_during_high > 0:
            self.log.error(f"Grants occurred during PWM high: {grants_during_high}")
            return False

        if grants_during_low == 0:
            self.log.warning("No grants during PWM low - may indicate blocking issue")

        # Verify PWM timing
        if abs(pwm_high_cycles - duty) > 1:  # Allow 1 cycle tolerance
            self.log.error(f"PWM timing incorrect: expected ~{duty} high cycles, got {pwm_high_cycles}")
            return False

        self.log.debug(f"Arbiter-PWM integration verified: {grants_during_low} grants during PWM low")
        return True

    async def test_monbus_arbiter_integration(self) -> bool:
        """Test integration between MonBus and arbiter"""
        self.log.debug("Testing MonBus-arbiter integration")

        self.components.monbus_slave.clear_received_packets()

        # Generate arbiter activity and monitor MonBus events
        await self.components.pattern_generator.apply_pattern(
            self.dut, RequestPattern.ALL_CLIENTS, duration_cycles=100
        )

        # Check for arbiter-related MonBus events
        all_packets = self.components.monbus_slave.get_received_packets()
        performance_packets = self.components.monbus_slave.get_performance_packets()

        if len(all_packets) == 0:
            self.log.error("No MonBus packets generated during arbiter activity")
            return False

        # Look for grant efficiency events
        grant_efficiency_packets = [
            p for p in performance_packets
            if p.event_code == AXIPerformanceCode.GRANT_EFFICIENCY.value
        ]

        if len(grant_efficiency_packets) == 0:
            self.log.error("No grant efficiency packets found")
            return False

        # Validate grant efficiency packet data
        for packet in grant_efficiency_packets[:3]:  # Check first 3
            if packet.channel_id >= self.params['clients']:
                self.log.error(f"Invalid client ID in grant efficiency packet: {packet.channel_id}")
                return False

        self.log.debug(f"MonBus-arbiter integration verified: {len(grant_efficiency_packets)} efficiency events")
        return True

    async def test_monitoring_packet_filtering_integration(self) -> bool:
        """Test integration of packet filtering with full system operation"""
        self.log.debug("Testing monitoring packet filtering integration")

        test_phases = [
            {
                'name': 'Phase 1: All packets disabled',
                'config': {'enable_all': False},
                'expected_packets': 0
            },
            {
                'name': 'Phase 2: Only performance packets',
                'config': {'enable_performance': True, 'enable_others': False},
                'expected_packet_types': ['PERF']
            },
            {
                'name': 'Phase 3: Performance + Error packets',
                'config': {'enable_performance': True, 'enable_errors': True, 'enable_others': False},
                'expected_packet_types': ['PERF', 'ERROR']
            },
            {
                'name': 'Phase 4: All packets enabled',
                'config': {'enable_all': True},
                'expected_packet_types': ['PERF', 'ERROR', 'THRESHOLD']
            }
        ]

        for phase in test_phases:
            self.log.debug(f"Running {phase['name']}")
            
            # Configure packet filtering for this phase
            if phase['config'].get('enable_all'):
                await self.components.configure_packet_filtering(
                    enable_errors=True,
                    enable_performance=True,
                    enable_thresholds=True,
                    enable_timeouts=False,
                    enable_completion=False,
                    enable_debug=False
                )
            elif phase['config'].get('enable_all') == False:
                await self.components.disable_all_monitoring_packets()
            else:
                await self.components.configure_packet_filtering(
                    enable_errors=phase['config'].get('enable_errors', False),
                    enable_performance=phase['config'].get('enable_performance', False),
                    enable_thresholds=phase['config'].get('enable_thresholds', False),
                    enable_timeouts=False,
                    enable_completion=False,
                    enable_debug=False
                )

            self.components.monbus_slave.clear_received_packets()

            # Generate system activity
            await self.components.pattern_generator.apply_pattern(
                self.dut, RequestPattern.ALL_CLIENTS, duration_cycles=80
            )

            # Analyze results
            all_packets = self.components.monbus_slave.get_received_packets()
            
            if 'expected_packets' in phase:
                expected_count = phase['expected_packets']
                if len(all_packets) != expected_count:
                    self.log.error(f"{phase['name']}: Expected {expected_count} packets, got {len(all_packets)}")
                    return False

            if 'expected_packet_types' in phase:
                packet_types_found = set()
                for packet in all_packets:
                    packet_types_found.add(packet.get_packet_type_name())
                
                expected_types = set(phase['expected_packet_types'])
                
                # Check that we only have expected types
                unexpected_types = packet_types_found - expected_types
                if unexpected_types:
                    self.log.error(f"{phase['name']}: Unexpected packet types: {unexpected_types}")
                    return False

                self.log.debug(f"{phase['name']}: Found packet types: {packet_types_found}")

        self.log.debug("Packet filtering integration test passed")
        return True

    # ==========================================================================
    # MEDIUM TESTS
    # ==========================================================================

    async def test_pwm_monbus_integration(self) -> bool:
        """Test integration between PWM and MonBus monitoring"""
        self.log.debug("Testing PWM-MonBus integration")

        self.components.monbus_slave.clear_received_packets()

        # Start PWM and monitor for related events
        duty = 3
        period = 6
        await self.pwm_controller.configure_pwm(duty, period, repeat_count=2)

        # Set up requests
        self.dut.req.value = (1 << self.params['clients']) - 1

        await self.pwm_controller.start_pwm()

        # Monitor during PWM operation
        await ClockCycles(self.dut.clk, period * 2 + 10)
        await self.pwm_controller.wait_pwm_complete(timeout_cycles=50)

        # Check MonBus activity during PWM
        packets_during_pwm = self.components.monbus_slave.get_received_packets()

        # Should have some monitoring activity
        if len(packets_during_pwm) == 0:
            self.log.warning("No MonBus packets during PWM operation")

        # Check for any threshold events that might be related to PWM blocking
        threshold_packets = self.components.monbus_slave.get_threshold_packets()

        self.log.debug(f"PWM-MonBus integration: {len(packets_during_pwm)} packets, "
                      f"{len(threshold_packets)} threshold events")
        return True

    async def test_full_system_scenarios(self) -> bool:
        """Test full system with multiple concurrent scenarios"""
        self.log.debug("Testing full system scenarios")

        # Scenario 1: PWM + Round-robin requests + MonBus monitoring
        self.components.monbus_slave.clear_received_packets()

        # Start PWM
        await self.pwm_controller.configure_pwm(duty=2, period=8, repeat_count=1)
        await self.pwm_controller.start_pwm()

        # Apply round-robin pattern during PWM
        await self.components.pattern_generator.apply_pattern(
            self.dut, RequestPattern.ROUND_ROBIN, duration_cycles=40
        )

        await self.pwm_controller.wait_pwm_complete(timeout_cycles=100)

        scenario1_packets = len(self.components.monbus_slave.get_received_packets())

        # Scenario 2: All clients + MonBus monitoring (no PWM)
        self.components.monbus_slave.clear_received_packets()

        await self.components.pattern_generator.apply_pattern(
            self.dut, RequestPattern.ALL_CLIENTS, duration_cycles=80
        )

        scenario2_packets = len(self.components.monbus_slave.get_received_packets())

        # Both scenarios should generate monitoring activity
        if scenario1_packets == 0 and scenario2_packets == 0:
            self.log.error("No monitoring activity in either scenario")
            return False

        self.log.debug(f"Full system scenarios: Scenario1={scenario1_packets} packets, "
                      f"Scenario2={scenario2_packets} packets")
        return True

    async def test_stress_integration(self) -> bool:
        """Test system integration under stress conditions"""
        self.log.debug("Testing stress integration")

        # Rapid PWM cycles with changing request patterns
        for cycle in range(5):
            # Vary PWM configuration
            duty = 2 + (cycle % 3)
            period = 6 + (cycle % 2)

            await self.pwm_controller.configure_pwm(duty, period, repeat_count=1)
            await self.pwm_controller.start_pwm()

            # Random request pattern during PWM
            pattern = self.components.pattern_generator.generate_pattern(RequestPattern.RANDOM, cycle)
            self.dut.req.value = pattern

            # Brief operation
            await ClockCycles(self.dut.clk, period + 5)
            await self.pwm_controller.wait_pwm_complete(timeout_cycles=20)

        # Check system integrity
        final_packets = self.components.monbus_slave.get_received_packets()
        arbiter_transactions = self.components.arbiter_monitor.get_transaction_count()

        if arbiter_transactions == 0:
            self.log.error("No arbiter transactions during stress test")
            return False

        self.log.debug(f"Stress integration completed: {arbiter_transactions} transactions, "
                      f"{len(final_packets)} MonBus packets")
        return True

    # ==========================================================================
    # FULL TESTS
    # ==========================================================================

    async def test_comprehensive_system_validation(self) -> bool:
        """Test comprehensive system validation with all components"""
        self.log.debug("Testing comprehensive system validation")

        # Reset system state
        self.components.monbus_slave.clear_received_packets()

        # Phase 1: Basic functionality verification
        self.log.debug("Phase 1: Basic functionality")
        await self.components.pattern_generator.apply_pattern(
            self.dut, RequestPattern.ALL_CLIENTS, duration_cycles=50
        )

        phase1_packets = len(self.components.monbus_slave.get_received_packets())

        # Phase 2: PWM integration
        self.log.debug("Phase 2: PWM integration")
        await self.pwm_controller.run_pwm_cycle(duty=4, period=8, repeat_count=1)

        phase2_packets = len(self.components.monbus_slave.get_received_packets())

        # Phase 3: Fairness validation
        self.log.debug("Phase 3: Fairness validation")
        await self.components.pattern_generator.apply_pattern(
            self.dut, RequestPattern.ALL_CLIENTS, duration_cycles=150
        )

        # Analyze final system state
        final_fairness = self.components.arbiter_monitor.get_fairness_index()
        final_transactions = self.components.arbiter_monitor.get_transaction_count()
        final_packets = len(self.components.monbus_slave.get_received_packets())

        # Validation criteria
        validation_results = {
            'phase1_packets': phase1_packets > 0,
            'phase2_packets': phase2_packets > phase1_packets,
            'fairness_acceptable': final_fairness > 0.5,
            'sufficient_transactions': final_transactions > 50,
            'monitoring_active': final_packets > 10
        }

        failed_validations = [k for k, v in validation_results.items() if not v]

        if failed_validations:
            self.log.error(f"System validation failures: {failed_validations}")
            return False

        self.log.debug(f"Comprehensive validation passed: fairness={final_fairness:.3f}, "
                      f"transactions={final_transactions}, packets={final_packets}")
        return True

    async def test_scenario_runner_integration(self) -> bool:
        """Test integration using the scenario runner framework"""
        self.log.debug("Testing scenario runner integration")

        # Get standard scenarios appropriate for integration testing
        scenarios = get_standard_test_scenarios(self.params['clients'])

        # Run a subset suitable for integration testing
        integration_scenarios = [
            s for s in scenarios
            if s.name in ['basic_round_robin', 'all_clients_fairness', 'pwm_50_percent_duty']
        ][:2]  # Limit to 2 scenarios

        if not integration_scenarios:
            self.log.warning("No suitable scenarios found for integration testing")
            return True

        # Update scenario runner with PWM controller
        self.components.scenario_runner.pwm_controller = self.pwm_controller

        success_count = 0
        for scenario in integration_scenarios:
            try:
                result = await self.components.scenario_runner.run_scenario(scenario)
                if result['success']:
                    success_count += 1
                else:
                    self.log.warning(f"Scenario {scenario.name} failed: {result.get('errors', [])}")
            except Exception as e:
                self.log.warning(f"Scenario {scenario.name} exception: {e}")

        # Consider successful if at least one scenario passes
        if success_count == 0:
            self.log.error("No scenarios passed in scenario runner integration")
            return False

        self.log.debug(f"Scenario runner integration: {success_count}/{len(integration_scenarios)} scenarios passed")
        return True

    async def test_end_to_end_monitoring(self) -> bool:
        """Test complete end-to-end monitoring flow"""
        self.log.debug("Testing end-to-end monitoring")

        # Clear state
        self.components.monbus_slave.clear_received_packets()

        # Create a comprehensive test scenario that exercises all monitoring aspects

        # Step 1: Generate activity with fairness monitoring
        await self.components.pattern_generator.apply_pattern(
            self.dut, RequestPattern.ALL_CLIENTS, duration_cycles=100
        )

        monitoring_packets_1 = len(self.components.monbus_slave.get_received_packets())

        # Step 2: Add PWM to create blocking behavior
        await self.pwm_controller.run_pwm_cycle(duty=3, period=6, repeat_count=2)

        monitoring_packets_2 = len(self.components.monbus_slave.get_received_packets())

        # Step 3: Create potential starvation scenario
        self.dut.req.value = 0b0001  # Only client 0
        await ClockCycles(self.dut.clk, 80)

        # Step 4: Resume normal operation
        self.dut.req.value = (1 << self.params['clients']) - 1
        await ClockCycles(self.dut.clk, 50)

        final_monitoring_packets = len(self.components.monbus_slave.get_received_packets())

        # Analyze end-to-end monitoring
        all_packets = self.components.monbus_slave.get_received_packets()

        # Check for different types of monitoring events
        performance_count = len(self.components.monbus_slave.get_performance_packets())
        threshold_count = len(self.components.monbus_slave.get_threshold_packets())
        error_count = len(self.components.monbus_slave.get_error_packets())

        monitoring_analysis = {
            'total_packets': len(all_packets),
            'performance_events': performance_count,
            'threshold_events': threshold_count,
            'error_events': error_count,
            'progression': [monitoring_packets_1, monitoring_packets_2, final_monitoring_packets]
        }

        # Validation: should have some monitoring activity
        if monitoring_analysis['total_packets'] < 5:
            self.log.error(f"Insufficient monitoring activity: {monitoring_analysis}")
            return False

        # Should have performance events at minimum
        if monitoring_analysis['performance_events'] == 0:
            self.log.error("No performance monitoring events detected")
            return False

        self.log.debug(f"End-to-end monitoring verified: {monitoring_analysis}")
        return True


class IntegrationPWMController:
    """PWM controller optimized for integration testing"""

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
        """Run a complete PWM cycle with integration-friendly timing"""
        await self.configure_pwm(duty, period, repeat_count)
        await self.start_pwm()

        # Wait for expected duration with generous buffer for integration testing
        expected_cycles = period * repeat_count
        await ClockCycles(self.dut.clk, expected_cycles + 15)

        return await self.wait_pwm_complete(timeout_cycles=100)
