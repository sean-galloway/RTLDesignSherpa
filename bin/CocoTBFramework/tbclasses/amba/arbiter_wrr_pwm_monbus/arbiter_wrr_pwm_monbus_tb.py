"""
Arbiter WRR PWM MonBus Testbench - Refactored Architecture

This testbench coordinates separate test classes for comprehensive testing of the combined
WRR Arbiter + PWM + MonBus module. Each test class focuses on specific functionality.
"""

import os
import asyncio
import random
from typing import List, Dict, Any, Optional, Tuple
from enum import Enum

import cocotb
from cocotb.clock import Clock
from cocotb.triggers import RisingEdge, Timer, ClockCycles
from cocotb.result import TestFailure

from CocoTBFramework.tbclasses.shared.tbbase import TBBase
from CocoTBFramework.components.shared.flex_randomizer import FlexRandomizer
from CocoTBFramework.tbclasses.amba.amba_random_configs import AXI_RANDOMIZER_CONFIGS
from CocoTBFramework.tbclasses.monbus import (
    MonbusSlave, ProtocolType, PktType, AXIErrorCode, AXIThresholdCode,
    AXIPerformanceCode, create_arbiter_starvation_event,
    create_arbiter_grant_latency_event, create_arbiter_active_count_event,
    create_arbiter_grant_efficiency_event, analyze_fairness,
    analyze_timing_patterns, validate_packet_sequence
)

# Import existing proven components
from CocoTBFramework.components.shared.arbiter_monitor import WeightedRoundRobinArbiterMonitor

# Import helper classes
from .test_helper_classes import (
    RequestPatternGenerator, PWMScenarioRunner, MonBusEventValidator,
    FairnessAnalyzer, TestScenarioRunner, get_standard_test_scenarios,
    get_fairness_focused_scenarios, TestScenario, RequestPattern
)

# Import the separate test classes (we'll define these)
from .arbiter_fairness_tests import ArbiterFairnessTests
from .pwm_functionality_tests import PWMFunctionalityTests
from .monbus_validation_tests import MonBusValidationTests
from .integration_tests import IntegrationTests


class TestLevel(Enum):
    """Test level enumeration"""
    BASIC = "basic"
    MEDIUM = "medium"
    FULL = "full"


class TestComponents:
    """Shared components container for all test classes"""

    def __init__(self, dut, params: Dict[str, Any], log, randomizer):
        self.dut = dut
        self.params = params
        self.log = log
        self.randomizer = randomizer

        # Core components
        self.monbus_slave = None
        self.arbiter_monitor = None

        # Helper components
        self.pattern_generator = None
        self.pwm_scenario_runner = None
        self.event_validator = None
        self.fairness_analyzer = None
        self.scenario_runner = None

    async def initialize(self, randomizer):
        """Initialize all shared components"""
        await self._setup_monbus()
        await self._setup_arbiter_monitor()
        await self._setup_helpers()
        await self._configure_monitoring()

    async def _setup_monbus(self):
        """Setup MonBus slave component"""
        self.monbus_slave = MonbusSlave(
            dut=self.dut,
            title="ArbiterMonBus",
            prefix="",
            clock=self.dut.clk,
            bus_name="monbus",
            pkt_prefix="",            
            expected_protocol=ProtocolType.AXI,
            expected_unit_id=0x0,
            expected_agent_id=0x00,
            timeout_cycles=1000,
            log=self.log,
            super_debug=False,
            # Add flow control parameters
            randomizer=self.randomizer
        )
        self.log.info("MonBus slave initialized")

    async def _setup_arbiter_monitor(self):
        """Setup the proven arbiter monitor"""
        self.arbiter_monitor = WeightedRoundRobinArbiterMonitor(
            dut=self.dut,
            title="ArbiterWRR",
            clock=self.dut.clk,
            reset_n=self.dut.rst_n,
            req_signal=self.dut.req,
            gnt_valid_signal=self.dut.gnt_valid,
            gnt_signal=self.dut.gnt,
            gnt_id_signal=self.dut.gnt_id,
            gnt_ack_signal=self.dut.gnt_ack if self.params['wait_gnt_ack'] else None,
            block_arb_signal=self.dut.pwm_out,  # PWM blocks arbitration
            max_thresh_signal=self.dut.cfg_arb_max_thresh,
            clients=self.params['clients'],
            log=self.log,
            clock_period_ns=10
        )

        # Start monitoring
        self.arbiter_monitor.start_monitoring()
        self.log.info("Arbiter monitor initialized and started")

    async def _setup_helpers(self):
        """Setup helper utility classes"""
        self.pattern_generator = RequestPatternGenerator(
            num_clients=self.params['clients'],
            seed=self.params.get('seed')
        )

        self.pwm_scenario_runner = PWMScenarioRunner(
            dut=self.dut,
            pwm_controller=None,  # We'll create a simple PWM interface
            log=self.log
        )

        self.event_validator = MonBusEventValidator(
            monbus_slave=self.monbus_slave,
            log=self.log
        )

        self.fairness_analyzer = FairnessAnalyzer(
            num_clients=self.params['clients'],
            log=self.log
        )

        self.scenario_runner = TestScenarioRunner(
            dut=self.dut,
            monbus_slave=self.monbus_slave,
            pwm_controller=None,  # Simple PWM interface
            arbiter_monitor=self.arbiter_monitor,
            log=self.log
        )

        self.log.info("Helper components initialized")

    async def _configure_monitoring(self):
        """Configure monitoring parameters with packet type filtering"""
        # Enable monitoring
        self.dut.cfg_mon_enable.value = 1

        # Configure packet type filtering - enable all types by default for testing
        packet_type_enable = self._get_default_packet_type_config()
        self.dut.cfg_mon_pkt_type_enable.value = packet_type_enable

        # Configure thresholds
        self.dut.cfg_mon_latency.value = 50  # 50 cycle latency threshold
        self.dut.cfg_mon_starvation.value = 100  # 100 cycle starvation threshold
        self.dut.cfg_mon_fairness.value = self.params['fairness_thresh']
        self.dut.cfg_mon_active.value = self.params['clients']
        self.dut.cfg_mon_period.value = 8  # Sample period (2^8 = 256 cycles)

        # Configure arbiter weights (equal weights for fairness testing)
        weight_value = self.params['max_thresh'] // 2
        weights = 0
        for i in range(self.params['clients']):
            weights |= (weight_value << (i * self.params['max_thresh_width']))
        self.dut.cfg_arb_max_thresh.value = weights

        await RisingEdge(self.dut.clk)
        self.log.debug("Monitoring configuration complete with packet filtering")

    def _get_default_packet_type_config(self):
        """Get default packet type configuration for testing"""
        # Enable common packet types for testing:
        # - Error events (starvation)
        # - Threshold events (latency, active count)  
        # - Performance events (grant efficiency)
        config = 0
        config |= (1 << PktType.ERROR.value)      # Bit 0: Error events
        config |= (1 << PktType.THRESHOLD.value)  # Bit 2: Threshold events
        config |= (1 << PktType.PERF.value)       # Bit 4: Performance events
        return config

    async def configure_packet_filtering(self, enable_errors=True, enable_performance=True, 
                                        enable_thresholds=True, enable_timeouts=False,
                                        enable_completion=False, enable_debug=False):
        """
        Configure packet type filtering with granular control
        
        Args:
            enable_errors: Enable error packet generation (starvation)
            enable_performance: Enable performance packet generation (grant efficiency)
            enable_thresholds: Enable threshold packet generation (latency, active count)
            enable_timeouts: Enable timeout packet generation
            enable_completion: Enable completion packet generation
            enable_debug: Enable debug packet generation
        """
        config = 0
        
        if enable_errors:
            config |= (1 << PktType.ERROR.value)
        if enable_completion:
            config |= (1 << PktType.COMPLETION.value)
        if enable_thresholds:
            config |= (1 << PktType.THRESHOLD.value)
        if enable_timeouts:
            config |= (1 << PktType.TIMEOUT.value)
        if enable_performance:
            config |= (1 << PktType.PERF.value)
        if enable_debug:
            config |= (1 << PktType.DEBUG.value)
        
        self.dut.cfg_mon_pkt_type_enable.value = config
        await RisingEdge(self.dut.clk)
        
        self.log.debug(f"Packet filtering configured: 0x{config:04X}")

    async def disable_all_monitoring_packets(self):
        """Disable all monitoring packet generation"""
        self.dut.cfg_mon_pkt_type_enable.value = 0
        await RisingEdge(self.dut.clk)
        self.log.debug("All monitoring packets disabled")

    async def enable_only_performance_monitoring(self):
        """Enable only performance monitoring packets"""
        config = (1 << PktType.PERF.value)
        self.dut.cfg_mon_pkt_type_enable.value = config
        await RisingEdge(self.dut.clk)
        self.log.debug("Only performance monitoring enabled")

    async def enable_only_error_monitoring(self):
        """Enable only error monitoring packets"""
        config = (1 << PktType.ERROR.value)
        self.dut.cfg_mon_pkt_type_enable.value = config
        await RisingEdge(self.dut.clk)
        self.log.debug("Only error monitoring enabled")


class ArbiterWRRPWMMonBusTestTB(TBBase):
    """
    Main testbench coordinator for Arbiter WRR PWM MonBus module.
    Orchestrates separate test classes for focused testing.
    """

    def __init__(self, dut):
        super().__init__(dut)

        # Get test parameters from environment
        self.test_params = self._load_test_parameters()
        self.log.info(f"Testbench initialized for {self.test_params['test_level'].value} level testing")
        self._log_parameters()
        # Create FlexConfigGen manager and get randomizer instances directly
        self.monbus_randomizer = FlexRandomizer(AXI_RANDOMIZER_CONFIGS['fast']['slave'])

        # Shared components container
        self.components = TestComponents(dut, self.test_params, self.log, self.monbus_randomizer)

        # Test tracking
        self.test_failures = []
        self.test_results = {}
        self.test_classes = {}

    def _load_test_parameters(self) -> Dict[str, Any]:
        """Load test parameters from environment"""
        params = {
            'test_level': TestLevel(os.environ.get('TEST_LEVEL', 'basic')),
            'max_thresh': int(os.environ.get('MAX_THRESH', '8')),
            'clients': int(os.environ.get('CLIENTS', '4')),
            'pwm_width': int(os.environ.get('PWM_WIDTH', '8')),
            'wait_gnt_ack': int(os.environ.get('WAIT_GNT_ACK', '0')),
            'fairness_thresh': int(os.environ.get('MON_FAIRNESS_THRESH', '40')),
            'min_grants': int(os.environ.get('MIN_GRANTS_FOR_FAIRNESS', '100')),
            'seed': int(os.environ.get('SEED', '0'))
        }

        # Calculated parameters
        params['max_thresh_width'] = (params['max_thresh'] - 1).bit_length()

        return params

    def _log_parameters(self):
        """Log test parameters"""
        p = self.test_params
        self.log.info(f"Parameters: MAX_THRESH={p['max_thresh']}, CLIENTS={p['clients']}, "
                        f"PWM_WIDTH={p['pwm_width']}, WAIT_GNT_ACK={p['wait_gnt_ack']}")
        self.log.info(f"Fairness: THRESH={p['fairness_thresh']}%, MIN_GRANTS={p['min_grants']}")
        self.log.info(f"Packet filtering: Enabled for granular monitoring control")

    async def reset_dut(self):
        # Assert reset
        self.dut.rst_n.value = 0
        await self.wait_clocks('clk', 10)

        # Release reset
        self.dut.rst_n.value = 1
        await self.wait_clocks('clk', 5)

    async def run_packet_filtering_validation(self) -> bool:
        """Run comprehensive packet filtering validation"""
        self.log.info("Running packet filtering validation")

        # Test 1: Verify default configuration
        default_config = self.components._get_default_packet_type_config()
        self.dut.cfg_mon_pkt_type_enable.value = default_config
        await RisingEdge(self.dut.clk)

        # Test 2: Verify all packets can be disabled
        await self.components.disable_all_monitoring_packets()
        self.components.monbus_slave.clear_received_packets()

        # Generate activity with monitoring disabled
        await self.components.pattern_generator.apply_pattern(
            self.dut, RequestPattern.ALL_CLIENTS, duration_cycles=50
        )

        disabled_packets = self.components.monbus_slave.get_received_packets()
        if len(disabled_packets) > 0:
            self.log.error(f"Monitoring disabled but still received {len(disabled_packets)} packets")
            return False

        # Test 3: Verify selective enabling works
        await self.components.configure_packet_filtering(
            enable_errors=False,
            enable_performance=True,
            enable_thresholds=False
        )

        self.components.monbus_slave.clear_received_packets()

        # Generate activity
        await self.components.pattern_generator.apply_pattern(
            self.dut, RequestPattern.ALL_CLIENTS, duration_cycles=100
        )

        selective_packets = self.components.monbus_slave.get_received_packets()
        perf_packets = self.components.monbus_slave.get_performance_packets()

        # Should only have performance packets
        if len(selective_packets) != len(perf_packets):
            self.log.error("Selective filtering failed - got non-performance packets")
            return False

        self.log.info(f"Packet filtering validation passed: "
                        f"disabled={len(disabled_packets)}, selective={len(perf_packets)}")
        return True

    async def run_all_tests(self) -> bool:
        """Run all tests based on test level"""
        await self.components.initialize(self.monbus_randomizer)
        await self._initialize_test_classes()

        test_classes_to_run = self._get_test_classes_for_level()
        total_tests = 0
        passed_tests = 0

        self.log.info(f"Running {len(test_classes_to_run)} test classes for {self.test_params['test_level'].value} level")

        for test_class_name, test_class in test_classes_to_run:
            try:
                self.log.info(f"Running test class: {test_class_name}")

                class_results = await test_class.run_tests()

                # Aggregate results
                class_total = class_results['total_tests']
                class_passed = class_results['passed_tests']

                total_tests += class_total
                passed_tests += class_passed

                self.test_results[test_class_name] = class_results

                if class_results['success']:
                    self.log.info(f"✓ {test_class_name} PASSED ({class_passed}/{class_total})")
                else:
                    self.test_failures.extend([f"{test_class_name}.{t}" for t in class_results['failed_tests']])
                    self.log.error(f"✗ {test_class_name} FAILED ({class_passed}/{class_total})")

            except Exception as e:
                self.test_failures.append(f"{test_class_name}.EXCEPTION")
                self.test_results[test_class_name] = {'error': str(e)}
                self.log.error(f"✗ {test_class_name} ERROR: {str(e)}")

        # Final summary
        self.log.info(f"Test Summary: {passed_tests}/{total_tests} tests passed across all classes")
        self._log_component_statistics()

        if self.test_failures:
            self.log.error(f"Failed tests: {', '.join(self.test_failures)}")

        return len(self.test_failures) == 0

    async def _initialize_test_classes(self):
        """Initialize all test classes"""
        self.test_classes = {
            'arbiter_fairness': ArbiterFairnessTests(self.components),
            'pwm_functionality': PWMFunctionalityTests(self.components),
            'monbus_validation': MonBusValidationTests(self.components),
            'integration': IntegrationTests(self.components)
        }

    def _get_test_classes_for_level(self) -> List[Tuple[str, object]]:
        """Get test classes to run based on test level"""

        basic_classes = [
            ('arbiter_fairness', self.test_classes['arbiter_fairness']),
            ('pwm_functionality', self.test_classes['pwm_functionality'])
        ]

        medium_classes = basic_classes + [
            ('monbus_validation', self.test_classes['monbus_validation']),
        ]

        full_classes = medium_classes + [
            ('integration', self.test_classes['integration'])
        ]

        level_map = {
            TestLevel.BASIC: basic_classes,
            TestLevel.MEDIUM: medium_classes,
            TestLevel.FULL: full_classes
        }

        return level_map[self.test_params['test_level']]

    def _log_component_statistics(self):
        """Log final statistics from all components"""
        if self.components.arbiter_monitor:
            arbiter_stats = self.components.arbiter_monitor.get_stats_summary()
            self.log.info(f"Final Arbiter Statistics:\n{arbiter_stats}")

        if self.components.monbus_slave:
            monbus_summary = self.components.monbus_slave.get_stats_summary()
            self.log.info(f"Final MonBus Statistics:\n{monbus_summary}")

        if self.components.fairness_analyzer:
            fairness_analysis = self.components.fairness_analyzer.analyze_fairness_detailed()
            if 'error' not in fairness_analysis:
                self.log.info(f"Final Fairness Analysis: "
                            f"Jain Index = {fairness_analysis['jain_fairness_index']:.3f}, "
                            f"Max Deviation = {fairness_analysis['max_deviation_percent']:.2f}%")


# Simple PWM controller interface for helper classes
class SimplePWMController:
    """Simple PWM controller interface for compatibility with helper classes"""

    def __init__(self, dut, log):
        self.dut = dut
        self.log = log
        self.stats = {
            'pwm_cycles_run': 0,
            'pwm_starts': 0,
            'pwm_completions': 0,
            'duty_cycles_tested': set(),
            'periods_tested': set()
        }

    async def configure_pwm(self, duty: int, period: int, repeat_count: int = 1):
        """Configure PWM parameters"""
        self.dut.cfg_pwm_duty.value = duty
        self.dut.cfg_pwm_period.value = period
        self.dut.cfg_pwm_repeat_count.value = repeat_count
        self.stats['duty_cycles_tested'].add(duty)
        self.stats['periods_tested'].add(period)
        await RisingEdge(self.dut.clk)

    async def start_pwm(self):
        """Start PWM operation"""
        self.dut.cfg_pwm_start.value = 1
        await RisingEdge(self.dut.clk)
        self.dut.cfg_pwm_start.value = 0
        self.stats['pwm_starts'] += 1

    async def wait_pwm_complete(self, timeout_cycles: int = 1000):
        """Wait for PWM completion"""
        for _ in range(timeout_cycles):
            await RisingEdge(self.dut.clk)
            if self.dut.cfg_sts_pwm_done.value == 1:
                self.stats['pwm_completions'] += 1
                return True
        return False

    async def run_pwm_cycle(self, duty: int, period: int, repeat_count: int = 1):
        """Run a complete PWM cycle"""
        await self.configure_pwm(duty, period, repeat_count)
        await self.start_pwm()

        expected_cycles = period * repeat_count
        await ClockCycles(self.dut.clk, expected_cycles + 10)  # Add buffer

        completed = await self.wait_pwm_complete(timeout_cycles=50)
        if completed:
            self.stats['pwm_cycles_run'] += 1
        return completed

    def get_stats(self):
        """Get PWM controller statistics"""
        return self.stats.copy()
