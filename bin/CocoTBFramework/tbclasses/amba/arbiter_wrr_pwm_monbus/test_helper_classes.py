"""
Test Helper Classes for MonBus Testing

This module provides additional test helper classes that can be used
in various MonBus-related tests for pattern generation, validation,
and analysis.
"""

import os
import random
from typing import List, Dict, Any, Optional, Tuple, Callable
from dataclasses import dataclass
from enum import Enum

import cocotb
from cocotb.triggers import RisingEdge, Timer, ClockCycles
from cocotb.result import TestFailure

from CocoTBFramework.tbclasses.monbus import (
    MonbusPacket, ProtocolType, PktType, AXIErrorCode, AXIThresholdCode,
    AXIPerformanceCode, create_arbiter_starvation_event,
    create_arbiter_grant_efficiency_event, analyze_fairness
)


class RequestPattern(Enum):
    """Request pattern types for testing"""
    SINGLE_CLIENT = "single_client"
    ROUND_ROBIN = "round_robin"
    ALL_CLIENTS = "all_clients"
    RANDOM = "random"
    BURST = "burst"
    ALTERNATING = "alternating"


@dataclass
class TestScenario:
    """Test scenario configuration"""
    name: str
    duration_cycles: int
    request_pattern: RequestPattern
    pwm_config: Optional[Dict[str, int]] = None
    expected_events: Optional[List[Dict[str, Any]]] = None
    validation_criteria: Optional[Dict[str, Any]] = None


class RequestPatternGenerator:
    """Generate various request patterns for testing"""

    def __init__(self, num_clients: int, seed: Optional[int] = None):
        self.num_clients = num_clients
        self.max_pattern = (1 << num_clients) - 1
        if seed is not None:
            random.seed(seed)

    def generate_pattern(self, pattern_type: RequestPattern, cycle: int = 0) -> int:
        """Generate request pattern for given cycle"""

        if pattern_type == RequestPattern.SINGLE_CLIENT:
            # Cycle through clients one at a time
            client = cycle % self.num_clients
            return 1 << client

        elif pattern_type == RequestPattern.ROUND_ROBIN:
            # Round-robin activation of clients
            active_client = cycle % self.num_clients
            return 1 << active_client

        elif pattern_type == RequestPattern.ALL_CLIENTS:
            # All clients request
            return self.max_pattern

        elif pattern_type == RequestPattern.RANDOM:
            # Random pattern each cycle
            return random.randint(0, self.max_pattern)

        elif pattern_type == RequestPattern.BURST:
            # Bursts of activity followed by idle
            burst_length = 10
            idle_length = 5
            period = burst_length + idle_length
            if (cycle % period) < burst_length:
                return self.max_pattern
            else:
                return 0

        elif pattern_type == RequestPattern.ALTERNATING:
            # Alternating between even and odd clients
            if cycle % 2 == 0:
                # Even clients (0, 2, 4, ...)
                pattern = 0
                for i in range(0, self.num_clients, 2):
                    pattern |= (1 << i)
                return pattern
            else:
                # Odd clients (1, 3, 5, ...)
                pattern = 0
                for i in range(1, self.num_clients, 2):
                    pattern |= (1 << i)
                return pattern

        else:
            raise ValueError(f"Unknown pattern type: {pattern_type}")

    async def apply_pattern(self, dut, pattern_type: RequestPattern,
                          duration_cycles: int) -> List[int]:
        """Apply request pattern to DUT for specified duration"""
        applied_patterns = []

        for cycle in range(duration_cycles):
            pattern = self.generate_pattern(pattern_type, cycle)
            dut.req.value = pattern
            applied_patterns.append(pattern)
            await RisingEdge(dut.clk)

        return applied_patterns


class PWMScenarioRunner:
    """Run various PWM scenarios for testing"""

    def __init__(self, dut, pwm_controller, log):
        self.dut = dut
        self.pwm_controller = pwm_controller
        self.log = log

    async def run_duty_cycle_sweep(self, period: int = 8,
                                 repeat_count: int = 1) -> Dict[str, Any]:
        """Run PWM with various duty cycles"""
        results = {}

        duty_cycles = list(range(1, period))  # 1 to period-1

        for duty in duty_cycles:
            self.log.debug(f"Testing duty cycle {duty}/{period}")

            success = await self.pwm_controller.run_pwm_cycle(
                duty=duty, period=period, repeat_count=repeat_count
            )

            results[f"duty_{duty}"] = {
                'success': success,
                'duty_cycle_percent': (duty / period) * 100
            }

            if not success:
                self.log.warning(f"PWM duty cycle {duty}/{period} failed")

        return results

    async def run_period_sweep(self, duty_percent: float = 50,
                             repeat_count: int = 1) -> Dict[str, Any]:
        """Run PWM with various periods at fixed duty cycle percentage"""
        results = {}

        periods = [4, 8, 12, 16]  # Various periods

        for period in periods:
            duty = max(1, int(period * duty_percent / 100))
            self.log.debug(f"Testing period {period} with duty {duty}")

            success = await self.pwm_controller.run_pwm_cycle(
                duty=duty, period=period, repeat_count=repeat_count
            )

            results[f"period_{period}"] = {
                'success': success,
                'actual_duty_percent': (duty / period) * 100
            }

            if not success:
                self.log.warning(f"PWM period {period} failed")

        return results

    async def run_stress_scenario(self, num_iterations: int = 10) -> Dict[str, Any]:
        """Run stress test with random PWM configurations"""
        results = {
            'total_iterations': num_iterations,
            'successful_iterations': 0,
            'failed_iterations': 0,
            'configurations_tested': []
        }

        for i in range(num_iterations):
            # Random configuration
            period = random.randint(4, 16)
            duty = random.randint(1, period - 1)
            repeat_count = random.randint(1, 3)

            config = {'duty': duty, 'period': period, 'repeat_count': repeat_count}
            results['configurations_tested'].append(config)

            self.log.debug(f"Stress iteration {i+1}: {config}")

            success = await self.pwm_controller.run_pwm_cycle(
                duty=duty, period=period, repeat_count=repeat_count
            )

            if success:
                results['successful_iterations'] += 1
            else:
                results['failed_iterations'] += 1
                self.log.warning(f"Stress iteration {i+1} failed: {config}")

        return results


class MonBusEventValidator:
    """Validate MonBus events against expected patterns"""

    def __init__(self, monbus_slave, log):
        self.monbus_slave = monbus_slave
        self.log = log

    async def wait_for_event(self, expected_event: Dict[str, Any],
                           timeout_cycles: int = 100) -> bool:
        """Wait for specific MonBus event"""
        start_packet_count = len(self.monbus_slave.received_packets)

        for _ in range(timeout_cycles):
            await self.monbus_slave.wait_clock()

            # Check new packets
            current_packets = self.monbus_slave.received_packets[start_packet_count:]

            for packet in current_packets:
                if packet.matches(**expected_event):
                    self.log.debug(f"Expected event found: {packet}")
                    return True

        self.log.warning(f"Expected event not found: {expected_event}")
        return False

    async def validate_event_sequence(self, expected_sequence: List[Dict[str, Any]],
                                    timeout_cycles: int = 200) -> Dict[str, Any]:
        """Validate sequence of MonBus events"""
        result = {
            'success': False,
            'events_found': 0,
            'total_expected': len(expected_sequence),
            'missing_events': [],
            'unexpected_events': []
        }

        start_packet_count = len(self.monbus_slave.received_packets)

        for i, expected_event in enumerate(expected_sequence):
            found = await self.wait_for_event(expected_event, timeout_cycles // len(expected_sequence))

            if found:
                result['events_found'] += 1
            else:
                result['missing_events'].append(expected_event)

        # Check for unexpected events
        all_packets = self.monbus_slave.received_packets[start_packet_count:]

        for packet in all_packets:
            expected = False
            for expected_event in expected_sequence:
                if packet.matches(**expected_event):
                    expected = True
                    break

            if not expected:
                result['unexpected_events'].append(packet.to_dict())

        result['success'] = (result['events_found'] == result['total_expected'] and
                             len(result['unexpected_events']) == 0)

        return result

    def validate_starvation_events(self, expected_starved_clients: List[int]) -> Dict[str, Any]:
        """Validate starvation events for specific clients"""
        starvation_packets = [p for p in self.monbus_slave.get_error_packets()
                            if p.event_code == AXIErrorCode.ARBITER_STARVATION.value]

        result = {
            'expected_clients': expected_starved_clients,
            'detected_clients': [],
            'missing_starvation_events': [],
            'unexpected_starvation_events': []
        }

        # Check for expected starvation events
        for client_id in expected_starved_clients:
            found = False
            for packet in starvation_packets:
                if packet.channel_id == client_id:
                    result['detected_clients'].append(client_id)
                    found = True
                    break

            if not found:
                result['missing_starvation_events'].append(client_id)

        # Check for unexpected starvation events
        for packet in starvation_packets:
            if packet.channel_id not in expected_starved_clients:
                result['unexpected_starvation_events'].append(packet.channel_id)

        result['success'] = (len(result['missing_starvation_events']) == 0 and
                           len(result['unexpected_starvation_events']) == 0)

        return result

    def validate_performance_metrics(self, expected_ranges: Dict[str, Tuple[int, int]]) -> Dict[str, Any]:
        """Validate performance metrics are within expected ranges"""
        performance_packets = self.monbus_slave.get_performance_packets()

        result = {
            'total_performance_packets': len(performance_packets),
            'metrics_in_range': {},
            'metrics_out_of_range': {},
            'success': True
        }

        # Group packets by event code
        metrics_by_code = {}
        for packet in performance_packets:
            event_name = packet.get_event_code_name()
            if event_name not in metrics_by_code:
                metrics_by_code[event_name] = []
            metrics_by_code[event_name].append(packet.data)

        # Validate ranges
        for metric_name, (min_val, max_val) in expected_ranges.items():
            if metric_name in metrics_by_code:
                values = metrics_by_code[metric_name]
                in_range_count = sum(1 for v in values if min_val <= v <= max_val)
                out_of_range_count = len(values) - in_range_count

                result['metrics_in_range'][metric_name] = in_range_count
                result['metrics_out_of_range'][metric_name] = out_of_range_count

                if out_of_range_count > 0:
                    result['success'] = False
                    self.log.warning(f"Metric {metric_name} has {out_of_range_count} out-of-range values")

        return result


class FairnessAnalyzer:
    """Analyze arbiter fairness with detailed metrics"""

    def __init__(self, num_clients: int, log):
        self.num_clients = num_clients
        self.log = log
        self.grant_history = []
        self.request_history = []

    def record_grant(self, cycle: int, client_id: int, request_vector: int):
        """Record a grant event"""
        self.grant_history.append({
            'cycle': cycle,
            'client_id': client_id,
            'request_vector': request_vector,
            'requesting_clients': bin(request_vector).count('1')
        })

    def record_request_state(self, cycle: int, request_vector: int, blocked: bool = False):
        """Record request state for a cycle"""
        self.request_history.append({
            'cycle': cycle,
            'request_vector': request_vector,
            'active_requests': bin(request_vector).count('1'),
            'blocked': blocked
        })

    def analyze_fairness_detailed(self) -> Dict[str, Any]:
        """Perform detailed fairness analysis"""
        if not self.grant_history:
            return {'error': 'No grant history to analyze'}

        # Count grants per client
        grants_per_client = [0] * self.num_clients
        total_grants = len(self.grant_history)

        for grant in self.grant_history:
            client_id = grant['client_id']
            if 0 <= client_id < self.num_clients:
                grants_per_client[client_id] += 1

        # Calculate fairness metrics
        expected_per_client = total_grants / self.num_clients

        # Standard deviation of grants
        variance = sum((grants - expected_per_client) ** 2 for grants in grants_per_client) / self.num_clients
        std_dev = variance ** 0.5

        # Jain's fairness index
        sum_grants = sum(grants_per_client)
        sum_grants_squared = sum(g * g for g in grants_per_client)
        jain_index = (sum_grants * sum_grants) / (self.num_clients * sum_grants_squared) if sum_grants_squared > 0 else 0

        # Per-client analysis
        client_analysis = []
        for i, grants in enumerate(grants_per_client):
            percentage = (grants / total_grants) * 100 if total_grants > 0 else 0
            deviation = abs(grants - expected_per_client) / expected_per_client * 100 if expected_per_client > 0 else 0

            client_analysis.append({
                'client_id': i,
                'grants': grants,
                'percentage': percentage,
                'deviation_percent': deviation
            })

        # Time-based analysis
        time_windows = self.analyze_fairness_over_time()

        return {
            'total_grants': total_grants,
            'grants_per_client': grants_per_client,
            'expected_per_client': expected_per_client,
            'standard_deviation': std_dev,
            'jain_fairness_index': jain_index,
            'max_deviation_percent': max(c['deviation_percent'] for c in client_analysis),
            'client_analysis': client_analysis,
            'time_windows': time_windows
        }

    def analyze_fairness_over_time(self, window_size: int = 50) -> List[Dict[str, Any]]:
        """Analyze fairness over sliding time windows"""
        windows = []

        if len(self.grant_history) < window_size:
            return windows

        for start_idx in range(0, len(self.grant_history) - window_size + 1, window_size // 2):
            end_idx = start_idx + window_size
            window_grants = self.grant_history[start_idx:end_idx]

            # Count grants in this window
            window_grants_per_client = [0] * self.num_clients
            for grant in window_grants:
                if 0 <= grant['client_id'] < self.num_clients:
                    window_grants_per_client[grant['client_id']] += 1

            # Calculate window fairness
            window_total = sum(window_grants_per_client)
            window_expected = window_total / self.num_clients if self.num_clients > 0 else 0

            max_deviation = 0
            if window_expected > 0:
                for grants in window_grants_per_client:
                    deviation = abs(grants - window_expected) / window_expected * 100
                    max_deviation = max(max_deviation, deviation)

            windows.append({
                'start_cycle': window_grants[0]['cycle'],
                'end_cycle': window_grants[-1]['cycle'],
                'grants_per_client': window_grants_per_client,
                'total_grants': window_total,
                'max_deviation_percent': max_deviation
            })

        return windows

    def detect_starvation_periods(self, threshold_cycles: int = 100) -> List[Dict[str, Any]]:
        """Detect periods where clients were starved"""
        starvation_periods = []

        # Track last grant time for each client
        last_grant_cycle = [-1] * self.num_clients

        for grant in self.grant_history:
            client_id = grant['client_id']
            cycle = grant['cycle']

            if 0 <= client_id < self.num_clients:
                # Check if other clients were starved
                for other_client in range(self.num_clients):
                    if other_client != client_id:
                        if last_grant_cycle[other_client] >= 0:
                            starvation_duration = cycle - last_grant_cycle[other_client]
                            if starvation_duration > threshold_cycles:
                                starvation_periods.append({
                                    'client_id': other_client,
                                    'start_cycle': last_grant_cycle[other_client],
                                    'end_cycle': cycle,
                                    'duration': starvation_duration
                                })

                last_grant_cycle[client_id] = cycle

        return starvation_periods


class TestScenarioRunner:
    """Run complete test scenarios with validation"""

    def __init__(self, dut, monbus_slave, pwm_controller, arbiter_monitor, log):
        self.dut = dut
        self.monbus_slave = monbus_slave
        self.pwm_controller = pwm_controller
        self.arbiter_monitor = arbiter_monitor
        self.log = log

        self.pattern_generator = RequestPatternGenerator(
            num_clients=int(os.environ.get('CLIENTS', '4'))
        )
        self.event_validator = MonBusEventValidator(monbus_slave, log)

    async def run_scenario(self, scenario: TestScenario) -> Dict[str, Any]:
        """Run a complete test scenario"""
        self.log.info(f"Running scenario: {scenario.name}")

        result = {
            'scenario_name': scenario.name,
            'success': False,
            'duration_cycles': scenario.duration_cycles,
            'pwm_results': {},
            'pattern_results': {},
            'event_validation': {},
            'fairness_analysis': {},
            'errors': []
        }

        try:
            # Clear previous state
            self.monbus_slave.clear_received_packets()

            # Setup PWM if configured
            if scenario.pwm_config:
                pwm_success = await self.pwm_controller.run_pwm_cycle(**scenario.pwm_config)
                result['pwm_results'] = {
                    'configured': True,
                    'success': pwm_success,
                    'config': scenario.pwm_config
                }

                if not pwm_success:
                    result['errors'].append("PWM configuration failed")

            # Apply request pattern
            applied_patterns = await self.pattern_generator.apply_pattern(
                self.dut, scenario.request_pattern, scenario.duration_cycles
            )

            result['pattern_results'] = {
                'pattern_type': scenario.request_pattern.value,
                'cycles_applied': len(applied_patterns),
                'unique_patterns': len(set(applied_patterns))
            }

            # Monitor arbiter activity
            await self.arbiter_monitor.monitor_grants(scenario.duration_cycles)

            # Validate expected events
            if scenario.expected_events:
                event_validation = await self.event_validator.validate_event_sequence(
                    scenario.expected_events
                )
                result['event_validation'] = event_validation

                if not event_validation['success']:
                    result['errors'].append("Event validation failed")

            # Analyze fairness
            fairness_analysis = self.arbiter_monitor.analyze_fairness()
            result['fairness_analysis'] = fairness_analysis

            # Apply validation criteria
            if scenario.validation_criteria:
                validation_success = self.apply_validation_criteria(
                    scenario.validation_criteria, result
                )

                if not validation_success:
                    result['errors'].append("Validation criteria not met")

            # Determine overall success
            result['success'] = len(result['errors']) == 0

            self.log.info(f"Scenario {scenario.name} {'PASSED' if result['success'] else 'FAILED'}")

        except Exception as e:
            result['errors'].append(f"Exception: {str(e)}")
            result['success'] = False
            self.log.error(f"Scenario {scenario.name} failed with exception: {e}")

        return result

    def apply_validation_criteria(self, criteria: Dict[str, Any],
                                result: Dict[str, Any]) -> bool:
        """Apply validation criteria to scenario results"""
        success = True

        # Check fairness criteria
        if 'max_fairness_deviation' in criteria:
            fairness = result.get('fairness_analysis', {})
            if 'max_deviation' in fairness:
                if fairness['max_deviation'] > criteria['max_fairness_deviation']:
                    success = False
                    self.log.warning(f"Fairness deviation {fairness['max_deviation']:.2f}% "
                                   f"exceeds limit {criteria['max_fairness_deviation']}%")

        # Check minimum grants
        if 'min_total_grants' in criteria:
            fairness = result.get('fairness_analysis', {})
            if 'total_grants' in fairness:
                if fairness['total_grants'] < criteria['min_total_grants']:
                    success = False
                    self.log.warning(f"Total grants {fairness['total_grants']} "
                                   f"below minimum {criteria['min_total_grants']}")

        # Check PWM success
        if 'require_pwm_success' in criteria:
            pwm_results = result.get('pwm_results', {})
            if criteria['require_pwm_success'] and not pwm_results.get('success', True):
                success = False
                self.log.warning("PWM operation required but failed")

        # Check event validation
        if 'require_event_validation' in criteria:
            event_validation = result.get('event_validation', {})
            if criteria['require_event_validation'] and not event_validation.get('success', True):
                success = False
                self.log.warning("Event validation required but failed")

        return success


# Predefined test scenarios for common use cases
def get_standard_test_scenarios(num_clients: int = 4) -> List[TestScenario]:
    """Get standard test scenarios for comprehensive testing"""

    scenarios = [
        # Basic functionality scenarios
        TestScenario(
            name="basic_round_robin",
            duration_cycles=50,
            request_pattern=RequestPattern.ROUND_ROBIN,
            validation_criteria={'min_total_grants': 10}
        ),

        TestScenario(
            name="all_clients_fairness",
            duration_cycles=100,
            request_pattern=RequestPattern.ALL_CLIENTS,
            validation_criteria={'max_fairness_deviation': 50, 'min_total_grants': 20}
        ),

        # PWM interaction scenarios
        TestScenario(
            name="pwm_50_percent_duty",
            duration_cycles=80,
            request_pattern=RequestPattern.ALL_CLIENTS,
            pwm_config={'duty': 4, 'period': 8, 'repeat_count': 2},
            validation_criteria={'require_pwm_success': True}
        ),

        TestScenario(
            name="pwm_25_percent_duty",
            duration_cycles=60,
            request_pattern=RequestPattern.RANDOM,
            pwm_config={'duty': 2, 'period': 8, 'repeat_count': 1},
            validation_criteria={'require_pwm_success': True}
        ),

        # Stress scenarios
        TestScenario(
            name="random_stress",
            duration_cycles=150,
            request_pattern=RequestPattern.RANDOM,
            validation_criteria={'min_total_grants': 30}
        ),

        TestScenario(
            name="burst_pattern",
            duration_cycles=120,
            request_pattern=RequestPattern.BURST,
            validation_criteria={'min_total_grants': 20}
        ),

        # Starvation detection scenarios
        TestScenario(
            name="single_client_dominance",
            duration_cycles=80,
            request_pattern=RequestPattern.SINGLE_CLIENT,
            expected_events=[
                create_arbiter_starvation_event(client_id=1, timer_value=50),
                create_arbiter_starvation_event(client_id=2, timer_value=50),
            ]
        ),
    ]

    return scenarios


def get_fairness_focused_scenarios(num_clients: int = 4) -> List[TestScenario]:
    """Get scenarios focused on fairness testing"""

    scenarios = [
        TestScenario(
            name="fairness_strict",
            duration_cycles=200,
            request_pattern=RequestPattern.ALL_CLIENTS,
            validation_criteria={'max_fairness_deviation': 30, 'min_total_grants': 50}
        ),

        TestScenario(
            name="fairness_alternating",
            duration_cycles=100,
            request_pattern=RequestPattern.ALTERNATING,
            validation_criteria={'max_fairness_deviation': 60, 'min_total_grants': 25}
        ),

        TestScenario(
            name="fairness_with_pwm",
            duration_cycles=160,
            request_pattern=RequestPattern.ALL_CLIENTS,
            pwm_config={'duty': 3, 'period': 6, 'repeat_count': 3},
            validation_criteria={
                'max_fairness_deviation': 40,
                'min_total_grants': 30,
                'require_pwm_success': True
            }
        ),
    ]

    return scenarios


# Export all classes and functions
__all__ = [
    'RequestPattern', 'TestScenario', 'RequestPatternGenerator',
    'PWMScenarioRunner', 'MonBusEventValidator', 'FairnessAnalyzer',
    'TestScenarioRunner', 'get_standard_test_scenarios',
    'get_fairness_focused_scenarios'
]