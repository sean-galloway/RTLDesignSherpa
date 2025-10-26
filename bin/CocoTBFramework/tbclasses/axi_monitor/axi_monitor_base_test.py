# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: MySpecificTest
# Purpose: AXI Monitor Base Test Class
#
# Documentation: bin/CocoTBFramework/README.md
# Subsystem: framework
#
# Author: sean galloway
# Created: 2025-10-18

"""
AXI Monitor Base Test Class

This provides a foundation for building specific AXI monitor test scenarios.
It extends the main testbench with additional utilities and patterns for
creating focused test cases.

Usage:
    from axi_monitor_base_test import AXIMonitorBaseTest
    
    class MySpecificTest(AXIMonitorBaseTest):
        async def run_test(self):
            # Custom test logic here
            pass

Features:
- Transaction pattern generators
- Error injection utilities  
- Verification helpers
- Test reporting templates
- Configuration management
"""

import random
import asyncio
from typing import Dict, List, Optional, Tuple, Any
from abc import ABC, abstractmethod

import cocotb
from cocotb.triggers import RisingEdge, Timer
from cocotb.utils import get_sim_time

from .axi_monitor_tb import AXIMonitorTB, AXIMonitorTestContext
from .axi_monitor_packets import (
    AXICommandPacket, AXIReadDataPacket, AXIWriteDataPacket, AXIWriteResponsePacket,
    InterruptPacket, MonitorConfigPacket, MonitoredTransaction,
    AXITransactionState, MonitorEventCode, InterruptPacketType
)


class TransactionPattern:
    """Defines a pattern for transaction generation"""
    
    def __init__(self, name: str, description: str):
        self.name = name
        self.description = description
        self.transactions = []
        self.timing_constraints = {}
        self.error_injection = {}
        
    def add_read(self, addr: int, length: int = 0, delay: int = 0, expect_error: bool = False):
        """Add a read transaction to the pattern"""
        self.transactions.append({
            'type': 'read',
            'addr': addr,
            'length': length,
            'delay': delay,
            'expect_error': expect_error
        })
        
    def add_write(self, addr: int, length: int = 0, delay: int = 0, expect_error: bool = False):
        """Add a write transaction to the pattern"""
        self.transactions.append({
            'type': 'write',
            'addr': addr,
            'length': length,
            'delay': delay,
            'expect_error': expect_error
        })
        
    def add_delay(self, cycles: int):
        """Add a delay to the pattern"""
        self.transactions.append({
            'type': 'delay',
            'cycles': cycles
        })


class ErrorScenario:
    """Defines an error injection scenario"""
    
    def __init__(self, name: str, description: str):
        self.name = name
        self.description = description
        self.setup_steps = []
        self.trigger_condition = None
        self.expected_responses = []
        
    def add_setup_step(self, step_type: str, **kwargs):
        """Add a setup step for the error scenario"""
        self.setup_steps.append({
            'type': step_type,
            'params': kwargs
        })
        
    def set_trigger(self, condition: str, **kwargs):
        """Set the trigger condition for the error"""
        self.trigger_condition = {
            'condition': condition,
            'params': kwargs
        }
        
    def add_expected_response(self, response_type: str, **kwargs):
        """Add an expected response from the monitor"""
        self.expected_responses.append({
            'type': response_type,
            'params': kwargs
        })


class PerformanceTest:
    """Defines a performance test scenario"""
    
    def __init__(self, name: str, description: str):
        self.name = name
        self.description = description
        self.load_pattern = None
        self.duration_cycles = 1000
        self.success_criteria = {}
        
    def set_load_pattern(self, pattern_type: str, **kwargs):
        """Set the load pattern for the test"""
        self.load_pattern = {
            'type': pattern_type,
            'params': kwargs
        }
        
    def add_success_criterion(self, metric: str, threshold: float, comparison: str = 'max'):
        """Add a success criterion"""
        self.success_criteria[metric] = {
            'threshold': threshold,
            'comparison': comparison
        }


class AXIMonitorBaseTest(AXIMonitorTB, ABC):
    """
    Base class for AXI Monitor tests providing common utilities and patterns.
    
    This extends the main testbench with additional test-oriented functionality
    while maintaining the same core interface.
    """

    def __init__(self, dut):
        """Initialize base test"""
        super().__init__(dut)
        
        # Test-specific attributes
        self.test_name = self.__class__.__name__
        self.test_description = getattr(self, 'DESCRIPTION', 'AXI Monitor Test')
        self.test_patterns = []
        self.error_scenarios = []
        self.performance_tests = []
        
        # Results tracking
        self.test_results = {}
        self.performance_metrics = {}
        self.error_detection_results = {}
        
        # Configuration overrides
        self.config_overrides = {}
        
        self.log.info(f"Initialized {self.test_name}: {self.test_description}")

    @abstractmethod
    async def run_test(self) -> bool:
        """
        Main test method to be implemented by derived classes.
        
        Returns:
            bool: True if test passed, False otherwise
        """
        pass

    async def setup_test_specific_config(self):
        """Apply test-specific configuration overrides"""
        if self.config_overrides:
            self.log.info("Applying test-specific configuration overrides...")
            
            for config_name, value in self.config_overrides.items():
                if hasattr(self.dut, f'cfg_{config_name}'):
                    getattr(self.dut, f'cfg_{config_name}').value = value
                    self.log.debug(f"  {config_name}: {value}")
            
            # Record the configuration change
            config = MonitorConfigPacket(
                field_config=self.config_field_config,
                **self.config_overrides
            )
            self.scoreboard.record_configuration(config)

    async def execute_transaction_pattern(self, pattern: TransactionPattern) -> bool:
        """Execute a predefined transaction pattern"""
        self.log.info(f"🔄 Executing pattern: {pattern.name}")
        
        issued_transactions = []
        pattern_start_time = get_sim_time('ns')
        
        for transaction in pattern.transactions:
            if transaction['type'] == 'delay':
                await self.wait_clocks('aclk', transaction['cycles'])
                continue
                
            # Apply delay before transaction
            if transaction.get('delay', 0) > 0:
                await self.wait_clocks('aclk', transaction['delay'])
            
            # Issue transaction
            if transaction['type'] == 'read':
                txn_id = await self.issue_read_transaction(
                    transaction['addr'],
                    transaction['length'],
                    expect_error=transaction.get('expect_error', False)
                )
            elif transaction['type'] == 'write':
                txn_id = await self.issue_write_transaction(
                    transaction['addr'],
                    transaction['length'],
                    expect_error=transaction.get('expect_error', False)
                )
            else:
                self.log.warning(f"Unknown transaction type: {transaction['type']}")
                continue
                
            issued_transactions.append(txn_id)
        
        # Wait for all transactions to complete
        completion_success = await self.wait_for_all_transactions_complete()
        
        pattern_duration = get_sim_time('ns') - pattern_start_time
        self.log.info(f"✅ Pattern {pattern.name} completed in {pattern_duration:.1f}ns")
        
        return completion_success

    async def execute_error_scenario(self, scenario: ErrorScenario) -> bool:
        """Execute an error injection scenario"""
        self.log.info(f"💥 Executing error scenario: {scenario.name}")
        
        scenario_start_time = get_sim_time('ns')
        
        # Execute setup steps
        for step in scenario.setup_steps:
            step_type = step['type']
            params = step['params']
            
            if step_type == 'configure_timeouts':
                for timeout_type, value in params.items():
                    if hasattr(self.dut, f'cfg_{timeout_type}_cnt'):
                        getattr(self.dut, f'cfg_{timeout_type}_cnt').value = value
                        
            elif step_type == 'disable_monitoring':
                for monitor_type in params.get('types', []):
                    if hasattr(self.dut, f'cfg_{monitor_type}_enable'):
                        getattr(self.dut, f'cfg_{monitor_type}_enable').value = 0
                        
            elif step_type == 'issue_transaction':
                if params.get('type') == 'read':
                    await self.issue_read_transaction(
                        params.get('addr', 0x1000),
                        params.get('length', 0)
                    )
                elif params.get('type') == 'write':
                    await self.issue_write_transaction(
                        params.get('addr', 0x1000),
                        params.get('length', 0)
                    )
        
        # Trigger the error condition
        if scenario.trigger_condition:
            trigger = scenario.trigger_condition
            if trigger['condition'] == 'timeout':
                await self.inject_timeout(trigger['params'].get('type', 'data'))
            elif trigger['condition'] == 'protocol_violation':
                await self.inject_protocol_violation(trigger['params'].get('type', 'orphaned_data'))
            elif trigger['condition'] == 'response_error':
                await self.inject_response_error(trigger['params'].get('type', 'SLVERR'))
        
        # Wait for monitor response
        await self.wait_clocks('aclk', 100)
        
        # Verify expected responses
        scenario_passed = True
        for expected_response in scenario.expected_responses:
            response_type = expected_response['type']
            
            if response_type == 'interrupt':
                expected_packet_type = expected_response['params'].get('packet_type')
                interrupt_found = False
                
                for interrupt in self.scoreboard.interrupt_packets:
                    if interrupt.get_packet_type_name() == expected_packet_type:
                        interrupt_found = True
                        break
                
                if not interrupt_found:
                    self.log.error(f"❌ Expected interrupt {expected_packet_type} not found")
                    scenario_passed = False
                    
            elif response_type == 'error_detection':
                expected_error_count = expected_response['params'].get('min_errors', 1)
                actual_errors = len(self.scoreboard.verification_errors)
                
                if actual_errors < expected_error_count:
                    self.log.error(f"❌ Expected {expected_error_count} errors, got {actual_errors}")
                    scenario_passed = False
        
        scenario_duration = get_sim_time('ns') - scenario_start_time
        status = "✅ PASSED" if scenario_passed else "❌ FAILED"
        self.log.info(f"{status} Error scenario {scenario.name} in {scenario_duration:.1f}ns")
        
        return scenario_passed

    async def execute_performance_test(self, perf_test: PerformanceTest) -> bool:
        """Execute a performance test"""
        self.log.info(f"📊 Executing performance test: {perf_test.name}")
        
        test_start_time = get_sim_time('ns')
        initial_stats = dict(self.test_stats)
        
        # Execute load pattern
        if perf_test.load_pattern:
            pattern_type = perf_test.load_pattern['type']
            params = perf_test.load_pattern['params']
            
            if pattern_type == 'constant_rate':
                transactions_per_cycle = params.get('rate', 0.1)
                transaction_count = int(perf_test.duration_cycles * transactions_per_cycle)
                
                for i in range(transaction_count):
                    if i % 2 == 0:
                        await self.issue_read_transaction(0x10000 + i * 0x100, 0)
                    else:
                        await self.issue_write_transaction(0x10000 + i * 0x100, 0)
                    
                    # Wait based on rate
                    if transactions_per_cycle < 1.0:
                        wait_cycles = int(1.0 / transactions_per_cycle)
                        await self.wait_clocks('aclk', wait_cycles)
                        
            elif pattern_type == 'burst':
                burst_size = params.get('burst_size', 5)
                burst_interval = params.get('interval', 100)
                num_bursts = perf_test.duration_cycles // burst_interval
                
                for burst in range(num_bursts):
                    # Issue burst of transactions
                    for i in range(burst_size):
                        addr = 0x20000 + burst * 0x1000 + i * 0x100
                        if i % 2 == 0:
                            await self.issue_read_transaction(addr, 0)
                        else:
                            await self.issue_write_transaction(addr, 0)
                    
                    # Wait for interval
                    await self.wait_clocks('aclk', burst_interval)
        
        # Wait for all transactions to complete
        await self.wait_for_all_transactions_complete()
        
        test_duration = get_sim_time('ns') - test_start_time
        
        # Calculate performance metrics
        final_stats = dict(self.test_stats)
        transactions_completed = (final_stats['transactions_issued'] - 
                                initial_stats['transactions_issued'])
        
        metrics = {
            'transactions_completed': transactions_completed,
            'test_duration_ns': test_duration,
            'throughput_tps': transactions_completed / (test_duration / 1e9) if test_duration > 0 else 0,
            'avg_latency_ns': test_duration / transactions_completed if transactions_completed > 0 else 0
        }
        
        self.performance_metrics[perf_test.name] = metrics
        
        # Check success criteria
        test_passed = True
        for metric, criteria in perf_test.success_criteria.items():
            if metric in metrics:
                actual_value = metrics[metric]
                threshold = criteria['threshold']
                comparison = criteria['comparison']
                
                if comparison == 'max' and actual_value > threshold:
                    self.log.error(f"❌ {metric} {actual_value} exceeds threshold {threshold}")
                    test_passed = False
                elif comparison == 'min' and actual_value < threshold:
                    self.log.error(f"❌ {metric} {actual_value} below threshold {threshold}")
                    test_passed = False
        
        status = "✅ PASSED" if test_passed else "❌ FAILED"
        self.log.info(f"{status} Performance test {perf_test.name}")
        self.log.info(f"  Throughput: {metrics['throughput_tps']:.1f} TPS")
        self.log.info(f"  Avg Latency: {metrics['avg_latency_ns']:.1f} ns")
        
        return test_passed

    def create_basic_read_pattern(self, base_addr: int = 0x1000, count: int = 5) -> TransactionPattern:
        """Create a basic read transaction pattern"""
        pattern = TransactionPattern("basic_reads", f"Basic read pattern with {count} transactions")
        
        for i in range(count):
            addr = base_addr + i * 0x100
            length = i % 4  # Vary length
            pattern.add_read(addr, length, delay=random.randint(1, 5))
            
        return pattern

    def create_basic_write_pattern(self, base_addr: int = 0x2000, count: int = 5) -> TransactionPattern:
        """Create a basic write transaction pattern"""
        pattern = TransactionPattern("basic_writes", f"Basic write pattern with {count} transactions")
        
        for i in range(count):
            addr = base_addr + i * 0x100
            length = i % 4  # Vary length  
            pattern.add_write(addr, length, delay=random.randint(1, 5))
            
        return pattern

    def create_mixed_pattern(self, base_addr: int = 0x3000, count: int = 10) -> TransactionPattern:
        """Create a mixed read/write pattern"""
        pattern = TransactionPattern("mixed_rw", f"Mixed R/W pattern with {count} transactions")
        
        for i in range(count):
            addr = base_addr + i * 0x100
            length = random.randint(0, 3)
            delay = random.randint(1, 10)
            
            if i % 2 == 0:
                pattern.add_read(addr, length, delay)
            else:
                pattern.add_write(addr, length, delay)
                
        return pattern

    def create_timeout_error_scenario(self) -> ErrorScenario:
        """Create a timeout error scenario"""
        scenario = ErrorScenario("timeout_test", "Test timeout detection")
        
        # Setup shorter timeout
        scenario.add_setup_step('configure_timeouts', addr=4, data=4, resp=4)
        
        # Issue transaction that will timeout
        scenario.add_setup_step('issue_transaction', type='read', addr=0x5000, length=0)
        
        # Trigger timeout
        scenario.set_trigger('timeout', type='data')
        
        # Expect timeout interrupt
        scenario.add_expected_response('interrupt', packet_type='TIMEOUT')
        
        return scenario

    def create_response_error_scenario(self) -> ErrorScenario:
        """Create a response error scenario"""
        scenario = ErrorScenario("response_error_test", "Test response error detection")
        
        # Issue normal transaction
        scenario.add_setup_step('issue_transaction', type='read', addr=0x6000, length=0)
        
        # Trigger response error
        scenario.set_trigger('response_error', type='SLVERR')
        
        # Expect error interrupt
        scenario.add_expected_response('interrupt', packet_type='ERROR')
        scenario.add_expected_response('error_detection', min_errors=1)
        
        return scenario

    def create_throughput_performance_test(self) -> PerformanceTest:
        """Create a throughput performance test"""
        perf_test = PerformanceTest("throughput_test", "Test transaction throughput")
        
        # Constant rate load
        perf_test.set_load_pattern('constant_rate', rate=0.2)  # 20% utilization
        perf_test.duration_cycles = 1000
        
        # Success criteria
        perf_test.add_success_criterion('throughput_tps', 100, 'min')  # Min 100 TPS
        perf_test.add_success_criterion('avg_latency_ns', 1000, 'max')  # Max 1000ns latency
        
        return perf_test

    async def run_all_patterns(self) -> bool:
        """Run all registered transaction patterns"""
        all_passed = True
        
        for pattern in self.test_patterns:
            passed = await self.execute_transaction_pattern(pattern)
            if not passed:
                all_passed = False
                
        return all_passed

    async def run_all_error_scenarios(self) -> bool:
        """Run all registered error scenarios"""
        all_passed = True
        
        for scenario in self.error_scenarios:
            passed = await self.execute_error_scenario(scenario)
            if not passed:
                all_passed = False
                
        return all_passed

    async def run_all_performance_tests(self) -> bool:
        """Run all registered performance tests"""
        all_passed = True
        
        for perf_test in self.performance_tests:
            passed = await self.execute_performance_test(perf_test)
            if not passed:
                all_passed = False
                
        return all_passed

    def print_test_specific_report(self):
        """Print test-specific report"""
        self.log.info(f"\n📋 {self.test_name} Specific Results:")
        
        if self.performance_metrics:
            self.log.info("Performance Metrics:")
            for test_name, metrics in self.performance_metrics.items():
                self.log.info(f"  {test_name}:")
                for metric, value in metrics.items():
                    self.log.info(f"    {metric}: {value}")
        
        if self.error_detection_results:
            self.log.info("Error Detection Results:")
            for error_type, detected in self.error_detection_results.items():
                status = "✅" if detected else "❌"
                self.log.info(f"  {status} {error_type}")

    async def run_base_test_flow(self) -> bool:
        """
        Standard test flow that can be used by derived classes.
        
        This provides a template that most tests can follow:
        1. Setup test-specific configuration
        2. Run the main test logic
        3. Generate reports
        """
        try:
            # Setup
            await self.setup_test_specific_config()
            
            # Run main test
            test_passed = await self.run_test()
            
            # Additional verification
            monitor_verification = self.scoreboard.verify_monitor_behavior()
            
            # Generate reports
            self.print_test_specific_report()
            
            overall_passed = test_passed and monitor_verification
            
            status = "✅ PASSED" if overall_passed else "❌ FAILED"
            self.log.info(f"{status} {self.test_name}")
            
            return overall_passed
            
        except Exception as e:
            self.log.error(f"❌ {self.test_name} failed with exception: {e}")
            import traceback
            self.log.error(f"Traceback: {traceback.format_exc()}")
            return False


# Example derived test class
class ExampleBasicTest(AXIMonitorBaseTest):
    """Example of how to use the base test class"""
    
    DESCRIPTION = "Example basic AXI monitor test using patterns"
    
    def __init__(self, dut):
        super().__init__(dut)
        
        # Configure test-specific settings
        self.config_overrides = {
            'addr_cnt': 0x10,
            'data_cnt': 0x10,
            'resp_cnt': 0x10
        }
        
        # Create test patterns
        self.test_patterns = [
            self.create_basic_read_pattern(),
            self.create_basic_write_pattern(),
            self.create_mixed_pattern()
        ]
        
        # Create error scenarios
        self.error_scenarios = [
            self.create_timeout_error_scenario(),
            self.create_response_error_scenario()
        ]
        
        # Create performance tests
        self.performance_tests = [
            self.create_throughput_performance_test()
        ]

    async def run_test(self) -> bool:
        """Main test implementation"""
        self.log.info(f"🧪 Running {self.test_name}")
        
        # Run transaction patterns
        patterns_passed = await self.run_all_patterns()
        
        # Run error scenarios
        errors_passed = await self.run_all_error_scenarios()
        
        # Run performance tests
        perf_passed = await self.run_all_performance_tests()
        
        return patterns_passed and errors_passed and perf_passed


# Cocotb test using the base class
@cocotb.test()
async def test_example_basic(dut):
    """Example test using the base test class"""
    test = ExampleBasicTest(dut)
    await test.setup_clocks_and_reset()
    result = await test.run_base_test_flow()
    await test.shutdown()
    
    if not result:
        raise cocotb.result.TestFailure("Example basic test failed")
    else:
        test.log.info("🎉 Example basic test passed!")
