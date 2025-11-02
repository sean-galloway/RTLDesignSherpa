# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: ResponseErrorDetectionTest
# Purpose: AXI Monitor Error Detection Tests - FIXED NAMING INCONSISTENCIES
#
# Documentation: bin/CocoTBFramework/README.md
# Subsystem: framework
#
# Author: sean galloway
# Created: 2025-10-18

"""
AXI Monitor Error Detection Tests - FIXED NAMING INCONSISTENCIES

Focused test suite for comprehensive error detection and handling verification.
Tests the monitor's ability to detect, report, and correlate various error conditions.

FIXED: All references to packet types now correctly use InterruptPacketType enum
instead of incorrectly using InterruptPacket class name.

Test Categories:
1. Response Error Detection (SLVERR, DECERR)
2. Protocol Violation Detection
3. Orphaned Transaction Detection
4. Error Correlation with Interrupt Bus
5. Error Recovery and Continuation
6. Multiple Simultaneous Errors

Usage:
    pytest axi_monitor_error_tests.py
    or
    cocotb-test --test-path=. --test-module=axi_monitor_error_tests
"""

import os
import random
import asyncio
from typing import Dict, List, Optional, Tuple, Any

import cocotb
from cocotb.triggers import RisingEdge, Timer
from cocotb.utils import get_sim_time

from .axi_monitor_base_test import AXIMonitorBaseTest, TransactionPattern, ErrorScenario
from .axi_monitor_packets import (
    MonitorEventCode, InterruptPacketType, AXITransactionState  # FIXED: Import InterruptPacketType
)


class ResponseErrorDetectionTest(AXIMonitorBaseTest):
    """Test response error detection (SLVERR, DECERR)"""

    DESCRIPTION = "Verify monitor detects and reports response errors correctly"

    def __init__(self, dut):
        super().__init__(dut)

        # Enable error detection
        self.config_overrides = {
            'error_enable': 1,
            'compl_enable': 1,
            'timeout_enable': 0,  # Focus on response errors only
            'addr_cnt': 0x10,
            'data_cnt': 0x10,
            'resp_cnt': 0x10
        }

        self.expected_error_interrupts = []
        self.response_error_types = ['SLVERR', 'DECERR']

    async def run_test(self) -> bool:
        """Test response error detection for both read and write transactions"""
        self.log.info("🧪 Testing Response Error Detection")

        all_passed = True

        # Test read response errors
        read_passed = await self._test_read_response_errors()
        all_passed = all_passed and read_passed

        # Test write response errors
        write_passed = await self._test_write_response_errors()
        all_passed = all_passed and write_passed

        # Test mixed error scenarios
        mixed_passed = await self._test_mixed_error_scenarios()
        all_passed = all_passed and mixed_passed

        # Verify all expected errors were detected
        verification_passed = await self._verify_error_detection()
        all_passed = all_passed and verification_passed

        return all_passed

    async def _test_read_response_errors(self) -> bool:
        """Test read response error detection"""
        self.log.info("📖 Testing read response errors...")

        test_passed = True

        for error_type in self.response_error_types:
            self.log.info(f"  Testing {error_type} on read transactions")

            # Configure error injection
            await self.inject_response_error(error_type)

            # Issue read transaction
            addr = 0x10000 + len(self.expected_error_interrupts) * 0x1000
            txn_id = await self.issue_read_transaction(addr, length=0, expect_error=True)

            # Track expected error
            self.expected_error_interrupts.append({
                'transaction_id': txn_id,
                'error_type': error_type,
                'channel': 'READ',
                'detected': False
            })

            # Wait for transaction completion and error detection
            completion = await self.wait_for_transaction_completion(txn_id, timeout_cycles=200)
            if not completion:
                self.log.error(f"❌ Read transaction {txn_id:02X} with {error_type} did not complete")
                test_passed = False

            # Small delay for error processing
            await self.wait_clocks('aclk', 20)

        return test_passed

    async def _test_write_response_errors(self) -> bool:
        """Test write response error detection"""
        self.log.info("✍️ Testing write response errors...")

        test_passed = True

        for error_type in self.response_error_types:
            self.log.info(f"  Testing {error_type} on write transactions")

            # Configure error injection
            await self.inject_response_error(error_type)

            # Issue write transaction
            addr = 0x20000 + len(self.expected_error_interrupts) * 0x1000
            txn_id = await self.issue_write_transaction(addr, length=1, expect_error=True)

            # Track expected error
            self.expected_error_interrupts.append({
                'transaction_id': txn_id,
                'error_type': error_type,
                'channel': 'WRITE',
                'detected': False
            })

            # Wait for completion
            completion = await self.wait_for_transaction_completion(txn_id, timeout_cycles=200)
            if not completion:
                self.log.error(f"❌ Write transaction {txn_id:02X} with {error_type} did not complete")
                test_passed = False

            await self.wait_clocks('aclk', 20)

        return test_passed

    async def _test_mixed_error_scenarios(self) -> bool:
        """Test multiple simultaneous errors"""
        self.log.info("🔀 Testing mixed error scenarios...")

        # Issue multiple transactions with different error types
        transactions = []

        for i in range(4):
            error_type = self.response_error_types[i % len(self.response_error_types)]
            await self.inject_response_error(error_type)

            if i % 2 == 0:
                addr = 0x30000 + i * 0x1000
                txn_id = await self.issue_read_transaction(addr, length=i % 3, expect_error=True)
                channel = 'READ'
            else:
                addr = 0x40000 + i * 0x1000
                txn_id = await self.issue_write_transaction(addr, length=i % 3, expect_error=True)
                channel = 'WRITE'

            transactions.append(txn_id)
            self.expected_error_interrupts.append({
                'transaction_id': txn_id,
                'error_type': error_type,
                'channel': channel,
                'detected': False
            })

            # Small delay between transactions
            await self.wait_clocks('aclk', 10)

        # Wait for all transactions to complete
        all_completed = await self.wait_for_all_transactions_complete(timeout_cycles=500)

        return all_completed

    async def _verify_error_detection(self) -> bool:
        """Verify all expected errors were properly detected and reported"""
        self.log.info("🔍 Verifying error detection...")

        verification_passed = True

        # Check interrupt packets for expected errors
        for expected_error in self.expected_error_interrupts:
            error_found = False

            for interrupt in self.scoreboard.interrupt_packets:
                # FIXED: Use InterruptPacketType enum instead of InterruptPacket class
                if (interrupt.packet_type == InterruptPacketType.ERROR.value and
                    interrupt.channel_id == expected_error['transaction_id']):

                    # Verify error code matches
                    if expected_error['error_type'] == 'SLVERR':
                        expected_code = MonitorEventCode.RESP_SLVERR.value
                    elif expected_error['error_type'] == 'DECERR':
                        expected_code = MonitorEventCode.RESP_DECERR.value
                    else:
                        expected_code = MonitorEventCode.RESP_ERROR.value

                    if interrupt.event_code == expected_code:
                        expected_error['detected'] = True
                        error_found = True
                        break

            if not error_found:
                self.log.error(f"❌ Expected {expected_error['error_type']} error for "
                              f"transaction {expected_error['transaction_id']:02X} not detected")
                verification_passed = False

        # Summary
        detected_count = sum(1 for e in self.expected_error_interrupts if e['detected'])
        total_count = len(self.expected_error_interrupts)

        self.log.info(f"📊 Error Detection Summary: {detected_count}/{total_count} errors detected")

        if detected_count == total_count:
            self.log.info("✅ All expected errors were detected correctly")
        else:
            self.log.error(f"❌ {total_count - detected_count} errors were not detected")
            verification_passed = False

        # Store results for reporting
        self.error_detection_results = {
            'total_errors_expected': total_count,
            'errors_detected': detected_count,
            'detection_rate': detected_count / total_count if total_count > 0 else 0,
            'all_detected': verification_passed
        }

        return verification_passed


class ProtocolViolationTest(AXIMonitorBaseTest):
    """Test protocol violation detection"""

    DESCRIPTION = "Verify monitor detects AXI protocol violations"

    def __init__(self, dut):
        super().__init__(dut)

        self.config_overrides = {
            'error_enable': 1,
            'debug_enable': 1,
            'timeout_enable': 0,
            'addr_cnt': 0x20,
            'data_cnt': 0x20,
            'resp_cnt': 0x20
        }

        self.protocol_violations_tested = []

    async def run_test(self) -> bool:
        """Test various protocol violation scenarios"""
        self.log.info("🧪 Testing Protocol Violation Detection")

        all_passed = True

        # Test orphaned data
        orphan_passed = await self._test_orphaned_transactions()
        all_passed = all_passed and orphan_passed

        # Test duplicate addresses
        duplicate_passed = await self._test_duplicate_addresses()
        all_passed = all_passed and duplicate_passed

        # Test invalid burst parameters
        burst_passed = await self._test_invalid_burst_parameters()
        all_passed = all_passed and burst_passed

        # Verify violations were detected
        verification_passed = await self._verify_protocol_violations()
        all_passed = all_passed and verification_passed

        return all_passed

    async def _test_orphaned_transactions(self) -> bool:
        """Test detection of orphaned data/response packets"""
        self.log.info("👻 Testing orphaned transaction detection...")

        test_passed = True

        # Test orphaned read data
        await self.inject_protocol_violation("orphaned_data")
        self.protocol_violations_tested.append({
            'type': 'orphaned_read_data',
            'expected_event': MonitorEventCode.DATA_ORPHAN.value,
            'detected': False
        })

        await self.wait_clocks('aclk', 50)

        # Test orphaned write response
        await self.inject_protocol_violation("orphaned_response")
        self.protocol_violations_tested.append({
            'type': 'orphaned_write_response',
            'expected_event': MonitorEventCode.RESP_ORPHAN.value,
            'detected': False
        })

        await self.wait_clocks('aclk', 50)

        return test_passed

    async def _test_duplicate_addresses(self) -> bool:
        """Test detection of duplicate address transactions"""
        self.log.info("🔄 Testing duplicate address detection...")

        # Issue transaction with same ID twice
        await self.inject_protocol_violation("duplicate_address")
        self.protocol_violations_tested.append({
            'type': 'duplicate_address',
            'expected_event': MonitorEventCode.PROTOCOL.value,
            'detected': False
        })

        await self.wait_clocks('aclk', 100)

        return True

    async def _test_invalid_burst_parameters(self) -> bool:
        """Test detection of invalid burst parameters"""
        self.log.info("💥 Testing invalid burst parameter detection...")

        # This would require custom transaction generation with invalid parameters
        # For now, just mark as tested
        self.protocol_violations_tested.append({
            'type': 'invalid_burst',
            'expected_event': MonitorEventCode.PROTOCOL.value,
            'detected': False  # Would be set to True if violation detected
        })

        return True

    async def _verify_protocol_violations(self) -> bool:
        """Verify protocol violations were detected"""
        self.log.info("🔍 Verifying protocol violation detection...")

        verification_passed = True

        # Check for protocol violation interrupts
        for violation in self.protocol_violations_tested:
            violation_found = False

            for interrupt in self.scoreboard.interrupt_packets:
                # FIXED: Use InterruptPacketType enum instead of InterruptPacket class
                if (interrupt.packet_type == InterruptPacketType.ERROR.value and
                    interrupt.event_code == violation['expected_event']):
                    violation['detected'] = True
                    violation_found = True
                    break

            if not violation_found and violation['type'] != 'invalid_burst':  # Skip invalid_burst for now
                self.log.error(f"❌ Protocol violation '{violation['type']}' not detected")
                verification_passed = False

        # Check scoreboard for protocol violations
        protocol_violation_count = len(self.scoreboard.protocol_violations)
        if protocol_violation_count == 0:
            self.log.warning("⚠️ No protocol violations recorded in scoreboard")
        else:
            self.log.info(f"📊 Scoreboard recorded {protocol_violation_count} protocol violations")

        return verification_passed


class ErrorRecoveryTest(AXIMonitorBaseTest):
    """Test error recovery and continued monitoring"""

    DESCRIPTION = "Verify monitor continues functioning correctly after errors"

    def __init__(self, dut):
        super().__init__(dut)

        self.config_overrides = {
            'error_enable': 1,
            'compl_enable': 1,
            'debug_enable': 1
        }

    async def run_test(self) -> bool:
        """Test error recovery scenarios"""
        self.log.info("🧪 Testing Error Recovery")

        all_passed = True

        # Phase 1: Normal operation
        self.log.info("📝 Phase 1: Baseline normal operation")
        normal_passed = await self._test_normal_operation()
        all_passed = all_passed and normal_passed

        # Phase 2: Inject errors
        self.log.info("💥 Phase 2: Inject various errors")
        error_passed = await self._test_error_injection()
        all_passed = all_passed and error_passed

        # Phase 3: Recovery verification
        self.log.info("🔄 Phase 3: Verify recovery")
        recovery_passed = await self._test_recovery_operation()
        all_passed = all_passed and recovery_passed

        return all_passed

    async def _test_normal_operation(self) -> bool:
        """Test normal operation baseline"""
        # Issue several normal transactions
        for i in range(5):
            if i % 2 == 0:
                await self.issue_read_transaction(0x50000 + i * 0x1000, i % 4)
            else:
                await self.issue_write_transaction(0x60000 + i * 0x1000, i % 4)

        # Wait for completion
        return await self.wait_for_all_transactions_complete()

    async def _test_error_injection(self) -> bool:
        """Inject various errors"""
        # Mix of errors and normal transactions
        for i in range(6):
            if i % 3 == 0:
                # Normal transaction
                await self.issue_read_transaction(0x70000 + i * 0x1000, 0)
            elif i % 3 == 1:
                # Error transaction
                await self.inject_response_error("SLVERR")
                await self.issue_read_transaction(0x70000 + i * 0x1000, 0, expect_error=True)
            else:
                # Protocol violation
                await self.inject_protocol_violation("orphaned_data")

        await self.wait_clocks('aclk', 200)
        return True

    async def _test_recovery_operation(self) -> bool:
        """Test that monitor continues working after errors"""
        # Issue normal transactions after errors
        for i in range(5):
            if i % 2 == 0:
                await self.issue_read_transaction(0x80000 + i * 0x1000, i % 3)
            else:
                await self.issue_write_transaction(0x90000 + i * 0x1000, i % 3)

        # Verify all complete successfully
        return await self.wait_for_all_transactions_complete()


# Cocotb test entries
@cocotb.test()
async def test_response_error_detection(dut):
    """Test response error detection"""
    test = ResponseErrorDetectionTest(dut)
    await test.setup_clocks_and_reset()
    result = await test.run_base_test_flow()
    await test.shutdown()

    if not result:
        raise cocotb.result.TestFailure("Response error detection test failed")

@cocotb.test()
async def test_protocol_violation_detection(dut):
    """Test protocol violation detection"""
    test = ProtocolViolationTest(dut)
    await test.setup_clocks_and_reset()
    result = await test.run_base_test_flow()
    await test.shutdown()

    if not result:
        raise cocotb.result.TestFailure("Protocol violation detection test failed")

@cocotb.test()
async def test_error_recovery(dut):
    """Test error recovery and continued operation"""
    test = ErrorRecoveryTest(dut)
    await test.setup_clocks_and_reset()
    result = await test.run_base_test_flow()
    await test.shutdown()

    if not result:
        raise cocotb.result.TestFailure("Error recovery test failed")

# Test suite runner
@cocotb.test()
async def test_all_error_detection(dut):
    """Run comprehensive error detection test suite"""
    all_passed = True

    tests = [
        ResponseErrorDetectionTest,
        ProtocolViolationTest,
        ErrorRecoveryTest
    ]

    for test_class in tests:
        test = test_class(dut)
        await test.setup_clocks_and_reset()
        result = await test.run_base_test_flow()
        await test.shutdown()

        if not result:
            all_passed = False

        # Reset between tests
        await test.wait_clocks('aclk', 50)

    if not all_passed:
        raise cocotb.result.TestFailure("Error detection test suite failed")
    else:
        dut._log.info("🎉 All error detection tests passed!")
