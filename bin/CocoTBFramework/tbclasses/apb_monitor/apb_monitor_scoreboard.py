# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: APBScoreboardConfig
# Purpose: APB Monitor Scoreboard
#
# Documentation: bin/CocoTBFramework/README.md
# Subsystem: framework
#
# Author: sean galloway
# Created: 2025-10-18

"""
APB Monitor Scoreboard

Generic scoreboard for validating APB monitor behavior. Tracks transactions,
correlates with monitor bus packets, and validates expected monitor behavior.
Works both standalone and integrated with APB master/slave components.
"""

import time
from typing import Dict, List, Optional, Tuple, Any, Callable
from dataclasses import dataclass, field

from CocoTBFramework.tbclasses.monbus.monbus_components import (
    MonbusPacket, MonbusProtocol, MonbusPktType,
    APBErrorCode, APBTimeoutCode, APBCompletionCode,
    APBPerformanceCode, APBThresholdCode, APBDebugCode
)
from .apb_monitor_packets import (
    APBCommandPacket, APBResponsePacket, APBTransaction, APBTransactionState,
    APBMonitorEvent, APBMonitorEventType, format_packet_summary
)


@dataclass
class APBScoreboardConfig:
    """Configuration for APB scoreboard behavior"""

    # Transaction tracking
    max_transactions: int = 16
    transaction_timeout_ns: float = 10000.0  # 10us default timeout

    # Event validation
    event_timeout_ns: float = 1000.0  # 1us for monitor events
    strict_event_ordering: bool = False  # Require events in strict order

    # Error detection
    enable_protocol_checking: bool = True
    enable_performance_checking: bool = True
    enable_timeout_checking: bool = True

    # Latency thresholds for validation
    max_expected_latency_ns: float = 5000.0  # 5us max expected latency

    # APB-specific configuration
    enable_strobe_validation: bool = True
    enable_protection_validation: bool = True
    enable_phase_timing_validation: bool = True

    # Debug options
    verbose_logging: bool = False
    log_all_packets: bool = False


class APBMonitorScoreboard:
    """
    Generic scoreboard for APB monitor validation.

    Tracks APB transactions and correlates them with monitor bus events to validate
    that the monitor correctly detects and reports various conditions.
    """

    def __init__(self, log=None, component_name: str = "APB_MONITOR_SB",
                 config: Optional[APBScoreboardConfig] = None):
        """
        Initialize APB monitor scoreboard.

        Args:
            log: Logger instance
            component_name: Name for logging
            config: Scoreboard configuration
        """
        self.log = log
        self.component_name = component_name
        self.config = config or APBScoreboardConfig()

        # Transaction tracking
        self.active_transactions: Dict[int, APBTransaction] = {}
        self.completed_transactions: List[APBTransaction] = []
        self.transaction_id_counter = 0

        # Monitor event tracking
        self.monitor_packets: List[MonbusPacket] = []
        self.expected_events: List[APBMonitorEvent] = []
        self.matched_events: List[Tuple[APBMonitorEvent, MonbusPacket]] = []
        self.unmatched_events: List[MonbusPacket] = []

        # Statistics
        self.stats = {
            'transactions_started': 0,
            'transactions_completed': 0,
            'transactions_error': 0,
            'transactions_timeout': 0,
            'monitor_packets_received': 0,
            'expected_events_matched': 0,
            'unexpected_events': 0,
            'protocol_violations': 0,
            'performance_violations': 0,
            'strobe_violations': 0,
            'protection_violations': 0
        }

        # Error tracking
        self.verification_errors: List[Dict[str, Any]] = []
        self.protocol_violations: List[Dict[str, Any]] = []
        self.performance_violations: List[Dict[str, Any]] = []

        # Callbacks
        self.transaction_callbacks: List[Callable] = []
        self.event_callbacks: List[Callable] = []

        if self.log:
            self.log.info(f"APB Monitor Scoreboard initialized: {component_name}")

    def get_next_transaction_id(self) -> int:
        """Get next unique transaction ID"""
        self.transaction_id_counter += 1
        return self.transaction_id_counter

    def record_command(self, cmd_packet: APBCommandPacket, timestamp: float = None) -> int:
        """
        Record an APB command packet.

        Args:
            cmd_packet: Command packet
            timestamp: Timestamp (current time if None)

        Returns:
            Transaction ID
        """
        if timestamp is None:
            timestamp = time.time()

        txn_id = self.get_next_transaction_id()

        # Create new transaction
        transaction = APBTransaction(
            transaction_id=txn_id,
            timestamp_start=timestamp
        )
        transaction.add_command(cmd_packet, timestamp)

        self.active_transactions[txn_id] = transaction
        self.stats['transactions_started'] += 1

        # Validate command packet
        if self.config.enable_strobe_validation:
            strobe_errors = cmd_packet.validate_strobe_alignment()
            if strobe_errors:
                for error in strobe_errors:
                    transaction.add_error(f"Strobe validation: {error}")
                self.stats['strobe_violations'] += len(strobe_errors)

        # Validate protection settings
        if self.config.enable_protection_validation:
            prot_flags = cmd_packet.get_protection_flags()
            # Add any specific protection validation logic here
            if cmd_packet.is_secure_access() and cmd_packet.is_privileged_access():
                # Example: some systems might not allow secure+privileged
                pass

        if self.config.verbose_logging and self.log:
            self.log.debug(f"📝 CMD recorded: ID={txn_id:02X} {format_packet_summary(cmd_packet)}")

        # Call callbacks
        for callback in self.transaction_callbacks:
            try:
                callback('command', transaction)
            except Exception as e:
                if self.log:
                    self.log.error(f"Error in transaction callback: {e}")

        return txn_id

    def record_response(self, rsp_packet: APBResponsePacket, timestamp: float = None,
                       transaction_id: Optional[int] = None) -> bool:
        """
        Record an APB response packet.

        Args:
            rsp_packet: Response packet
            timestamp: Timestamp (current time if None)
            transaction_id: Specific transaction ID (auto-match if None)

        Returns:
            True if response was matched to a transaction
        """
        if timestamp is None:
            timestamp = time.time()

        # Find matching transaction
        target_txn_id = transaction_id
        if target_txn_id is None:
            # Auto-match to oldest pending transaction
            for txn_id, txn in self.active_transactions.items():
                if txn.state == APBTransactionState.CMD_SENT:
                    target_txn_id = txn_id
                    break

        if target_txn_id is None or target_txn_id not in self.active_transactions:
            self._record_error(
                "orphaned_response",
                f"Response packet with no matching command: {format_packet_summary(rsp_packet)}",
                timestamp
            )
            return False

        # Add response to transaction
        transaction = self.active_transactions[target_txn_id]
        transaction.add_response(rsp_packet, timestamp)

        # Move to completed transactions
        self.completed_transactions.append(transaction)
        del self.active_transactions[target_txn_id]

        # Update statistics
        if transaction.state == APBTransactionState.COMPLETE:
            self.stats['transactions_completed'] += 1
        elif transaction.state == APBTransactionState.ERROR:
            self.stats['transactions_error'] += 1

        # Validate completed transaction
        if self.config.enable_phase_timing_validation:
            self._validate_transaction_timing(transaction)

        if self.config.verbose_logging and self.log:
            self.log.debug(f"📝 RSP recorded: ID={target_txn_id:02X} {format_packet_summary(rsp_packet)}")

        # Call callbacks
        for callback in self.transaction_callbacks:
            try:
                callback('response', transaction)
            except Exception as e:
                if self.log:
                    self.log.error(f"Error in transaction callback: {e}")

        return True

    def record_monitor_packet(self, packet: MonbusPacket, timestamp: float = None):
        """
        Record a monitor bus packet.

        Args:
            packet: Monitor bus packet
            timestamp: Timestamp (current time if None)
        """
        if timestamp is None:
            timestamp = time.time()

        # Add timestamp to packet
        packet.timestamp = timestamp
        self.monitor_packets.append(packet)
        self.stats['monitor_packets_received'] += 1

        if self.config.log_all_packets and self.log:
            self.log.debug(f"📦 Monitor packet: {format_packet_summary(packet)}")

        # Try to match with expected events
        self._match_monitor_event(packet)

        # Associate with transactions if possible
        self._associate_packet_with_transaction(packet)

        # Call callbacks
        for callback in self.event_callbacks:
            try:
                callback(packet)
            except Exception as e:
                if self.log:
                    self.log.error(f"Error in event callback: {e}")

    def expect_monitor_event(self, event: APBMonitorEvent, timestamp_expected: float = None):
        """
        Register an expected monitor event.

        Args:
            event: Expected event
            timestamp_expected: When the event is expected (current time if None)
        """
        if timestamp_expected is None:
            timestamp_expected = time.time()

        event.timestamp_expected = timestamp_expected
        self.expected_events.append(event)

        if self.config.verbose_logging and self.log:
            self.log.debug(f"📋 Expected event: {event}")

    def expect_error_event(self, error_code: int, expected_addr: int = None,
                          tolerance_ns: float = None) -> APBMonitorEvent:
        """Convenience method to expect an error event"""
        if tolerance_ns is None:
            tolerance_ns = self.config.event_timeout_ns

        # Convert int to proper enum if possible
        try:
            apb_error = APBErrorCode(error_code)
            event = APBMonitorEvent.create_error_event(apb_error, expected_addr, tolerance_ns=tolerance_ns)
        except ValueError:
            # Fallback for invalid error codes
            event = APBMonitorEvent(APBMonitorEventType.ERROR, error_code, expected_addr, tolerance_ns)

        self.expect_monitor_event(event)
        return event

    def expect_completion_event(self, expected_addr: int = None,
                               tolerance_ns: float = None) -> APBMonitorEvent:
        """Convenience method to expect a completion event"""
        if tolerance_ns is None:
            tolerance_ns = self.config.event_timeout_ns

        event = APBMonitorEvent.create_completion_event(
            APBCompletionCode.TRANS_COMPLETE, expected_addr, tolerance_ns=tolerance_ns
        )
        self.expect_monitor_event(event)
        return event

    def expect_timeout_event(self, timeout_code: int, expected_addr: int = None,
                            tolerance_ns: float = None) -> APBMonitorEvent:
        """Convenience method to expect a timeout event"""
        if tolerance_ns is None:
            tolerance_ns = self.config.event_timeout_ns

        # Convert int to proper enum if possible
        try:
            apb_timeout = APBTimeoutCode(timeout_code)
            event = APBMonitorEvent.create_timeout_event(apb_timeout, expected_addr, tolerance_ns=tolerance_ns)
        except ValueError:
            # Fallback for invalid timeout codes
            event = APBMonitorEvent(APBMonitorEventType.TIMEOUT, timeout_code, expected_addr, tolerance_ns)

        self.expect_monitor_event(event)
        return event

    def expect_performance_event(self, perf_code: APBPerformanceCode, expected_data: int = None,
                                tolerance_ns: float = None) -> APBMonitorEvent:
        """Convenience method to expect a performance event"""
        if tolerance_ns is None:
            tolerance_ns = self.config.event_timeout_ns

        event = APBMonitorEvent.create_performance_event(perf_code, expected_data, tolerance_ns=tolerance_ns)
        self.expect_monitor_event(event)
        return event

    def expect_debug_event(self, debug_code: APBDebugCode, expected_data: int = None,
                          tolerance_ns: float = None) -> APBMonitorEvent:
        """Convenience method to expect a debug event"""
        if tolerance_ns is None:
            tolerance_ns = self.config.event_timeout_ns

        event = APBMonitorEvent.create_debug_event(debug_code, expected_data, tolerance_ns=tolerance_ns)
        self.expect_monitor_event(event)
        return event

    def _match_monitor_event(self, packet: MonbusPacket):
        """Try to match a monitor packet with expected events"""
        for i, expected_event in enumerate(self.expected_events):
            if expected_event.found_event is None and expected_event.matches_packet(packet):
                expected_event.found_event = packet
                self.matched_events.append((expected_event, packet))
                self.stats['expected_events_matched'] += 1

                if self.config.verbose_logging and self.log:
                    self.log.debug(f"✅ Matched expected event: {expected_event}")
                return

        # No match found - this is unexpected
        self.unmatched_events.append(packet)
        self.stats['unexpected_events'] += 1

        if self.log:
            self.log.warning(f"❓ Unexpected monitor event: {format_packet_summary(packet)}")

    def _associate_packet_with_transaction(self, packet: MonbusPacket):
        """Associate monitor packet with relevant transactions"""
        # Try to match packet address with transaction addresses
        packet_addr = packet.data & 0xFFFFFFFF

        # Check active transactions first
        for txn in self.active_transactions.values():
            if txn.get_address() == packet_addr:
                txn.add_monitor_event(packet)
                return

        # Check recently completed transactions
        for txn in self.completed_transactions[-10:]:  # Last 10 transactions
            if txn.get_address() == packet_addr:
                txn.add_monitor_event(packet)
                return

    def _record_error(self, error_type: str, message: str, timestamp: float):
        """Record a verification error"""
        error = {
            'type': error_type,
            'message': message,
            'timestamp': timestamp,
            'component': self.component_name
        }
        self.verification_errors.append(error)

        if self.log:
            self.log.error(f"❌ {error_type.upper()}: {message}")

    def _validate_transaction_timing(self, transaction: APBTransaction):
        """Validate APB transaction timing"""
        if not transaction.total_latency:
            return

        # Check if latency exceeds threshold
        if transaction.total_latency > (self.config.max_expected_latency_ns / 1e9):
            self.performance_violations.append({
                'type': 'latency_violation',
                'transaction': transaction,
                'latency_ns': transaction.total_latency * 1e9,
                'threshold_ns': self.config.max_expected_latency_ns
            })
            self.stats['performance_violations'] += 1

    def check_timeout_transactions(self, current_time: float = None) -> List[APBTransaction]:
        """Check for timed out transactions and mark them"""
        if current_time is None:
            current_time = time.time()

        timed_out = []

        for txn_id, txn in list(self.active_transactions.items()):
            if (current_time - txn.timestamp_start) > (self.config.transaction_timeout_ns / 1e9):
                txn.mark_timeout()
                self.completed_transactions.append(txn)
                del self.active_transactions[txn_id]
                timed_out.append(txn)
                self.stats['transactions_timeout'] += 1

                self._record_error(
                    "transaction_timeout",
                    f"Transaction {txn_id:02X} timed out after {self.config.transaction_timeout_ns}ns",
                    current_time
                )

        return timed_out

    def check_expected_events(self, current_time: float = None) -> List[APBMonitorEvent]:
        """Check for expected events that haven't been matched"""
        if current_time is None:
            current_time = time.time()

        missing_events = []

        for event in self.expected_events:
            if (event.found_event is None and
                event.timestamp_expected is not None and
                (current_time - event.timestamp_expected) > (event.tolerance_ns / 1e9)):

                missing_events.append(event)
                self._record_error(
                    "missing_monitor_event",
                    f"Expected monitor event not found: {event}",
                    current_time
                )

        return missing_events

    def verify_monitor_behavior(self) -> bool:
        """
        Comprehensive verification of monitor behavior.

        Returns:
            True if all verifications pass
        """
        if self.log:
            self.log.info("🔍 Verifying APB monitor behavior...")

        verification_passed = True

        # Check for timeouts
        self.check_timeout_transactions()
        self.check_expected_events()

        # Verify expected events were matched
        unmatched_expected = [e for e in self.expected_events if e.found_event is None]
        if unmatched_expected:
            verification_passed = False
            for event in unmatched_expected:
                self._record_error(
                    "unmatched_expected_event",
                    f"Expected event never occurred: {event}",
                    time.time()
                )

        # Check for protocol violations
        if self.config.enable_protocol_checking:
            verification_passed &= self._check_protocol_compliance()

        # Check performance violations
        if self.config.enable_performance_checking:
            verification_passed &= self._check_performance_compliance()

        # Log results
        if self.log:
            status = "✅ PASSED" if verification_passed else "❌ FAILED"
            self.log.info(f"{status} APB monitor verification")
            self.log.info(f"  Transactions: {self.stats['transactions_completed']} completed, "
                         f"{self.stats['transactions_error']} errors, "
                         f"{self.stats['transactions_timeout']} timeouts")
            self.log.info(f"  Monitor events: {self.stats['monitor_packets_received']} received, "
                         f"{self.stats['expected_events_matched']} matched, "
                         f"{self.stats['unexpected_events']} unexpected")

        return verification_passed

    def _check_protocol_compliance(self) -> bool:
        """Check for APB protocol violations"""
        violations_found = False

        # Check for orphaned responses
        if len(self.unmatched_events) > 0:
            # Look for error events indicating protocol violations
            for packet in self.unmatched_events:
                if (packet.is_error_packet() and
                    packet.event_code in [APBErrorCode.SETUP_VIOLATION.value,
                                         APBErrorCode.ACCESS_VIOLATION.value,
                                         APBErrorCode.PROT_VIOLATION.value]):
                    violations_found = True
                    self.protocol_violations.append({
                        'type': 'protocol_violation',
                        'packet': packet,
                        'timestamp': packet.timestamp
                    })
                    self.stats['protocol_violations'] += 1

        return not violations_found

    def _check_performance_compliance(self) -> bool:
        """Check for performance violations"""
        violations_found = False

        # Check transaction latencies
        for txn in self.completed_transactions:
            if (txn.total_latency is not None and
                txn.total_latency > (self.config.max_expected_latency_ns / 1e9)):
                violations_found = True

        return not violations_found

    def get_statistics(self) -> Dict[str, Any]:
        """Get comprehensive statistics"""
        stats = self.stats.copy()

        # Add derived statistics
        if stats['transactions_started'] > 0:
            stats['completion_rate'] = stats['transactions_completed'] / stats['transactions_started']
            stats['error_rate'] = stats['transactions_error'] / stats['transactions_started']
        else:
            stats['completion_rate'] = 0.0
            stats['error_rate'] = 0.0

        stats['active_transactions'] = len(self.active_transactions)
        stats['verification_errors'] = len(self.verification_errors)

        # Latency statistics
        completed_latencies = [txn.total_latency for txn in self.completed_transactions
                              if txn.total_latency is not None]
        if completed_latencies:
            stats['avg_latency_ns'] = (sum(completed_latencies) / len(completed_latencies)) * 1e9
            stats['max_latency_ns'] = max(completed_latencies) * 1e9
            stats['min_latency_ns'] = min(completed_latencies) * 1e9
        else:
            stats['avg_latency_ns'] = 0.0
            stats['max_latency_ns'] = 0.0
            stats['min_latency_ns'] = 0.0

        return stats

    def get_comprehensive_report(self) -> str:
        """Generate a comprehensive validation report"""
        stats = self.get_statistics()

        report = f"\n📊 {self.component_name} Validation Report\n"
        report += "=" * 60 + "\n"

        # Transaction statistics
        report += f"📝 Transaction Statistics:\n"
        report += f"  Started: {stats['transactions_started']}\n"
        report += f"  Completed: {stats['transactions_completed']}\n"
        report += f"  Errors: {stats['transactions_error']}\n"
        report += f"  Timeouts: {stats['transactions_timeout']}\n"
        report += f"  Active: {stats['active_transactions']}\n"
        report += f"  Completion Rate: {stats['completion_rate']:.1%}\n"
        report += f"  Error Rate: {stats['error_rate']:.1%}\n\n"

        # Latency statistics
        if stats['avg_latency_ns'] > 0:
            report += f"⏱️  Latency Statistics:\n"
            report += f"  Average: {stats['avg_latency_ns']:.1f} ns\n"
            report += f"  Maximum: {stats['max_latency_ns']:.1f} ns\n"
            report += f"  Minimum: {stats['min_latency_ns']:.1f} ns\n\n"

        # Monitor event statistics
        report += f"📦 Monitor Event Statistics:\n"
        report += f"  Packets Received: {stats['monitor_packets_received']}\n"
        report += f"  Expected Matched: {stats['expected_events_matched']}\n"
        report += f"  Unexpected Events: {stats['unexpected_events']}\n\n"

        # APB-specific statistics
        report += f"🔧 APB-Specific Validation:\n"
        report += f"  Strobe Violations: {stats['strobe_violations']}\n"
        report += f"  Protocol Violations: {stats['protocol_violations']}\n"
        report += f"  Performance Violations: {stats['performance_violations']}\n"
        report += f"  Protection Violations: {stats['protection_violations']}\n\n"

        # Error summary
        if stats['verification_errors'] > 0:
            report += f"❌ Verification Errors ({stats['verification_errors']}):\n"
            for error in self.verification_errors[-5:]:  # Show last 5
                report += f"  - {error['type']}: {error['message']}\n"
            report += "\n"
        else:
            report += "✅ No verification errors detected\n\n"

        return report

    def reset(self):
        """Reset scoreboard state"""
        self.active_transactions.clear()
        self.completed_transactions.clear()
        self.monitor_packets.clear()
        self.expected_events.clear()
        self.matched_events.clear()
        self.unmatched_events.clear()
        self.verification_errors.clear()
        self.protocol_violations.clear()
        self.performance_violations.clear()

        # Reset statistics
        for key in self.stats:
            self.stats[key] = 0

        self.transaction_id_counter = 0

        if self.log:
            self.log.info(f"APB Monitor Scoreboard reset: {self.component_name}")

    def add_transaction_callback(self, callback: Callable):
        """Add callback for transaction events"""
        self.transaction_callbacks.append(callback)

    def add_event_callback(self, callback: Callable):
        """Add callback for monitor events"""
        self.event_callbacks.append(callback)
