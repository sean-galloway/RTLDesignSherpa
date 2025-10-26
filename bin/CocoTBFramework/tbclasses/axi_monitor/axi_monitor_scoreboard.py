# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: AXIMonitorScoreboard
# Purpose: AXI4/AXIL Monitor Scoreboard - FIXED NAMING INCONSISTENCIES
#
# Documentation: bin/CocoTBFramework/README.md
# Subsystem: framework
#
# Author: sean galloway
# Created: 2025-10-18

"""
AXI4/AXIL Monitor Scoreboard - FIXED NAMING INCONSISTENCIES

Fixed the naming inconsistency between InterruptPacket (class) and InterruptPacketType (enum).
All references to packet types now correctly use InterruptPacketType enum.
"""

import os
from collections import deque, defaultdict
from typing import Dict, List, Optional, Tuple, Any, Set
import time

from cocotb.utils import get_sim_time

from .axi_monitor_packets import (
    AXICommandPacket, AXIReadDataPacket, AXIWriteDataPacket, AXIWriteResponsePacket,
    InterruptPacket, MonitorConfigPacket, MonitoredTransaction,
    AXITransactionState, MonitorEventCode, InterruptPacketType, PerformanceMetric,  # FIXED: Use InterruptPacketType
    convert_gaxi_to_axi_address, convert_gaxi_to_axi_read_data,
    convert_gaxi_to_axi_write_data, convert_gaxi_to_axi_write_response,
    convert_raw_to_interrupt_packet,
    create_axi_command_field_config, create_axi_read_data_field_config,
    create_axi_write_data_field_config, create_axi_write_response_field_config,
    create_interrupt_packet_field_config, create_monitor_config_field_config
)


class AXIMonitorScoreboard:
    """
    Comprehensive AXI Monitor Scoreboard with protocol verification,
    error detection validation, and interrupt bus correlation.
    FIXED: All packet type references now use InterruptPacketType enum.
    """

    def __init__(self, log=None, component_name: str = "AXI_MONITOR_SB",
                    id_width: int = 8, addr_width: int = 32, data_width: int = 32, user_width: int = 1,
                    is_axi4: bool = True, max_transactions: int = 16):
        """Initialize the AXI monitor scoreboard"""

        self.log = log
        self.component_name = component_name

        # Configuration parameters
        self.id_width = id_width
        self.addr_width = addr_width
        self.data_width = data_width
        self.user_width = user_width
        self.is_axi4 = is_axi4
        self.max_transactions = max_transactions

        # Create field configurations for all packet types
        self.addr_field_config = create_axi_command_field_config(id_width, addr_width, user_width)
        self.read_data_field_config = create_axi_read_data_field_config(id_width, data_width, user_width)
        self.write_data_field_config = create_axi_write_data_field_config(data_width, user_width)
        self.write_resp_field_config = create_axi_write_response_field_config(id_width, user_width)
        self.interrupt_field_config = create_interrupt_packet_field_config()
        self.config_field_config = create_monitor_config_field_config()

        # Transaction tracking
        self.active_transactions = {}  # id -> MonitoredTransaction
        self.completed_transactions = {}  # id -> MonitoredTransaction (recent history)
        self.orphaned_packets = []  # Packets without matching transactions

        # Interrupt bus tracking
        self.interrupt_packets = []  # List[InterruptPacket] - FIXED: This is correct (list of packet instances)
        self.interrupt_correlation = {}  # Maps interrupt packets to transactions

        # Configuration tracking
        self.current_config = None  # MonitorConfigPacket
        self.config_history = []  # List of configuration changes

        # Error and event tracking
        self.protocol_violations = []
        self.timeout_events = []
        self.error_events = []
        self.performance_violations = []

        # Statistics
        self.stats = {
            'read_transactions': 0,
            'write_transactions': 0,
            'completed_transactions': 0,
            'error_transactions': 0,
            'timeout_events': 0,
            'protocol_violations': 0,
            'interrupt_packets': 0,
            'orphaned_packets': 0,
            'config_updates': 0
        }

        # Timing tracking using cocotb
        self.transaction_start_times = {}  # id -> start_time
        self.transaction_end_times = {}    # id -> end_time

        # Verification results
        self.verification_errors = []
        self.verification_warnings = []

        if self.log:
            self.log.info(f"{component_name} initialized for {'AXI4' if is_axi4 else 'AXI-Lite'}")
            self.log.info(f"  ID Width: {id_width}, Addr Width: {addr_width}, Data Width: {data_width}")
            self.log.info(f"  Max Transactions: {max_transactions}")

    def get_current_time_ns(self) -> float:
        """Get current simulation time in nanoseconds"""
        return get_sim_time('ns')

    def get_time_str(self) -> str:
        """Get formatted time string"""
        time_ns = self.get_current_time_ns()
        return f' @ {time_ns:.1f}ns'

    def record_read_address(self, packet) -> None:
        """Record a read address transaction (AR channel)"""
        current_time = self.get_current_time_ns()

        # Convert to AXI address packet if needed
        if not isinstance(packet, AXICommandPacket):
            ar_packet = convert_gaxi_to_axi_address(packet, self.addr_field_config)
        else:
            ar_packet = packet

        # Create or update monitored transaction
        txn_id = ar_packet.id
        if txn_id in self.active_transactions:
            # Unexpected - transaction already exists
            self._add_protocol_violation(
                f"Duplicate read address for ID {txn_id:02X}",
                txn_id, current_time
            )
            return

        # Create new transaction
        monitored_txn = MonitoredTransaction(
            transaction_id=txn_id,
            is_read=True,
            is_axi4=self.is_axi4,
            address_packet=ar_packet,
            address_timestamp=current_time,
            state=AXITransactionState.ADDR_PHASE,
            start_time=current_time
        )

        self.active_transactions[txn_id] = monitored_txn
        self.transaction_start_times[txn_id] = current_time
        self.stats['read_transactions'] += 1

        if self.log:
            time_str = self.get_time_str()
            self.log.debug(f"📍 AR{time_str}: ID={txn_id:02X} ADDR=0x{ar_packet.addr:08X} "
                          f"LEN={ar_packet.len} SIZE={ar_packet.size}")

    def record_write_address(self, packet) -> None:
        """Record a write address transaction (AW channel)"""
        current_time = self.get_current_time_ns()

        # Convert to AXI address packet if needed
        if not isinstance(packet, AXICommandPacket):
            aw_packet = convert_gaxi_to_axi_address(packet, self.addr_field_config)
        else:
            aw_packet = packet

        # Create or update monitored transaction
        txn_id = aw_packet.id
        if txn_id in self.active_transactions:
            # Unexpected - transaction already exists
            self._add_protocol_violation(
                f"Duplicate write address for ID {txn_id:02X}",
                txn_id, current_time
            )
            return

        # Create new transaction
        monitored_txn = MonitoredTransaction(
            transaction_id=txn_id,
            is_read=False,
            is_axi4=self.is_axi4,
            address_packet=aw_packet,
            address_timestamp=current_time,
            state=AXITransactionState.ADDR_PHASE,
            start_time=current_time
        )

        self.active_transactions[txn_id] = monitored_txn
        self.transaction_start_times[txn_id] = current_time
        self.stats['write_transactions'] += 1

        if self.log:
            time_str = self.get_time_str()
            self.log.debug(f"📍 AW{time_str}: ID={txn_id:02X} ADDR=0x{aw_packet.addr:08X} "
                          f"LEN={aw_packet.len} SIZE={aw_packet.size}")

    def record_read_data(self, packet) -> None:
        """Record read data transaction (R channel)"""
        current_time = self.get_current_time_ns()

        # Convert to AXI read data packet if needed
        if not isinstance(packet, AXIReadDataPacket):
            r_packet = convert_gaxi_to_axi_read_data(packet, self.read_data_field_config)
        else:
            r_packet = packet

        txn_id = r_packet.id

        # Find corresponding transaction
        if txn_id not in self.active_transactions:
            # Orphaned read data
            self._add_orphaned_packet(r_packet, current_time, "READ_DATA")
            return

        monitored_txn = self.active_transactions[txn_id]

        # Verify this is a read transaction
        if not monitored_txn.is_read:
            self._add_protocol_violation(
                f"Read data for write transaction ID {txn_id:02X}",
                txn_id, current_time
            )
            return

        # Add data packet
        monitored_txn.add_data_packet(r_packet, current_time)

        # Update transaction state
        if monitored_txn.state == AXITransactionState.ADDR_PHASE:
            monitored_txn.state = AXITransactionState.DATA_PHASE

        # Check for completion (RLAST)
        if r_packet.last:
            self._complete_transaction(txn_id, current_time)

        # Check for response errors
        if r_packet.is_error_response():
            monitored_txn.add_error(f"Read response error: {r_packet.get_response_name()}")

        if self.log:
            time_str = self.get_time_str()
            self.log.debug(f"📥 R{time_str}: ID={txn_id:02X} "
                          f"RESP={r_packet.get_response_name()} LAST={r_packet.last}")

    def record_write_data(self, packet) -> None:
        """Record write data transaction (W channel)"""
        current_time = self.get_current_time_ns()

        # Convert to AXI write data packet if needed
        if not isinstance(packet, AXIWriteDataPacket):
            w_packet = convert_gaxi_to_axi_write_data(packet, self.write_data_field_config)
        else:
            w_packet = packet

        # For AXI-Lite, W channel doesn't have ID, so we need to associate it
        # with an active write transaction. For AXI4, we could use ID if available.
        # For simplicity, associate with the oldest incomplete write transaction

        write_txn_id = None
        for txn_id, txn in self.active_transactions.items():
            if (not txn.is_read and
                txn.state in [AXITransactionState.ADDR_PHASE, AXITransactionState.DATA_PHASE] and
                len(txn.data_packets) < txn.get_expected_data_beats()):
                write_txn_id = txn_id
                break

        if write_txn_id is None:
            # Orphaned write data
            self._add_orphaned_packet(w_packet, current_time, "WRITE_DATA")
            return

        monitored_txn = self.active_transactions[write_txn_id]

        # Add data packet
        monitored_txn.add_data_packet(w_packet, current_time)

        # Update transaction state
        if monitored_txn.state == AXITransactionState.ADDR_PHASE:
            monitored_txn.state = AXITransactionState.DATA_PHASE

        # Check if all write data received
        expected_beats = monitored_txn.get_expected_data_beats()
        actual_beats = monitored_txn.get_actual_data_beats()

        if w_packet.last or actual_beats >= expected_beats:
            # Write data phase complete, now waiting for response
            monitored_txn.state = AXITransactionState.RESP_PHASE

        if self.log:
            time_str = self.get_time_str()
            self.log.debug(f"📤 W{time_str}: LAST={w_packet.last} "
                          f"STRB={w_packet.get_strobe_pattern()} "
                          f"(beat {actual_beats}/{expected_beats})")

    def record_write_response(self, packet) -> None:
        """Record write response transaction (B channel)"""
        current_time = self.get_current_time_ns()

        # Convert to AXI write response packet if needed
        if not isinstance(packet, AXIWriteResponsePacket):
            b_packet = convert_gaxi_to_axi_write_response(packet, self.write_resp_field_config)
        else:
            b_packet = packet

        txn_id = b_packet.id

        # Find corresponding transaction
        if txn_id not in self.active_transactions:
            # Orphaned write response
            self._add_orphaned_packet(b_packet, current_time, "WRITE_RESPONSE")
            return

        monitored_txn = self.active_transactions[txn_id]

        # Verify this is a write transaction
        if monitored_txn.is_read:
            self._add_protocol_violation(
                f"Write response for read transaction ID {txn_id:02X}",
                txn_id, current_time
            )
            return

        # Add response packet
        monitored_txn.response_packet = b_packet
        monitored_txn.response_timestamp = current_time

        # Check for response errors
        if b_packet.is_error_response():
            monitored_txn.add_error(f"Write response error: {b_packet.get_response_name()}")

        # Complete the transaction
        self._complete_transaction(txn_id, current_time)

        if self.log:
            time_str = self.get_time_str()
            self.log.debug(f"📥 B{time_str}: ID={txn_id:02X} "
                          f"RESP={b_packet.get_response_name()}")

    def record_interrupt_packet(self, packet_value: int) -> None:
        """Record an interrupt bus packet"""
        current_time = self.get_current_time_ns()

        # Convert raw 64-bit value to interrupt packet
        if isinstance(packet_value, int):
            interrupt_packet = convert_raw_to_interrupt_packet(packet_value)
        else:
            interrupt_packet = packet_value

        interrupt_packet.timestamp = current_time
        self.interrupt_packets.append(interrupt_packet)
        self.stats['interrupt_packets'] += 1

        # Try to correlate with active transactions
        self._correlate_interrupt_packet(interrupt_packet)

        if self.log:
            time_str = self.get_time_str()
            self.log.debug(f"🚨 INTERRUPT{time_str}: "
                          f"TYPE={interrupt_packet.get_packet_type_name()} "
                          f"CODE={interrupt_packet.get_event_code_name()} "
                          f"CHAN={interrupt_packet.channel_id:02X}")

    def record_configuration(self, config_packet) -> None:
        """Record monitor configuration update"""
        current_time = self.get_current_time_ns()

        if not isinstance(config_packet, MonitorConfigPacket):
            # Convert from generic packet or dict
            if isinstance(config_packet, dict):
                config = MonitorConfigPacket.from_dict(config_packet, self.config_field_config)
            else:
                config_data = {field: getattr(config_packet, field, 0)
                              for field in self.config_field_config.field_names()}
                config = MonitorConfigPacket.from_dict(config_data, self.config_field_config)
        else:
            config = config_packet

        config.timestamp = current_time
        self.current_config = config
        self.config_history.append(config)
        self.stats['config_updates'] += 1

        if self.log:
            time_str = self.get_time_str()
            self.log.debug(f"⚙️ CONFIG{time_str}: "
                          f"FREQ={config.freq_sel} TIMEOUTS=({config.addr_cnt},"
                          f"{config.data_cnt},{config.resp_cnt})")

    def _complete_transaction(self, txn_id: int, completion_time: float):
        """Mark a transaction as complete and move to history"""
        if txn_id not in self.active_transactions:
            return

        monitored_txn = self.active_transactions[txn_id]
        monitored_txn.mark_complete(completion_time)

        # Move to completed transactions
        self.completed_transactions[txn_id] = monitored_txn
        del self.active_transactions[txn_id]

        self.transaction_end_times[txn_id] = completion_time
        self.stats['completed_transactions'] += 1

        if monitored_txn.has_errors():
            self.stats['error_transactions'] += 1

        if self.log:
            time_str = self.get_time_str()
            duration = completion_time - monitored_txn.start_time
            self.log.info(f"✅ TRANSACTION_COMPLETE{time_str}: ID={txn_id:02X} "
                         f"{'READ' if monitored_txn.is_read else 'WRITE'} "
                         f"DURATION={duration:.1f}ns")

    def _add_protocol_violation(self, message: str, txn_id: int, timestamp: float):
        """Add a protocol violation"""
        violation = {
            'message': message,
            'transaction_id': txn_id,
            'timestamp': timestamp,
            'time_str': f' @ {timestamp:.1f}ns'
        }
        self.protocol_violations.append(violation)
        self.stats['protocol_violations'] += 1

        if self.log:
            self.log.error(f"🚫 PROTOCOL_VIOLATION{violation['time_str']}: {message}")

    def _add_orphaned_packet(self, packet, timestamp: float, packet_type: str):
        """Add an orphaned packet (no matching transaction)"""
        orphan_info = {
            'packet': packet,
            'packet_type': packet_type,
            'timestamp': timestamp,
            'time_str': f' @ {timestamp:.1f}ns'
        }
        self.orphaned_packets.append(orphan_info)
        self.stats['orphaned_packets'] += 1

        if self.log:
            self.log.warning(f"⚠️ ORPHANED_{packet_type}{orphan_info['time_str']}")

    def _correlate_interrupt_packet(self, interrupt_packet: InterruptPacket):
        """Try to correlate interrupt packet with active transactions"""

        # Extract potential transaction ID from channel_id field
        potential_id = interrupt_packet.channel_id & ((1 << self.id_width) - 1)

        # Try to find matching transaction
        target_txn = None
        if potential_id in self.active_transactions:
            target_txn = self.active_transactions[potential_id]
        elif potential_id in self.completed_transactions:
            target_txn = self.completed_transactions[potential_id]

        if target_txn:
            target_txn.add_event(interrupt_packet)
            self.interrupt_correlation[id(interrupt_packet)] = target_txn

            if self.log:
                time_str = self.get_time_str()
                self.log.debug(f"🔗 INTERRUPT_CORRELATED{time_str}: "
                              f"ID={potential_id:02X} "
                              f"TYPE={interrupt_packet.get_packet_type_name()}")
        else:
            if self.log:
                time_str = self.get_time_str()
                self.log.warning(f"❓ INTERRUPT_UNCORRELATED{time_str}: "
                                f"CHAN={interrupt_packet.channel_id:02X}")

    def verify_transaction_protocol(self, txn_id: int) -> bool:
        """Verify protocol compliance for a specific transaction"""

        if txn_id in self.active_transactions:
            txn = self.active_transactions[txn_id]
        elif txn_id in self.completed_transactions:
            txn = self.completed_transactions[txn_id]
        else:
            self._add_verification_error(f"Transaction {txn_id:02X} not found")
            return False

        verification_passed = True

        # Verify address phase
        if not txn.address_packet:
            self._add_verification_error(f"Transaction {txn_id:02X} missing address packet")
            verification_passed = False

        # Verify data phase
        expected_beats = txn.get_expected_data_beats()
        actual_beats = txn.get_actual_data_beats()

        if actual_beats != expected_beats:
            self._add_verification_error(
                f"Transaction {txn_id:02X} data beat mismatch: "
                f"expected {expected_beats}, got {actual_beats}"
            )
            verification_passed = False

        # Verify response phase (for writes)
        if not txn.is_read:
            if not txn.response_packet:
                self._add_verification_error(f"Write transaction {txn_id:02X} missing response")
                verification_passed = False

        # Verify LAST signals
        if txn.is_read and txn.data_packets:
            last_packet = txn.data_packets[-1]
            if not last_packet.last:
                self._add_verification_error(f"Read transaction {txn_id:02X} missing RLAST")
                verification_passed = False
        elif not txn.is_read and txn.data_packets:
            last_packet = txn.data_packets[-1]
            if not last_packet.last:
                self._add_verification_error(f"Write transaction {txn_id:02X} missing WLAST")
                verification_passed = False

        # Verify transaction ordering and timing
        if txn.address_timestamp and txn.data_timestamps:
            if txn.data_timestamps[0] < txn.address_timestamp:
                self._add_verification_error(
                    f"Transaction {txn_id:02X} data before address"
                )
                verification_passed = False

        return verification_passed

    def verify_monitor_behavior(self) -> bool:
        """Verify overall monitor behavior and error detection"""
        verification_passed = True

        # Verify all completed transactions
        for txn_id, txn in self.completed_transactions.items():
            if not self.verify_transaction_protocol(txn_id):
                verification_passed = False

        # Verify error detection
        verification_passed &= self._verify_error_detection()

        # Verify timeout detection
        verification_passed &= self._verify_timeout_detection()

        # Verify interrupt packet generation
        verification_passed &= self._verify_interrupt_packets()

        return verification_passed

    def _verify_error_detection(self) -> bool:
        """Verify that monitor properly detected errors"""
        verification_passed = True

        # Check for transactions with response errors
        for txn_id, txn in self.completed_transactions.items():
            has_response_error = False

            # Check read data response errors
            if txn.is_read:
                for data_packet in txn.data_packets:
                    if data_packet.is_error_response():
                        has_response_error = True
                        break
            else:
                # Check write response errors
                if txn.response_packet and txn.response_packet.is_error_response():
                    has_response_error = True

            # Verify corresponding interrupt packet was generated
            if has_response_error:
                error_interrupt_found = False
                for event in txn.events:
                    # FIXED: Use InterruptPacketType enum
                    if (event.packet_type == InterruptPacketType.ERROR.value and
                        event.event_code in [MonitorEventCode.RESP_SLVERR.value,
                                            MonitorEventCode.RESP_DECERR.value]):
                        error_interrupt_found = True
                        break

                if not error_interrupt_found:
                    self._add_verification_error(
                        f"Missing error interrupt for transaction {txn_id:02X} with response error"
                    )
                    verification_passed = False

        return verification_passed

    def _verify_timeout_detection(self) -> bool:
        """Verify timeout detection behavior"""
        verification_passed = True

        # This would require injecting timeout conditions in the testbench
        # For now, just verify that timeout interrupts correlate properly

        timeout_interrupts = [
            pkt for pkt in self.interrupt_packets
            if pkt.packet_type == InterruptPacketType.TIMEOUT.value  # FIXED: Use InterruptPacketType enum
        ]

        for timeout_int in timeout_interrupts:
            if id(timeout_int) not in self.interrupt_correlation:
                self._add_verification_warning(
                    f"Timeout interrupt not correlated to any transaction"
                )

        return verification_passed

    def _verify_interrupt_packets(self) -> bool:
        """Verify interrupt packet format and content"""
        verification_passed = True

        for interrupt_pkt in self.interrupt_packets:
            # Verify packet format
            if interrupt_pkt.packet_type > 0xF:
                self._add_verification_error(f"Invalid interrupt packet type: {interrupt_pkt.packet_type}")
                verification_passed = False

            if interrupt_pkt.event_code > 0xF:
                self._add_verification_error(f"Invalid interrupt event code: {interrupt_pkt.event_code}")
                verification_passed = False

            # Verify unit/agent IDs are within expected ranges
            if self.current_config:
                # Additional configuration-based verification could be added here
                pass

        return verification_passed

    def _add_verification_error(self, message: str):
        """Add a verification error"""
        error = {
            'message': message,
            'timestamp': self.get_current_time_ns(),
            'time_str': self.get_time_str()
        }
        self.verification_errors.append(error)

        if self.log:
            self.log.error(f"❌ VERIFICATION_ERROR{error['time_str']}: {message}")

    def _add_verification_warning(self, message: str):
        """Add a verification warning"""
        warning = {
            'message': message,
            'timestamp': self.get_current_time_ns(),
            'time_str': self.get_time_str()
        }
        self.verification_warnings.append(warning)

        if self.log:
            self.log.warning(f"⚠️ VERIFICATION_WARNING{warning['time_str']}: {message}")

    def get_transaction_status(self, txn_id: int) -> Optional[Dict[str, Any]]:
        """Get detailed status for a specific transaction"""
        txn = None
        is_active = False

        if txn_id in self.active_transactions:
            txn = self.active_transactions[txn_id]
            is_active = True
        elif txn_id in self.completed_transactions:
            txn = self.completed_transactions[txn_id]
        else:
            return None

        return {
            'transaction_id': txn_id,
            'is_active': is_active,
            'is_read': txn.is_read,
            'state': txn.state.value,
            'start_time': txn.start_time,
            'completion_time': txn.completion_time,
            'duration': txn.total_latency,
            'expected_beats': txn.get_expected_data_beats(),
            'actual_beats': txn.get_actual_data_beats(),
            'has_errors': txn.has_errors(),
            'error_count': len(txn.errors),
            'event_count': len(txn.events)
        }

    def get_comprehensive_report(self) -> str:
        """Generate comprehensive verification report"""
        time_str = self.get_time_str()
        report = f"\n{self.component_name} Comprehensive Report{time_str}\n"
        report += "=" * 80 + "\n"

        # Configuration
        report += f"Configuration:\n"
        report += f"  Protocol: {'AXI4' if self.is_axi4 else 'AXI-Lite'}\n"
        report += f"  ID Width: {self.id_width}, Addr Width: {self.addr_width}\n"
        report += f"  Data Width: {self.data_width}, User Width: {self.user_width}\n"
        report += f"  Max Transactions: {self.max_transactions}\n"

        # Statistics
        report += f"\nStatistics:\n"
        for key, value in self.stats.items():
            report += f"  {key}: {value}\n"

        # Active transactions
        report += f"\nActive Transactions: {len(self.active_transactions)}\n"
        for txn_id, txn in self.active_transactions.items():
            report += f"  ID={txn_id:02X}: {txn.state.value} ({'R' if txn.is_read else 'W'})\n"

        # Recent completed transactions
        recent_completed = list(self.completed_transactions.items())[-10:]
        report += f"\nRecent Completed Transactions: {len(recent_completed)}\n"
        for txn_id, txn in recent_completed:
            status = "✅" if not txn.has_errors() else "❌"
            report += f"  {status} ID={txn_id:02X}: {txn.total_latency:.1f}ns ({'R' if txn.is_read else 'W'})\n"

        # Protocol violations
        if self.protocol_violations:
            report += f"\nProtocol Violations ({len(self.protocol_violations)}):\n"
            for violation in self.protocol_violations[-5:]:  # Show last 5
                report += f"  {violation['time_str']}: {violation['message']}\n"

        # Verification errors
        if self.verification_errors:
            report += f"\nVerification Errors ({len(self.verification_errors)}):\n"
            for error in self.verification_errors[-5:]:  # Show last 5
                report += f"  {error['time_str']}: {error['message']}\n"

        # Interrupt packets summary
        if self.interrupt_packets:
            report += f"\nInterrupt Packets: {len(self.interrupt_packets)}\n"
            packet_types = {}
            for pkt in self.interrupt_packets:
                pkt_type = pkt.get_packet_type_name()
                packet_types[pkt_type] = packet_types.get(pkt_type, 0) + 1

            for pkt_type, count in packet_types.items():
                report += f"  {pkt_type}: {count}\n"

        return report

    def get_verification_summary(self) -> Dict[str, Any]:
        """Get verification summary for external reporting"""
        return {
            'total_transactions': self.stats['completed_transactions'],
            'error_transactions': self.stats['error_transactions'],
            'protocol_violations': len(self.protocol_violations),
            'verification_errors': len(self.verification_errors),
            'verification_warnings': len(self.verification_warnings),
            'orphaned_packets': len(self.orphaned_packets),
            'interrupt_packets': len(self.interrupt_packets),
            'correlated_interrupts': len(self.interrupt_correlation),
            'overall_status': 'PASS' if (len(self.verification_errors) == 0 and
                                       len(self.protocol_violations) == 0) else 'FAIL'
        }

    def reset(self):
        """Reset scoreboard state"""
        self.active_transactions.clear()
        self.completed_transactions.clear()
        self.orphaned_packets.clear()
        self.interrupt_packets.clear()
        self.interrupt_correlation.clear()
        self.config_history.clear()
        self.protocol_violations.clear()
        self.timeout_events.clear()
        self.error_events.clear()
        self.performance_violations.clear()
        self.verification_errors.clear()
        self.verification_warnings.clear()
        self.transaction_start_times.clear()
        self.transaction_end_times.clear()

        for key in self.stats:
            self.stats[key] = 0

        if self.log:
            time_str = self.get_time_str()
            self.log.info(f"{self.component_name} reset{time_str}")
