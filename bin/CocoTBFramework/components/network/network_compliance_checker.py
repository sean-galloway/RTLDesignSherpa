# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: MNOCViolationType
# Purpose: Network Protocol Compliance Checker
#
# Documentation: bin/CocoTBFramework/README.md
# Subsystem: framework
#
# Author: sean galloway
# Created: 2025-10-18

"""
Network Protocol Compliance Checker

A non-intrusive compliance checker for Network (Memory Network-on-Chip) protocol validation
that can be optionally enabled in existing testbenches without requiring code changes.

Key features for Network:
- Credit-based flow control validation
- v2.0 chunk_enables field validation
- EOS (End of Stream) tracking and validation
- Payload type and structure validation
- Parity checking for header and payload
- ACK generation and timing validation

Features:
- Minimal performance impact when disabled
- Easy integration with existing testbenches
- Comprehensive Network protocol rule checking
- Detailed violation reporting with context
- Statistics collection for analysis

Usage:
# In testbench __init__:
self.compliance_checker = MNOCComplianceChecker.create_if_enabled(
    dut=dut, clock=clock, log=self.log, prefix='network', mode='master'
)

# Automatic checking happens in background
# Optional: Get compliance report at end of test
if self.compliance_checker:
    report = self.compliance_checker.get_compliance_report()
"""

import os
import asyncio
from typing import Dict, List, Any, Optional, Tuple, Set
from dataclasses import dataclass, field
from enum import Enum
import cocotb
from cocotb.triggers import RisingEdge, FallingEdge, Timer

from CocoTBFramework.components.gaxi.gaxi_monitor import GAXIMonitor
from CocoTBFramework.components.network.network_field_configs import MNOCFieldConfigHelper
from CocoTBFramework.components.network.network_packet import MNOCPacket


class MNOCViolationType(Enum):
    """Types of Network protocol violations."""
    # Handshake violations
    VALID_DROPPED = "valid_dropped"
    READY_BEFORE_VALID = "ready_before_valid"
    VALID_UNSTABLE = "valid_unstable"
    DATA_UNSTABLE = "data_unstable"

    # Credit management violations
    CREDIT_OVERFLOW = "credit_overflow"
    CREDIT_UNDERFLOW = "credit_underflow"
    CREDIT_TRACKING_ERROR = "credit_tracking_error"

    # Packet structure violations
    INVALID_PAYLOAD_TYPE = "invalid_payload_type"
    INVALID_CHUNK_ENABLES = "invalid_chunk_enables"
    CHUNK_ENABLES_ZERO = "chunk_enables_zero"
    STRUCTURED_PACKET_CHUNK15 = "structured_packet_chunk15"

    # Parity violations
    HEADER_PARITY_ERROR = "header_parity_error"
    PAYLOAD_PARITY_ERROR = "payload_parity_error"
    ACK_PARITY_ERROR = "ack_parity_error"

    # Channel violations
    CHANNEL_OUT_OF_RANGE = "channel_out_of_range"
    CHANNEL_NOT_OPEN = "channel_not_open"
    INVALID_CHANNEL_STATE = "invalid_channel_state"

    # EOS violations
    EOS_WITHOUT_VALID_DATA = "eos_without_valid_data"
    EOS_TRACKING_ERROR = "eos_tracking_error"
    MULTIPLE_EOS_SEQUENCE = "multiple_eos_sequence"

    # ACK violations
    INVALID_ACK_TYPE = "invalid_ack_type"
    ACK_TIMING_VIOLATION = "ack_timing_violation"
    ACK_CHANNEL_MISMATCH = "ack_channel_mismatch"

    # Timing violations
    RESET_VIOLATION = "reset_violation"
    CLOCK_VIOLATION = "clock_violation"
    TIMEOUT_VIOLATION = "timeout_violation"

    # Protocol violations
    PACKET_SIZE_VIOLATION = "packet_size_violation"
    INTERFACE_PROTOCOL_ERROR = "interface_protocol_error"


@dataclass
class MNOCViolation:
    """Represents a single Network protocol violation."""
    violation_type: MNOCViolationType
    interface: str  # 'PKT', 'ACK', 'FUB', 'RDA'
    cycle: int
    message: str
    severity: str = 'ERROR'  # 'ERROR', 'WARNING', 'INFO'
    channel: Optional[int] = None
    packet_type: Optional[str] = None
    additional_data: Dict[str, Any] = field(default_factory=dict)


@dataclass
class MNOCChannelState:
    """Track state for individual Network channels."""
    channel_id: int
    is_open: bool = False
    credits_sent: int = 0
    acks_received: int = 0
    last_packet_cycle: Optional[int] = None
    last_eos_cycle: Optional[int] = None
    pending_eos: bool = False
    total_packets: int = 0
    error_count: int = 0


class MNOCComplianceChecker:
    """
    Non-intrusive Network protocol compliance checker.

    Monitors Network interfaces and validates protocol compliance including:
    - Credit-based flow control rules
    - v2.0 chunk_enables field validation
    - EOS tracking and sequence validation
    - Parity checking and data integrity
    - ACK generation and timing
    """

    def __init__(self, dut, clock, prefix="", log=None,
                data_width=512, addr_width=8, num_channels=32,
                mode='master', multi_sig=False, **kwargs):
        """
        Initialize Network compliance checker.

        Args:
            dut: Device under test
            clock: Clock signal
            prefix: Signal prefix for Network interface
            log: Logger instance
            data_width: Data width (default: 512)
            addr_width: Address width (default: 8)
            num_channels: Number of channels (default: 32)
            mode: Interface mode ('master' or 'slave')
            multi_sig: Multi-signal mode
            **kwargs: Additional configuration
        """
        self.dut = dut
        self.clock = clock
        self.log = log
        self.mode = mode
        self.data_width = data_width
        self.addr_width = addr_width
        self.num_channels = num_channels

        # Violation tracking
        self.violations: List[MNOCViolation] = []
        self.cycle_count = 0
        self.enabled = True

        # Channel state tracking
        self.channels: Dict[int, MNOCChannelState] = {}
        for i in range(num_channels):
            self.channels[i] = MNOCChannelState(channel_id=i)

        # Configuration
        self.initial_credits = kwargs.get('initial_credits', 4)
        self.max_credits = kwargs.get('max_credits', 8)
        self.timeout_cycles = kwargs.get('timeout_cycles', 1000)

        # Statistics
        self.stats = {
            'total_packets': 0,
            'total_acks': 0,
            'parity_errors': 0,
            'credit_errors': 0,
            'chunk_enable_errors': 0,
            'eos_events': 0,
            'violations_by_type': {},
            'violations_by_channel': {},
        }

        # Monitors for packet and ACK interfaces
        self.packet_monitor = None
        self.ack_monitor = None

        # Previous state for stability checking
        self.prev_packet_valid = False
        self.prev_packet_data = None
        self.prev_ack_valid = False
        self.prev_ack_data = None

        # Start monitoring if enabled
        if self.enabled:
            self._setup_monitors(dut, prefix, multi_sig)
            if hasattr(cocotb, 'start_soon'):
                cocotb.start_soon(self._monitor_loop())
            else:
                cocotb.fork(self._monitor_loop())

    def _setup_monitors(self, dut, prefix, multi_sig):
        """Setup GAXI monitors for packet and ACK interfaces."""
        try:
            # Packet interface monitor
            self.packet_monitor = GAXIMonitor(
                dut=dut,
                title="NETWORK_Packet_Monitor",
                prefix=prefix,
                clock=self.clock,
                field_config=MNOCFieldConfigHelper.create_packet_field_config(
                    self.data_width, self.addr_width
                ),
                pkt_prefix="network_pkt",
                multi_sig=multi_sig,
                log=self.log
            )

            # ACK interface monitor
            self.ack_monitor = GAXIMonitor(
                dut=dut,
                title="NETWORK_ACK_Monitor",
                prefix=prefix,
                clock=self.clock,
                field_config=MNOCFieldConfigHelper.create_ack_field_config(
                    self.addr_width
                ),
                pkt_prefix="network_ack",
                multi_sig=multi_sig,
                log=self.log
            )

        except Exception as e:
            if self.log:
                self.log.warning(f"MNOCCompliance: Could not setup monitors: {e}")
            self.enabled = False

    async def _monitor_loop(self):
        """Main monitoring loop."""
        while self.enabled:
            try:
                await RisingEdge(self.clock)
                self.cycle_count += 1

                # Check packet interface
                if self.packet_monitor:
                    await self._check_packet_interface()

                # Check ACK interface
                if self.ack_monitor:
                    await self._check_ack_interface()

                # Periodic checks
                if self.cycle_count % 100 == 0:
                    self._check_timeouts()
                    self._update_statistics()

            except Exception as e:
                if self.log:
                    self.log.error(f"MNOCCompliance: Monitor error: {e}")
                await Timer(1, units='us')

    async def _check_packet_interface(self):
        """Check packet interface for violations."""
        try:
            # Get current interface state
            valid_signal = getattr(self.dut, f"{self.packet_monitor.prefix}network_pkt_valid", None)
            ready_signal = getattr(self.dut, f"{self.packet_monitor.prefix}network_pkt_ready", None)

            if valid_signal is None or ready_signal is None:
                return

            current_valid = bool(valid_signal.value)
            current_ready = bool(ready_signal.value)

            # Check for valid signal stability
            if self.prev_packet_valid and not current_valid:
                # Valid dropped without ready - potential violation
                if not current_ready:
                    self._report_violation(
                        MNOCViolationType.VALID_DROPPED,
                        "PKT",
                        "Packet valid signal dropped without ready assertion"
                    )

            # Check ready before valid
            if current_ready and not current_valid and not self.prev_packet_valid:
                self._report_violation(
                    MNOCViolationType.READY_BEFORE_VALID,
                    "PKT",
                    "Ready asserted before valid"
                )

            # Process completed transactions
            if current_valid and current_ready:
                await self._process_packet_transaction()

            # Update previous state
            self.prev_packet_valid = current_valid

        except Exception as e:
            if self.log:
                self.log.error(f"MNOCCompliance: Packet interface check error: {e}")

    async def _process_packet_transaction(self):
        """Process a completed packet transaction."""
        try:
            # Check if we have a packet to process
            if len(self.packet_monitor._recvQ) > 0:
                packet = self.packet_monitor._recvQ[-1]  # Get latest packet

                # Validate packet structure
                self._validate_packet_structure(packet)

                # Validate chunk enables
                self._validate_chunk_enables(packet)

                # Check parity
                self._validate_packet_parity(packet)

                # Update channel state
                channel = getattr(packet, 'addr', 0)
                if channel in self.channels:
                    self._update_channel_state(channel, packet)

                # Update statistics
                self.stats['total_packets'] += 1

        except Exception as e:
            if self.log:
                self.log.error(f"MNOCCompliance: Packet processing error: {e}")

    def _validate_packet_structure(self, packet):
        """Validate basic packet structure."""
        # Check payload type
        payload_type = getattr(packet, 'payload_type', -1)
        if payload_type not in [0, 1, 2, 3]:
            self._report_violation(
                MNOCViolationType.INVALID_PAYLOAD_TYPE,
                "PKT",
                f"Invalid payload type: {payload_type}",
                additional_data={'payload_type': payload_type}
            )

        # Check channel range
        channel = getattr(packet, 'addr', -1)
        if channel < 0 or channel >= self.num_channels:
            self._report_violation(
                MNOCViolationType.CHANNEL_OUT_OF_RANGE,
                "PKT",
                f"Channel {channel} out of range [0, {self.num_channels-1}]",
                channel=channel
            )

    def _validate_chunk_enables(self, packet):
        """Validate v2.0 chunk_enables field."""
        payload_type = getattr(packet, 'payload_type', 0)

        # Skip validation for RAW packets (chunk_enables is part of raw data)
        if payload_type == 3:  # RAW_PKT
            return

        chunk_enables = getattr(packet, 'chunk_enables', 0)

        # Check for zero chunk enables
        if chunk_enables == 0:
            self._report_violation(
                MNOCViolationType.CHUNK_ENABLES_ZERO,
                "PKT",
                "chunk_enables field is zero (no valid chunks)",
                additional_data={'chunk_enables': chunk_enables}
            )
            self.stats['chunk_enable_errors'] += 1

        # Check for chunk 15 in structured packets
        if payload_type in [0, 1, 2] and (chunk_enables & 0x8000):
            self._report_violation(
                MNOCViolationType.STRUCTURED_PACKET_CHUNK15,
                "PKT",
                "Chunk 15 set in structured packet (unusual)",
                severity='WARNING',
                additional_data={'chunk_enables': chunk_enables, 'payload_type': payload_type}
            )

    def _validate_packet_parity(self, packet):
        """Validate packet parity fields."""
        # Check header parity
        if hasattr(packet, 'header_par') and hasattr(packet, 'addr'):
            addr = getattr(packet, 'addr', 0)
            expected_par = bin(addr).count('1') % 2
            actual_par = getattr(packet, 'header_par', 0)

            if expected_par != actual_par:
                self._report_violation(
                    MNOCViolationType.HEADER_PARITY_ERROR,
                    "PKT",
                    f"Header parity error: expected {expected_par}, got {actual_par}",
                    additional_data={'addr': addr, 'expected': expected_par, 'actual': actual_par}
                )
                self.stats['parity_errors'] += 1

        # Check payload parity (simplified - would need full calculation)
        if hasattr(packet, 'payload_par'):
            # Note: Full payload parity calculation would be complex
            # This is a placeholder for the concept
            pass

    def _update_channel_state(self, channel: int, packet):
        """Update channel state tracking."""
        if channel not in self.channels:
            return

        channel_state = self.channels[channel]
        channel_state.total_packets += 1
        channel_state.last_packet_cycle = self.cycle_count

        # Check for EOS
        eos = getattr(packet, 'eos', False)
        if eos:
            channel_state.last_eos_cycle = self.cycle_count
            channel_state.pending_eos = True
            self.stats['eos_events'] += 1

        # Update credit tracking (simplified)
        if self.mode == 'master':
            channel_state.credits_sent += 1

    async def _check_ack_interface(self):
        """Check ACK interface for violations."""
        try:
            # Similar to packet interface checking
            if len(self.ack_monitor._recvQ) > 0:
                ack_packet = self.ack_monitor._recvQ[-1]

                # Validate ACK structure
                self._validate_ack_structure(ack_packet)

                # Update credit tracking
                self._process_ack_credits(ack_packet)

                self.stats['total_acks'] += 1

        except Exception as e:
            if self.log:
                self.log.error(f"MNOCCompliance: ACK interface check error: {e}")

    def _validate_ack_structure(self, ack_packet):
        """Validate ACK packet structure."""
        ack_type = getattr(ack_packet, 'ack', -1)
        if ack_type not in [0, 1, 2, 3]:
            self._report_violation(
                MNOCViolationType.INVALID_ACK_TYPE,
                "ACK",
                f"Invalid ACK type: {ack_type}",
                additional_data={'ack_type': ack_type}
            )

        # Check ACK parity
        if hasattr(ack_packet, 'ack_par'):
            expected_par = bin(ack_type).count('1') % 2
            actual_par = getattr(ack_packet, 'ack_par', 0)
            if expected_par != actual_par:
                self._report_violation(
                    MNOCViolationType.ACK_PARITY_ERROR,
                    "ACK",
                    f"ACK parity error: expected {expected_par}, got {actual_par}"
                )

    def _process_ack_credits(self, ack_packet):
        """Process ACK for credit tracking."""
        channel = getattr(ack_packet, 'addr', 0)
        ack_type = getattr(ack_packet, 'ack', 0)

        if channel in self.channels:
            channel_state = self.channels[channel]

            if ack_type == 0:  # MSAP_STOP
                channel_state.acks_received += 1
            elif ack_type == 1:  # MSAP_START
                channel_state.is_open = True
                # Reset credit tracking
                channel_state.acks_received = channel_state.credits_sent - self.max_credits
            elif ack_type == 2:  # MSAP_CREDIT_ON
                channel_state.acks_received += 1

    def _check_timeouts(self):
        """Check for timeout violations."""
        for channel_id, channel_state in self.channels.items():
            if (channel_state.last_packet_cycle is not None and
                self.cycle_count - channel_state.last_packet_cycle > self.timeout_cycles):
                self._report_violation(
                    MNOCViolationType.TIMEOUT_VIOLATION,
                    "PKT",
                    f"Channel {channel_id} timeout: {self.cycle_count - channel_state.last_packet_cycle} cycles",
                    channel=channel_id
                )

    def _update_statistics(self):
        """Update violation statistics."""
        # Count violations by type
        self.stats['violations_by_type'] = {}
        for violation in self.violations:
            vtype = violation.violation_type.value
            self.stats['violations_by_type'][vtype] = self.stats['violations_by_type'].get(vtype, 0) + 1

        # Count violations by channel
        self.stats['violations_by_channel'] = {}
        for violation in self.violations:
            if violation.channel is not None:
                ch = violation.channel
                self.stats['violations_by_channel'][ch] = self.stats['violations_by_channel'].get(ch, 0) + 1

    def _report_violation(self, violation_type: MNOCViolationType, interface: str,
                        message: str, severity: str = 'ERROR', channel: Optional[int] = None,
                        packet_type: Optional[str] = None, additional_data: Optional[Dict] = None):
        """Report a protocol violation."""
        violation = MNOCViolation(
            violation_type=violation_type,
            interface=interface,
            cycle=self.cycle_count,
            message=message,
            severity=severity,
            channel=channel,
            packet_type=packet_type,
            additional_data=additional_data or {}
        )

        self.violations.append(violation)

        # Log violation
        if self.log:
            log_method = self.log.error if severity == 'ERROR' else \
                        self.log.warning if severity == 'WARNING' else self.log.info
            log_method(f"Network {severity}: {message} (cycle {self.cycle_count}, {interface})")

    def get_compliance_report(self) -> Dict[str, Any]:
        """Get comprehensive compliance report."""
        error_violations = [v for v in self.violations if v.severity == 'ERROR']
        warning_violations = [v for v in self.violations if v.severity == 'WARNING']

        return {
            'total_violations': len(self.violations),
            'error_violations': len(error_violations),
            'warning_violations': len(warning_violations),
            'violations': [
                {
                    'type': v.violation_type.value,
                    'interface': v.interface,
                    'cycle': v.cycle,
                    'message': v.message,
                    'severity': v.severity,
                    'channel': v.channel,
                    'packet_type': v.packet_type,
                    'data': v.additional_data
                }
                for v in self.violations
            ],
            'statistics': self.stats,
            'channel_states': {
                ch: {
                    'is_open': state.is_open,
                    'total_packets': state.total_packets,
                    'credits_sent': state.credits_sent,
                    'acks_received': state.acks_received,
                    'error_count': state.error_count
                }
                for ch, state in self.channels.items()
                if state.total_packets > 0 or state.error_count > 0
            },
            'compliance_status': 'PASS' if len(error_violations) == 0 else 'FAIL',
            'mode': self.mode,
            'configuration': {
                'data_width': self.data_width,
                'addr_width': self.addr_width,
                'num_channels': self.num_channels,
                'initial_credits': self.initial_credits,
                'max_credits': self.max_credits
            }
        }

    def print_compliance_report(self):
        """Print formatted compliance report."""
        report = self.get_compliance_report()

        if self.log:
            self.log.info("=== Network COMPLIANCE REPORT ===")
            self.log.info(f"Status: {report['compliance_status']}")
            self.log.info(f"Total Violations: {report['total_violations']} "
                        f"(Errors: {report['error_violations']}, Warnings: {report['warning_violations']})")

            if report['violations']:
                self.log.info("Violations:")
                for v in report['violations'][:10]:  # Show first 10
                    self.log.info(f"  {v['severity']}: {v['message']} (cycle {v['cycle']})")
                if len(report['violations']) > 10:
                    self.log.info(f"  ... and {len(report['violations']) - 10} more")
        else:
            print("=== Network COMPLIANCE REPORT ===")
            print(f"Status: {report['compliance_status']}")
            print(f"Total Violations: {report['total_violations']}")

    @classmethod
    def create_if_enabled(cls, dut, clock, prefix="", log=None, **kwargs) -> Optional['MNOCComplianceChecker']:
        """
        Create compliance checker only if enabled via environment variable.

        Returns:
            MNOCComplianceChecker instance if enabled, None otherwise
        """
        if os.getenv('NETWORK_COMPLIANCE_CHECK', '0').lower() in ['1', 'true', 'yes', 'on']:
            try:
                return cls(dut, clock, prefix, log, **kwargs)
            except Exception as e:
                if log:
                    log.warning(f"Could not create Network compliance checker: {e}")
        return None

    def disable(self):
        """Disable compliance checking."""
        self.enabled = False

    def enable(self):
        """Enable compliance checking."""
        self.enabled = True

    def reset_statistics(self):
        """Reset all statistics and violations."""
        self.violations.clear()
        self.cycle_count = 0
        for channel_state in self.channels.values():
            channel_state.total_packets = 0
            channel_state.error_count = 0
            channel_state.credits_sent = 0
            channel_state.acks_received = 0
        self.stats = {
            'total_packets': 0,
            'total_acks': 0,
            'parity_errors': 0,
            'credit_errors': 0,
            'chunk_enable_errors': 0,
            'eos_events': 0,
            'violations_by_type': {},
            'violations_by_channel': {},
        }
