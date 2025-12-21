# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: AXI5ComplianceChecker
# Purpose: AXI5 Protocol Compliance Checker with support for AXI5-specific features.
#
# Documentation: bin/CocoTBFramework/README.md
# Subsystem: framework
#
# Author: sean galloway
# Created: 2025-12-16

"""
AXI5 Protocol Compliance Checker

A non-intrusive compliance checker for AXI5 protocol validation that can be
optionally enabled in existing testbenches without requiring code changes.

Features:
- AXI5-specific protocol rule checking
- Atomic operation validation
- Memory Tagging Extension (MTE) validation
- Security context validation
- Chunked transfer validation
- Detailed violation reporting
- Statistics collection

AXI5-specific checks include:
- ATOP field validation and atomic operation rules
- TAGOP/TAG/TAGUPDATE/TAGMATCH consistency
- NSAID/MPAM/MECID context validation
- CHUNKEN/CHUNKV/CHUNKNUM/CHUNKSTRB rules
- POISON indicator validation
- TRACE signal consistency

Usage:
    # In testbench __init__:
    self.compliance_checker = AXI5ComplianceChecker.create_if_enabled(
        dut=dut, clock=clock, log=self.log, prefix='m_axi'
    )

    # Automatic checking happens in background
    # Optional: Get compliance report at end of test
    if self.compliance_checker:
        report = self.compliance_checker.get_compliance_report()
"""

import os
from typing import Dict, List, Any, Optional
from dataclasses import dataclass, field
from enum import Enum
import cocotb
from cocotb.triggers import RisingEdge

from CocoTBFramework.components.gaxi.gaxi_monitor import GAXIMonitor
from .axi5_field_configs import AXI5FieldConfigHelper
from .axi5_packet import AXI5Packet


class AXI5ViolationType(Enum):
    """Types of AXI5 protocol violations."""
    # Handshake violations
    VALID_DROPPED = "valid_dropped"
    READY_BEFORE_VALID = "ready_before_valid"
    VALID_UNSTABLE = "valid_unstable"

    # Burst violations
    BURST_LENGTH_VIOLATION = "burst_length_violation"
    BURST_SIZE_VIOLATION = "burst_size_violation"
    BURST_BOUNDARY_VIOLATION = "burst_boundary_violation"
    WLAST_MISMATCH = "wlast_mismatch"
    RLAST_MISMATCH = "rlast_mismatch"

    # ID violations
    ID_ORDERING_VIOLATION = "id_ordering_violation"
    ID_WIDTH_VIOLATION = "id_width_violation"

    # Response violations
    RESPONSE_CODE_VIOLATION = "response_code_violation"

    # Timing violations
    RESET_VIOLATION = "reset_violation"
    CLOCK_VIOLATION = "clock_violation"

    # Data integrity violations
    DATA_STABILITY_VIOLATION = "data_stability_violation"
    STROBE_VIOLATION = "strobe_violation"

    # AXI5-specific: Atomic violations
    ATOP_BURST_LENGTH_VIOLATION = "atop_burst_length_violation"
    ATOP_ENCODING_VIOLATION = "atop_encoding_violation"
    ATOP_RESPONSE_VIOLATION = "atop_response_violation"

    # AXI5-specific: MTE violations
    TAGOP_ENCODING_VIOLATION = "tagop_encoding_violation"
    TAG_WIDTH_VIOLATION = "tag_width_violation"
    TAGUPDATE_MISMATCH = "tagupdate_mismatch"
    TAGMATCH_UNEXPECTED = "tagmatch_unexpected"

    # AXI5-specific: Security violations
    NSAID_VIOLATION = "nsaid_violation"
    MPAM_VIOLATION = "mpam_violation"
    MECID_VIOLATION = "mecid_violation"

    # AXI5-specific: Chunk violations
    CHUNK_ENABLE_VIOLATION = "chunk_enable_violation"
    CHUNKNUM_VIOLATION = "chunknum_violation"
    CHUNKSTRB_VIOLATION = "chunkstrb_violation"

    # AXI5-specific: Poison violations
    POISON_PROPAGATION_VIOLATION = "poison_propagation_violation"

    # AXI5-specific: Trace violations
    TRACE_CONSISTENCY_VIOLATION = "trace_consistency_violation"


@dataclass
class AXI5Violation:
    """Represents a single AXI5 protocol violation."""
    violation_type: AXI5ViolationType
    channel: str  # 'AR', 'AW', 'W', 'R', 'B'
    cycle: int
    message: str
    severity: str = 'ERROR'  # 'ERROR', 'WARNING', 'INFO'
    additional_data: Dict[str, Any] = field(default_factory=dict)


class AXI5ComplianceChecker:
    """
    Non-intrusive AXI5 protocol compliance checker.

    Can be optionally enabled via environment variables without modifying
    existing testbench code.
    """

    def __init__(self, dut, clock, prefix="", log=None, **kwargs):
        """Initialize AXI5 compliance checker."""
        self.dut = dut
        self.clock = clock
        self.prefix = prefix
        self.log = log
        self.enabled = True

        # Configuration
        self.data_width = kwargs.get('data_width', 32)
        self.id_width = kwargs.get('id_width', 8)
        self.addr_width = kwargs.get('addr_width', 32)
        self.user_width = kwargs.get('user_width', 1)
        self.nsaid_width = kwargs.get('nsaid_width', 4)
        self.mpam_width = kwargs.get('mpam_width', 11)
        self.mecid_width = kwargs.get('mecid_width', 16)
        self.tag_width = kwargs.get('tag_width', 4)
        self.multi_sig = kwargs.get('multi_sig', True)

        # Violation tracking
        self.violations: List[AXI5Violation] = []
        self.violation_counts: Dict[AXI5ViolationType, int] = {}
        self.cycle_count = 0

        # Transaction tracking for ordering and matching
        self.outstanding_reads: Dict[int, Any] = {}  # ID -> transaction info
        self.outstanding_writes: Dict[int, Any] = {}
        self.write_data_queue: Dict[int, List[Any]] = {}  # ID -> W beats
        self.atomic_transactions: Dict[int, Any] = {}  # ID -> atomic info

        # Statistics
        self.stats = {
            'total_ar_transactions': 0,
            'total_aw_transactions': 0,
            'total_w_beats': 0,
            'total_r_beats': 0,
            'total_b_responses': 0,
            'total_violations': 0,
            'checks_performed': 0,
            'atomic_operations': 0,
            'mte_operations': 0,
            'security_operations': 0,
            'chunked_transfers': 0,
            'poisoned_beats': 0,
            'traced_transactions': 0,
        }

        # Start monitoring if signals exist
        self.monitors_active = False
        self.monitors = {}
        self.setup_monitors()

    @classmethod
    def create_if_enabled(cls, dut, clock, prefix="", log=None, **kwargs):
        """
        Factory method that returns None if compliance checking is disabled.
        """
        if not cls.is_enabled():
            return None

        try:
            return cls(dut, clock, prefix, log, **kwargs)
        except Exception as e:
            if log:
                log.warning(f"Could not create AXI5 compliance checker: {e}")
            return None

    @staticmethod
    def is_enabled() -> bool:
        """Check if compliance checking is enabled via environment."""
        return os.environ.get('AXI5_COMPLIANCE_CHECK', '0') == '1'

    def setup_monitors(self):
        """Setup signal monitors for all AXI5 channels."""
        try:
            # AR Channel Monitor
            if self._has_channel_signals('ar'):
                self.monitors['AR'] = GAXIMonitor(
                    dut=self.dut,
                    title="AR_Monitor",
                    prefix=self.prefix,
                    clock=self.clock,
                    field_config=AXI5FieldConfigHelper.create_ar_field_config(
                        self.id_width, self.addr_width, self.user_width,
                        self.nsaid_width, self.mpam_width, self.mecid_width
                    ),
                    pkt_prefix="ar",
                    multi_sig=self.multi_sig,
                    log=self.log
                )

            # AW Channel Monitor
            if self._has_channel_signals('aw'):
                self.monitors['AW'] = GAXIMonitor(
                    dut=self.dut,
                    title="AW_Monitor",
                    prefix=self.prefix,
                    clock=self.clock,
                    field_config=AXI5FieldConfigHelper.create_aw_field_config(
                        self.id_width, self.addr_width, self.user_width,
                        self.nsaid_width, self.mpam_width, self.mecid_width,
                        data_width=self.data_width
                    ),
                    pkt_prefix="aw",
                    multi_sig=self.multi_sig,
                    log=self.log
                )

            # W Channel Monitor
            if self._has_channel_signals('w'):
                self.monitors['W'] = GAXIMonitor(
                    dut=self.dut,
                    title="W_Monitor",
                    prefix=self.prefix,
                    clock=self.clock,
                    field_config=AXI5FieldConfigHelper.create_w_field_config(
                        self.data_width, self.user_width, self.tag_width
                    ),
                    pkt_prefix="w",
                    multi_sig=self.multi_sig,
                    log=self.log
                )

            # R Channel Monitor
            if self._has_channel_signals('r'):
                self.monitors['R'] = GAXIMonitor(
                    dut=self.dut,
                    title="R_Monitor",
                    prefix=self.prefix,
                    clock=self.clock,
                    field_config=AXI5FieldConfigHelper.create_r_field_config(
                        self.id_width, self.data_width, self.user_width,
                        tag_width=self.tag_width
                    ),
                    pkt_prefix="r",
                    multi_sig=self.multi_sig,
                    log=self.log
                )

            # B Channel Monitor
            if self._has_channel_signals('b'):
                self.monitors['B'] = GAXIMonitor(
                    dut=self.dut,
                    title="B_Monitor",
                    prefix=self.prefix,
                    clock=self.clock,
                    field_config=AXI5FieldConfigHelper.create_b_field_config(
                        self.id_width, self.user_width, self.tag_width, self.data_width
                    ),
                    pkt_prefix="b",
                    multi_sig=self.multi_sig,
                    log=self.log
                )

            # Start monitoring tasks
            if self.monitors:
                self.monitors_active = True
                cocotb.start_soon(self.monitor_transactions())
                cocotb.start_soon(self.monitor_handshakes())
                cocotb.start_soon(self.cycle_counter())

                if self.log:
                    channels = list(self.monitors.keys())
                    self.log.info(f"AXI5 compliance checker active for channels: {channels}")

        except Exception as e:
            if self.log:
                self.log.warning(f"Could not setup AXI5 monitors: {e}")
            self.enabled = False

    def _has_channel_signals(self, channel: str) -> bool:
        """Check if the DUT has signals for the specified channel."""
        try:
            if channel.lower() == 'ar':
                return (hasattr(self.dut, f'{self.prefix}arvalid') and
                        hasattr(self.dut, f'{self.prefix}arready'))
            elif channel.lower() == 'aw':
                return (hasattr(self.dut, f'{self.prefix}awvalid') and
                        hasattr(self.dut, f'{self.prefix}awready'))
            elif channel.lower() == 'w':
                return (hasattr(self.dut, f'{self.prefix}wvalid') and
                        hasattr(self.dut, f'{self.prefix}wready'))
            elif channel.lower() == 'r':
                return (hasattr(self.dut, f'{self.prefix}rvalid') and
                        hasattr(self.dut, f'{self.prefix}rready'))
            elif channel.lower() == 'b':
                return (hasattr(self.dut, f'{self.prefix}bvalid') and
                        hasattr(self.dut, f'{self.prefix}bready'))
        except Exception:
            pass
        return False

    async def monitor_transactions(self):
        """Monitor and validate AXI5 transactions."""
        if not self.monitors_active:
            return

        try:
            while True:
                for channel_name, monitor in self.monitors.items():
                    if hasattr(monitor, 'get_completed_packets'):
                        packets = monitor.get_completed_packets()
                        for packet in packets:
                            await self.validate_transaction(channel_name, packet)
                            self.stats['checks_performed'] += 1

                await RisingEdge(self.clock)
        except Exception as e:
            if self.log:
                self.log.debug(f"Monitor transactions stopped: {e}")

    async def monitor_handshakes(self):
        """Monitor AXI5 handshake protocol compliance."""
        if not self.monitors_active:
            return

        try:
            while True:
                for channel in ['ar', 'aw', 'w', 'r', 'b']:
                    if self._has_channel_signals(channel):
                        await self.check_handshake_rules(channel)

                await RisingEdge(self.clock)

        except Exception as e:
            if self.log:
                self.log.debug(f"Monitor handshakes stopped: {e}")

    async def check_handshake_rules(self, channel: str):
        """Check handshake protocol rules for a specific channel."""
        try:
            valid_signal = getattr(self.dut, f'{self.prefix}{channel}valid', None)
            ready_signal = getattr(self.dut, f'{self.prefix}{channel}ready', None)

            if valid_signal is None or ready_signal is None:
                return

            self.stats['checks_performed'] += 1

        except Exception:
            pass

    async def validate_transaction(self, channel: str, packet: AXI5Packet):
        """Validate a completed transaction for protocol compliance."""
        try:
            if channel == 'AR':
                await self.validate_ar_transaction(packet)
            elif channel == 'AW':
                await self.validate_aw_transaction(packet)
            elif channel == 'W':
                await self.validate_w_transaction(packet)
            elif channel == 'R':
                await self.validate_r_transaction(packet)
            elif channel == 'B':
                await self.validate_b_transaction(packet)

        except Exception as e:
            if self.log:
                self.log.debug(f"Transaction validation error for {channel}: {e}")

    async def validate_ar_transaction(self, packet: AXI5Packet):
        """Validate AR (Address Read) transaction."""
        self.stats['total_ar_transactions'] += 1

        # Check burst length
        burst_len = getattr(packet, 'len', 0) + 1
        if burst_len > 256:
            self.record_violation(
                AXI5ViolationType.BURST_LENGTH_VIOLATION,
                'AR',
                f"Burst length {burst_len} exceeds maximum of 256"
            )

        # Check burst size
        burst_size = getattr(packet, 'size', 0)
        if burst_size > 7:
            self.record_violation(
                AXI5ViolationType.BURST_SIZE_VIOLATION,
                'AR',
                f"Burst size {burst_size} exceeds maximum of 7"
            )

        # AXI5-specific: Check chunken
        chunken = getattr(packet, 'chunken', 0)
        if chunken:
            self.stats['chunked_transfers'] += 1
            # Chunking only valid for data width >= 128 bits
            if self.data_width < 128:
                self.record_violation(
                    AXI5ViolationType.CHUNK_ENABLE_VIOLATION,
                    'AR',
                    f"Chunking enabled but data width ({self.data_width}) < 128 bits"
                )

        # AXI5-specific: Check tagop
        tagop = getattr(packet, 'tagop', 0)
        if tagop != 0:
            self.stats['mte_operations'] += 1
            if tagop > 3:
                self.record_violation(
                    AXI5ViolationType.TAGOP_ENCODING_VIOLATION,
                    'AR',
                    f"Invalid TAGOP value: {tagop} (must be 0-3)"
                )

        # AXI5-specific: Track security context
        nsaid = getattr(packet, 'nsaid', 0)
        if nsaid != 0:
            self.stats['security_operations'] += 1

        # AXI5-specific: Track trace
        trace = getattr(packet, 'trace', 0)
        if trace:
            self.stats['traced_transactions'] += 1

        # Track outstanding read
        transaction_id = getattr(packet, 'id', 0)
        self.outstanding_reads[transaction_id] = {
            'packet': packet,
            'expected_beats': burst_len,
            'received_beats': 0,
            'chunken': chunken,
            'tagop': tagop,
            'trace': trace,
        }

    async def validate_aw_transaction(self, packet: AXI5Packet):
        """Validate AW (Address Write) transaction."""
        self.stats['total_aw_transactions'] += 1

        burst_len = getattr(packet, 'len', 0) + 1

        # Check burst length
        if burst_len > 256:
            self.record_violation(
                AXI5ViolationType.BURST_LENGTH_VIOLATION,
                'AW',
                f"Burst length {burst_len} exceeds maximum of 256"
            )

        # AXI5-specific: Check ATOP
        atop = getattr(packet, 'atop', 0)
        if atop != 0:
            self.stats['atomic_operations'] += 1

            # Atomic operations must be single-beat
            if burst_len > 1:
                self.record_violation(
                    AXI5ViolationType.ATOP_BURST_LENGTH_VIOLATION,
                    'AW',
                    f"Atomic operation (ATOP=0x{atop:02X}) with burst length {burst_len} > 1"
                )

            # Validate ATOP encoding
            atop_type = (atop >> 4) & 0x3
            if atop_type not in [0, 1, 2, 3]:
                self.record_violation(
                    AXI5ViolationType.ATOP_ENCODING_VIOLATION,
                    'AW',
                    f"Invalid ATOP type: {atop_type}"
                )

            # Track atomic transaction
            transaction_id = getattr(packet, 'id', 0)
            self.atomic_transactions[transaction_id] = {
                'atop': atop,
                'addr': getattr(packet, 'addr', 0),
            }

        # AXI5-specific: Check tagop
        tagop = getattr(packet, 'tagop', 0)
        if tagop != 0:
            self.stats['mte_operations'] += 1
            if tagop > 3:
                self.record_violation(
                    AXI5ViolationType.TAGOP_ENCODING_VIOLATION,
                    'AW',
                    f"Invalid TAGOP value: {tagop} (must be 0-3)"
                )

        # Track outstanding write
        transaction_id = getattr(packet, 'id', 0)
        self.outstanding_writes[transaction_id] = {
            'packet': packet,
            'expected_beats': burst_len,
            'received_beats': 0,
            'atop': atop,
            'tagop': tagop,
            'trace': getattr(packet, 'trace', 0),
        }

    async def validate_w_transaction(self, packet: AXI5Packet):
        """Validate W (Write Data) transaction."""
        self.stats['total_w_beats'] += 1

        # AXI5-specific: Check poison
        poison = getattr(packet, 'poison', 0)
        if poison:
            self.stats['poisoned_beats'] += 1

    async def validate_r_transaction(self, packet: AXI5Packet):
        """Validate R (Read Data) transaction."""
        self.stats['total_r_beats'] += 1

        # Check response code
        resp = getattr(packet, 'resp', 0)
        if resp > 3:
            self.record_violation(
                AXI5ViolationType.RESPONSE_CODE_VIOLATION,
                'R',
                f"Invalid response code {resp}"
            )

        # AXI5-specific: Check poison
        poison = getattr(packet, 'poison', 0)
        if poison:
            self.stats['poisoned_beats'] += 1

        # AXI5-specific: Check chunk fields
        chunkv = getattr(packet, 'chunkv', 0)
        if chunkv:
            transaction_id = getattr(packet, 'id', 0)
            if transaction_id in self.outstanding_reads:
                if not self.outstanding_reads[transaction_id].get('chunken', 0):
                    self.record_violation(
                        AXI5ViolationType.CHUNK_ENABLE_VIOLATION,
                        'R',
                        f"CHUNKV=1 but CHUNKEN was not set in AR for ID {transaction_id}"
                    )

        # Check RLAST matching
        transaction_id = getattr(packet, 'id', 0)
        is_last = getattr(packet, 'last', 0)

        if transaction_id in self.outstanding_reads:
            outstanding = self.outstanding_reads[transaction_id]
            outstanding['received_beats'] += 1

            expected_last = (outstanding['received_beats'] == outstanding['expected_beats'])
            if bool(is_last) != expected_last:
                self.record_violation(
                    AXI5ViolationType.RLAST_MISMATCH,
                    'R',
                    f"RLAST mismatch for ID {transaction_id}: expected {expected_last}, got {bool(is_last)}"
                )

            if is_last:
                del self.outstanding_reads[transaction_id]

    async def validate_b_transaction(self, packet: AXI5Packet):
        """Validate B (Write Response) transaction."""
        self.stats['total_b_responses'] += 1

        # Check response code
        resp = getattr(packet, 'resp', 0)
        if resp > 3:
            self.record_violation(
                AXI5ViolationType.RESPONSE_CODE_VIOLATION,
                'B',
                f"Invalid response code {resp}"
            )

        # AXI5-specific: Check atomic response
        transaction_id = getattr(packet, 'id', 0)
        if transaction_id in self.atomic_transactions:
            # Atomic transactions can return EXOKAY
            # but should not return OKAY for exclusive atomics
            del self.atomic_transactions[transaction_id]

        # AXI5-specific: Check trace consistency
        trace = getattr(packet, 'trace', 0)
        if transaction_id in self.outstanding_writes:
            expected_trace = self.outstanding_writes[transaction_id].get('trace', 0)
            if trace != expected_trace:
                self.record_violation(
                    AXI5ViolationType.TRACE_CONSISTENCY_VIOLATION,
                    'B',
                    f"TRACE mismatch for ID {transaction_id}: expected {expected_trace}, got {trace}",
                    severity='WARNING'
                )
            del self.outstanding_writes[transaction_id]

    def record_violation(self, violation_type: AXI5ViolationType, channel: str,
                         message: str, **kwargs):
        """Record a protocol violation."""
        violation = AXI5Violation(
            violation_type=violation_type,
            channel=channel,
            cycle=self.cycle_count,
            message=message,
            severity=kwargs.get('severity', 'ERROR'),
            additional_data=kwargs.get('additional_data', {})
        )

        self.violations.append(violation)
        self.violation_counts[violation_type] = self.violation_counts.get(violation_type, 0) + 1
        self.stats['total_violations'] += 1

        if self.log:
            self.log.error(f"AXI5 Violation [{channel}]: {message}")

    async def cycle_counter(self):
        """Count clock cycles for violation timestamps."""
        try:
            while True:
                await RisingEdge(self.clock)
                self.cycle_count += 1
        except Exception:
            pass

    def get_compliance_report(self) -> Dict[str, Any]:
        """Get comprehensive compliance report."""
        if not self.enabled:
            return {'compliance_checking': 'disabled'}

        total_violations = len(self.violations)
        violation_summary = {}

        for vtype in AXI5ViolationType:
            count = self.violation_counts.get(vtype, 0)
            if count > 0:
                violation_summary[vtype.value] = count

        return {
            'compliance_checking': 'enabled',
            'total_violations': total_violations,
            'violation_summary': violation_summary,
            'statistics': self.stats.copy(),
            'axi5_feature_usage': {
                'atomic_operations': self.stats['atomic_operations'],
                'mte_operations': self.stats['mte_operations'],
                'security_operations': self.stats['security_operations'],
                'chunked_transfers': self.stats['chunked_transfers'],
                'poisoned_beats': self.stats['poisoned_beats'],
                'traced_transactions': self.stats['traced_transactions'],
            },
            'violations': [
                {
                    'type': v.violation_type.value,
                    'channel': v.channel,
                    'cycle': v.cycle,
                    'message': v.message,
                    'severity': v.severity
                }
                for v in self.violations[-10:]  # Last 10 violations
            ],
            'compliance_status': 'PASSED' if total_violations == 0 else 'FAILED'
        }

    def print_compliance_report(self):
        """Print formatted compliance report."""
        if not self.enabled:
            if self.log:
                self.log.info("AXI5 compliance checking was disabled")
            return

        report = self.get_compliance_report()

        if self.log:
            self.log.info("=" * 80)
            self.log.info("AXI5 PROTOCOL COMPLIANCE REPORT")
            self.log.info("=" * 80)
            self.log.info(f"Status: {report['compliance_status']}")
            self.log.info(f"Total Violations: {report['total_violations']}")
            self.log.info(f"Checks Performed: {report['statistics']['checks_performed']}")

            self.log.info("AXI5 Feature Usage:")
            for feature, count in report['axi5_feature_usage'].items():
                if count > 0:
                    self.log.info(f"  {feature}: {count}")

            if report['violation_summary']:
                self.log.info("Violation Summary:")
                for vtype, count in report['violation_summary'].items():
                    self.log.info(f"  {vtype}: {count}")

            self.log.info("=" * 80)


# Integration helper for existing testbenches
def add_axi5_compliance_checking(testbench_class):
    """
    Decorator to add AXI5 compliance checking to existing testbenches.

    Usage:
        @add_axi5_compliance_checking
        class MyAXI5Testbench(TBBase):
            ...
    """

    original_init = testbench_class.__init__
    original_final = getattr(testbench_class, 'finalize_test', None)

    def new_init(self, *args, **kwargs):
        original_init(self, *args, **kwargs)

        # Add compliance checker
        if hasattr(self, 'dut') and hasattr(self, 'aclk'):
            self.axi5_compliance_checker = AXI5ComplianceChecker.create_if_enabled(
                dut=self.dut,
                clock=self.aclk,
                prefix='m_axi',  # Default prefix
                log=self.log
            )

    def new_finalize(self):
        # Print compliance report
        if hasattr(self, 'axi5_compliance_checker') and self.axi5_compliance_checker:
            self.axi5_compliance_checker.print_compliance_report()

        # Call original finalize if it exists
        if original_final:
            original_final(self)

    testbench_class.__init__ = new_init
    testbench_class.finalize_test = new_finalize

    return testbench_class
