# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: AxiReadSplitterScoreboard
# Purpose: AXI Master Read Splitter Scoreboard - FIXED TIMING
#
# Documentation: bin/CocoTBFramework/README.md
# Subsystem: framework
#
# Author: sean galloway
# Created: 2025-10-18

"""
AXI Master Read Splitter Scoreboard - FIXED TIMING

TIMING FIXES:
1. Use cocotb get_sim_time directly instead of manual tracking
2. Consistent timing in all error reports
3. Proper simulation time formatting
4. No dependency on external timing updates
"""

import os
from collections import deque, defaultdict
from typing import Dict, List, Optional, Tuple, Any
import time

from cocotb.utils import get_sim_time

from .axi_read_splitter_packets import (
    AXIAddressPacket, AXIDataPacket, SplitInfoPacket, SplitTransaction,
    SplitTransactionState, convert_gaxi_packet_to_axi_address,
    convert_gaxi_packet_to_axi_data, create_axi_address_field_config,
    create_axi_data_field_config, create_split_info_field_config
)


class AxiReadSplitterScoreboard:
    """
    Enhanced scoreboard with FIXED timing for debugging.
    """

    def __init__(self, alignment_mask: int = 0xFFF, log=None, component_name: str = "AXI_RD_SPLITTER_SB",
                    id_width: int = 8, addr_width: int = 32, data_width: int = 32, user_width: int = 1):
        """
        Initialize the scoreboard with proper timing tracking.
        """
        self.alignment_mask = alignment_mask
        self.boundary_size = alignment_mask + 1
        self.log = log
        self.component_name = component_name

        # Store field widths for packet creation
        self.id_width = id_width
        self.addr_width = addr_width
        self.data_width = data_width
        self.user_width = user_width

        # Create field configurations for packet types
        self.addr_field_config = create_axi_address_field_config(id_width, addr_width, user_width)
        self.data_field_config = create_axi_data_field_config(id_width, data_width, user_width)
        self.split_field_config = create_split_info_field_config(id_width, addr_width)

        # Transaction tracking using common packet types
        self.upstream_transactions = {}  # id -> AXIAddressPacket (original transactions)
        self.downstream_transactions = defaultdict(list)  # id -> List[AXIAddressPacket] (split transactions)
        self.response_tracking = defaultdict(list)  # id -> List[AXIDataPacket]
        self.split_info_tracking = {}  # id -> SplitInfoPacket
        self.active_split_transactions = {}  # id -> SplitTransaction

        # FIXED: Timing tracking using cocotb directly
        self.transaction_start_times = {}  # id -> start_time
        self.transaction_end_times = {}    # id -> end_time

        # Statistics and error tracking
        self.stats = {
            'upstream_transactions': 0,
            'downstream_transactions': 0,
            'responses_received': 0,
            'splits_detected': 0,
            'boundary_crossings_detected': 0,
            'verification_checks': 0,
            'total_errors': 0
        }

        self.errors = []
        self.verification_results = []

        if self.log:
            self.log.info(f"{component_name} initialized with boundary_size=0x{self.boundary_size:X}")

    def get_current_time_ns(self) -> float:
        """Get current simulation time in nanoseconds"""
        return get_sim_time('ns')

    def get_time_str(self) -> str:
        """Get formatted time string like TBBase"""
        time_ns = self.get_current_time_ns()
        return f' @ {time_ns:.1f}ns'

    def record_upstream_transaction(self, packet) -> None:
        """
        Record an upstream transaction with FIXED timing.
        """
        current_time = self.get_current_time_ns()

        # Convert GAXI packet to AXI address packet if needed
        if not isinstance(packet, AXIAddressPacket):
            ar_packet = convert_gaxi_packet_to_axi_address(packet, self.addr_field_config)
        else:
            ar_packet = packet

        # Store the original transaction
        self.upstream_transactions[ar_packet.id] = ar_packet
        self.stats['upstream_transactions'] += 1

        # FIXED: Enhanced timing tracking using cocotb
        self.transaction_start_times[ar_packet.id] = current_time

        # Create split transaction tracker with enhanced info
        expected_responses = self._calculate_expected_responses(ar_packet)
        split_txn = SplitTransaction(
            original_ar=ar_packet,
            split_info=None,
            split_ars=[],
            expected_responses=expected_responses,
            received_responses=[],
            state=SplitTransactionState.PENDING,
            start_time=current_time
        )
        self.active_split_transactions[ar_packet.id] = split_txn

        # Check if this transaction should split
        if ar_packet.will_cross_boundary(self.boundary_size):
            self.stats['boundary_crossings_detected'] += 1

        if self.log:
            time_str = self.get_time_str()
            self.log.debug(f"Recorded upstream AR{time_str}: ID={ar_packet.id:02X}, "
                            f"ADDR=0x{ar_packet.addr:08X}, LEN={ar_packet.len}, "
                            f"BURST={ar_packet.get_burst_type_name()}")

    def record_downstream_transaction(self, packet) -> None:
        """
        Record a downstream transaction with FIXED timing.
        """
        current_time = self.get_current_time_ns()

        # Handle both address and data packets
        if hasattr(packet, 'addr'):  # Address packet
            if not isinstance(packet, AXIAddressPacket):
                ar_packet = convert_gaxi_packet_to_axi_address(packet, self.addr_field_config)
            else:
                ar_packet = packet

            self.downstream_transactions[ar_packet.id].append(ar_packet)
            self.stats['downstream_transactions'] += 1

            # Add to split transaction tracker
            if ar_packet.id in self.active_split_transactions:
                self.active_split_transactions[ar_packet.id].add_split_ar(ar_packet)

            if self.log:
                time_str = self.get_time_str()
                self.log.debug(f"Recorded downstream AR{time_str}: ID={ar_packet.id:02X}, "
                                f"ADDR=0x{ar_packet.addr:08X}, LEN={ar_packet.len}")

        elif hasattr(packet, 'data'):  # Data packet
            if not isinstance(packet, AXIDataPacket):
                r_packet = convert_gaxi_packet_to_axi_data(packet, self.data_field_config)
            else:
                r_packet = packet

            self.response_tracking[r_packet.id].append(r_packet)
            self.stats['responses_received'] += 1

            # FIXED: Track completion timing using cocotb time
            if r_packet.last:
                self.transaction_end_times[r_packet.id] = current_time

            # Add to split transaction tracker
            if r_packet.id in self.active_split_transactions:
                self.active_split_transactions[r_packet.id].add_response(r_packet)

            if self.log:
                time_str = self.get_time_str()
                self.log.debug(f"Recorded response R{time_str}: ID={r_packet.id:02X}, "
                                f"DATA=0x{r_packet.data:08X}, RESP={r_packet.get_response_name()}, "
                                f"LAST={r_packet.last}")

    def record_split_info(self, packet) -> None:
        """
        Record split information with FIXED timing.
        """
        current_time = self.get_current_time_ns()

        if not isinstance(packet, SplitInfoPacket):
            if isinstance(packet, dict):
                split_packet = SplitInfoPacket.from_dict(packet, self.split_field_config)
            else:
                # Convert from generic packet
                split_data = {
                    'addr': getattr(packet, 'addr', 0),
                    'id': getattr(packet, 'id', 0),
                    'cnt': getattr(packet, 'cnt', 0)
                }
                split_packet = SplitInfoPacket.from_dict(split_data, self.split_field_config)
        else:
            split_packet = packet

        self.split_info_tracking[split_packet.id] = split_packet
        self.stats['splits_detected'] += 1

        # Update split transaction tracker
        if split_packet.id in self.active_split_transactions:
            self.active_split_transactions[split_packet.id].split_info = split_packet

        if self.log:
            time_str = self.get_time_str()
            self.log.debug(f"Recorded split info{time_str}: ID={split_packet.id:02X}, "
                            f"ADDR=0x{split_packet.addr:08X}, CNT={split_packet.cnt}")

    def _add_error_with_context(self, error_msg: str, txn_id: int = None,
                               error_category: str = "GENERAL", severity: str = "ERROR"):
        """
        Enhanced error reporting with FIXED timing and full transaction context.
        """
        # FIXED: Use proper cocotb timing
        current_time = self.get_current_time_ns()
        current_time_str = self.get_time_str()

        # Build detailed error report
        error_report = f"\n{'='*80}\n"
        error_report += f"{severity}: {error_category} - {error_msg}\n"
        error_report += f"{'='*80}\n"

        if txn_id is not None and txn_id in self.upstream_transactions:
            # Add transaction context
            original_ar = self.upstream_transactions[txn_id]
            split_txn = self.active_split_transactions.get(txn_id)

            error_report += f"TRANSACTION CONTEXT:\n"
            error_report += f"  Transaction ID: 0x{txn_id:02X}\n"
            error_report += f"  Original Address: 0x{original_ar.addr:08X}\n"
            error_report += f"  Original Length: {original_ar.len} ({original_ar.len + 1} beats)\n"
            error_report += f"  Size: {original_ar.size} ({1 << original_ar.size} bytes/beat)\n"
            error_report += f"  Burst Type: {original_ar.get_burst_type_name()}\n"
            error_report += f"  Total Bytes: {original_ar.calculate_total_bytes()}\n"
            error_report += f"  End Address: 0x{original_ar.addr + original_ar.calculate_total_bytes() - 1:08X}\n"

            # Add boundary information
            error_report += f"\nBOUNDARY INFORMATION:\n"
            error_report += f"  Alignment Mask: 0x{self.alignment_mask:03X}\n"
            error_report += f"  Boundary Size: {self.boundary_size} bytes (0x{self.boundary_size:X})\n"
            error_report += f"  Should Cross Boundary: {original_ar.will_cross_boundary(self.boundary_size)}\n"

            # FIXED: Add timing information using proper cocotb timing
            start_time = self.transaction_start_times.get(txn_id, 0.0)
            end_time = self.transaction_end_times.get(txn_id, current_time)
            duration = end_time - start_time

            error_report += f"\nTIMING INFORMATION:\n"
            error_report += f"  Start Time: {start_time:.1f}ns\n"
            error_report += f"  Current/End Time: {end_time:.1f}ns\n"
            error_report += f"  Duration: {duration:.1f}ns\n"
            error_report += f"  Error Time: {current_time_str}\n"

            # Add split transaction details
            split_ars = self.downstream_transactions.get(txn_id, [])
            responses = self.response_tracking.get(txn_id, [])
            split_info = self.split_info_tracking.get(txn_id)

            error_report += f"\nACTUAL SPLIT BEHAVIOR:\n"
            error_report += f"  Split Transactions Generated: {len(split_ars)}\n"
            for i, split_ar in enumerate(split_ars):
                error_report += f"    Split {i+1}: ADDR=0x{split_ar.addr:08X}, LEN={split_ar.len} ({split_ar.len + 1} beats)\n"

            error_report += f"  Responses Received: {len(responses)}\n"
            last_count = sum(1 for r in responses if r.last)
            error_report += f"  LAST Signals Received: {last_count}\n"

            if split_info:
                error_report += f"  Split Info Count: {split_info.cnt}\n"
            else:
                error_report += f"  Split Info: NOT RECEIVED\n"

            # Add expected behavior with DW=512 debugging
            error_report += f"\nEXPECTED BEHAVIOR:\n"
            expected_splits = self._calculate_expected_splits(original_ar)
            error_report += f"  Expected Split Count: {expected_splits}\n"
            error_report += f"  Expected Total Responses: {original_ar.len + 1}\n"
            error_report += f"  Expected LAST Signals: {expected_splits}\n"

            # Add detailed boundary analysis for wide data buses
            if self.data_width >= 512:
                error_report += f"\n🔍 DW={self.data_width} BOUNDARY ANALYSIS:\n"
                start_addr = original_ar.addr
                bytes_per_beat = 1 << original_ar.size
                total_bytes = (original_ar.len + 1) * bytes_per_beat
                end_addr = start_addr + total_bytes - 1

                start_boundary = start_addr // self.boundary_size
                end_boundary = end_addr // self.boundary_size

                error_report += f"  Start: 0x{start_addr:08X} -> boundary {start_boundary} (0x{start_boundary * self.boundary_size:08X})\n"
                error_report += f"  End: 0x{end_addr:08X} -> boundary {end_boundary} (0x{end_boundary * self.boundary_size:08X})\n"
                error_report += f"  Bytes per beat: {bytes_per_beat}\n"
                error_report += f"  Total bytes: {total_bytes}\n"
                error_report += f"  Boundaries crossed: {end_boundary - start_boundary}\n"

                # Calculate expected split points
                error_report += f"  Expected split calculation:\n"
                current_addr = start_addr
                remaining_beats = original_ar.len + 1
                split_count = 0

                while remaining_beats > 0:
                    # Find next boundary
                    current_boundary = current_addr // self.boundary_size
                    next_boundary_addr = (current_boundary + 1) * self.boundary_size
                    bytes_to_boundary = next_boundary_addr - current_addr
                    beats_to_boundary = bytes_to_boundary // bytes_per_beat

                    split_count += 1

                    if beats_to_boundary >= remaining_beats:
                        # Remaining fits before boundary
                        error_report += f"    Final split {split_count}: ADDR=0x{current_addr:08X}, "
                        error_report += f"LEN={remaining_beats - 1} ({remaining_beats} beats)\n"
                        break
                    else:
                        # Split at boundary
                        split_len = max(0, beats_to_boundary - 1)
                        actual_beats = split_len + 1
                        error_report += f"    Split {split_count}: ADDR=0x{current_addr:08X}, "
                        error_report += f"LEN={split_len} ({actual_beats} beats) -> boundary at 0x{next_boundary_addr:08X}\n"
                        current_addr = next_boundary_addr
                        remaining_beats -= actual_beats

                error_report += f"  Calculated expected splits: {split_count}\n"

        error_report += f"{'='*80}\n"

        # Store the detailed error
        self.errors.append(error_report)
        self.stats['total_errors'] += 1

        if self.log:
            self.log.error(error_report)

    def _calculate_expected_splits(self, ar_packet: AXIAddressPacket) -> int:
        """Calculate expected number of split transactions with detailed logging"""
        if not ar_packet.will_cross_boundary(self.boundary_size):
            return 1

        # Enhanced calculation for debugging
        start_addr = ar_packet.addr
        bytes_per_beat = 1 << ar_packet.size
        total_bytes = (ar_packet.len + 1) * bytes_per_beat
        end_addr = start_addr + total_bytes - 1

        start_boundary = start_addr // self.boundary_size
        end_boundary = end_addr // self.boundary_size

        expected_splits = int(end_boundary - start_boundary + 1)

        # Extra logging for wide data buses
        if self.data_width >= 512 and self.log:
            time_str = self.get_time_str()
            self.log.debug(f"🔍 DW={self.data_width} Split calculation{time_str}:")
            self.log.debug(f"  Start: 0x{start_addr:08X} -> boundary {start_boundary}")
            self.log.debug(f"  End: 0x{end_addr:08X} -> boundary {end_boundary}")
            self.log.debug(f"  Bytes per beat: {bytes_per_beat}")
            self.log.debug(f"  Total bytes: {total_bytes}")
            self.log.debug(f"  Expected splits: {expected_splits}")

        return expected_splits

    def verify_transaction_splitting(self, txn_id: int) -> bool:
        """
        Verify that a specific transaction was split correctly with FIXED timing.
        """
        if txn_id not in self.upstream_transactions:
            self._add_error_with_context(
                f"Transaction {txn_id:02X} not found in upstream transactions",
                txn_id, "MISSING_TRANSACTION", "ERROR"
            )
            return False

        if txn_id not in self.active_split_transactions:
            self._add_error_with_context(
                f"Split transaction tracker not found for {txn_id:02X}",
                txn_id, "MISSING_TRACKER", "ERROR"
            )
            return False

        original_ar = self.upstream_transactions[txn_id]
        split_txn = self.active_split_transactions[txn_id]
        split_ars = self.downstream_transactions.get(txn_id, [])
        responses = self.response_tracking.get(txn_id, [])

        self.stats['verification_checks'] += 1
        verification_passed = True

        # Check if transaction should have been split
        should_split = original_ar.will_cross_boundary(self.boundary_size)
        expected_splits = self._calculate_expected_splits(original_ar)

        if should_split:
            # Verify split occurred
            if len(split_ars) < expected_splits:
                self._add_error_with_context(
                    f"Insufficient splits: expected {expected_splits}, got {len(split_ars)}",
                    txn_id, "SPLIT_COUNT", "ERROR"
                )
                verification_passed = False
            elif len(split_ars) > expected_splits:
                self._add_error_with_context(
                    f"Too many splits: expected {expected_splits}, got {len(split_ars)}",
                    txn_id, "SPLIT_COUNT", "ERROR"
                )
                verification_passed = False
            else:
                # Verify split addresses are correct
                verification_passed &= self._verify_split_addresses(original_ar, split_ars, txn_id)

                # Verify split info is present
                if txn_id in self.split_info_tracking:
                    split_info = self.split_info_tracking[txn_id]
                    if split_info.cnt != len(split_ars):
                        self._add_error_with_context(
                            f"Split count mismatch: FIFO reports {split_info.cnt}, actual splits {len(split_ars)}",
                            txn_id, "SPLIT_INFO_MISMATCH", "ERROR"
                        )
                        verification_passed = False
                else:
                    self._add_error_with_context(
                        f"Split info missing from FIFO",
                        txn_id, "MISSING_SPLIT_INFO", "ERROR"
                    )
                    verification_passed = False
        else:
            # Verify no unnecessary split
            if len(split_ars) > 1:
                self._add_error_with_context(
                    f"Unnecessary split detected: transaction doesn't cross boundary but {len(split_ars)} splits generated",
                    txn_id, "UNNECESSARY_SPLIT", "ERROR"
                )
                verification_passed = False

        # Verify response completeness
        expected_total_responses = original_ar.len + 1
        if len(responses) != expected_total_responses:
            self._add_error_with_context(
                f"Response count mismatch: expected {expected_total_responses}, got {len(responses)}",
                txn_id, "RESPONSE_COUNT", "ERROR"
            )
            verification_passed = False

        # Verify response order and LAST flags
        if responses:
            verification_passed &= self._verify_response_order(responses, txn_id)

        return verification_passed

    def _verify_split_addresses(self, original_ar: AXIAddressPacket, split_ars: List[AXIAddressPacket], txn_id: int) -> bool:
        """Verify that split addresses are correct with detailed error reporting"""
        if not split_ars:
            return True

        verification_passed = True
        bytes_per_beat = 1 << original_ar.size

        for i, split_ar in enumerate(split_ars):
            # First split should start at original address
            if i == 0 and split_ar.addr != original_ar.addr:
                self._add_error_with_context(
                    f"First split address wrong: expected 0x{original_ar.addr:08X}, got 0x{split_ar.addr:08X}",
                    txn_id, "SPLIT_ADDRESS", "ERROR"
                )
                verification_passed = False

            # Each split should be properly aligned to boundaries
            if i > 0:  # Skip first split
                boundary_aligned = (split_ar.addr % self.boundary_size) == 0
                if not boundary_aligned:
                    self._add_error_with_context(
                        f"Split {i+1} not boundary aligned: address 0x{split_ar.addr:08X} not aligned to 0x{self.boundary_size:X}",
                        txn_id, "SPLIT_ALIGNMENT", "ERROR"
                    )
                    verification_passed = False

        return verification_passed

    def _verify_response_order(self, responses: List[AXIDataPacket], txn_id: int) -> bool:
        """Verify response ordering with detailed error reporting"""
        if not responses:
            return True

        verification_passed = True
        split_ars = self.downstream_transactions.get(txn_id, [])

        # Check if this transaction was split
        if len(split_ars) > 1:
            # SPLIT TRANSACTION: Verify aggregate correctness
            last_signals = [r for r in responses if r.last == 1]
            expected_last_count = len(split_ars)

            if len(last_signals) != expected_last_count:
                self._add_error_with_context(
                    f"LAST signal count wrong: expected {expected_last_count}, got {len(last_signals)}",
                    txn_id, "LAST_SIGNALS", "ERROR"
                )
                verification_passed = False

            # Verify total response count
            expected_total_responses = sum(split_ar.len + 1 for split_ar in split_ars)
            if len(responses) != expected_total_responses:
                self._add_error_with_context(
                    f"Total response count wrong: expected {expected_total_responses}, got {len(responses)}",
                    txn_id, "RESPONSE_TOTAL", "ERROR"
                )
                verification_passed = False

        else:
            # NON-SPLIT TRANSACTION: Traditional sequential LAST signaling
            for i, response in enumerate(responses):
                is_last_response = (i == len(responses) - 1)
                expected_last = 1 if is_last_response else 0

                if response.last != expected_last:
                    self._add_error_with_context(
                        f"Response {i+1}/{len(responses)} LAST signal wrong: expected {expected_last}, got {response.last}",
                        txn_id, "LAST_SEQUENCE", "ERROR"
                    )
                    verification_passed = False

        return verification_passed

    def _calculate_expected_responses(self, ar_packet: AXIAddressPacket) -> int:
        """Calculate expected number of responses for a transaction"""
        return ar_packet.len + 1  # len field is number of transfers - 1

    def is_transaction_complete(self, txn_id: int) -> bool:
        """Check if a transaction is complete"""
        if txn_id not in self.active_split_transactions:
            return False

        split_txn = self.active_split_transactions[txn_id]
        return split_txn.is_complete()

    def verify_split_correctness(self) -> bool:
        """Verify all transactions were split correctly with enhanced reporting"""
        overall_passed = True
        failed_transactions = []

        for txn_id in self.upstream_transactions.keys():
            passed = self.verify_transaction_splitting(txn_id)
            if not passed:
                failed_transactions.append(txn_id)
            overall_passed &= passed

        if self.log:
            time_str = self.get_time_str()
            if overall_passed:
                self.log.info(f"✓ All split verifications passed{time_str}")
            else:
                self.log.error(f"✗ Split verification failed{time_str}: {len(self.errors)} errors")
                self.log.error(f"Failed transaction IDs: {[f'0x{tid:02X}' for tid in failed_transactions]}")

        return overall_passed

    def get_detailed_report(self) -> str:
        """Generate detailed verification report with enhanced debugging info"""
        time_str = self.get_time_str()
        report = f"\n{self.component_name} Detailed Report{time_str}\n"
        report += "=" * 50 + "\n"

        # Statistics
        report += f"Statistics:\n"
        for key, value in self.stats.items():
            report += f"  {key}: {value}\n"

        # Transaction summary
        report += f"\nTransaction Summary:\n"
        report += f"  Upstream transactions: {len(self.upstream_transactions)}\n"
        report += f"  Active split transactions: {len(self.active_split_transactions)}\n"
        report += f"  Completed transactions: {sum(1 for t in self.active_split_transactions.values() if t.is_complete())}\n"

        # Enhanced error summary
        if self.errors:
            report += f"\nErrors ({len(self.errors)}):\n"
            # Just show count here, detailed errors are already logged above
            error_categories = {}
            for error in self.errors:
                for category in ["SPLIT_COUNT", "RESPONSE_COUNT", "LAST_SIGNALS", "SPLIT_ADDRESS"]:
                    if category in error:
                        error_categories[category] = error_categories.get(category, 0) + 1
                        break

            for category, count in error_categories.items():
                report += f"  {category}: {count} errors\n"
        else:
            report += f"\n✓ No errors detected\n"

        return report

    def get_error_summary(self) -> Dict[str, Any]:
        """Get error summary for external reporting"""
        error_types = defaultdict(int)
        for error in self.errors:
            if "SPLIT_COUNT" in error:
                error_types["split_count"] += 1
            elif "RESPONSE_COUNT" in error:
                error_types["response_count"] += 1
            elif "LAST_SIGNALS" in error:
                error_types["last_signals"] += 1
            elif "SPLIT_ADDRESS" in error:
                error_types["address"] += 1
            else:
                error_types["other"] += 1

        return {
            'total_errors': len(self.errors),
            'error_types': dict(error_types),
            'recent_errors': self.errors[-3:] if self.errors else []  # Show last 3 detailed errors
        }

    def reset(self):
        """Reset scoreboard state"""
        self.upstream_transactions.clear()
        self.downstream_transactions.clear()
        self.response_tracking.clear()
        self.split_info_tracking.clear()
        self.active_split_transactions.clear()
        self.transaction_start_times.clear()
        self.transaction_end_times.clear()

        for key in self.stats:
            self.stats[key] = 0

        self.errors.clear()
        self.verification_results.clear()

        if self.log:
            time_str = self.get_time_str()
            self.log.info(f"{self.component_name} reset{time_str}")

    # REMOVED: set_sim_time method - no longer needed since we use cocotb directly
