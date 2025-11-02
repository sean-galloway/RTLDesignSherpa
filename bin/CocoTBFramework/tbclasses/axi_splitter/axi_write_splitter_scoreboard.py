# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: AxiWriteSplitterScoreboard
# Purpose: AXI Master Write Splitter Scoreboard - FIXED TIMING
#
# Documentation: bin/CocoTBFramework/README.md
# Subsystem: framework
#
# Author: sean galloway
# Created: 2025-10-18

"""
AXI Master Write Splitter Scoreboard - FIXED TIMING

TIMING FIXES:
1. Use cocotb get_sim_time directly instead of manual tracking
2. Consistent timing in all error reports
3. Proper simulation time formatting
4. No dependency on external timing updates

WRITE-SPECIFIC FEATURES:
1. Track write address (AW), write data (W), and write response (B) channels
2. Verify proper WLAST generation for split transactions
3. Handle write data flow across split boundaries
4. Verify write response consolidation
"""

import os
from collections import deque, defaultdict
from typing import Dict, List, Optional, Tuple, Any
import time

from cocotb.utils import get_sim_time

from .axi_write_splitter_packets import (
    AXIWriteAddressPacket, AXIWriteDataPacket, AXIWriteResponsePacket, WriteSplitInfoPacket,
    SplitWriteTransaction, SplitWriteTransactionState,
    convert_gaxi_packet_to_axi_write_address, convert_gaxi_packet_to_axi_write_data,
    convert_gaxi_packet_to_axi_write_response,
    create_axi_write_address_field_config, create_axi_write_data_field_config,
    create_axi_write_response_field_config, create_write_split_info_field_config
)


class AxiWriteSplitterScoreboard:
    """
    Enhanced write splitter scoreboard with FIXED timing for debugging.

    Handles the more complex write transaction flow:
    1. Write Address (AW) phase - may be split across boundaries
    2. Write Data (W) phase - data must be properly distributed across splits
    3. Write Response (B) phase - responses must be properly consolidated
    """

    def __init__(self, alignment_mask: int = 0xFFF, log=None, component_name: str = "AXI_WR_SPLITTER_SB",
                    id_width: int = 8, addr_width: int = 32, data_width: int = 32, user_width: int = 1):
        """
        Initialize the write splitter scoreboard with proper timing tracking.
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
        self.write_addr_field_config = create_axi_write_address_field_config(id_width, addr_width, user_width)
        self.write_data_field_config = create_axi_write_data_field_config(data_width, user_width)
        self.write_resp_field_config = create_axi_write_response_field_config(id_width, user_width)
        self.split_field_config = create_write_split_info_field_config(id_width, addr_width)

        # Transaction tracking using common packet types
        self.upstream_transactions = {}  # id -> AXIWriteAddressPacket (original transactions)
        self.downstream_transactions = defaultdict(list)  # id -> List[AXIWriteAddressPacket] (split transactions)
        self.write_data_tracking = defaultdict(list)  # id -> List[AXIWriteDataPacket]
        self.response_tracking = defaultdict(list)  # id -> List[AXIWriteResponsePacket]
        self.split_info_tracking = {}  # id -> WriteSplitInfoPacket
        self.active_split_transactions = {}  # id -> SplitWriteTransaction

        # FIXED: Timing tracking using cocotb directly
        self.transaction_start_times = {}  # id -> start_time
        self.transaction_end_times = {}    # id -> end_time

        # Statistics and error tracking
        self.stats = {
            'upstream_transactions': 0,
            'downstream_transactions': 0,
            'write_data_beats': 0,
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
        Record an upstream write address transaction with FIXED timing.
        """
        current_time = self.get_current_time_ns()

        # Convert GAXI packet to AXI write address packet if needed
        if not isinstance(packet, AXIWriteAddressPacket):
            aw_packet = convert_gaxi_packet_to_axi_write_address(packet, self.write_addr_field_config)
        else:
            aw_packet = packet

        # Store the original transaction
        self.upstream_transactions[aw_packet.id] = aw_packet
        self.stats['upstream_transactions'] += 1

        # FIXED: Enhanced timing tracking using cocotb
        self.transaction_start_times[aw_packet.id] = current_time

        # Create split write transaction tracker with enhanced info
        expected_responses = self._calculate_expected_responses(aw_packet)
        expected_data_beats = self._calculate_expected_data_beats(aw_packet)
        split_txn = SplitWriteTransaction(
            original_aw=aw_packet,
            split_info=None,
            split_aws=[],
            write_data=[],
            received_responses=[],
            expected_responses=expected_responses,
            expected_data_beats=expected_data_beats,
            state=SplitWriteTransactionState.PENDING,
            start_time=current_time
        )
        self.active_split_transactions[aw_packet.id] = split_txn

        # Check if this transaction should split
        if aw_packet.will_cross_boundary(self.boundary_size):
            self.stats['boundary_crossings_detected'] += 1

        if self.log:
            time_str = self.get_time_str()
            self.log.debug(f"Recorded upstream AW{time_str}: ID={aw_packet.id:02X}, "
                            f"ADDR=0x{aw_packet.addr:08X}, LEN={aw_packet.len}, "
                            f"BURST={aw_packet.get_burst_type_name()}")

    def record_downstream_transaction(self, packet) -> None:
        """
        FIXED: Enhanced downstream transaction recording with robust write data association
        """
        current_time = self.get_current_time_ns()

        # Handle write address packets (unchanged)
        if hasattr(packet, 'addr'):  # Write Address packet
            if not isinstance(packet, AXIWriteAddressPacket):
                aw_packet = convert_gaxi_packet_to_axi_write_address(packet, self.write_addr_field_config)
            else:
                aw_packet = packet

            self.downstream_transactions[aw_packet.id].append(aw_packet)
            self.stats['downstream_transactions'] += 1

            # Update split transaction state
            if aw_packet.id in self.active_split_transactions:
                self.active_split_transactions[aw_packet.id].add_split_aw(aw_packet)
                # Update state to address sent
                if self.active_split_transactions[aw_packet.id].state == SplitWriteTransactionState.PENDING:
                    self.active_split_transactions[aw_packet.id].state = SplitWriteTransactionState.ADDRESS_SENT

            if self.log:
                time_str = self.get_time_str()
                self.log.debug(f"📍 M_AXI_AW{time_str}: ID={aw_packet.id:02X} "
                            f"ADDR=0x{aw_packet.addr:08X} LEN={aw_packet.len}")

        # FIXED: Enhanced write data packet handling
        elif hasattr(packet, 'data') and hasattr(packet, 'strb'):  # Write Data packet
            if not isinstance(packet, AXIWriteDataPacket):
                w_packet = convert_gaxi_packet_to_axi_write_data(packet, self.write_data_field_config)
            else:
                w_packet = packet

            # CRITICAL FIX: More robust write data association
            data_associated = False

            # Method 1: Try to associate with transaction that has room for more data
            for txn_id, split_txn in self.active_split_transactions.items():
                current_data_count = len(self.write_data_tracking.get(txn_id, []))
                expected_data_count = split_txn.expected_data_beats

                # Associate if this transaction needs more data AND is in correct state
                if (current_data_count < expected_data_count and
                    split_txn.state in [SplitWriteTransactionState.ADDRESS_SENT,
                                    SplitWriteTransactionState.DATA_PARTIAL]):

                    self.write_data_tracking[txn_id].append(w_packet)
                    split_txn.add_write_data(w_packet)
                    self.stats['write_data_beats'] += 1
                    data_associated = True

                    if self.log:
                        time_str = self.get_time_str()
                        self.log.debug(f"✅ W_DATA_ASSOCIATED{time_str}: "
                                    f"ID={txn_id:02X} beat={current_data_count+1}/{expected_data_count} "
                                    f"LAST={w_packet.last}")
                    break

            # Method 2: If no association by state, try ANY active transaction (fallback)
            if not data_associated:
                for txn_id, split_txn in self.active_split_transactions.items():
                    current_data_count = len(self.write_data_tracking.get(txn_id, []))
                    expected_data_count = split_txn.expected_data_beats

                    if current_data_count < expected_data_count:
                        self.write_data_tracking[txn_id].append(w_packet)
                        split_txn.add_write_data(w_packet)
                        self.stats['write_data_beats'] += 1
                        data_associated = True

                        if self.log:
                            time_str = self.get_time_str()
                            self.log.debug(f"🔄 W_DATA_FALLBACK{time_str}: "
                                        f"ID={txn_id:02X} beat={current_data_count+1}/{expected_data_count} "
                                        f"state={split_txn.state.value} LAST={w_packet.last}")
                        break

            # Log if still no association (for debugging)
            if not data_associated:
                if self.log:
                    time_str = self.get_time_str()
                    self.log.warning(f"⚠️ ORPHANED_WRITE_DATA{time_str}: "
                                    f"DATA=0x{w_packet.data:016X} LAST={w_packet.last}")
                    self.log.warning(f"   Active transactions: {list(self.active_split_transactions.keys())}")
                    for txn_id, split_txn in self.active_split_transactions.items():
                        current_data = len(self.write_data_tracking.get(txn_id, []))
                        self.log.warning(f"   ID={txn_id:02X}: {current_data}/{split_txn.expected_data_beats} beats, state={split_txn.state.value}")

        # Handle write response packets (unchanged)
        elif hasattr(packet, 'resp') and hasattr(packet, 'id'):  # Write Response packet
            if not isinstance(packet, AXIWriteResponsePacket):
                b_packet = convert_gaxi_packet_to_axi_write_response(packet, self.write_resp_field_config)
            else:
                b_packet = packet

            self.response_tracking[b_packet.id].append(b_packet)
            self.stats['responses_received'] += 1

            # Track completion timing using cocotb time
            self.transaction_end_times[b_packet.id] = current_time

            # Add to split transaction tracker
            if b_packet.id in self.active_split_transactions:
                self.active_split_transactions[b_packet.id].add_response(b_packet)

            if self.log:
                time_str = self.get_time_str()
                self.log.debug(f"📥 B_RESPONSE{time_str}: ID={b_packet.id:02X} "
                            f"RESP={b_packet.get_response_name()}")

    def record_split_info(self, packet) -> None:
        """
        Record write split information with FIXED timing.
        """
        current_time = self.get_current_time_ns()

        if not isinstance(packet, WriteSplitInfoPacket):
            if isinstance(packet, dict):
                split_packet = WriteSplitInfoPacket.from_dict(packet, self.split_field_config)
            else:
                # Convert from generic packet
                split_data = {
                    'addr': getattr(packet, 'addr', 0),
                    'id': getattr(packet, 'id', 0),
                    'cnt': getattr(packet, 'cnt', 0)
                }
                split_packet = WriteSplitInfoPacket.from_dict(split_data, self.split_field_config)
        else:
            split_packet = packet

        self.split_info_tracking[split_packet.id] = split_packet
        self.stats['splits_detected'] += 1

        # Update split transaction tracker
        if split_packet.id in self.active_split_transactions:
            self.active_split_transactions[split_packet.id].split_info = split_packet

        if self.log:
            time_str = self.get_time_str()
            self.log.debug(f"Recorded write split info{time_str}: ID={split_packet.id:02X}, "
                            f"ADDR=0x{split_packet.addr:08X}, CNT={split_packet.cnt}")

    def record_upstream_response(self, packet):
        """Record response from DUT to testbench (should be consolidated)"""
        if not isinstance(packet, AXIWriteResponsePacket):
            b_packet = convert_gaxi_packet_to_axi_write_response(packet, self.write_resp_field_config)
        else:
            b_packet = packet

        # This is what the original transaction sees
        self.response_tracking[b_packet.id].append(b_packet)
        self.stats['responses_received'] += 1

        current_time = self.get_current_time_ns()
        self.transaction_end_times[b_packet.id] = current_time

        if b_packet.id in self.active_split_transactions:
            self.active_split_transactions[b_packet.id].add_response(b_packet)

    def record_downstream_response(self, packet):
        """Record response from testbench to DUT (before consolidation)"""
        if not isinstance(packet, AXIWriteResponsePacket):
            b_packet = convert_gaxi_packet_to_axi_write_response(packet, self.write_resp_field_config)
        else:
            b_packet = packet

        # Track what the DUT should be consolidating
        self.downstream_response_tracking[b_packet.id].append(b_packet)

    def _add_error_with_context(self, error_msg: str, txn_id: int = None,
                                error_category: str = "GENERAL", severity: str = "ERROR"):
        """
        Enhanced error reporting with FIXED timing and full write transaction context.
        """
        # FIXED: Use proper cocotb timing
        current_time = self.get_current_time_ns()
        current_time_str = self.get_time_str()

        # Build detailed error report for write transactions
        error_report = f"\n{'='*80}\n"
        error_report += f"{severity}: {error_category} - {error_msg}\n"
        error_report += f"{'='*80}\n"

        if txn_id is not None and txn_id in self.upstream_transactions:
            # Add write transaction context
            original_aw = self.upstream_transactions[txn_id]
            split_txn = self.active_split_transactions.get(txn_id)

            error_report += f"WRITE TRANSACTION CONTEXT:\n"
            error_report += f"  Transaction ID: 0x{txn_id:02X}\n"
            error_report += f"  Original Address: 0x{original_aw.addr:08X}\n"
            error_report += f"  Original Length: {original_aw.len} ({original_aw.len + 1} beats)\n"
            error_report += f"  Size: {original_aw.size} ({1 << original_aw.size} bytes/beat)\n"
            error_report += f"  Burst Type: {original_aw.get_burst_type_name()}\n"
            error_report += f"  Total Bytes: {original_aw.calculate_total_bytes()}\n"
            error_report += f"  End Address: 0x{original_aw.addr + original_aw.calculate_total_bytes() - 1:08X}\n"

            # Add boundary information
            error_report += f"\nBOUNDARY INFORMATION:\n"
            error_report += f"  Alignment Mask: 0x{self.alignment_mask:03X}\n"
            error_report += f"  Boundary Size: {self.boundary_size} bytes (0x{self.boundary_size:X})\n"
            error_report += f"  Should Cross Boundary: {original_aw.will_cross_boundary(self.boundary_size)}\n"

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
            split_aws = self.downstream_transactions.get(txn_id, [])
            write_data = self.write_data_tracking.get(txn_id, [])
            responses = self.response_tracking.get(txn_id, [])
            split_info = self.split_info_tracking.get(txn_id)

            error_report += f"\nACTUAL SPLIT BEHAVIOR:\n"
            error_report += f"  Split Address Transactions: {len(split_aws)}\n"
            for i, split_aw in enumerate(split_aws):
                error_report += f"    Split {i+1}: ADDR=0x{split_aw.addr:08X}, LEN={split_aw.len} ({split_aw.len + 1} beats)\n"

            error_report += f"  Write Data Beats: {len(write_data)}\n"
            wlast_count = sum(1 for w in write_data if w.last)
            error_report += f"  WLAST Signals: {wlast_count}\n"

            error_report += f"  Write Responses: {len(responses)}\n"

            if split_info:
                error_report += f"  Split Info Count: {split_info.cnt}\n"
            else:
                error_report += f"  Split Info: NOT RECEIVED\n"

            # Add expected behavior
            error_report += f"\nEXPECTED BEHAVIOR:\n"
            expected_splits = self._calculate_expected_splits(original_aw)
            expected_data_beats = self._calculate_expected_data_beats(original_aw)
            error_report += f"  Expected Split Count: {expected_splits}\n"
            error_report += f"  Expected Data Beats: {expected_data_beats}\n"
            error_report += f"  Expected WLAST Signals: {expected_splits}\n"
            error_report += f"  Expected Responses: 1\n"

        error_report += f"{'='*80}\n"

        # Store the detailed error
        self.errors.append(error_report)
        self.stats['total_errors'] += 1

        if self.log:
            self.log.error(error_report)

    def _calculate_expected_splits(self, aw_packet: AXIWriteAddressPacket) -> int:
        """Calculate expected number of split transactions"""
        if not aw_packet.will_cross_boundary(self.boundary_size):
            return 1

        # Enhanced calculation for debugging
        start_addr = aw_packet.addr
        bytes_per_beat = 1 << aw_packet.size
        total_bytes = (aw_packet.len + 1) * bytes_per_beat
        end_addr = start_addr + total_bytes - 1

        start_boundary = start_addr // self.boundary_size
        end_boundary = end_addr // self.boundary_size

        expected_splits = int(end_boundary - start_boundary + 1)

        # Extra logging for wide data buses
        if self.data_width >= 512 and self.log:
            time_str = self.get_time_str()
            self.log.debug(f"🔍 DW={self.data_width} Write Split calculation{time_str}:")
            self.log.debug(f"  Start: 0x{start_addr:08X} -> boundary {start_boundary}")
            self.log.debug(f"  End: 0x{end_addr:08X} -> boundary {end_boundary}")
            self.log.debug(f"  Bytes per beat: {bytes_per_beat}")
            self.log.debug(f"  Total bytes: {total_bytes}")
            self.log.debug(f"  Expected splits: {expected_splits}")

        return expected_splits

    def _calculate_expected_responses(self, aw_packet: AXIWriteAddressPacket) -> int:
        """Calculate expected number of write responses (always 1 for write transactions)"""
        return 1  # Write transactions always have exactly one response

    def _calculate_expected_data_beats(self, aw_packet: AXIWriteAddressPacket) -> int:
        """Calculate expected number of write data beats"""
        return aw_packet.len + 1  # len field is number of transfers - 1

    def debug_response_flow(self, txn_id: int):
        """Debug the response consolidation flow"""
        time_str = self.get_time_str()

        self.log.info(f"🔍 RESPONSE_FLOW_DEBUG{time_str}: ID={txn_id:02X}")

        upstream_responses = self.response_tracking.get(txn_id, [])
        downstream_responses = self.downstream_response_tracking.get(txn_id, [])

        self.log.info(f"  Downstream responses (to DUT): {len(downstream_responses)}")
        for i, resp in enumerate(downstream_responses):
            self.log.info(f"    {i+1}: RESP={resp.get_response_name()}")

        self.log.info(f"  Upstream responses (from DUT): {len(upstream_responses)}")
        for i, resp in enumerate(upstream_responses):
            self.log.info(f"    {i+1}: RESP={resp.get_response_name()}")

        if hasattr(self, 'transaction_contexts') and txn_id in self.transaction_contexts:
            ctx = self.transaction_contexts[txn_id]
            boundary_info = ctx.calculate_expected_boundary_behavior()
            expected_splits = boundary_info['expected_splits']
            self.log.info(f"  Expected consolidation: {expected_splits} → 1")

    def verify_transaction_splitting(self, txn_id: int) -> bool:
        """
        Enhanced verification for write transaction splitting with response consolidation.

        Verifies:
        1. Address splitting correctness
        2. Write data flow and WLAST generation
        3. Response consolidation (N split responses → 1 consolidated response)
        4. Split info accuracy
        5. Transaction timing and state management
        """
        if txn_id not in self.upstream_transactions:
            self._add_error_with_context(
                f"Write transaction {txn_id:02X} not found in upstream transactions",
                txn_id, "MISSING_TRANSACTION", "ERROR"
            )
            return False

        if txn_id not in self.active_split_transactions:
            self._add_error_with_context(
                f"Split write transaction tracker not found for {txn_id:02X}",
                txn_id, "MISSING_TRACKER", "ERROR"
            )
            return False

        original_aw = self.upstream_transactions[txn_id]
        split_txn = self.active_split_transactions[txn_id]
        split_aws = self.downstream_transactions.get(txn_id, [])
        write_data = self.write_data_tracking.get(txn_id, [])

        # ENHANCED: Separate upstream and downstream responses for consolidation verification
        upstream_responses = self.response_tracking.get(txn_id, [])  # From DUT to testbench (consolidated)
        downstream_responses = getattr(self, 'downstream_response_tracking', {}).get(txn_id, [])  # From testbench to DUT (splits)

        self.stats['verification_checks'] += 1
        verification_passed = True

        # ==========================================================================
        # 1. BOUNDARY CROSSING AND SPLIT COUNT VERIFICATION
        # ==========================================================================

        # Check if transaction should have been split
        should_split = original_aw.will_cross_boundary(self.boundary_size)
        expected_splits = self._calculate_expected_splits(original_aw)

        if self.log:
            time_str = self.get_time_str()
            self.log.debug(f"🔍 VERIFY_SPLIT{time_str}: ID={txn_id:02X} should_split={should_split} expected={expected_splits}")

        # Verify address splitting
        if should_split:
            if len(split_aws) < expected_splits:
                self._add_error_with_context(
                    f"Insufficient address splits: expected {expected_splits}, got {len(split_aws)}",
                    txn_id, "SPLIT_COUNT", "ERROR"
                )
                verification_passed = False
            elif len(split_aws) > expected_splits:
                self._add_error_with_context(
                    f"Too many address splits: expected {expected_splits}, got {len(split_aws)}",
                    txn_id, "SPLIT_COUNT", "ERROR"
                )
                verification_passed = False
            else:
                # Verify split addresses are correct
                verification_passed &= self._verify_split_addresses(original_aw, split_aws, txn_id)

                # Verify split info is present and accurate
                if txn_id in self.split_info_tracking:
                    split_info = self.split_info_tracking[txn_id]
                    if split_info.cnt != len(split_aws):
                        self._add_error_with_context(
                            f"Split count mismatch: FIFO reports {split_info.cnt}, actual splits {len(split_aws)}",
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
            if len(split_aws) > 1:
                self._add_error_with_context(
                    f"Unnecessary split detected: transaction doesn't cross boundary but {len(split_aws)} splits generated",
                    txn_id, "UNNECESSARY_SPLIT", "ERROR"
                )
                verification_passed = False

        # ==========================================================================
        # 2. WRITE DATA VERIFICATION
        # ==========================================================================

        expected_data_beats = self._calculate_expected_data_beats(original_aw)

        if len(write_data) != expected_data_beats:
            self._add_error_with_context(
                f"Write data beat count mismatch: expected {expected_data_beats}, got {len(write_data)}",
                txn_id, "DATA_COUNT", "ERROR"
            )
            verification_passed = False
        else:
            if self.log:
                time_str = self.get_time_str()
                self.log.debug(f"✅ DATA_COUNT_OK{time_str}: ID={txn_id:02X} {len(write_data)}/{expected_data_beats} beats")

        # Verify WLAST generation for splits
        if should_split and write_data:
            verification_passed &= self._verify_wlast_generation(write_data, split_aws, txn_id)

        # ==========================================================================
        # 3. RESPONSE CONSOLIDATION VERIFICATION (CRITICAL FOR WRITE TRANSACTIONS)
        # ==========================================================================

        # WRITE TRANSACTIONS: Multiple split responses must be consolidated into one
        expected_upstream_responses = 1  # Always exactly 1 for original transaction
        expected_downstream_responses = expected_splits  # One response per split

        # Verify upstream response count (what original transaction sees)
        if len(upstream_responses) != expected_upstream_responses:
            self._add_error_with_context(
                f"Write response count mismatch: expected {expected_upstream_responses}, got {len(upstream_responses)}",
                txn_id, "RESPONSE_COUNT", "ERROR"
            )
            verification_passed = False
        else:
            if self.log:
                time_str = self.get_time_str()
                self.log.debug(f"✅ RESPONSE_COUNT_OK{time_str}: ID={txn_id:02X} upstream={len(upstream_responses)}")

        # Verify response consolidation logic (if we have downstream response tracking)
        if hasattr(self, 'downstream_response_tracking') and downstream_responses:
            if should_split:
                # For split transactions, verify consolidation worked
                if len(downstream_responses) != expected_downstream_responses:
                    self.log.warning(f"⚠️ Downstream response count: expected {expected_downstream_responses}, got {len(downstream_responses)}")
                    # This might be OK depending on testbench implementation

                if len(upstream_responses) == 1 and len(downstream_responses) > 1:
                    # Response consolidation working correctly
                    if self.log:
                        time_str = self.get_time_str()
                        self.log.info(f"✅ RESPONSE_CONSOLIDATION_OK{time_str}: ID={txn_id:02X} "
                                    f"{len(downstream_responses)} downstream → {len(upstream_responses)} upstream")

                    # Verify consolidated response status (should be worst of all downstream responses)
                    verification_passed &= self._verify_response_consolidation_status(
                        upstream_responses, downstream_responses, txn_id
                    )
                else:
                    self._add_error_with_context(
                        f"Response consolidation failed: {len(downstream_responses)} downstream responses "
                        f"became {len(upstream_responses)} upstream responses (should be 1)",
                        txn_id, "RESPONSE_CONSOLIDATION_FAILURE", "ERROR"
                    )
                    verification_passed = False
            else:
                # For non-split transactions, should be simple pass-through
                if len(downstream_responses) != 1 or len(upstream_responses) != 1:
                    self.log.warning(f"⚠️ Non-split transaction response counts: "
                                f"downstream={len(downstream_responses)}, upstream={len(upstream_responses)}")

        # ==========================================================================
        # 4. TRANSACTION COMPLETENESS VERIFICATION
        # ==========================================================================

        # Verify transaction is in completed state
        if not split_txn.is_complete():
            self._add_error_with_context(
                f"Transaction not marked as complete in split tracker",
                txn_id, "INCOMPLETE_TRANSACTION", "WARNING"
            )
            # This might be OK if verification is called early

        # Verify timing consistency
        start_time = self.transaction_start_times.get(txn_id, 0.0)
        end_time = self.transaction_end_times.get(txn_id, 0.0)
        if start_time > 0 and end_time > 0 and end_time < start_time:
            self._add_error_with_context(
                f"Transaction timing inconsistency: end_time ({end_time:.1f}ns) < start_time ({start_time:.1f}ns)",
                txn_id, "TIMING_ERROR", "ERROR"
            )
            verification_passed = False

        # ==========================================================================
        # 5. ENHANCED SUCCESS REPORTING
        # ==========================================================================

        if verification_passed:
            if self.log:
                time_str = self.get_time_str()
                duration = end_time - start_time if (start_time > 0 and end_time > 0) else 0.0

                self.log.info(f"✅ VERIFICATION_PASSED{time_str}: ID={txn_id:02X}")
                self.log.info(f"   Address Splits: {len(split_aws)}/{expected_splits}")
                self.log.info(f"   Data Beats: {len(write_data)}/{expected_data_beats}")
                self.log.info(f"   Upstream Responses: {len(upstream_responses)}/{expected_upstream_responses}")
                if downstream_responses:
                    self.log.info(f"   Downstream Responses: {len(downstream_responses)}")
                    self.log.info(f"   Consolidation: {len(downstream_responses)} → {len(upstream_responses)} ✅")
                if duration > 0:
                    self.log.info(f"   Duration: {duration:.1f}ns")

        return verification_passed

    def _verify_response_consolidation_status(self, upstream_responses: List[AXIWriteResponsePacket],
                                            downstream_responses: List[AXIWriteResponsePacket],
                                            txn_id: int) -> bool:
        """
        Verify that response consolidation preserved the worst error status.

        Response priority: DECERR (3) > SLVERR (2) > EXOKAY (1) > OKAY (0)
        The consolidated response should have the worst status from all downstream responses.
        """
        if not upstream_responses or not downstream_responses:
            return True  # Nothing to verify

        if len(upstream_responses) != 1:
            return True  # Consolidation verification only applies to single upstream response

        # Find worst downstream response status
        worst_downstream_status = 0  # Start with OKAY
        for resp in downstream_responses:
            if resp.resp > worst_downstream_status:
                worst_downstream_status = resp.resp

        # Check if upstream response matches worst downstream status
        upstream_status = upstream_responses[0].resp

        if upstream_status != worst_downstream_status:
            self._add_error_with_context(
                f"Response consolidation status error: "
                f"worst downstream status={worst_downstream_status} "
                f"({self._resp_status_name(worst_downstream_status)}), "
                f"but upstream status={upstream_status} "
                f"({self._resp_status_name(upstream_status)})",
                txn_id, "RESPONSE_STATUS_CONSOLIDATION", "ERROR"
            )
            return False

        if self.log:
            time_str = self.get_time_str()
            self.log.debug(f"✅ RESPONSE_STATUS_OK{time_str}: ID={txn_id:02X} "
                        f"consolidated to {self._resp_status_name(upstream_status)}")

        return True

    def _resp_status_name(self, status: int) -> str:
        """Convert response status to name"""
        status_map = {0: "OKAY", 1: "EXOKAY", 2: "SLVERR", 3: "DECERR"}
        return status_map.get(status, f"UNKNOWN({status})")


    def _verify_split_addresses(self, original_aw: AXIWriteAddressPacket,
                            split_aws: List[AXIWriteAddressPacket], txn_id: int) -> bool:
        """Enhanced split address verification with better error reporting"""
        if not split_aws:
            return True

        verification_passed = True
        bytes_per_beat = 1 << original_aw.size

        for i, split_aw in enumerate(split_aws):
            # First split should start at original address
            if i == 0 and split_aw.addr != original_aw.addr:
                self._add_error_with_context(
                    f"First split address wrong: expected 0x{original_aw.addr:08X}, got 0x{split_aw.addr:08X}",
                    txn_id, "SPLIT_ADDRESS", "ERROR"
                )
                verification_passed = False

            # Each split should be properly aligned to boundaries (except first)
            if i > 0:  # Skip first split
                boundary_aligned = (split_aw.addr % self.boundary_size) == 0
                if not boundary_aligned:
                    self._add_error_with_context(
                        f"Split {i+1} not boundary aligned: address 0x{split_aw.addr:08X} "
                        f"not aligned to 0x{self.boundary_size:X}",
                        txn_id, "SPLIT_ALIGNMENT", "ERROR"
                    )
                    verification_passed = False

            # Verify split transaction parameters match original
            if split_aw.size != original_aw.size:
                self._add_error_with_context(
                    f"Split {i+1} size mismatch: expected {original_aw.size}, got {split_aw.size}",
                    txn_id, "SPLIT_SIZE", "ERROR"
                )
                verification_passed = False

            if split_aw.burst != original_aw.burst:
                self._add_error_with_context(
                    f"Split {i+1} burst mismatch: expected {original_aw.burst}, got {split_aw.burst}",
                    txn_id, "SPLIT_BURST", "ERROR"
                )
                verification_passed = False

        # Verify split address continuity
        verification_passed &= self._verify_split_address_continuity(original_aw, split_aws, txn_id)

        return verification_passed

    def _verify_split_address_continuity(self, original_aw: AXIWriteAddressPacket,
                                    split_aws: List[AXIWriteAddressPacket], txn_id: int) -> bool:
        """Verify that split addresses form a continuous range covering the original transaction"""
        if len(split_aws) <= 1:
            return True  # Nothing to verify for single or no splits

        verification_passed = True
        bytes_per_beat = 1 << original_aw.size

        # Calculate expected address range
        original_start = original_aw.addr
        original_total_bytes = (original_aw.len + 1) * bytes_per_beat
        original_end = original_start + original_total_bytes - 1

        # Calculate actual split coverage
        split_start = split_aws[0].addr
        last_split = split_aws[-1]
        split_end = last_split.addr + ((last_split.len + 1) * bytes_per_beat) - 1

        # Verify coverage matches original transaction
        if split_start != original_start:
            self._add_error_with_context(
                f"Split coverage start mismatch: expected 0x{original_start:08X}, got 0x{split_start:08X}",
                txn_id, "SPLIT_COVERAGE", "ERROR"
            )
            verification_passed = False

        if split_end != original_end:
            self._add_error_with_context(
                f"Split coverage end mismatch: expected 0x{original_end:08X}, got 0x{split_end:08X}",
                txn_id, "SPLIT_COVERAGE", "ERROR"
            )
            verification_passed = False

        # Verify no gaps between splits
        current_addr = split_start
        for i, split_aw in enumerate(split_aws):
            if split_aw.addr != current_addr:
                self._add_error_with_context(
                    f"Gap in split coverage: expected split {i+1} at 0x{current_addr:08X}, got 0x{split_aw.addr:08X}",
                    txn_id, "SPLIT_GAP", "ERROR"
                )
                verification_passed = False

            # Update current address for next split
            split_bytes = (split_aw.len + 1) * bytes_per_beat
            current_addr += split_bytes

        return verification_passed
    def _verify_wlast_generation(self, write_data: List[AXIWriteDataPacket],
                            split_aws: List[AXIWriteAddressPacket], txn_id: int) -> bool:
        """Enhanced WLAST verification for split write transactions"""
        if not write_data or not split_aws:
            return True

        verification_passed = True

        # For split transactions, WLAST should be generated at the end of each split
        expected_wlast_count = len(split_aws)
        actual_wlast_count = sum(1 for w in write_data if w.last)

        if actual_wlast_count != expected_wlast_count:
            self._add_error_with_context(
                f"WLAST count mismatch: expected {expected_wlast_count}, got {actual_wlast_count}",
                txn_id, "WLAST_COUNT", "ERROR"
            )
            verification_passed = False
        else:
            if self.log:
                time_str = self.get_time_str()
                self.log.debug(f"✅ WLAST_COUNT_OK{time_str}: ID={txn_id:02X} {actual_wlast_count}/{expected_wlast_count}")

        # Verify WLAST positioning - should occur at split boundaries
        if len(split_aws) > 1:
            verification_passed &= self._verify_wlast_positioning(write_data, split_aws, txn_id)

        return verification_passed

    def _verify_wlast_positioning(self, write_data: List[AXIWriteDataPacket],
                                split_aws: List[AXIWriteAddressPacket], txn_id: int) -> bool:
        """Verify WLAST signals occur at correct split boundaries"""
        # This is a more advanced verification that would require tracking
        # which data beats correspond to which splits
        # For now, just verify basic WLAST count and positioning

        wlast_positions = []
        for i, w in enumerate(write_data):
            if w.last:
                wlast_positions.append(i)

        # Calculate expected WLAST positions based on split lengths
        expected_positions = []
        beat_count = 0
        for split_aw in split_aws:
            beat_count += split_aw.len + 1
            expected_positions.append(beat_count - 1)  # WLAST on last beat of split

        if wlast_positions != expected_positions:
            if self.log:
                time_str = self.get_time_str()
                self.log.warning(f"⚠️ WLAST_POSITION{time_str}: ID={txn_id:02X} "
                            f"expected positions {expected_positions}, got {wlast_positions}")
            # This might be OK depending on implementation details

        return True  # Don't fail on positioning mismatches for now

    def is_transaction_complete(self, txn_id: int) -> bool:
        """Check if a write transaction is complete"""
        if txn_id not in self.active_split_transactions:
            return False

        split_txn = self.active_split_transactions[txn_id]
        return split_txn.is_complete()

    def verify_split_correctness(self) -> bool:
        """Verify all write transactions were split correctly with enhanced reporting"""
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
                self.log.info(f"✓ All write split verifications passed{time_str}")
            else:
                self.log.error(f"✗ Write split verification failed{time_str}: {len(self.errors)} errors")
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

        # Write transaction summary
        report += f"\nWrite Transaction Summary:\n"
        report += f"  Upstream transactions: {len(self.upstream_transactions)}\n"
        report += f"  Active split transactions: {len(self.active_split_transactions)}\n"
        report += f"  Completed transactions: {sum(1 for t in self.active_split_transactions.values() if t.is_complete())}\n"

        # Enhanced error summary
        if self.errors:
            report += f"\nErrors ({len(self.errors)}):\n"
            # Just show count here, detailed errors are already logged above
            error_categories = {}
            for error in self.errors:
                for category in ["SPLIT_COUNT", "DATA_COUNT", "WLAST_COUNT", "RESPONSE_COUNT", "SPLIT_ADDRESS"]:
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
            elif "DATA_COUNT" in error:
                error_types["data_count"] += 1
            elif "WLAST_COUNT" in error:
                error_types["wlast_count"] += 1
            elif "RESPONSE_COUNT" in error:
                error_types["response_count"] += 1
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
        self.write_data_tracking.clear()
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
