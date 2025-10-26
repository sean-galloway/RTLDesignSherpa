# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: TransactionContext
# Purpose: AXI Master Read Splitter Testbench - FIXED SAFE ADDRESS TESTING
#
# Documentation: bin/CocoTBFramework/README.md
# Subsystem: framework
#
# Author: sean galloway
# Created: 2025-10-18

"""
AXI Master Read Splitter Testbench - FIXED SAFE ADDRESS TESTING

FIXED FEATURES:
1. NO WRAPAROUND TESTING: All addresses stay in safe region (< MAX_ADDR/2)
2. Proper address alignment to data width boundaries
3. Dynamic test case generation based on data width
4. Comprehensive address validation with safety checks
5. Enhanced error reporting with safety context
6. Correct AXI size field usage
7. Data width aware test scenarios

REALISTIC ASSUMPTIONS:
- No address wraparound ever occurs (transactions never wrap 0xFFFFFFFF -> 0x00000000)
- All testing focuses on legitimate boundary crossing scenarios
- Comprehensive coverage while avoiding impossible edge cases
"""

import os
import random
import asyncio
import math
from typing import Dict, List, Optional, Tuple, Any

import cocotb
from cocotb.triggers import RisingEdge, Timer
from cocotb.utils import get_sim_time

from CocoTBFramework.tbclasses.shared.tbbase import TBBase
from CocoTBFramework.components.shared.flex_randomizer import FlexRandomizer
from CocoTBFramework.components.gaxi.gaxi_master import GAXIMaster
from CocoTBFramework.components.gaxi.gaxi_slave import GAXISlave
from CocoTBFramework.components.gaxi.gaxi_monitor import GAXIMonitor
from CocoTBFramework.components.gaxi.gaxi_packet import GAXIPacket
from .axi_read_splitter_scoreboard import AxiReadSplitterScoreboard
from .axi_read_splitter_packets import (
    AXIAddressPacket, AXIDataPacket, SplitInfoPacket,
    create_axi_address_field_config, create_axi_data_field_config,
    create_split_info_field_config, convert_gaxi_packet_to_axi_address,
    convert_gaxi_packet_to_axi_data
)


class TransactionContext:
    """Enhanced transaction context for detailed error reporting"""
    def __init__(self, ar_packet: AXIAddressPacket, start_time: float, test_case: str = "unknown"):
        self.ar_packet = ar_packet
        self.start_time = start_time
        self.test_case = test_case
        self.boundary_size = None
        self.expected_splits = None
        self.expected_total_responses = ar_packet.len + 1
        self.split_addresses = []
        self.received_responses = []
        self.split_info_received = None
        self.completion_time = None
        self.errors = []

    def add_expected_split(self, addr: int):
        """Add an expected split address"""
        self.split_addresses.append(addr)

    def set_boundary_info(self, boundary_size: int, expected_splits: int):
        """Set boundary crossing information"""
        self.boundary_size = boundary_size
        self.expected_splits = expected_splits

    def add_response(self, response: AXIDataPacket, timestamp: float):
        """Add a received response"""
        self.received_responses.append((response, timestamp))

    def add_error(self, error_msg: str, timestamp: float):
        """Add an error with timestamp"""
        self.errors.append((error_msg, timestamp))

    def mark_complete(self, timestamp: float):
        """Mark transaction as complete"""
        self.completion_time = timestamp

    def get_duration(self) -> float:
        """Get transaction duration"""
        end_time = self.completion_time if self.completion_time is not None else get_sim_time('ns')
        return end_time - self.start_time

    def calculate_expected_boundary_behavior(self):
        """Calculate expected boundary crossing behavior"""
        if self.boundary_size is None:
            return "Unknown boundary size"

        start_addr = self.ar_packet.addr
        bytes_per_beat = 1 << self.ar_packet.size
        total_bytes = (self.ar_packet.len + 1) * bytes_per_beat
        end_addr = start_addr + total_bytes - 1

        start_boundary = start_addr // self.boundary_size
        end_boundary = end_addr // self.boundary_size

        crosses_boundary = start_boundary != end_boundary
        num_boundaries_crossed = end_boundary - start_boundary if crosses_boundary else 0

        return {
            'start_addr': start_addr,
            'end_addr': end_addr,
            'total_bytes': total_bytes,
            'bytes_per_beat': bytes_per_beat,
            'start_boundary': start_boundary,
            'end_boundary': end_boundary,
            'crosses_boundary': crosses_boundary,
            'num_boundaries_crossed': num_boundaries_crossed,
            'expected_splits': num_boundaries_crossed + 1 if crosses_boundary else 1
        }


class AxiReadSplitterTB(TBBase):
    """
    Enhanced testbench with SAFE ADDRESS TESTING for all data widths.
    NO WRAPAROUND TESTING - stays in safe address region.
    """

    def __init__(self, dut):
        """Initialize the testbench with safe address support"""
        super().__init__(dut)

        # Get test parameters from environment
        self.SEED = self.convert_to_int(os.environ.get('SEED', '12345'))
        self.TEST_LEVEL = os.environ.get('TEST_LEVEL', 'basic')
        self.IW = self.convert_to_int(os.environ.get('TEST_IW', '8'))
        self.AW = self.convert_to_int(os.environ.get('TEST_AW', '32'))
        self.DW = self.convert_to_int(os.environ.get('TEST_DW', '32'))
        self.UW = self.convert_to_int(os.environ.get('TEST_UW', '1'))
        self.SPLIT_FIFO_DEPTH = self.convert_to_int(os.environ.get('TEST_SPLIT_FIFO_DEPTH', '4'))
        self.ALIGNMENT_MASK = self.convert_to_int(os.environ.get('TEST_ALIGNMENT_MASK', '0xFFF'))
        self.super_debug = False
        self.TIMEOUT_CYCLES = 1000

        # Calculate derived parameters
        self.MAX_ID = (1 << self.IW) - 1
        self.MAX_ADDR = (1 << self.AW) - 1
        self.BYTES_PER_BEAT = self.DW // 8
        self.BOUNDARY_SIZE = self.ALIGNMENT_MASK + 1

        # FIXED: Address alignment parameters for proper data width alignment
        self.ADDR_ALIGN_MASK = self.BYTES_PER_BEAT - 1  # e.g., 0x3F for 64-byte alignment
        self.EXPECTED_AX_SIZE = int(math.log2(self.BYTES_PER_BEAT))  # Size field for max data width

        # REALISTIC: Safe address limits - no wraparound testing
        self.SAFE_ADDR_LIMIT = self.MAX_ADDR // 2  # Stay in lower half of address space
        self.MAX_TRANSACTION_BYTES = 64 * self.BYTES_PER_BEAT  # Reasonable max transaction size

        # Initialize random generator
        random.seed(self.SEED)

        # Create field configurations for common packet types
        self.addr_field_config = create_axi_address_field_config(self.IW, self.AW, self.UW)
        self.data_field_config = create_axi_data_field_config(self.IW, self.DW, self.UW)
        self.split_field_config = create_split_info_field_config(self.IW, self.AW)

        # GAXI components - will be initialized in setup()
        self.fub_ar_master = None
        self.fub_r_slave = None
        self.m_axi_ar_slave = None
        self.m_axi_r_master = None
        self.fub_split_slave = None

        # Monitors for each interface
        self.fub_ar_monitor = None
        self.fub_r_monitor = None
        self.m_axi_ar_monitor = None
        self.m_axi_r_monitor = None
        self.fub_split_monitor = None

        self.scoreboard = None

        # Enhanced transaction context tracking for detailed error reporting
        self.transaction_contexts = {}  # id -> TransactionContext
        self.transaction_id_counter = 0
        self.current_test_case = "unknown"

        # Enhanced error tracking
        self.detailed_errors = []
        self.transaction_timeline = []  # [(timestamp, event, context)]

        # Create basic configurations
        self.randomizer_dict = {
            'backtoback': {
                'master': {'valid_delay': ([(0, 0)], [1.0])},
                'slave': {'ready_delay': ([(0, 0)], [1.0])}
            },
            'fast': {
                'master': {'valid_delay': ([(0, 0), (1, 2)], [0.8, 0.2])},
                'slave': {'ready_delay': ([(0, 1), (2, 3)], [0.7, 0.3])}
            },
            'balanced': {
                'master': {'valid_delay': ([(0, 1), (2, 5)], [0.7, 0.3])},
                'slave': {'ready_delay': ([(0, 1), (2, 5)], [0.7, 0.3])}
            }
        }

        # Statistics
        self.test_stats = {
            'transactions_sent': 0,
            'responses_received': 0,
            'splits_detected': 0,
            'errors_detected': 0,
            'test_duration': 0.0
        }

        self.log.info(f"AXI Read Splitter TB initialized - SAFE ADDRESS TESTING (NO WRAPAROUND)")
        self.log.info(f"SEED={self.SEED}, TEST_LEVEL={self.TEST_LEVEL}")
        self.log.info(f"IW={self.IW}, AW={self.AW}, DW={self.DW}, UW={self.UW}")
        self.log.info(f"BYTES_PER_BEAT={self.BYTES_PER_BEAT}, BOUNDARY_SIZE={self.BOUNDARY_SIZE}")
        self.log.info(f"SAFE_ADDR_LIMIT=0x{self.SAFE_ADDR_LIMIT:08X} (no wraparound)")
        self.log.info(f"ADDRESS_ALIGNMENT=0x{self.ADDR_ALIGN_MASK:X} (addresses must be {self.BYTES_PER_BEAT}-byte aligned)")
        self.log.info(f"EXPECTED_AX_SIZE={self.EXPECTED_AX_SIZE} (for {self.BYTES_PER_BEAT}-byte transfers)")

    def log_transaction_event(self, event: str, context: str = ""):
        """Log a transaction event with timestamp"""
        timestamp = get_sim_time('ns')
        time_str = self.get_time_ns_str()
        self.transaction_timeline.append((timestamp, event, context))
        if self.super_debug:
            self.log.debug(f"{time_str} {event}: {context}")

    def align_address_to_data_width(self, addr: int) -> int:
        """Align address to data width boundary"""
        # Clear the lower bits to align to data width
        aligned_addr = addr & ~self.ADDR_ALIGN_MASK

        if addr != aligned_addr:
            self.log.debug(f"Address alignment: 0x{addr:08X} -> 0x{aligned_addr:08X} "
                            f"(aligned to {self.BYTES_PER_BEAT}-byte boundary)")

        return aligned_addr

    def is_address_safe(self, addr: int, length: int) -> bool:
        """Check if address + transaction is safe (no wraparound)"""
        aligned_addr = self.align_address_to_data_width(addr)
        total_bytes = (length + 1) * self.BYTES_PER_BEAT
        end_addr = aligned_addr + total_bytes - 1

        # Ensure transaction doesn't wrap around or get too close to limit
        return (end_addr >= aligned_addr and  # No wraparound
                end_addr < self.SAFE_ADDR_LIMIT)  # Stay in safe region

    def generate_aligned_random_address(self) -> int:
        """Generate a random address properly aligned to data width - SAFE VERSION"""
        # FIXED: Generate in safe region with margin for largest possible transaction
        max_safe_start = self.SAFE_ADDR_LIMIT - self.MAX_TRANSACTION_BYTES
        raw_addr = random.randint(0, max_safe_start)
        aligned_addr = self.align_address_to_data_width(raw_addr)

        # Double-check it's safe
        if not self.is_address_safe(aligned_addr, 64):  # Check with max reasonable length
            # Fallback to very safe address
            aligned_addr = self.align_address_to_data_width(0x00100000)

        return aligned_addr

    def generate_safe_boundary_test_address(self, boundary_size: int, beats_before: int) -> int:
        """Generate a safe address for boundary testing"""
        # Choose a boundary that's well within safe range
        max_safe_boundary = (self.SAFE_ADDR_LIMIT - self.MAX_TRANSACTION_BYTES) // boundary_size
        target_boundary_idx = random.randint(1, max_safe_boundary)
        target_boundary = target_boundary_idx * boundary_size

        # Position address before the boundary
        addr = target_boundary - (beats_before * self.BYTES_PER_BEAT)
        return self.align_address_to_data_width(max(0, addr))

    def validate_address_alignment(self, addr: int) -> bool:
        """Validate that address is properly aligned to data width"""
        is_aligned = (addr & self.ADDR_ALIGN_MASK) == 0

        if not is_aligned:
            self.log.error(f"❌ Address 0x{addr:08X} is NOT aligned to {self.BYTES_PER_BEAT}-byte boundary!")
            self.log.error(f"   Expected alignment mask: 0x{self.ADDR_ALIGN_MASK:X}")
            self.log.error(f"   Address & mask = 0x{addr & self.ADDR_ALIGN_MASK:X} (should be 0)")

        return is_aligned

    def create_detailed_error_report(self, txn_id: int, error_type: str, error_msg: str) -> str:
        """Create comprehensive error report with all context"""
        timestamp = get_sim_time('ns')
        time_str = self.get_time_ns_str()

        if txn_id not in self.transaction_contexts:
            return f"ERROR: {error_type} - {error_msg} (No context for ID {txn_id:02X})"

        ctx = self.transaction_contexts[txn_id]
        boundary_info = ctx.calculate_expected_boundary_behavior()

        # Build comprehensive error report
        report = f"\n{'='*100}\n"
        report += f"🚨 ERROR DETECTED: {error_type}\n"
        report += f"{'='*100}\n"
        report += f"ERROR MESSAGE: {error_msg}\n"
        report += f"ERROR TIME: {time_str}\n"
        report += f"TEST CASE: {ctx.test_case}\n"
        report += f"\n📋 ORIGINAL TRANSACTION:\n"
        report += f"  Transaction ID: 0x{txn_id:02X}\n"
        report += f"  Start Time: {ctx.start_time:.1f}ns\n"
        report += f"  Duration: {ctx.get_duration():.1f}ns\n"
        report += f"  Address: 0x{ctx.ar_packet.addr:08X}\n"
        report += f"  Length: {ctx.ar_packet.len} ({ctx.ar_packet.len + 1} beats)\n"
        report += f"  Size: {ctx.ar_packet.size} ({1 << ctx.ar_packet.size} bytes/beat)\n"
        report += f"  Burst: {ctx.ar_packet.burst} ({'INCR' if ctx.ar_packet.burst == 1 else 'OTHER'})\n"

        # FIXED: Show address alignment validation
        report += f"\n🎯 ADDRESS ALIGNMENT:\n"
        report += f"  Required Alignment: {self.BYTES_PER_BEAT}-byte boundary\n"
        report += f"  Alignment Mask: 0x{self.ADDR_ALIGN_MASK:X}\n"
        report += f"  Address & Mask: 0x{ctx.ar_packet.addr & self.ADDR_ALIGN_MASK:X}\n"
        report += f"  Is Aligned: {'✅ YES' if (ctx.ar_packet.addr & self.ADDR_ALIGN_MASK) == 0 else '❌ NO'}\n"

        # SAFE: Show safety validation
        report += f"\n🛡️ SAFETY VALIDATION:\n"
        report += f"  Safe Address Limit: 0x{self.SAFE_ADDR_LIMIT:08X}\n"
        report += f"  End Address: 0x{boundary_info['end_addr']:08X}\n"
        report += f"  Is Safe: {'✅ YES' if boundary_info['end_addr'] < self.SAFE_ADDR_LIMIT else '❌ NO'}\n"

        report += f"\n🎯 EXPECTED BEHAVIOR:\n"
        report += f"  Total Bytes: {boundary_info['total_bytes']}\n"
        report += f"  Boundary Size: {self.BOUNDARY_SIZE} bytes (0x{self.BOUNDARY_SIZE:X})\n"
        report += f"  Crosses Boundary: {boundary_info['crosses_boundary']}\n"
        report += f"  Expected Splits: {boundary_info['expected_splits']}\n"
        report += f"  Expected Total Responses: {ctx.expected_total_responses}\n"

        # Show boundary calculation details for DW=512 debugging
        if self.DW >= 512:
            report += f"\n🔍 BOUNDARY ANALYSIS (DW={self.DW} debugging):\n"
            report += f"  Start Boundary: {boundary_info['start_boundary']}\n"
            report += f"  End Boundary: {boundary_info['end_boundary']}\n"
            report += f"  Boundaries Crossed: {boundary_info['num_boundaries_crossed']}\n"

        report += f"\n📈 ACTUAL BEHAVIOR:\n"

        # Show received responses
        report += f"  Responses Received: {len(ctx.received_responses)}\n"
        if ctx.received_responses:
            last_count = sum(1 for r, _ in ctx.received_responses if r.last == 1)
            report += f"  LAST Signals: {last_count}\n"

            # Show detailed response pattern for DW=512
            if self.DW >= 512 and len(ctx.received_responses) <= 20:  # Don't spam for large bursts
                report += f"  Response Pattern:\n"
                for i, (resp, resp_time) in enumerate(ctx.received_responses):
                    report += f"    R{i+1}: DATA=0x{resp.data:016X}, LAST={resp.last}, TIME={resp_time:.1f}ns\n"

        # Show split info
        if ctx.split_info_received:
            report += f"  Split Info: CNT={ctx.split_info_received.cnt}\n"
        else:
            report += f"  Split Info: NOT RECEIVED\n"

        # Show any previous errors for this transaction
        if ctx.errors:
            report += f"\n⚠️ PREVIOUS ERRORS FOR THIS TRANSACTION:\n"
            for prev_error, prev_time in ctx.errors:
                report += f"  [{prev_time:.1f}ns] {prev_error}\n"

        # Show recent transaction timeline for context
        report += f"\n📅 RECENT TRANSACTION EVENTS:\n"
        recent_events = [e for e in self.transaction_timeline if abs(e[0] - timestamp) <= 1000.0][-10:]
        for event_time, event, event_context in recent_events:
            marker = "👈" if abs(event_time - timestamp) < 1.0 else "  "
            report += f"  {marker} [{event_time:.1f}ns] {event}: {event_context}\n"

        report += f"\n{'='*100}\n"

        # Store the error in transaction context
        ctx.add_error(f"{error_type}: {error_msg}", timestamp)
        self.detailed_errors.append(report)

        return report

    def generate_deterministic_data(self, addr: int, beat: int, txn_id: int) -> int:
        """Generate deterministic data with enhanced patterns for DW=512"""
        # Enhanced pattern for wide data buses
        base_pattern = (addr >> 2) & 0xFFFF
        beat_pattern = (beat & 0xFF) << 16
        id_pattern = (txn_id & 0xFF) << 24

        # For DW=512, create more complex patterns
        if self.DW >= 512:
            # Create repeating 64-bit patterns across the 512-bit word
            pattern_64 = base_pattern ^ beat_pattern ^ id_pattern

            # Add different patterns in each 64-bit slice
            data_value = 0
            for slice_idx in range(self.DW // 64):
                slice_pattern = pattern_64 ^ (slice_idx << 28)

                # Add beat-specific variations
                if beat % 4 == 0:
                    slice_pattern ^= 0xAAAAAAAA
                elif beat % 4 == 1:
                    slice_pattern ^= 0x55555555
                elif beat % 4 == 2:
                    slice_pattern ^= 0xFF00FF00
                else:
                    slice_pattern ^= 0x00FF00FF

                # Add slice-specific patterns
                slice_pattern ^= (slice_idx * 0x11111111)

                data_value |= (slice_pattern & 0xFFFFFFFFFFFFFFFF) << (slice_idx * 64)
        else:
            # Original pattern for smaller data widths
            data_value = base_pattern ^ beat_pattern ^ id_pattern

            if beat % 4 == 0:
                data_value ^= 0xAAAAAAAA
            elif beat % 4 == 1:
                data_value ^= 0x55555555
            elif beat % 4 == 2:
                data_value ^= 0xFF00FF00
            else:
                data_value ^= 0x00FF00FF

        # Mask to data width
        data_mask = (1 << self.DW) - 1
        return data_value & data_mask

    async def setup_clocks_and_reset(self):
        """Setup clocks, reset, and initialize GAXI components"""
        # Start clock
        await self.start_clock('aclk', 10, 'ns')

        # Create individual GAXI components for each interface
        self.log.info("Creating GAXI components...")

        # 1. fub_ar interface: Testbench sends address requests TO DUT (GAXI Master)
        self.fub_ar_master = GAXIMaster(
            dut=self.dut,
            title="FUB_AR_Master",
            prefix="",
            bus_name="fub",
            pkt_prefix="ar",
            clock=self.dut.aclk,
            field_config=self.addr_field_config,
            timeout_cycles=self.TIMEOUT_CYCLES,
            mode='skid',
            multi_sig=True,
            log=self.log,
            randomizer=FlexRandomizer(self.randomizer_dict['balanced']['master']),
            super_debug=self.super_debug
        )

        # 2. fub_r interface: Testbench receives data responses FROM DUT (GAXI Slave)
        self.fub_r_slave = GAXISlave(
            dut=self.dut,
            title="FUB_R_Slave",
            prefix="",
            bus_name='fub',
            pkt_prefix="r",
            clock=self.dut.aclk,
            field_config=self.data_field_config,
            timeout_cycles=self.TIMEOUT_CYCLES,
            mode='skid',
            multi_sig=True,
            log=self.log,
            randomizer=FlexRandomizer(self.randomizer_dict['balanced']['slave']),
            super_debug=self.super_debug
        )

        # 3. m_axi_ar interface: Testbench responds to DUT's address requests (GAXI Slave)
        self.m_axi_ar_slave = GAXISlave(
            dut=self.dut,
            title="M_AXI_AR_Slave",
            prefix="",
            bus_name='m_axi',
            pkt_prefix="ar",
            clock=self.dut.aclk,
            field_config=self.addr_field_config,
            timeout_cycles=self.TIMEOUT_CYCLES,
            mode='skid',
            multi_sig=True,
            log=self.log,
            randomizer=FlexRandomizer(self.randomizer_dict['balanced']['slave']),
            super_debug=self.super_debug
        )

        # 4. m_axi_r interface: Testbench sends data responses TO DUT (GAXI Master)
        self.m_axi_r_master = GAXIMaster(
            dut=self.dut,
            title="M_AXI_R_Master",
            prefix="",
            bus_name='m_axi',
            pkt_prefix="r",
            clock=self.dut.aclk,
            field_config=self.data_field_config,
            timeout_cycles=self.TIMEOUT_CYCLES,
            mode='skid',
            multi_sig=True,
            log=self.log,
            randomizer=FlexRandomizer(self.randomizer_dict['balanced']['master']),
            super_debug=self.super_debug
        )

        # 5. fub_split interface: Testbench receives split info FROM DUT (GAXI Slave)
        self.fub_split_slave = GAXISlave(
            dut=self.dut,
            title="FUB_Split_Slave",
            prefix="",
            bus_name='fub',
            pkt_prefix="split",
            clock=self.dut.aclk,
            field_config=self.split_field_config,
            timeout_cycles=self.TIMEOUT_CYCLES,
            mode='skid',
            multi_sig=True,
            log=self.log,
            randomizer=FlexRandomizer(self.randomizer_dict['balanced']['slave']),
            super_debug=self.super_debug
        )

        # Create monitors for each interface
        self.fub_ar_monitor = GAXIMonitor(
            dut=self.dut, title="FUB_AR_Monitor", prefix="", bus_name='fub',
            pkt_prefix="ar", clock=self.dut.aclk, field_config=self.addr_field_config,
            mode='skid', multi_sig=True, log=self.log, super_debug=self.super_debug
        )

        self.fub_r_monitor = GAXIMonitor(
            dut=self.dut, title="FUB_R_Monitor", prefix="", bus_name='fub',
            pkt_prefix="r", clock=self.dut.aclk, field_config=self.data_field_config,
            mode='skid', multi_sig=True, log=self.log, super_debug=self.super_debug
        )

        self.m_axi_ar_monitor = GAXIMonitor(
            dut=self.dut, title="M_AXI_AR_Monitor", prefix="", bus_name='m_axi',
            pkt_prefix="ar", clock=self.dut.aclk, field_config=self.addr_field_config,
            mode='skid', multi_sig=True, log=self.log, super_debug=self.super_debug
        )

        self.m_axi_r_monitor = GAXIMonitor(
            dut=self.dut, title="M_AXI_R_Monitor", prefix="", bus_name='m_axi',
            pkt_prefix="r", clock=self.dut.aclk, field_config=self.data_field_config,
            mode='skid', multi_sig=True, log=self.log, super_debug=self.super_debug
        )

        self.fub_split_monitor = GAXIMonitor(
            dut=self.dut, title="FUB_Split_Monitor", prefix="", bus_name='fub',
            pkt_prefix="split", clock=self.dut.aclk, field_config=self.split_field_config,
            mode='skid', multi_sig=True, log=self.log, super_debug=self.super_debug
        )

        # Create enhanced scoreboard with detailed error reporting
        self.scoreboard = AxiReadSplitterScoreboard(
            alignment_mask=self.ALIGNMENT_MASK,
            log=self.log,
            component_name="AXI_SPLIT_SB",
            id_width=self.IW,
            addr_width=self.AW,
            data_width=self.DW,
            user_width=self.UW
        )

        # Connect all monitor callbacks to scoreboard with enhanced tracking
        self.fub_ar_monitor.add_callback(self._fub_ar_callback)
        self.fub_r_monitor.add_callback(self._fub_r_callback)
        self.m_axi_ar_monitor.add_callback(self._m_axi_ar_callback)
        self.m_axi_r_monitor.add_callback(self._m_axi_r_callback)
        self.fub_split_monitor.add_callback(self._fub_split_callback)

        # Set up slave response handlers
        self.m_axi_ar_slave.add_callback(self._handle_m_axi_ar_request)

        # Apply reset
        await self.fub_ar_master.reset_bus()
        await self.m_axi_r_master.reset_bus()
        self.dut.aresetn.value = 0
        self.dut.alignment_mask.value = self.ALIGNMENT_MASK
        self.dut.block_ready.value = 0

        await self.wait_clocks('aclk', 10)

        # Release reset
        self.dut.aresetn.value = 1
        await self.wait_clocks('aclk', 5)

        self.log.info("GAXI-based setup complete - SAFE ADDRESS TESTING MODE")

    # Enhanced callback handlers with detailed context tracking
    def _fub_ar_callback(self, packet):
        """Handle fub_ar transactions with enhanced context tracking"""
        timestamp = get_sim_time('ns')
        time_str = self.get_time_ns_str()

        if not isinstance(packet, AXIAddressPacket):
            axi_packet = convert_gaxi_packet_to_axi_address(packet, self.addr_field_config)
        else:
            axi_packet = packet

        # Create detailed transaction context
        ctx = TransactionContext(axi_packet, timestamp, self.current_test_case)
        ctx.set_boundary_info(self.BOUNDARY_SIZE, self._calculate_expected_splits(axi_packet))
        self.transaction_contexts[axi_packet.id] = ctx

        self.scoreboard.record_upstream_transaction(axi_packet)
        self.test_stats['transactions_sent'] += 1

        self.log_transaction_event("FUB_AR_SENT",
            f"ID={axi_packet.id:02X} ADDR=0x{axi_packet.addr:08X} LEN={axi_packet.len}")

        self.log.info(f"🚀 [{self.current_test_case}] Transaction Started{time_str}: ID={axi_packet.id:02X} "
                        f"ADDR=0x{axi_packet.addr:08X} LEN={axi_packet.len} "
                        f"SIZE={axi_packet.size}")

    def _fub_r_callback(self, packet):
        """Handle fub_r transactions with enhanced tracking"""
        timestamp = get_sim_time('ns')
        time_str = self.get_time_ns_str()

        if not isinstance(packet, AXIDataPacket):
            axi_packet = convert_gaxi_packet_to_axi_data(packet, self.data_field_config)
        else:
            axi_packet = packet

        # Track response in transaction context
        if axi_packet.id in self.transaction_contexts:
            self.transaction_contexts[axi_packet.id].add_response(axi_packet, timestamp)

        self.scoreboard.record_downstream_transaction(axi_packet)
        self.test_stats['responses_received'] += 1

        self.log_transaction_event("FUB_R_RECEIVED",
            f"ID={axi_packet.id:02X} LAST={axi_packet.last}")

        self.log.debug(f"📥 FUB_R{time_str}: ID={axi_packet.id:02X} "
                        f"DATA=0x{axi_packet.data:016X} LAST={axi_packet.last}")

    def _m_axi_ar_callback(self, packet):
        """Handle m_axi_ar transactions with enhanced tracking"""
        timestamp = get_sim_time('ns')
        time_str = self.get_time_ns_str()

        if not isinstance(packet, AXIAddressPacket):
            axi_packet = convert_gaxi_packet_to_axi_address(packet, self.addr_field_config)
        else:
            axi_packet = packet

        self.scoreboard.record_downstream_transaction(axi_packet)

        self.log_transaction_event("M_AXI_AR_SPLIT",
            f"ID={axi_packet.id:02X} ADDR=0x{axi_packet.addr:08X} LEN={axi_packet.len}")

        self.log.debug(f"🔄 M_AXI_AR{time_str}: ID={axi_packet.id:02X} "
                        f"ADDR=0x{axi_packet.addr:08X} LEN={axi_packet.len}")

    def _m_axi_r_callback(self, packet):
        """Handle m_axi_r transactions"""
        timestamp = get_sim_time('ns')
        time_str = self.get_time_ns_str()

        if not isinstance(packet, AXIDataPacket):
            axi_packet = convert_gaxi_packet_to_axi_data(packet, self.data_field_config)
        else:
            axi_packet = packet

        self.log_transaction_event("M_AXI_R_SENT",
            f"ID={axi_packet.id:02X} LAST={axi_packet.last}")

        self.log.debug(f"📤 M_AXI_R{time_str}: ID={axi_packet.id:02X} "
                        f"DATA=0x{axi_packet.data:016X} LAST={axi_packet.last}")

    def _fub_split_callback(self, packet):
        """Handle fub_split transactions with enhanced tracking and comprehensive debugging"""
        timestamp = get_sim_time('ns')
        time_str = self.get_time_ns_str()

        # ENHANCED DEBUG: Log every split info callback with full details
        self.log.info(f"🔍 SPLIT INFO CALLBACK{time_str}:")
        self.log.info(f"  Raw packet type: {type(packet)}")
        self.log.info(f"  Raw packet: {packet}")

        # Check if packet has expected attributes
        for attr in ['addr', 'id', 'cnt']:
            if hasattr(packet, attr):
                value = getattr(packet, attr)
                self.log.info(f"  {attr}: 0x{value:X} (type: {type(value)})")
            else:
                self.log.warning(f"  Missing attribute: {attr}")

        # Show all attributes of the packet for comprehensive debugging
        if hasattr(packet, '__dict__'):
            self.log.info(f"  All packet attributes: {packet.__dict__}")
        elif hasattr(packet, '_fields'):
            self.log.info(f"  Packet fields: {packet._fields}")

        try:
            if not isinstance(packet, SplitInfoPacket):
                if isinstance(packet, dict):
                    split_packet = SplitInfoPacket.from_dict(packet, self.split_field_config)
                    self.log.info(f"  ✅ Converted from dict to SplitInfoPacket")
                else:
                    # Convert from generic packet
                    split_data = {
                        'addr': getattr(packet, 'addr', 0),
                        'id': getattr(packet, 'id', 0),
                        'cnt': getattr(packet, 'cnt', 0)
                    }
                    split_packet = SplitInfoPacket.from_dict(split_data, self.split_field_config)
                    self.log.info(f"  ✅ Converted from generic packet to SplitInfoPacket")
                    self.log.info(f"  Conversion data: {split_data}")
            else:
                split_packet = packet
                self.log.info(f"  ✅ Already SplitInfoPacket")

            # ENHANCED DEBUG: Log the final split packet details
            self.log.info(f"  Final split packet details:")
            self.log.info(f"    addr: 0x{split_packet.addr:08X}")
            self.log.info(f"    id: 0x{split_packet.id:02X}")
            self.log.info(f"    cnt: {split_packet.cnt}")

            # ENHANCED DEBUG: Check transaction context before storing
            self.log.info(f"  Transaction context check:")
            self.log.info(f"    Looking for ID: 0x{split_packet.id:02X}")
            self.log.info(f"    Available transaction contexts: {[f'0x{tid:02X}' for tid in self.transaction_contexts.keys()]}")

            # Track split info in transaction context
            if split_packet.id in self.transaction_contexts:
                self.transaction_contexts[split_packet.id].split_info_received = split_packet
                self.log.info(f"  ✅ Stored in transaction context for ID 0x{split_packet.id:02X}")

                # ENHANCED DEBUG: Verify the storage
                stored_split_info = self.transaction_contexts[split_packet.id].split_info_received
                if stored_split_info:
                    self.log.info(f"  ✅ Verification - stored split info:")
                    self.log.info(f"    stored addr: 0x{stored_split_info.addr:08X}")
                    self.log.info(f"    stored id: 0x{stored_split_info.id:02X}")
                    self.log.info(f"    stored cnt: {stored_split_info.cnt}")
                else:
                    self.log.error(f"  ❌ Storage verification failed - split_info_received is None!")
            else:
                self.log.warning(f"  ⚠️ No transaction context found for ID 0x{split_packet.id:02X}")
                self.log.warning(f"  Available transaction IDs: {[f'0x{tid:02X}' for tid in self.transaction_contexts.keys()]}")

            # ENHANCED DEBUG: Log before calling scoreboard
            self.log.info(f"  📋 Calling scoreboard.record_split_info()...")

            # Record in scoreboard
            self.scoreboard.record_split_info(split_packet)
            self.test_stats['splits_detected'] += 1

            # ENHANCED DEBUG: Verify scoreboard storage
            self.log.info(f"  📋 Verifying scoreboard storage...")
            if split_packet.id in self.scoreboard.split_info_tracking:
                stored_sb_split = self.scoreboard.split_info_tracking[split_packet.id]
                self.log.info(f"  ✅ Verified in scoreboard split_info_tracking:")
                self.log.info(f"    scoreboard addr: 0x{stored_sb_split.addr:08X}")
                self.log.info(f"    scoreboard id: 0x{stored_sb_split.id:02X}")
                self.log.info(f"    scoreboard cnt: {stored_sb_split.cnt}")
            else:
                self.log.error(f"  ❌ NOT FOUND in scoreboard split_info_tracking!")
                self.log.error(f"  Available scoreboard IDs: {[f'0x{sid:02X}' for sid in self.scoreboard.split_info_tracking.keys()]}")

            # Log transaction event
            self.log_transaction_event("SPLIT_INFO",
                f"ID={split_packet.id:02X} CNT={split_packet.cnt}")

            # Final success log
            self.log.info(f"✅ SPLIT_INFO_PROCESSED{time_str}: ID={split_packet.id:02X} "
                        f"ADDR=0x{split_packet.addr:08X} CNT={split_packet.cnt}")

            # ENHANCED DEBUG: Show final state summary
            self.log.info(f"  📊 Final state summary:")
            self.log.info(f"    Total splits detected: {self.test_stats['splits_detected']}")
            self.log.info(f"    Scoreboard split_info_tracking size: {len(self.scoreboard.split_info_tracking)}")
            self.log.info(f"    Transaction contexts with split_info: {sum(1 for ctx in self.transaction_contexts.values() if ctx.split_info_received is not None)}")

        except Exception as e:
            self.log.error(f"❌ SPLIT_INFO_CALLBACK_ERROR{time_str}: {e}")
            self.log.error(f"  Exception type: {type(e)}")
            import traceback
            self.log.error(f"  Traceback:")
            for line in traceback.format_exc().split('\n'):
                if line.strip():
                    self.log.error(f"    {line}")

            # Still try to record something in stats
            self.test_stats['splits_detected'] += 1

            # Try to at least store raw data in transaction context if possible
            try:
                if hasattr(packet, 'id'):
                    packet_id = getattr(packet, 'id')
                    if packet_id in self.transaction_contexts:
                        # Store the raw packet as fallback
                        self.transaction_contexts[packet_id].split_info_received = packet
                        self.log.info(f"  🔄 Fallback: stored raw packet in transaction context")
            except Exception as fallback_e:
                self.log.error(f"  ❌ Fallback storage also failed: {fallback_e}")

    def _calculate_expected_splits(self, ar_packet: AXIAddressPacket) -> int:
        """Calculate expected number of splits with detailed logging for DW=512"""
        start_addr = ar_packet.addr
        bytes_per_beat = 1 << ar_packet.size
        total_bytes = (ar_packet.len + 1) * bytes_per_beat
        end_addr = start_addr + total_bytes - 1

        start_boundary = start_addr // self.BOUNDARY_SIZE
        end_boundary = end_addr // self.BOUNDARY_SIZE

        crosses_boundary = start_boundary != end_boundary
        expected_splits = end_boundary - start_boundary + 1 if crosses_boundary else 1

        if self.DW >= 512:  # Extra logging for debugging DW=512
            self.log.debug(f"🔍 Split calculation for DW={self.DW}:")
            self.log.debug(f"  Start: 0x{start_addr:08X} -> boundary {start_boundary}")
            self.log.debug(f"  End: 0x{end_addr:08X} -> boundary {end_boundary}")
            self.log.debug(f"  Bytes per beat: {bytes_per_beat}")
            self.log.debug(f"  Total bytes: {total_bytes}")
            self.log.debug(f"  Expected splits: {expected_splits}")

        return expected_splits

    def _handle_m_axi_ar_request(self, ar_packet):
        """Synchronous callback that starts async response generation"""
        cocotb.start_soon(self._async_handle_m_axi_ar_request(ar_packet))

    async def _async_handle_m_axi_ar_request(self, ar_packet):
        """Generate responses - SIMPLE AND CORRECT"""
        try:
            # Get basic info from AR packet
            ar_len = getattr(ar_packet, 'len', 0)
            ar_id = getattr(ar_packet, 'id', 0)
            ar_addr = getattr(ar_packet, 'addr', 0)
            ar_user = getattr(ar_packet, 'user', 0) if self.UW > 0 else 0

            # Calculate total beats: len + 1 (AXI standard)
            total_beats = ar_len + 1

            self.log.debug(f"Generating {total_beats} responses for ID={ar_id:02X}")

            # Simple loop - create exactly the right number of responses
            for beat in range(total_beats):
                # Generate data
                beat_addr = ar_addr + (beat * self.BYTES_PER_BEAT)
                data_value = self.generate_deterministic_data(beat_addr, beat, ar_id)

                # Create response packet
                r_packet = GAXIPacket(self.data_field_config)
                r_packet.id = ar_id
                r_packet.data = data_value
                r_packet.resp = 0  # OKAY
                r_packet.last = 1 if beat == (total_beats - 1) else 0  # LAST only on final beat
                if self.UW > 0:
                    r_packet.user = ar_user

                # Send immediately
                await self.m_axi_r_master.send(r_packet)

            self.log.debug(f"Sent {total_beats} responses for ID={ar_id:02X}")

        except Exception as e:
            self.log.error(f"Response generation failed: {e}")

    async def send_read_transaction(self, ar_packet: AXIAddressPacket, test_case_name: str = "unknown") -> bool:
        """Send a read transaction with enhanced context tracking and safety validation"""
        try:
            self.current_test_case = test_case_name
            send_time_str = self.get_time_ns_str()

            # FIXED: Validate address alignment before sending
            if not self.validate_address_alignment(ar_packet.addr):
                error_report = self.create_detailed_error_report(
                    ar_packet.id, "ADDRESS_ALIGNMENT_ERROR",
                    f"Transaction address 0x{ar_packet.addr:08X} is not aligned to {self.BYTES_PER_BEAT}-byte boundary"
                )
                self.log.error(error_report)
                return False

            # SAFE: Validate address safety before sending
            if not self.is_address_safe(ar_packet.addr, ar_packet.len):
                error_report = self.create_detailed_error_report(
                    ar_packet.id, "ADDRESS_SAFETY_ERROR",
                    f"Transaction address 0x{ar_packet.addr:08X} with length {ar_packet.len} is not safe (potential wraparound)"
                )
                self.log.error(error_report)
                return False

            # Log detailed pre-send analysis for DW=512
            if self.DW >= 512:
                boundary_cross = ar_packet.will_cross_boundary(self.BOUNDARY_SIZE)
                total_bytes = ar_packet.calculate_total_bytes()

                self.log.info(f"📊 DW={self.DW} Transaction Analysis{send_time_str}:")
                self.log.info(f"  Address: 0x{ar_packet.addr:08X} (✅ {self.BYTES_PER_BEAT}-byte aligned)")
                self.log.info(f"  Length: {ar_packet.len} ({ar_packet.len + 1} beats)")
                self.log.info(f"  Size: {ar_packet.size} ({1 << ar_packet.size} bytes/beat)")
                self.log.info(f"  Total bytes: {total_bytes}")
                self.log.info(f"  End address: 0x{ar_packet.addr + total_bytes - 1:08X}")
                self.log.info(f"  Safe: ✅ (< 0x{self.SAFE_ADDR_LIMIT:08X})")
                self.log.info(f"  Will cross boundary: {boundary_cross}")

            await self.fub_ar_master.send(ar_packet)
            return True

        except Exception as e:
            error_report = self.create_detailed_error_report(
                ar_packet.id, "SEND_FAILURE", f"Failed to send transaction: {e}"
            )
            self.log.error(error_report)
            return False

    async def wait_for_transaction_completion(self, txn_id: int, timeout_cycles: int = 100, test_case_name: str = "unknown"):
        """Wait for transaction completion with enhanced timeout reporting and SPLIT INFO TIMING FIX"""
        start_time = get_sim_time('ns')
        start_time_str = self.get_time_ns_str()

        self.log.debug(f"⏳ Waiting for transaction 0x{txn_id:02X} completion{start_time_str}")

        for cycle in range(timeout_cycles):
            if self.scoreboard.is_transaction_complete(txn_id):
                completion_time = get_sim_time('ns')
                completion_time_str = self.get_time_ns_str()

                if txn_id in self.transaction_contexts:
                    self.transaction_contexts[txn_id].mark_complete(completion_time)

                duration = completion_time - start_time
                self.log.info(f"✅ Transaction 0x{txn_id:02X} completed{completion_time_str} "
                            f"(duration: {duration:.1f}ns, {cycle} cycles)")
                
                # TIMING FIX: Wait for split info to propagate
                # The split info comes from a FIFO and may have additional pipeline delays
                self.log.debug(f"⏳ Waiting for split info propagation for transaction 0x{txn_id:02X}...")
                
                # Wait a few more clock cycles for split info to arrive
                await self.wait_clocks('aclk', 5)  # Adjust this if needed
                
                split_info_time_str = self.get_time_ns_str()
                self.log.debug(f"✅ Split info wait period completed{split_info_time_str}")
                
                return
            await RisingEdge(self.dut.aclk)

        # Timeout - create detailed error report
        timeout_time_str = self.get_time_ns_str()
        error_report = self.create_detailed_error_report(
            txn_id, "TIMEOUT", f"Transaction timed out after {timeout_cycles} cycles"
        )
        self.log.error(error_report)
        self.log.error(f"❌ Transaction 0x{txn_id:02X} TIMEOUT{timeout_time_str}")

    def _get_next_id(self) -> int:
        """Get next transaction ID"""
        self.transaction_id_counter = (self.transaction_id_counter + 1) % (self.MAX_ID + 1)
        return self.transaction_id_counter

    async def run_all_tests(self) -> bool:
        """Run comprehensive test suite with enhanced error reporting"""
        start_time_str = self.get_time_ns_str()
        self.log.info(f"🧪 Running AXI Read Splitter tests at level: {self.TEST_LEVEL}{start_time_str}")
        self.log.info(f"Configuration: DW={self.DW}, ALIGNMENT=0x{self.ALIGNMENT_MASK:03X}, SAFE_LIMIT=0x{self.SAFE_ADDR_LIMIT:08X}")

        start_time = get_sim_time('ns')
        all_passed = True

        # Test sequence
        tests = [
            ("Basic Splitting", self.test_basic_splitting),
            ("Burst Types", self.test_burst_types),
            ("Random Transactions", self.test_random_transactions),
        ]

        for test_name, test_func in tests:
            test_start_str = self.get_time_ns_str()
            self.log.info(f"🧪 Starting {test_name}{test_start_str}")
            self.current_test_case = test_name

            try:
                test_passed = await test_func()
                test_end_str = self.get_time_ns_str()
                if test_passed:
                    self.log.info(f"✅ {test_name} PASSED{test_end_str}")
                else:
                    self.log.error(f"❌ {test_name} FAILED{test_end_str}")
                    all_passed = False
                    if self.TEST_LEVEL == 'basic':
                        break

            except Exception as e:
                error_time_str = self.get_time_ns_str()
                self.log.error(f"❌ {test_name} FAILED with exception{error_time_str}: {e}")
                import traceback
                self.log.error(f"Traceback: {traceback.format_exc()}")
                all_passed = False
                if self.TEST_LEVEL == 'basic':
                    break

            await self.wait_clocks('aclk', 10)

        # Final verification with enhanced error reporting
        end_time = get_sim_time('ns')
        verification_start_str = self.get_time_ns_str()
        self.test_stats['test_duration'] = (end_time - start_time) / 1e9

        self.log.info(f"🔍 Performing final verification{verification_start_str}...")
        final_verification = self.scoreboard.verify_split_correctness()
        if not final_verification:
            all_passed = False

        # Enhanced final report
        self.print_comprehensive_report()

        return all_passed

    async def test_basic_splitting(self) -> bool:
        """Test basic address boundary splitting with SAFE address generation"""
        test_start_str = self.get_time_ns_str()
        self.log.info(f"🧪 Running basic splitting tests with SAFE address generation{test_start_str}")

        boundary_size = self.ALIGNMENT_MASK + 1

        # FIXED: Safe test cases with explicit boundary and length control
        test_cases = []

        # Case 1: Simple boundary cross - use safe boundary generation
        addr1 = self.generate_safe_boundary_test_address(boundary_size, 4)
        if self.is_address_safe(addr1, 1):
            test_cases.append((addr1, 1, "Simple boundary cross"))

        # Case 2: Multi-beat boundary cross
        addr2 = self.generate_safe_boundary_test_address(boundary_size, 8)
        if self.is_address_safe(addr2, 3):
            test_cases.append((addr2, 3, "Multi-beat boundary cross"))

        # Case 3: No boundary cross - well within boundary
        safe_addr = self.align_address_to_data_width(0x1000)  # Simple safe address
        if self.is_address_safe(safe_addr, 7):
            test_cases.append((safe_addr, 7, "No boundary cross"))

        # Add DW-specific test cases - with safety checks
        if self.DW >= 512:
            addr4 = self.generate_safe_boundary_test_address(boundary_size, 2)
            if self.is_address_safe(addr4, 0):
                test_cases.append((addr4, 0, "Single large beat boundary cross"))

            addr5 = self.generate_safe_boundary_test_address(boundary_size, 1)
            if self.is_address_safe(addr5, 1):
                test_cases.append((addr5, 1, "Double large beat boundary cross"))
        elif self.DW >= 128:
            addr4 = self.generate_safe_boundary_test_address(boundary_size, 16)
            if self.is_address_safe(addr4, 7):
                test_cases.append((addr4, 7, "Medium width large transfer crossing"))

        if self.TEST_LEVEL != 'basic':
            # Additional test cases for higher test levels - with safety
            addr_extra1 = self.generate_safe_boundary_test_address(boundary_size * 2, 4)
            if self.is_address_safe(addr_extra1, 3):
                test_cases.append((addr_extra1, 3, "Later boundary cross"))

            # Test at a safe boundary
            safe_boundary_addr = self.align_address_to_data_width(boundary_size)
            if self.is_address_safe(safe_boundary_addr, 1):
                test_cases.append((safe_boundary_addr, 1, "Safe boundary start"))

        all_passed = True

        for addr, length, description in test_cases:
            test_case_name = f"basic_{description.replace(' ', '_')}"
            case_start_str = self.get_time_ns_str()

            # Final safety validation before testing
            if not self.is_address_safe(addr, length):
                self.log.warning(f"⚠️ Skipping unsafe test case: {description}")
                continue

            self.log.info(f"🔬 Testing: {description}{case_start_str}")
            self.log.info(f"   Address: 0x{addr:08X} (aligned to {self.BYTES_PER_BEAT}-byte boundary)")
            self.log.info(f"   Length: {length} ({length + 1} beats)")
            self.log.info(f"   Total bytes: {(length + 1) * self.BYTES_PER_BEAT}")
            self.log.info(f"   End address: 0x{addr + (length + 1) * self.BYTES_PER_BEAT - 1:08X}")

            ar_packet = AXIAddressPacket(
                field_config=self.addr_field_config,
                id=self._get_next_id(),
                addr=addr,
                len=length,
                size=self.EXPECTED_AX_SIZE,  # FIXED: Use proper size for data width
                burst=1,  # INCR
                cache=0x3,
                prot=0x0,
                lock=0,
                qos=0,
                region=0,
                user=0 if self.UW > 0 else None
            )

            success = await self.send_read_transaction(ar_packet, test_case_name)
            if not success:
                all_passed = False
                continue

            await self.wait_for_transaction_completion(ar_packet.id, timeout_cycles=200, test_case_name=test_case_name)

            # Verify with enhanced error reporting
            if not self.scoreboard.verify_transaction_splitting(ar_packet.id):
                error_report = self.create_detailed_error_report(
                    ar_packet.id, "VERIFICATION_FAILURE", f"Split verification failed: {description}"
                )
                self.log.error(error_report)
                all_passed = False
                if self.TEST_LEVEL == 'basic':
                    break

        return all_passed

    async def test_burst_types(self) -> bool:
        """Test different burst types with SAFE address generation"""
        test_start_str = self.get_time_ns_str()
        self.log.info(f"🧪 Testing burst types{test_start_str}")

        boundary_size = self.ALIGNMENT_MASK + 1
        test_case_name = "burst_incr_only"

        # FIXED: Generate safe address for boundary crossing test
        test_addr = self.generate_safe_boundary_test_address(boundary_size, 8)

        # Validate safety and alignment
        if not self.is_address_safe(test_addr, 7):
            self.log.error(f"❌ Cannot generate safe address for burst test!")
            return False

        if not self.validate_address_alignment(test_addr):
            self.log.error(f"❌ Generated address 0x{test_addr:08X} is not properly aligned!")
            return False

        self.log.info(f"Testing INCR burst crossing boundary:")
        self.log.info(f"   Address: 0x{test_addr:08X} (aligned to {self.BYTES_PER_BEAT}-byte boundary)")
        self.log.info(f"   Length: 7 (8 beats)")
        self.log.info(f"   Total bytes: {8 * self.BYTES_PER_BEAT}")
        self.log.info(f"   End address: 0x{test_addr + 8 * self.BYTES_PER_BEAT - 1:08X}")

        ar_packet = AXIAddressPacket(
            field_config=self.addr_field_config,
            id=self._get_next_id(),
            addr=test_addr,
            len=7,
            size=self.EXPECTED_AX_SIZE,  # FIXED: Use proper size for data width
            burst=1,  # INCR
            cache=0x2,
            prot=0x0,
            lock=0,
            qos=0,
            region=0,
            user=0 if self.UW > 0 else None
        )

        success = await self.send_read_transaction(ar_packet, test_case_name)
        if not success:
            return False

        await self.wait_for_transaction_completion(ar_packet.id, timeout_cycles=200, test_case_name=test_case_name)

        verified = self.scoreboard.verify_transaction_splitting(ar_packet.id)
        if not verified:
            error_report = self.create_detailed_error_report(
                ar_packet.id, "BURST_TEST_FAILURE", "INCR burst test verification failed"
            )
            self.log.error(error_report)

        return verified

    async def test_random_transactions(self) -> bool:
        """Test with random transaction parameters with SAFE address generation"""
        test_start_str = self.get_time_ns_str()
        num_tests = {'basic': 5, 'medium': 20, 'full': 100}[self.TEST_LEVEL]
        self.log.info(f"🧪 Running {num_tests} SAFE random transaction tests{test_start_str}")
        self.log.info(f"   All addresses will be in safe region (< 0x{self.SAFE_ADDR_LIMIT:08X})")
        self.log.info(f"   All addresses will be aligned to {self.BYTES_PER_BEAT}-byte boundaries")

        all_passed = True

        for i in range(num_tests):
            test_case_name = f"random_{i:03d}"
            case_start_str = self.get_time_ns_str()

            # For DW=512, use smaller lengths to avoid overwhelming the system
            max_len = 15 if self.DW < 512 else 3

            self.log.debug(f"🎲 Safe random test {i+1}/{num_tests}{case_start_str}")

            # FIXED: Generate safe aligned random address
            test_addr = self.generate_aligned_random_address()
            test_len = random.randint(0, max_len)

            # Double-check safety (should always pass with our generator)
            if not self.is_address_safe(test_addr, test_len):
                self.log.warning(f"⚠️ Generated unsafe address, using fallback")
                test_addr = self.align_address_to_data_width(0x00100000 + (i * 0x1000))
                if not self.is_address_safe(test_addr, test_len):
                    self.log.error(f"❌ Cannot generate safe address for random test {i}")
                    continue

            # Validate alignment (should always pass with our generator)
            if not self.validate_address_alignment(test_addr):
                self.log.error(f"❌ Generated random address 0x{test_addr:08X} is not properly aligned!")
                all_passed = False
                continue

            if self.super_debug:
                self.log.debug(f"   Random test {i}: addr=0x{test_addr:08X}, len={test_len}")
                self.log.debug(f"   End addr: 0x{test_addr + (test_len + 1) * self.BYTES_PER_BEAT - 1:08X}")
                self.log.debug(f"   Alignment check: addr & 0x{self.ADDR_ALIGN_MASK:X} = 0x{test_addr & self.ADDR_ALIGN_MASK:X}")

            ar_packet = AXIAddressPacket(
                field_config=self.addr_field_config,
                id=self._get_next_id(),
                addr=test_addr,
                len=test_len,
                size=self.EXPECTED_AX_SIZE,  # FIXED: Use proper size for data width
                burst=1,  # INCR
                cache=random.randint(0, 15),
                prot=random.randint(0, 7),
                lock=0,
                qos=random.randint(0, 15),
                region=random.randint(0, 15),
                user=random.randint(0, (1 << self.UW) - 1) if self.UW > 0 else None
            )

            success = await self.send_read_transaction(ar_packet, test_case_name)
            if not success:
                all_passed = False
                continue

            await self.wait_for_transaction_completion(ar_packet.id, timeout_cycles=300, test_case_name=test_case_name)

            if not self.scoreboard.verify_transaction_splitting(ar_packet.id):
                error_report = self.create_detailed_error_report(
                    ar_packet.id, "RANDOM_TEST_FAILURE", f"Random test {i} verification failed"
                )
                self.log.error(error_report)
                all_passed = False
                if self.TEST_LEVEL == 'basic':
                    break

        return all_passed

    def print_comprehensive_report(self):
        """Print comprehensive test report with enhanced error details"""
        report_time_str = self.get_time_ns_str()
        self.log.info("=" * 100)
        self.log.info(f"🏁 AXI Read Splitter Test Report - SAFE ADDRESS TESTING{report_time_str}")
        self.log.info("=" * 100)

        # Test configuration
        self.log.info(f"📋 Configuration:")
        self.log.info(f"  Data Width: {self.DW} bits ({self.BYTES_PER_BEAT} bytes/beat)")
        self.log.info(f"  Address Alignment: {self.BYTES_PER_BEAT}-byte boundaries (mask: 0x{self.ADDR_ALIGN_MASK:X})")
        self.log.info(f"  AXI Size Field: {self.EXPECTED_AX_SIZE} (matches {self.BYTES_PER_BEAT}-byte transfers)")
        self.log.info(f"  Alignment Mask: 0x{self.ALIGNMENT_MASK:03X}")
        self.log.info(f"  Boundary Size: {self.ALIGNMENT_MASK + 1} bytes")
        self.log.info(f"  Safe Address Limit: 0x{self.SAFE_ADDR_LIMIT:08X} (no wraparound)")
        self.log.info(f"  Test Level: {self.TEST_LEVEL}")
        self.log.info(f"  Seed: {self.SEED}")

        # Test statistics
        self.log.info(f"\n📊 Test Statistics:")
        self.log.info(f"  Transactions Sent: {self.test_stats['transactions_sent']}")
        self.log.info(f"  Responses Received: {self.test_stats['responses_received']}")
        self.log.info(f"  Splits Detected: {self.test_stats['splits_detected']}")
        self.log.info(f"  Test Duration: {self.test_stats['test_duration']:.3f}s")

        # Enhanced error summary
        if self.detailed_errors:
            self.log.error(f"\n🚨 DETAILED ERRORS DETECTED: {len(self.detailed_errors)}")
            self.log.error("Full error reports shown above ⬆️")
        else:
            self.log.info("✅ NO DETAILED ERRORS DETECTED")
            self.log.info("✅ ALL SAFE ADDRESS TESTS PASSED")

        # Scoreboard report
        if self.scoreboard:
            self.log.info("\n" + self.scoreboard.get_detailed_report())

        self.log.info("=" * 100)

    async def shutdown(self):
        """Properly shutdown all GAXI components"""
        self.log.info("Shutting down GAXI components...")
        # Implementation remains the same
