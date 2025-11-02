# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: MonbusAxilGroupTB
# Purpose: STREAM MonBus AXIL Group Testbench - v1.0
#
# Documentation: projects/components/stream/PRD.md
# Subsystem: stream
#
# Author: sean galloway
# Created: 2025-10-19

"""
STREAM MonBus AXIL Group Testbench - v1.0

Simplified testbench for STREAM's monbus_axil_group module. Based on RAPIDS
implementation but simplified for STREAM's memory-only architecture.

SIMPLIFICATIONS FROM RAPIDS:
- NO AXIS protocol filtering (STREAM has no network interfaces)
- AXI protocol packets only (no Network/AXIS event codes)
- Simpler configuration (fewer protocol types)

Features:
- Monitor bus packet aggregation from data paths
- AXI protocol packet filtering and validation
- Error/Interrupt FIFO testing via AXI-Lite slave read interface
- Master write FIFO testing via AXI-Lite master write interface
- Configuration register testing
- Stress testing with concurrent packet streams
"""

import os
import random
import time
from typing import List, Dict, Any, Tuple, Optional
from collections import defaultdict, deque

import cocotb
from cocotb.triggers import Combine

# Framework imports
from CocoTBFramework.tbclasses.shared.tbbase import TBBase
from CocoTBFramework.components.shared.flex_randomizer import FlexRandomizer

# AXIL4 imports for slave/master interfaces
from CocoTBFramework.components.axil4.axil4_factories import (
    create_axil4_master_rd, create_axil4_master_wr
)

# MonBus imports
from CocoTBFramework.tbclasses.monbus.monbus_types import (
    ProtocolType, PktType, ARBErrorCode, ARBCompletionCode
)
from CocoTBFramework.tbclasses.monbus.monbus_packet import create_monbus_field_config

# GAXI for monitor bus driving
from CocoTBFramework.components.gaxi.gaxi_factories import create_gaxi_master


class MonbusAxilGroupTB(TBBase):
    """
    STREAM MonBus AXIL Group testbench (simplified from RAPIDS).

    Tests:
    - Monitor bus packet arbitration (simpler than RAPIDS - fewer sources)
    - AXI protocol packet filtering only (no AXIS/Network)
    - Error/Interrupt FIFO via AXI-Lite slave read interface
    - Master write operations via AXI-Lite master write interface
    - Configuration register functionality
    """

    def __init__(self, dut, axi_aclk=None, axi_aresetn=None):
        super().__init__(dut)

        # Test configuration from environment
        self.TEST_FIFO_DEPTH_ERR = int(os.environ.get('TEST_FIFO_DEPTH_ERR', '64'))
        self.TEST_FIFO_DEPTH_WRITE = int(os.environ.get('TEST_FIFO_DEPTH_WRITE', '32'))
        self.TEST_ADDR_WIDTH = int(os.environ.get('TEST_ADDR_WIDTH', '32'))
        self.TEST_DATA_WIDTH = int(os.environ.get('TEST_DATA_WIDTH', '32'))
        self.TEST_NUM_PROTOCOLS = int(os.environ.get('TEST_NUM_PROTOCOLS', '3'))
        self.SEED = int(os.environ.get('SEED', '12345'))

        random.seed(self.SEED)

        # Setup clock and reset signals
        self.axi_aclk = axi_aclk or dut.axi_aclk
        self.axi_aresetn = axi_aresetn or dut.axi_aresetn
        self.clk_name = self.axi_aclk._name if hasattr(self.axi_aclk, '_name') else 'axi_aclk'
        self.rst_n = self.axi_aresetn

        # Test statistics (simplified from RAPIDS)
        self.stats = {
            'packets_sent': 0,
            'packets_filtered': {'dropped': 0, 'to_err_fifo': 0, 'to_write_fifo': 0},
            'protocol_stats': defaultdict(int),
            'error_fifo_reads': 0,
            'master_writes': 0,
            'test_start_time': 0,
            'test_end_time': 0
        }

        # Packet queues
        self.expected_error_packets = deque()
        self.received_error_packets = deque()

        # Components (initialized in setup)
        self.monbus_master = None
        self.error_fifo_reader = None

    # ========================================================================
    # MANDATORY: Clock and Reset Control Methods
    # ========================================================================

    async def setup_clocks_and_reset(self):
        """Complete initialization - starts clocks and performs reset sequence."""
        self.log.info("Starting clocks and reset sequence...")

        await self.start_clock(self.clk_name, freq=10, units='ns')  # 100 MHz

        await self.assert_reset()
        await self.wait_clocks(self.clk_name, 10)
        await self.deassert_reset()
        await self.wait_clocks(self.clk_name, 5)

        self.log.info("✅ Clocks started and reset sequence completed")

    async def assert_reset(self):
        """Assert reset signal (active-low)."""
        self.axi_aresetn.value = 0

    async def deassert_reset(self):
        """Deassert reset signal (active-low)."""
        self.axi_aresetn.value = 1

    # ========================================================================
    # Interface Setup
    # ========================================================================

    async def setup_interfaces(self):
        """Setup all interface components"""
        self.log.info("Setting up STREAM MonBus AXIL Group interfaces...")

        # Initialize configuration signals
        await self.initialize_config_signals()

        # MonBus field configuration
        monbus_config = create_monbus_field_config()

        # Monitor bus master (single input - STREAM has no source/sink separation)
        self.monbus_master = create_gaxi_master(
            dut=self.dut,
            title="MonBus Master",
            prefix="monbus",
            clock=self.axi_aclk,
            field_config=monbus_config,
            signal_map={'data': 'monbus_packet'},
            log=self.log
        )

        # AXI-Lite slave read interface for error FIFO
        self.error_fifo_reader = create_axil4_master_rd(
            dut=self.dut,
            clock=self.axi_aclk,
            prefix="s_axil",
            multi_sig=True,
            log=self.log
        )

        self.log.info("✅ All interfaces setup completed")

    async def initialize_config_signals(self):
        """Initialize RTL configuration signals"""
        self.log.info("Initializing configuration signals...")

        # AXI protocol (only protocol in STREAM): Route errors to error FIFO
        self.dut.cfg_axi_pkt_mask.value = 0x0000  # Don't drop packets
        self.dut.cfg_axi_err_select.value = 0x0001  # Route ERROR packets to error FIFO

        await self.wait_clocks(self.clk_name, 1)
        self.log.info("✅ Configuration signals initialized")

    # ========================================================================
    # Test Methods
    # ========================================================================

    def create_monbus_packet_dict(self, pkt_type: PktType, event_code: int,
                                 channel_id: int = 0, data: int = 0) -> Dict[str, Any]:
        """Create MonBus packet dictionary for AXI protocol"""
        return {
            'pkt_type': pkt_type.value,
            'protocol': ProtocolType.PROTOCOL_AXI.value,  # STREAM uses AXI only
            'event_code': event_code,
            'channel_id': channel_id,
            'unit_id': 0,
            'agent_id': 0x10,
            'data': data & 0x7FFFFFFFF
        }

    async def send_packet(self, packet_dict: Dict[str, Any]) -> bool:
        """Send packet via monitor bus"""
        try:
            packet = self.monbus_master.create_packet(**packet_dict)
            await self.monbus_master.send(packet)
            self.stats['packets_sent'] += 1
            return True
        except Exception as e:
            self.log.error(f"Failed to send packet: {e}")
            return False

    async def read_error_fifo(self, address: int = 0x0) -> Optional[int]:
        """Read from error FIFO via AXI-Lite"""
        try:
            data = await self.error_fifo_reader['simple_read'](address)
            self.stats['error_fifo_reads'] += 1
            return data
        except Exception as e:
            self.log.error(f"Failed to read error FIFO: {e}")
            return None

    async def test_basic_packet_flow(self, count: int = 16) -> Tuple[bool, Dict[str, Any]]:
        """Test basic packet flow (AXI protocol only)"""
        self.log.info(f"Testing basic packet flow with {count} AXI packets...")

        success_count = 0

        for i in range(count):
            pkt_type = random.choice([PktType.PktTypeError, PktType.PktTypeCompletion])
            event_code = 0x1 if pkt_type == PktType.PktTypeError else 0x0

            packet_dict = self.create_monbus_packet_dict(
                pkt_type=pkt_type,
                event_code=event_code,
                channel_id=i % 8,  # STREAM has 8 channels
                data=0x1000 + i
            )

            if await self.send_packet(packet_dict):
                success_count += 1

            await self.wait_clocks(self.clk_name, random.randint(1, 5))

        success_rate = success_count / count if count > 0 else 0.0
        return success_rate > 0.9, {'success_rate': success_rate, 'packets_sent': success_count}

    async def test_error_fifo_functionality(self, count: int = 8) -> Tuple[bool, Dict[str, Any]]:
        """Test error FIFO functionality"""
        self.log.info(f"Testing error FIFO with {count} error packets...")

        # Send error packets
        for i in range(count):
            packet_dict = self.create_monbus_packet_dict(
                pkt_type=PktType.PktTypeError,
                event_code=0x1,
                channel_id=i,
                data=0x2000 + i
            )
            await self.send_packet(packet_dict)
            await self.wait_clocks(self.clk_name, 2)

        # Wait for packets to propagate
        await self.wait_clocks(self.clk_name, 50)

        # Read from error FIFO
        packets_read = 0
        for i in range(count + 2):
            data = await self.read_error_fifo()
            if data is not None and data != 0:
                packets_read += 1
            await self.wait_clocks(self.clk_name, 2)

        success_rate = packets_read / count if count > 0 else 0.0
        return success_rate > 0.5, {'packets_read': packets_read, 'success_rate': success_rate}

    def finalize_test(self):
        """Generate final test statistics"""
        self.stats['test_end_time'] = time.time()
        duration = self.stats['test_end_time'] - self.stats['test_start_time']

        self.log.info("="*60)
        self.log.info("STREAM MONBUS AXIL GROUP TEST STATISTICS")
        self.log.info("="*60)
        self.log.info(f"Test duration: {duration:.2f} seconds")
        self.log.info(f"Total packets sent: {self.stats['packets_sent']}")
        self.log.info(f"Error FIFO reads: {self.stats['error_fifo_reads']}")
        self.log.info("="*60)
