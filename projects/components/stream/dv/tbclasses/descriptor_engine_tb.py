# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: DescriptorEngineTB
# Purpose: STREAM Descriptor Engine Testbench - v1.0
#
# Documentation: projects/components/stream/PRD.md
# Subsystem: stream
#
# Author: sean galloway
# Created: 2025-10-19

"""
STREAM Descriptor Engine Testbench - v1.0

Testbench for STREAM descriptor engine, adapted from RAPIDS.

Features:
- APB programming interface → AXI read → Descriptor output flow (APB ONLY)
- Channel filtering and validation
- Uses AXI4 factory (create_axi4_slave_rd) for AXI read slave responder
- GAXI BFM for APB interface
- Background descriptor monitoring for 100% capture
- Multiple delay timing profiles

SIMPLIFICATIONS FROM RAPIDS:
- NO RDA interface (STREAM has APB interface only)
- APB-only testing (no network interfaces)
- 256-bit descriptors (not 512-bit data width)
- Fewer delay profiles (5 instead of 10)
- Simpler test infrastructure
- Focus on memory-to-memory DMA
"""

import os
import random
from typing import List, Dict, Any, Tuple, Optional
from enum import Enum

import cocotb

# Framework imports
from CocoTBFramework.tbclasses.shared.tbbase import TBBase
from CocoTBFramework.components.shared.memory_model import MemoryModel
from CocoTBFramework.components.axi4.axi4_factories import create_axi4_slave_rd
from CocoTBFramework.components.gaxi.gaxi_factories import create_gaxi_master
from CocoTBFramework.components.shared.field_config import FieldConfig, FieldDefinition

# STREAM-specific imports
from projects.components.stream.dv.tbclasses.descriptor_packet_builder import DescriptorPacketBuilder


class DelayProfile(Enum):
    """Delay profiles for timing randomization"""
    FAST_PRODUCER = "fast_producer"
    FAST_CONSUMER = "fast_consumer"
    FIXED_DELAY = "fixed_delay"
    MINIMAL_DELAY = "minimal_delay"
    BACKPRESSURE = "backpressure"


class DescriptorEngineTB(TBBase):
    """
    STREAM Descriptor Engine testbench (adapted from RAPIDS).

    Tests:
    - APB programming interface for descriptor fetches
    - AXI read operations from memory
    - Descriptor output validation (256-bit)
    - Channel filtering
    - Error handling

    NOTE: STREAM uses APB interface ONLY (no RDA/CDA interfaces)
    """

    def __init__(self, dut, clk=None, rst_n=None):
        super().__init__(dut)

        # Get test parameters from environment
        self.SEED = self.convert_to_int(os.environ.get('SEED', '12345'))
        self.TEST_LEVEL = os.environ.get('TEST_LEVEL', 'basic').lower()
        self.DEBUG = self.convert_to_int(os.environ.get('TEST_DEBUG', '0'))

        # Validate test level
        valid_levels = ['basic', 'medium', 'full']
        if self.TEST_LEVEL not in valid_levels:
            self.log.warning(f"Invalid TEST_LEVEL '{self.TEST_LEVEL}', using 'basic'. Valid: {valid_levels}")
            self.TEST_LEVEL = 'basic'

        # Test parameters
        self.TEST_NUM_CHANNELS = int(os.environ.get('STREAM_NUM_CHANNELS', '8'))
        self.TEST_ADDR_WIDTH = int(os.environ.get('STREAM_ADDR_WIDTH', '64'))
        self.TEST_DATA_WIDTH = int(os.environ.get('STREAM_DATA_WIDTH', '256'))  # 256-bit descriptors
        self.TEST_AXI_ID_WIDTH = int(os.environ.get('STREAM_AXI_ID_WIDTH', '8'))
        self.TEST_CLK_PERIOD = int(os.environ.get('TEST_CLK_PERIOD', '10'))
        self.SEED = int(os.environ.get('SEED', '12345'))

        random.seed(self.SEED)

        # Clock and reset
        self.clk = clk if clk else dut.clk
        self.clk_name = self.clk._name if hasattr(self.clk, '_name') else 'clk'
        self.rst_n = rst_n if rst_n else dut.rst_n

        self.MAX_ADDR = (2**self.TEST_ADDR_WIDTH) - 1

        # Test tracking
        self.apb_requests_sent = 0
        self.descriptors_received = 0
        self.axi_reads_completed = 0
        self.test_errors = []

        # Simplified delay profiles (5 instead of RAPIDS' 10)
        self.delay_params = {
            DelayProfile.FAST_PRODUCER: {
                'producer_delay': (1, 3),
                'consumer_delay': (5, 10),
                'burst_size': (10, 20),
                'backpressure_freq': 0.1
            },
            DelayProfile.FAST_CONSUMER: {
                'producer_delay': (5, 10),
                'consumer_delay': (1, 3),
                'burst_size': (5, 15),
                'backpressure_freq': 0.2
            },
            DelayProfile.FIXED_DELAY: {
                'producer_delay': 5,
                'consumer_delay': 5,
                'burst_size': (5, 15),
                'backpressure_freq': 0.2
            },
            DelayProfile.MINIMAL_DELAY: {
                'producer_delay': 1,
                'consumer_delay': 1,
                'burst_size': (20, 40),
                'backpressure_freq': 0.1
            },
            DelayProfile.BACKPRESSURE: {
                'producer_delay': (1, 5),
                'consumer_delay': (10, 20),
                'burst_size': (2, 8),
                'backpressure_freq': 0.5
            }
        }

        # Components (initialized after clock setup)
        self.axi_slave = None
        self.r_slave = None
        self.memory_model = None
        self.apb_master = None

        # Test data storage
        self.received_descriptors = []

    # ========================================================================
    # MANDATORY: Clock and Reset Control Methods
    # ========================================================================

    async def setup_clocks_and_reset(self):
        """Complete initialization - starts clocks and performs reset sequence."""
        self.log.info("=== Setting up clocks and reset ===")

        await self.start_clock(self.clk_name, freq=self.TEST_CLK_PERIOD, units='ns')

        await self.assert_reset()
        await self.wait_clocks(self.clk_name, 10)
        await self.deassert_reset()
        await self.wait_clocks(self.clk_name, 10)

        self.log.info("✅ Clocks and reset setup complete")

    async def assert_reset(self):
        """Assert reset signal (active-low)."""
        self.rst_n.value = 0

        # Reset AXI slave bus if initialized
        if self.axi_slave is not None and 'R' in self.axi_slave:
            await self.axi_slave['R'].reset_bus()
        if self.axi_slave is not None and 'AR' in self.axi_slave:
            await self.axi_slave['AR'].reset_bus()

    async def deassert_reset(self):
        """Deassert reset signal (active-low)."""
        self.rst_n.value = 1

    # ========================================================================
    # Initialization
    # ========================================================================

    async def initialize_test(self):
        """Initialize test components"""
        self.log.info("=== Initializing Descriptor Engine Test ===")

        try:
            # Create memory model (32 bytes per line for 256-bit descriptor AXI data)
            # Note: descriptor_engine.sv now uses FIXED 256-bit AXI interface
            # Size: 16384 lines * 32 bytes = 512KB (covers 0x00000 - 0x7FFFF)
            self.memory_model = MemoryModel(
                num_lines=16384,   # 512KB total (16384 * 32 bytes)
                bytes_per_line=32, # 256-bit AXI data width (FIXED in descriptor_engine.sv)
                log=self.log
            )

            # Create AXI4 slave read responder (256-bit AXI data)
            # Note: RTL was changed to use FIXED 256-bit descriptors (not parameterized)
            self.axi_slave = create_axi4_slave_rd(
                dut=self.dut,
                clock=self.clk,
                prefix="",  # No prefix - connects to top-level signals
                log=self.log,
                data_width=256,  # FIXED 256-bit descriptor width
                id_width=self.TEST_AXI_ID_WIDTH,
                addr_width=self.TEST_ADDR_WIDTH,
                user_width=1,
                multi_sig=True,
                memory_model=self.memory_model
            )

            self.r_slave = self.axi_slave['R']
            self.log.info("✓ AXI4 slave read responder initialized (256-bit)")

            # Create GAXI Master for APB interface
            # Note: GAXI master uses 'addr' field name, not 'apb_addr'
            apb_field_config = FieldConfig()
            apb_field_config.add_field(FieldDefinition(
                name='addr',  # GAXI standard field name
                bits=self.TEST_ADDR_WIDTH,
                format='hex',
                description='APB address'
            ))

            self.apb_master = create_gaxi_master(
                dut=self.dut,
                title="APBMaster",
                prefix="apb",  # Connects to apb_valid, apb_ready, apb_addr
                clock=self.clk,
                field_config=apb_field_config,
                log=self.log,
                mode='skid',
                multi_sig=True
            )
            self.log.info("✓ GAXI APB Master initialized")

            # Initialize DUT configuration
            await self.configure_descriptor_engine()

        except Exception as e:
            self.log.error(f"Initialization failed: {e}")
            raise

    async def configure_descriptor_engine(self):
        """Configure descriptor engine"""
        self.log.info("Configuring descriptor engine...")

        self.dut.cfg_prefetch_enable.value = 0
        self.dut.cfg_fifo_threshold.value = 4
        self.dut.cfg_addr0_base.value = 0x10000
        self.dut.cfg_addr0_limit.value = 0x4FFFF
        self.dut.cfg_channel_reset.value = 0

        self.dut.descriptor_ready.value = 1

        # Channel idle signal (indicates scheduler is idle, enables APB)
        # For standalone descriptor engine tests, tie high to allow APB writes
        self.dut.channel_idle.value = 1

        await self.wait_clocks(self.clk_name, 10)
        self.log.info("✓ Descriptor engine configured")

    # ========================================================================
    # Memory and Descriptor Operations
    # ========================================================================

    def write_memory(self, addr, data):
        """Write data to memory model (256-bit AXI interface)"""
        data_bytes = bytearray(data.to_bytes(32, byteorder='little'))  # 32 bytes for 256 bits
        self.memory_model.write(addr, data_bytes)

    # ========================================================================
    # Test Cases
    # ========================================================================

    async def run_apb_basic_test(self, num_requests=5):
        """Test APB→AXI→Descriptor flow with chained descriptors"""
        self.log.info(f"=== APB Basic Test: {num_requests} chained descriptors ===")

        descriptors_received = 0

        # Create chain of descriptors
        # First descriptor starts at 0x10100 (NOT 0x0!)
        base_addr = 0x10100
        descriptor_spacing = 0x100  # 256-byte spacing (aligned to 32 bytes)

        # Write all descriptors to memory first
        for i in range(num_requests):
            test_addr = base_addr + (i * descriptor_spacing)

            # Calculate next descriptor address (0 for last descriptor)
            if i < num_requests - 1:
                next_ptr = base_addr + ((i + 1) * descriptor_spacing)
                is_last = False
            else:
                next_ptr = 0  # Last descriptor
                is_last = True

            # Create properly-formed descriptor using DescriptorPacketBuilder
            descriptor = DescriptorPacketBuilder.build_descriptor_packet(
                src_addr=0x80000000 + (i * 0x1000),  # Source address
                dst_addr=0x90000000 + (i * 0x1000),  # Destination address
                length=64,                            # 64 beats transfer
                next_ptr=next_ptr,                    # Chain to next descriptor
                valid=True,                           # ← CRITICAL: valid bit set!
                gen_irq=False,
                last=is_last,                         # Only last descriptor has last=1
                error=False,
                channel_id=0,
                priority=0
            )

            # Write 256-bit descriptor to memory
            self.write_memory(test_addr, descriptor)
            self.log.info(f"  Wrote descriptor {i+1} at addr=0x{test_addr:X}, next_ptr=0x{next_ptr:X}, last={is_last}")

        # Send single APB request to kick off the chain (only write FIRST descriptor address)
        first_addr = base_addr
        self.log.info(f"APB kick-off: addr=0x{first_addr:X} (start of chain)")

        # Send APB request for first descriptor
        packet = self.apb_master.create_packet(addr=first_addr)
        try:
            await self.apb_master.send(packet)
            self.apb_requests_sent += 1
        except Exception as e:
            self.log.error(f"Failed to send APB request: {e}")
            self.test_errors.append("APB request failed")
            return False

        # Monitor for ALL descriptors in the chain
        # Descriptor engine should autonomously fetch all chained descriptors
        max_timeout = 500  # Total timeout for entire chain
        timeout = 0
        while descriptors_received < num_requests and timeout < max_timeout:
            await self.wait_clocks(self.clk_name, 1)
            if int(self.dut.descriptor_valid.value) == 1:
                desc_data = int(self.dut.descriptor_packet.value)
                descriptors_received += 1
                self.descriptors_received += 1
                self.log.info(f"  ✅ Descriptor {descriptors_received} received")

                # Store received descriptor
                self.received_descriptors.append({
                    'data': desc_data,
                    'sequence': descriptors_received
                })
            timeout += 1

        if descriptors_received < num_requests:
            self.test_errors.append(f"Timeout: received {descriptors_received}/{num_requests} descriptors")

        self.log.info(f"APB Basic Test: {descriptors_received}/{num_requests} descriptors received")
        return descriptors_received == num_requests

    async def run_test_with_profile(self, num_packets: int, profile: DelayProfile):
        """Run test with specific delay profile - tests autonomous chaining"""
        self.log.info(f"Testing with {profile.value} delay profile: {num_packets} chained packets")

        params = self.delay_params[profile]
        descriptors_collected = []
        monitor_active = True

        # Background descriptor monitor
        async def descriptor_monitor():
            while monitor_active:
                await self.wait_clocks(self.clk_name, 1)
                if int(self.dut.descriptor_valid.value) == 1:
                    desc_data = int(self.dut.descriptor_packet.value)
                    descriptors_collected.append(desc_data)
                    self.log.info(f"  ✅ Descriptor {len(descriptors_collected)} received")

        monitor_task = cocotb.start_soon(descriptor_monitor())

        # Create chained descriptors (autonomous chaining test)
        base_addr = 0x30000
        descriptor_spacing = 0x100

        # Write all descriptors to memory first
        for i in range(num_packets):
            test_addr = base_addr + (i * descriptor_spacing)

            # Calculate next descriptor address (0 for last descriptor)
            if i < num_packets - 1:
                next_ptr = base_addr + ((i + 1) * descriptor_spacing)
                is_last = False
            else:
                next_ptr = 0  # Last descriptor
                is_last = True

            # Create properly-formed descriptor
            descriptor = DescriptorPacketBuilder.build_descriptor_packet(
                src_addr=0xA0000000 + (i * 0x1000),
                dst_addr=0xB0000000 + (i * 0x1000),
                length=32,
                next_ptr=next_ptr,  # Chain to next descriptor
                valid=True,
                last=is_last,
                channel_id=0,
                priority=i % 8
            )
            self.write_memory(test_addr, descriptor)

        # Send SINGLE APB request to kick off the chain
        # Descriptor engine should autonomously fetch all chained descriptors
        first_addr = base_addr
        self.log.info(f"APB kick-off: addr=0x{first_addr:X} (chain of {num_packets} descriptors)")

        # Apply delay profile before APB request
        producer_delay = self.get_delay_value(params['producer_delay'])
        await self.wait_clocks(self.clk_name, producer_delay)

        # Send APB request
        packet = self.apb_master.create_packet(addr=first_addr)
        await self.apb_master.send(packet)
        self.apb_requests_sent += 1

        # Wait for all descriptors
        await self.wait_clocks(self.clk_name, 500)

        monitor_active = False
        await self.wait_clocks(self.clk_name, 2)

        descriptors_received = len(descriptors_collected)
        self.descriptors_received += descriptors_received

        success_rate = (descriptors_received / num_packets) * 100
        self.log.info(f"{profile.value} test: {descriptors_received}/{num_packets} ({success_rate:.1f}%)")

        return success_rate >= 100  # Must receive ALL descriptors

    def get_delay_value(self, delay_param):
        """Get delay value (int or tuple)"""
        if isinstance(delay_param, tuple):
            return random.randint(delay_param[0], delay_param[1])
        return delay_param

    # ========================================================================
    # Reporting
    # ========================================================================

    def generate_final_report(self):
        """Generate test report"""
        self.log.info("\n=== DESCRIPTOR ENGINE TEST REPORT ===")
        self.log.info(f"APB requests sent: {self.apb_requests_sent}")
        self.log.info(f"Descriptors received: {self.descriptors_received}")
        self.log.info(f"AXI reads completed: {self.axi_reads_completed}")

        if self.test_errors:
            self.log.error(f"Test errors ({len(self.test_errors)}):")
            for error in self.test_errors:
                self.log.error(f"  - {error}")
            return False
        else:
            self.log.info("✅ All tests passed!")
            return True
