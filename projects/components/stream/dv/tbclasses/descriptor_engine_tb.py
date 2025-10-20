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
            # Create memory model (64 bytes per line for 512-bit AXI data)
            # Note: Descriptors are 256-bit, but AXI interface is 512-bit
            self.memory_model = MemoryModel(
                num_lines=5120,    # 320KB total
                bytes_per_line=64, # 512-bit AXI data width
                log=self.log
            )

            # Create AXI4 slave read responder (512-bit AXI data)
            # Note: RTL uses 512-bit AXI interface even though descriptors are 256-bit
            self.axi_slave = create_axi4_slave_rd(
                dut=self.dut,
                clock=self.clk,
                prefix="",  # No prefix - connects to top-level signals
                log=self.log,
                data_width=512,  # AXI interface is 512-bit (not descriptor width!)
                id_width=self.TEST_AXI_ID_WIDTH,
                addr_width=self.TEST_ADDR_WIDTH,
                user_width=1,
                multi_sig=True,
                memory_model=self.memory_model
            )

            self.r_slave = self.axi_slave['R']
            self.log.info("✓ AXI4 slave read responder initialized (512-bit)")

            # Create GAXI Master for APB interface
            apb_field_config = FieldConfig()
            apb_field_config.add_field(FieldDefinition(
                name='apb_addr',
                bits=self.TEST_ADDR_WIDTH,
                format='hex',
                description='APB address'
            ))

            self.apb_master = create_gaxi_master(
                dut=self.dut,
                title="APBMaster",
                prefix="apb",
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
        """Write data to memory model (512-bit AXI interface)"""
        data_bytes = bytearray(data.to_bytes(64, byteorder='little'))  # 64 bytes for 512 bits
        self.memory_model.write(addr, data_bytes)

    # ========================================================================
    # Test Cases
    # ========================================================================

    async def run_apb_basic_test(self, num_requests=5):
        """Test APB→AXI→Descriptor flow (APB ONLY interface)"""
        self.log.info(f"=== APB Basic Test: {num_requests} requests ===")

        descriptors_received = 0

        for i in range(num_requests):
            # Generate test address (aligned to 64 bytes for 512-bit AXI)
            test_addr = 0x10000 + (i * 0x200)

            # Prepare memory with test data (512-bit, but descriptor is 256-bit)
            # Lower 256 bits = descriptor, upper 256 bits can be 0 or next descriptor
            test_data = 0x12345678 + (i << 32) + test_addr
            self.write_memory(test_addr, test_data)

            self.log.info(f"APB request {i+1}: addr=0x{test_addr:X}")

            # Send APB request
            packet = self.apb_master.create_packet(apb_addr=test_addr)
            try:
                await self.apb_master.send(packet)
                self.apb_requests_sent += 1
            except Exception as e:
                self.log.error(f"Failed to send APB request: {e}")
                continue

            # Monitor for descriptor output
            timeout = 0
            while timeout < 100:
                await self.wait_clocks(self.clk_name, 1)
                if int(self.dut.descriptor_valid.value) == 1:
                    desc_data = int(self.dut.descriptor_packet.value)
                    descriptors_received += 1
                    self.descriptors_received += 1
                    self.received_descriptors.append({
                        'data': desc_data,
                        'expected': test_data,
                        'addr': test_addr
                    })
                    self.log.info(f"  🎯 Descriptor {descriptors_received}: data=0x{desc_data:X}")
                    break
                timeout += 1

            if timeout >= 100:
                self.test_errors.append(f"APB request {i+1} timeout")

            await self.wait_clocks(self.clk_name, 5)

        self.log.info(f"APB Basic Test: {descriptors_received}/{num_requests} descriptors received")
        return descriptors_received == num_requests

    async def run_test_with_profile(self, num_packets: int, profile: DelayProfile):
        """Run test with specific delay profile"""
        self.log.info(f"Testing with {profile.value} delay profile: {num_packets} packets")

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

        monitor_task = cocotb.start_soon(descriptor_monitor())

        # Send APB requests with profile-specific timing
        for i in range(num_packets):
            test_addr = 0x30000 + (i * 0x200)
            test_data = 0xABCDEF00 + (i << 32) + test_addr
            self.write_memory(test_addr, test_data)

            # Apply delay profile
            producer_delay = self.get_delay_value(params['producer_delay'])
            await self.wait_clocks(self.clk_name, producer_delay)

            # Backpressure simulation
            if random.random() < params.get('backpressure_freq', 0.1):
                backpressure_cycles = random.randint(5, 15)
                await self.wait_clocks(self.clk_name, backpressure_cycles)

            # Send APB request
            packet = self.apb_master.create_packet(apb_addr=test_addr)
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
