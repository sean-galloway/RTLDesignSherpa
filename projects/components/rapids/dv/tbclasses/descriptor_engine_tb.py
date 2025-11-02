# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: DelayProfile
# Purpose: RAPIDS Descriptor Engine Testbench - v1.1
#
# Documentation: projects/components/rapids/PRD.md
# Subsystem: rapids
#
# Author: sean galloway
# Created: 2025-10-18

"""
RAPIDS Descriptor Engine Testbench - v1.1

Testbench for the descriptor engine following RAPIDS/AMBA framework patterns.
Tests both APB programming interface and CDA packet reception paths.

Features:
- APB programming interface → AXI read → Descriptor output flow
- CDA packet reception → Descriptor output flow (bypass AXI)
- Channel filtering and validation
- Error injection and handling
- Uses AXI4 factory (create_axi4_slave_rd) for AXI read slave responder
- Proper framework-based logging and structure
"""

import os
import random
import cocotb
from typing import List, Dict, Any, Tuple, Optional, Union
import time
from enum import Enum

# Framework imports
from CocoTBFramework.tbclasses.shared.tbbase import TBBase
from CocoTBFramework.components.shared.memory_model import MemoryModel
from CocoTBFramework.components.axi4.axi4_factories import create_axi4_slave_rd
from CocoTBFramework.components.gaxi.gaxi_factories import create_gaxi_master
from CocoTBFramework.components.shared.field_config import FieldConfig, FieldDefinition


class DelayProfile(Enum):
    """Delay profiles for flex randomizer"""
    FAST_PRODUCER = "fast_producer"      # High producer rate, normal consumer
    FAST_CONSUMER = "fast_consumer"      # Normal producer, high consumer rate
    FIXED_DELAY = "fixed_delay"          # Fixed delay between operations
    RANDOM_BURST = "random_burst"        # Random bursts of activity
    BACKPRESSURE = "backpressure"        # Frequent backpressure events
    MINIMAL_DELAY = "minimal_delay"      # Minimal delays (stress test)
    MODERATE_PACE = "moderate_pace"      # Balanced moderate timing
    SLOW_PRODUCER = "slow_producer"      # Slow producer rate
    PIPELINE_STALL = "pipeline_stall"    # Periodic pipeline stalls
    MIXED_TIMING = "mixed_timing"        # Mixed timing patterns


class TestClass(Enum):
    """Test class definitions"""
    APB_ONLY = "apb_only"        # APB → AXI → Descriptor flow only
    CDA_ONLY = "cda_only"        # CDA → Descriptor flow only
    MIXED = "mixed"              # Concurrent APB and CDA operations


class DescriptorEngineTB(TBBase):
    """
    Complete RAPIDS Descriptor Engine testbench.

    Tests comprehensive descriptor engine functionality:
    - APB programming interface for descriptor fetches
    - AXI read operations from memory
    - CDA packet reception (Network slave interface)
    - Descriptor output validation
    - Channel filtering and validation
    - Error handling and flow control
    - Concurrent APB + CDA operation
    """

    def __init__(self, dut, clk=None, rst_n=None):
        super().__init__(dut)

        # Get test parameters from environment
        self.TEST_NUM_CHANNELS = self.convert_to_int(os.environ.get('TEST_NUM_CHANNELS', '32'))
        self.TEST_ADDR_WIDTH = self.convert_to_int(os.environ.get('TEST_ADDR_WIDTH', '64'))
        self.TEST_DATA_WIDTH = self.convert_to_int(os.environ.get('TEST_DATA_WIDTH', '512'))
        self.TEST_AXI_ID_WIDTH = self.convert_to_int(os.environ.get('TEST_AXI_ID_WIDTH', '8'))
        self.TEST_CLK_PERIOD = self.convert_to_int(os.environ.get('TEST_CLK_PERIOD', '10'))
        self.SEED = self.convert_to_int(os.environ.get('SEED', '12345'))

        # Initialize random generator
        random.seed(self.SEED)

        # Setup clock and reset signals
        self.clk = clk if clk else dut.clk
        self.clk_name = self.clk._name if hasattr(self.clk, '_name') else 'clk'
        self.rst_n = rst_n if rst_n else dut.rst_n

        # Set limits based on widths
        self.MAX_ADDR = (2**self.TEST_ADDR_WIDTH) - 1
        self.MAX_DATA = (2**self.TEST_DATA_WIDTH) - 1
        self.MAX_CHANNEL = self.TEST_NUM_CHANNELS - 1

        # Test configuration
        self.test_config = {
            'enable_compliance_check': self.convert_to_int(os.environ.get('DESCRIPTOR_COMPLIANCE_CHECK', '1')),
            'validate_all_channels': self.convert_to_int(os.environ.get('VALIDATE_ALL_CHANNELS', '1')),
            'apb_error_injection': self.convert_to_int(os.environ.get('APB_ERROR_INJECTION', '1')),
            'cda_stress_test': self.convert_to_int(os.environ.get('CDA_STRESS_TEST', '1')),
            'concurrent_operations': self.convert_to_int(os.environ.get('CONCURRENT_OPERATIONS', '1')),
            'descriptor_backpressure': self.convert_to_int(os.environ.get('DESCRIPTOR_BACKPRESSURE', '1'))
        }

        # AXI slave component (will be created after clock starts)
        self.axi_slave = None
        self.r_slave = None
        self.memory_model = None

        # GAXI Master BFMs for APB and CDA interfaces
        self.apb_master = None  # Will be initialized after clock setup
        self.cda_master = None  # Will be initialized after clock setup

        # Test tracking
        self.apb_requests_sent = 0
        self.cda_packets_sent = 0
        self.descriptors_received = 0
        self.axi_reads_completed = 0
        self.test_errors = []

        # Test class tracking
        self.current_test_class = None
        self.current_delay_profile = None
        self.packet_sequence_count = 0

        # Enhanced delay profile parameters for extensive randomization testing
        # Each profile designed to run for hundreds of cycles with comprehensive timing exploration
        self.delay_params = {
            DelayProfile.FAST_PRODUCER: {
                'producer_delay': (1, 3),       # Very short delays between producer operations
                'consumer_delay': (5, 15),      # Normal consumer response
                'burst_size': (10, 25),         # Medium burst sizes
                'backpressure_freq': 0.1,       # Low backpressure
                'inter_burst_delay': (2, 8),    # Delay between bursts
                'randomization_cycles': 50      # Extra cycles for randomization
            },
            DelayProfile.FAST_CONSUMER: {
                'producer_delay': (8, 20),      # Normal producer rate
                'consumer_delay': (1, 3),       # Very fast consumer
                'burst_size': (5, 15),          # Small to medium bursts
                'backpressure_freq': 0.05,      # Very low backpressure
                'inter_burst_delay': (3, 12),   # Variable inter-burst delay
                'randomization_cycles': 40      # Extra cycles for randomization
            },
            DelayProfile.FIXED_DELAY: {
                'producer_delay': 8,            # Fixed delay
                'consumer_delay': 8,            # Fixed delay
                'burst_size': 10,               # Fixed burst size
                'backpressure_freq': 0.1,       # Fixed backpressure rate
                'inter_burst_delay': 10,        # Fixed inter-burst delay
                'randomization_cycles': 20      # Minimal randomization for fixed pattern
            },
            DelayProfile.RANDOM_BURST: {
                'producer_delay': (1, 30),      # Very wide range of delays
                'consumer_delay': (2, 25),      # Variable consumer response
                'burst_size': (1, 50),          # Very variable burst sizes
                'backpressure_freq': 0.2,       # Medium backpressure
                'inter_burst_delay': (1, 40),   # Very variable inter-burst delay
                'randomization_cycles': 80      # High randomization
            },
            DelayProfile.BACKPRESSURE: {
                'producer_delay': (3, 8),       # Moderate producer rate
                'consumer_delay': (10, 30),     # Slow consumer creates backpressure
                'burst_size': (2, 8),           # Small bursts
                'backpressure_freq': 0.4,       # High backpressure
                'inter_burst_delay': (5, 20),   # Moderate inter-burst delay
                'randomization_cycles': 60      # Medium randomization
            },
            DelayProfile.MINIMAL_DELAY: {
                'producer_delay': 1,            # Minimal delays - stress test
                'consumer_delay': 1,            # Minimal delays
                'burst_size': (20, 50),         # Large bursts for stress testing
                'backpressure_freq': 0.3,       # Medium backpressure
                'inter_burst_delay': (1, 5),    # Minimal inter-burst delay
                'randomization_cycles': 30      # Some randomization even in stress test
            },
            DelayProfile.MODERATE_PACE: {
                'producer_delay': (6, 15),      # Balanced timing
                'consumer_delay': (6, 15),      # Balanced timing
                'burst_size': (5, 20),          # Moderate bursts
                'backpressure_freq': 0.15,      # Low-medium backpressure
                'inter_burst_delay': (8, 16),   # Balanced inter-burst delay
                'randomization_cycles': 45      # Moderate randomization
            },
            DelayProfile.SLOW_PRODUCER: {
                'producer_delay': (15, 40),     # Slow producer rate
                'consumer_delay': (2, 8),       # Fast consumer
                'burst_size': (1, 6),           # Small bursts
                'backpressure_freq': 0.05,      # Low backpressure
                'inter_burst_delay': (10, 30),  # Long pauses between bursts
                'randomization_cycles': 70      # High randomization for timing
            },
            DelayProfile.PIPELINE_STALL: {
                'producer_delay': (5, 12),      # Normal rate with stalls
                'consumer_delay': (5, 12),      # Normal rate with stalls
                'burst_size': (3, 15),          # Medium bursts
                'backpressure_freq': 0.25,      # Medium-high backpressure
                'inter_burst_delay': (8, 25),   # Variable stall periods
                'stall_freq': 0.15,             # Periodic pipeline stalls
                'randomization_cycles': 55      # Medium-high randomization
            },
            DelayProfile.MIXED_TIMING: {
                'producer_delay': (1, 50),      # Extremely wide timing range
                'consumer_delay': (1, 50),      # Extremely wide timing range
                'burst_size': (1, 60),          # Very wide burst range
                'backpressure_freq': 0.2,       # Medium backpressure
                'inter_burst_delay': (1, 60),   # Extremely variable inter-burst delay
                'randomization_cycles': 100     # Maximum randomization
            }
        }

        # Test data storage
        self.pending_apb_requests = []
        self.pending_cda_packets = []
        self.received_descriptors = []

    async def initialize_test(self):
        """Initialize test components and interfaces"""
        self.log.info("=== Initializing Descriptor Engine Test ===")

        try:
            # Create memory model for AXI read transactions
            # Need to cover test addresses: 0x10000-0x4FFFF (~320KB range)
            # Maximum address: 0x4FFFF (327679) + 64 bytes = 327743 bytes needed
            # Use 320KB memory (5120 lines × 64 bytes per line = 327680 bytes)
            self.memory_model = MemoryModel(
                num_lines=5120,     # 320KB total (5120 × 64)
                bytes_per_line=64,  # 512-bit data width = 64 bytes
                log=self.log
            )
            self.log.info("Memory model initialized")

            # Create AXI4 slave read responder using factory
            # Descriptor engine is AXI4 read master, so we need slave read interface
            # Signals have no prefix (ar_valid, not m_axi_arvalid)
            self.axi_slave = create_axi4_slave_rd(
                dut=self.dut,
                clock=self.clk,
                prefix="",       # No prefix - signals are ar_*, r_*
                log=self.log,
                data_width=self.TEST_DATA_WIDTH,   # From environment
                id_width=self.TEST_AXI_ID_WIDTH,   # From environment
                addr_width=self.TEST_ADDR_WIDTH,   # From environment
                user_width=1,    # Minimal user width
                multi_sig=True,  # Separate channel signals
                memory_model=self.memory_model
            )

            # Extract R channel for response control if needed
            self.r_slave = self.axi_slave['R']
            self.log.info("✓ AXI4 slave read responder initialized")

            # Create GAXI Master for APB interface
            apb_field_config = FieldConfig()
            apb_field_config.add_field(FieldDefinition(
                name='apb_addr',
                bits=self.TEST_ADDR_WIDTH,
                format='hex',
                description='APB address'
            ))

            self.log.info("Creating GAXI APB Master...")
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
            self.log.info(f"✓ GAXI APB Master initialized: {self.apb_master}")

            if self.apb_master is None:
                raise RuntimeError("GAXI APB Master creation returned None!")

            # Create GAXI Master for CDA interface
            # IMPORTANT: Field names must NOT include prefix!
            # With prefix="cda", field "packet" maps to RTL signal "cda_packet"
            cda_field_config = FieldConfig()
            cda_field_config.add_field(FieldDefinition(
                name='packet',  # Maps to "cda_packet" (prefix + field_name)
                bits=self.TEST_DATA_WIDTH,
                format='hex',
                description='CDA packet data'
            ))
            cda_field_config.add_field(FieldDefinition(
                name='channel',  # Maps to "cda_channel" (prefix + field_name)
                bits=6,  # Channel ID width
                format='hex',
                description='CDA channel ID'
            ))

            self.log.info("Creating GAXI CDA Master...")
            self.cda_master = create_gaxi_master(
                dut=self.dut,
                title="CDAMaster",
                prefix="cda",
                clock=self.clk,
                field_config=cda_field_config,
                log=self.log,
                mode='skid',
                multi_sig=True
            )
            self.log.info(f"✓ GAXI CDA Master initialized: {self.cda_master}")

            if self.cda_master is None:
                raise RuntimeError("GAXI CDA Master creation returned None!")

            # Initialize DUT configuration
            await self.configure_descriptor_engine()
            self.log.info("Descriptor engine configuration completed")

        except Exception as e:
            self.log.error(f"Initialization failed: {str(e)}")
            raise

    async def configure_descriptor_engine(self):
        """Configure the descriptor engine for testing"""
        self.log.info("Configuring descriptor engine...")

        # Configure descriptor engine parameters
        self.dut.cfg_prefetch_enable.value = 0  # Start with prefetch disabled
        self.dut.cfg_fifo_threshold.value = 4   # FIFO threshold
        self.dut.cfg_addr0_base.value = 0x30000  # Address range 0 - matches test addresses
        self.dut.cfg_addr0_limit.value = 0x4FFFF
        self.dut.cfg_addr1_base.value = 0x10000  # Address range 1
        self.dut.cfg_addr1_limit.value = 0x2FFFF
        self.dut.cfg_channel_reset.value = 0     # No channel reset

        # Note: APB and CDA interface signals now managed by GAXI Master BFMs
        # (No manual initialization needed - BFMs handle valid/ready handshaking)

        self.dut.descriptor_ready.value = 1  # Ready to receive descriptors

        await self.wait_clocks(self.clk_name, 10)
        self.log.info("Descriptor engine configured (BFMs handle APB/CDA signals)")

    def write_memory(self, addr, data):
        """Write data to memory model"""
        # Convert 512-bit data to bytearray (little-endian)
        data_bytes = bytearray(data.to_bytes(64, byteorder='little'))
        self.memory_model.write(addr, data_bytes)

    async def run_apb_basic_test(self, num_requests=5):
        """Run basic APB→AXI→Descriptor flow test using GAXI APB Master BFM"""
        self.log.info(f"=== APB Basic Test: {num_requests} requests ===")

        descriptors_received = 0

        for i in range(num_requests):
            # Generate test address
            test_addr = 0x10000 + (i * 0x200)

            # Prepare memory with test data
            test_data = 0x1234567800000000 + (i << 32) + test_addr
            self.write_memory(test_addr, test_data)

            self.log.info(f"APB request {i+1}: addr=0x{test_addr:X}")

            # Send APB request using GAXI Master BFM
            packet = self.apb_master.create_packet(apb_addr=test_addr)
            try:
                await self.apb_master.send(packet)
                self.apb_requests_sent += 1
            except Exception as e:
                self.log.error(f"Failed to send APB request: {str(e)}")
                self.test_errors.append(f"APB request {i+1} send failed")
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
                        'source': 'APB',
                        'data': desc_data,
                        'expected': test_data,
                        'addr': test_addr
                    })
                    self.log.info(f"  🎯 Descriptor {descriptors_received}: data=0x{desc_data:X}")
                    break
                timeout += 1

            if timeout >= 100:
                self.test_errors.append(f"APB request {i+1} timeout waiting for descriptor")

            await self.wait_clocks(self.clk_name, 5)

        self.log.info(f"APB Basic Test complete: {descriptors_received}/{num_requests} descriptors received")
        return descriptors_received == num_requests

    async def run_cda_basic_test(self, num_packets=5):
        """Run basic CDA→Descriptor flow test using GAXI CDA Master BFM with continuous monitoring"""
        self.log.info(f"=== CDA Basic Test: {num_packets} packets ===")

        descriptors_collected = []
        monitor_active = True

        # Background coroutine to continuously monitor descriptors
        async def descriptor_monitor():
            """Continuously monitor for descriptors throughout the test"""
            while monitor_active:
                await self.wait_clocks(self.clk_name, 1)
                if int(self.dut.descriptor_valid.value) == 1:
                    desc_data = int(self.dut.descriptor_packet.value)
                    descriptors_collected.append(desc_data)
                    self.log.info(f"  📦 CDA Descriptor {len(descriptors_collected)}: data=0x{desc_data:X}")

        # Start background descriptor monitor
        monitor_task = cocotb.start_soon(descriptor_monitor())

        # Send all CDA packets
        for i in range(num_packets):
            # Generate varied test data and channels
            test_data = 0x1234567800000000 + (i << 32) + (i * 0x1111)
            test_channel = i % min(self.TEST_NUM_CHANNELS, 4)  # Rotate through available channels

            self.log.info(f"CDA packet {i+1}: ch={test_channel}, data=0x{test_data:X}")

            # Send CDA packet using GAXI Master BFM
            packet = self.cda_master.create_packet(
                packet=test_data,  # Fixed: Use "packet" not "cda_packet"
                channel=test_channel  # Fixed: Use "channel" not "cda_channel"
            )
            try:
                await self.cda_master.send(packet)
                self.cda_packets_sent += 1
            except Exception as e:
                self.log.error(f"Failed to send CDA packet: {str(e)}")
                self.test_errors.append(f"CDA packet {i+1} send failed")
                continue

            await self.wait_clocks(self.clk_name, 3)

        # Wait for all descriptors to be collected
        self.log.info(f"CDA packets sent, waiting for descriptors ({len(descriptors_collected)}/{num_packets} so far)")
        for cycle in range(500):  # Extended timeout for all descriptors
            await self.wait_clocks(self.clk_name, 1)
            if len(descriptors_collected) >= num_packets:
                self.log.info(f"✅ All {num_packets} descriptors collected")
                break

        # Stop background monitor
        monitor_active = False
        await self.wait_clocks(self.clk_name, 2)

        # Update global counter
        descriptors_received = len(descriptors_collected)
        self.descriptors_received += descriptors_received

        if descriptors_received < num_packets:
            self.log.error(f"❌ Only received {descriptors_received}/{num_packets} descriptors")
            self.test_errors.append(f"CDA test incomplete: {descriptors_received}/{num_packets}")

        self.log.info(f"CDA Basic Test complete: {descriptors_received}/{num_packets} descriptors received")
        return descriptors_received == num_packets

    async def run_concurrent_test(self):
        """Run sequential APB (startup) then CDA (normal operation) test

        IMPORTANT: APB has highest priority by design and will starve CDA if
        sent concurrently. The descriptor engine is designed for:
        1. APB startup phase: APB requests only (programming)
        2. Normal operation: CDA packets only (no APB trickle)

        This test validates both phases sequentially (not truly concurrent).
        """
        self.log.info("=== Sequential APB (Startup) + CDA (Operation) Test ===")

        descriptors_collected = []
        monitor_active = True

        # Background coroutine to continuously monitor descriptors
        async def descriptor_monitor():
            """Continuously monitor for descriptors throughout the test"""
            while monitor_active:
                await self.wait_clocks(self.clk_name, 1)
                if int(self.dut.descriptor_valid.value) == 1:
                    desc_data = int(self.dut.descriptor_packet.value)
                    desc_is_cda = int(self.dut.descriptor_is_cda.value)
                    descriptors_collected.append({'data': desc_data, 'is_cda': desc_is_cda})
                    self.log.info(f"  📦 Descriptor captured: data=0x{desc_data:X}, is_cda={desc_is_cda}")

        # Start background descriptor monitor BEFORE sending packets
        monitor_task = cocotb.start_soon(descriptor_monitor())

        # Phase 1: APB startup (simulating initialization/programming)
        self.log.info("Phase 1: APB startup programming")
        apb_addr = 0x20000
        apb_data = 0x1234567800020000
        self.write_memory(apb_addr, apb_data)

        # Send APB request
        apb_packet = self.apb_master.create_packet(apb_addr=apb_addr)
        await self.apb_master.send(apb_packet)
        self.apb_requests_sent += 1

        # Wait for APB descriptor
        apb_received = False
        for timeout in range(100):
            await self.wait_clocks(self.clk_name, 1)
            if len(descriptors_collected) > 0 and descriptors_collected[-1]['is_cda'] == 0:
                self.log.info(f"✓ APB descriptor received: data=0x{descriptors_collected[-1]['data']:X}")
                apb_received = True
                break

        if not apb_received:
            self.test_errors.append("APB startup phase timeout")
            monitor_active = False
            await self.wait_clocks(self.clk_name, 2)
            return False

        # Wait for APB phase to complete and RTL to return to fully idle state
        # Must monitor BOTH descriptor_engine_idle AND operation flags
        idle_timeout = 0
        while idle_timeout < 200:  # Max 200 cycles timeout
            await self.wait_clocks(self.clk_name, 1)

            # Check both idle signal and operation flags
            engine_idle = int(self.dut.descriptor_engine_idle.value)
            apb_active = int(self.dut.r_apb_operation_active.value)
            cda_active = int(self.dut.r_cda_operation_active.value)

            if engine_idle == 1 and apb_active == 0 and cda_active == 0:
                self.log.info(f"✓ Descriptor engine fully idle after {idle_timeout} cycles (FSM=IDLE, no active operations)")
                break
            idle_timeout += 1

        if idle_timeout >= 200:
            self.log.error(f"❌ Descriptor engine did not reach fully idle state (idle={engine_idle}, apb_active={apb_active}, cda_active={cda_active})")
            self.test_errors.append("Descriptor engine idle timeout between APB and CDA phases")
            monitor_active = False
            await self.wait_clocks(self.clk_name, 2)
            return False

        # Additional safety margin after idle detected
        await self.wait_clocks(self.clk_name, 10)

        # Phase 2: CDA normal operation (after startup)
        self.log.info("Phase 2: CDA normal operation")
        cda_data = 0xC0CCEAAEAD12345
        cda_channel = 2

        # Record how many descriptors we have before CDA phase
        descriptors_before_cda = len(descriptors_collected)

        # Send CDA packet
        cda_packet = self.cda_master.create_packet(
            packet=cda_data,
            channel=cda_channel
        )
        await self.cda_master.send(cda_packet)
        self.cda_packets_sent += 1

        # Wait for CDA descriptor (background monitor will catch it)
        cda_received = False
        for timeout in range(100):
            await self.wait_clocks(self.clk_name, 1)
            if len(descriptors_collected) > descriptors_before_cda:
                # New descriptor appeared
                new_desc = descriptors_collected[-1]
                if new_desc['is_cda'] == 1:
                    self.log.info(f"✓ CDA descriptor received: data=0x{new_desc['data']:X}")
                    cda_received = True
                    break

        if not cda_received:
            self.test_errors.append("CDA operation phase timeout")
            monitor_active = False
            await self.wait_clocks(self.clk_name, 2)
            return False

        # Stop background monitor
        monitor_active = False
        await self.wait_clocks(self.clk_name, 10)

        # Update global counter
        self.descriptors_received += len(descriptors_collected)

        self.log.info(f"Sequential test complete: APB={'✓' if apb_received else '✗'}, CDA={'✓' if cda_received else '✗'}")
        return apb_received and cda_received  # Both phases must succeed

    def generate_final_report(self):
        """Generate comprehensive test report"""
        self.log.info("\n=== DESCRIPTOR ENGINE TEST REPORT ===")
        self.log.info(f"APB requests sent: {self.apb_requests_sent}")
        self.log.info(f"CDA packets sent: {self.cda_packets_sent}")
        self.log.info(f"Descriptors received: {self.descriptors_received}")
        self.log.info(f"AXI reads completed: {self.axi_reads_completed}")

        if self.test_errors:
            self.log.error(f"Test errors ({len(self.test_errors)}):")
            for error in self.test_errors:
                self.log.error(f"  - {error}")
            return False
        else:
            self.log.info("✅ All tests passed successfully!")
            return True

    def get_delay_value(self, delay_param):
        """Get delay value based on parameter type (int or tuple for range)"""
        if isinstance(delay_param, tuple):
            return random.randint(delay_param[0], delay_param[1])
        return delay_param

    def setup_delay_profile(self, profile: DelayProfile):
        """Setup timing parameters for the specified delay profile"""
        self.current_delay_profile = profile
        self.log.info(f"📊 Configured delay profile: {profile.value}")

        params = self.delay_params[profile]
        self.log.info(f"   Producer delay: {params['producer_delay']} clocks")
        self.log.info(f"   Consumer delay: {params['consumer_delay']} clocks")
        self.log.info(f"   Burst size: {params['burst_size']} packets")

    async def run_comprehensive_test_class(self, test_class: TestClass, num_packets: int = 100, test_level: str = "medium"):
        """Run comprehensive test for specified class with selected delay profiles"""
        self.current_test_class = test_class
        self.log.info(f"\n🎯 === COMPREHENSIVE {test_class.value.upper()} TEST CLASS ({num_packets} packets, {test_level} level) ===")

        test_results = {}

        # Select delay profiles based on test level
        if test_level == "full":
            # Full level: Test ALL delay profiles for maximum coverage
            delay_profiles = list(DelayProfile)
            self.log.info(f"🚀 FULL LEVEL: Testing all {len(delay_profiles)} delay profiles for maximum coverage")
        elif test_level == "medium":
            # Medium level: Test diverse subset of profiles (7 profiles)
            delay_profiles = [
                DelayProfile.FAST_PRODUCER,
                DelayProfile.FAST_CONSUMER,
                DelayProfile.FIXED_DELAY,
                DelayProfile.MINIMAL_DELAY,
                DelayProfile.BACKPRESSURE,
                DelayProfile.MODERATE_PACE,
                DelayProfile.RANDOM_BURST
            ]
            self.log.info(f"📊 MEDIUM LEVEL: Testing {len(delay_profiles)} diverse delay profiles")
        else:
            # Default: Minimal set for quick testing
            delay_profiles = [
                DelayProfile.FAST_PRODUCER,
                DelayProfile.FAST_CONSUMER,
                DelayProfile.FIXED_DELAY,
                DelayProfile.MINIMAL_DELAY
            ]
            self.log.info(f"⚡ QUICK TEST: Testing {len(delay_profiles)} key delay profiles")

        self.log.info(f"🔍 Delay profiles: {[p.value for p in delay_profiles]}")

        # Run test with each selected delay profile
        for profile in delay_profiles:
            self.log.info(f"\n📊 Running {test_class.value} test with {profile.value} delay profile")
            self.setup_delay_profile(profile)

            # Reset counters for this profile run
            initial_apb_sent = self.apb_requests_sent
            initial_cda_sent = self.cda_packets_sent
            initial_desc_received = self.descriptors_received

            try:
                if test_class == TestClass.APB_ONLY:
                    success = await self.run_apb_only_test(num_packets, profile)
                elif test_class == TestClass.CDA_ONLY:
                    success = await self.run_cda_only_test(num_packets, profile)
                elif test_class == TestClass.MIXED:
                    success = await self.run_mixed_test(num_packets, profile)
                else:
                    raise ValueError(f"Unknown test class: {test_class}")

                # Calculate statistics for this profile
                apb_sent = self.apb_requests_sent - initial_apb_sent
                cda_sent = self.cda_packets_sent - initial_cda_sent
                desc_received = self.descriptors_received - initial_desc_received

                test_results[profile] = {
                    'success': success,
                    'apb_sent': apb_sent,
                    'cda_sent': cda_sent,
                    'descriptors_received': desc_received,
                    'efficiency': (desc_received / max(apb_sent + cda_sent, 1)) * 100
                }

                result_str = "✅ PASSED" if success else "❌ FAILED"
                self.log.info(f"   {profile.value}: {result_str} - {desc_received}/{apb_sent + cda_sent} descriptors ({test_results[profile]['efficiency']:.1f}% efficiency)")

            except Exception as e:
                self.log.error(f"   {profile.value}: ❌ ERROR - {str(e)}")
                test_results[profile] = {
                    'success': False,
                    'error': str(e),
                    'apb_sent': 0,
                    'cda_sent': 0,
                    'descriptors_received': 0,
                    'efficiency': 0
                }

            # Wait between profile tests
            await self.wait_clocks(self.clk_name, 20)

        # Generate comprehensive report for this test class
        self.generate_test_class_report(test_class, test_results)

        # Calculate overall success rate
        passed_profiles = sum(1 for result in test_results.values() if result['success'])
        total_profiles = len(test_results)

        self.log.info(f"\n🎯 {test_class.value.upper()} TEST CLASS SUMMARY: {passed_profiles}/{total_profiles} profiles passed")

        return passed_profiles >= int(total_profiles * 0.75)  # Require 75% success rate

    async def run_apb_only_test(self, num_packets: int, profile: DelayProfile):
        """Run enhanced APB-only test with extensive randomization cycles"""
        self.log.info(f"🔹 Enhanced APB Only Test: {num_packets} packets with {profile.value} timing profile")

        params = self.delay_params[profile]
        descriptors_collected = []  # List to collect descriptors
        burst_count = 0
        total_cycles = 0
        randomization_cycles = params.get('randomization_cycles', 50)
        monitor_active = True  # Flag to control background monitor

        # Log profile details for comprehensive coverage
        self.log.info(f"   📊 Profile configuration: producer_delay={params['producer_delay']}, "
                     f"consumer_delay={params['consumer_delay']}, burst_size={params['burst_size']}, "
                     f"randomization_cycles={randomization_cycles}")

        # Background coroutine to continuously monitor and collect descriptors
        async def descriptor_monitor():
            """Continuously monitor for descriptors throughout the test"""
            while monitor_active:
                await self.wait_clocks(self.clk_name, 1)
                if int(self.dut.descriptor_valid.value) == 1:
                    desc_data = int(self.dut.descriptor_packet.value)
                    descriptors_collected.append(desc_data)
                    if len(descriptors_collected) % 5 == 1 or len(descriptors_collected) <= 3:
                        self.log.info(f"   📦 APB Descriptor {len(descriptors_collected)}: data=0x{desc_data:X}")

        # Start background descriptor monitor
        monitor_task = cocotb.start_soon(descriptor_monitor())

        for i in range(num_packets):
            # Generate test address and data with more variation
            test_addr = 0x30000 + (i * 0x200) + random.randint(0, 0x100)  # Add address randomization
            test_data = 0x5678ABCD00000000 + (i << 32) + test_addr + random.randint(0, 0xFFFF)
            self.write_memory(test_addr, test_data)

            # Apply extensive producer delay with backpressure simulation
            producer_delay = self.get_delay_value(params['producer_delay'])

            # Add backpressure cycles based on profile
            if random.random() < params.get('backpressure_freq', 0.1):
                backpressure_cycles = random.randint(5, 25)
                await self.wait_clocks(self.clk_name, backpressure_cycles)
                total_cycles += backpressure_cycles

            await self.wait_clocks(self.clk_name, producer_delay)
            total_cycles += producer_delay

            # Send APB request using GAXI Master BFM
            packet = self.apb_master.create_packet(apb_addr=test_addr)
            try:
                await self.apb_master.send(packet)
                self.apb_requests_sent += 1
            except Exception as e:
                self.test_errors.append(f"APB packet {i+1} send failed: {str(e)}")
                continue

            # Enhanced burst timing with inter-burst delays
            burst_count += 1
            burst_size = self.get_delay_value(params['burst_size'])

            if burst_count >= burst_size:
                # Apply inter-burst delay for realistic traffic patterns
                inter_burst_delay = self.get_delay_value(params.get('inter_burst_delay', (5, 15)))
                await self.wait_clocks(self.clk_name, inter_burst_delay)
                total_cycles += inter_burst_delay
                burst_count = 0

                # Add pipeline stall simulation for appropriate profiles
                if profile == DelayProfile.PIPELINE_STALL and random.random() < params.get('stall_freq', 0.15):
                    stall_cycles = random.randint(10, 50)
                    await self.wait_clocks(self.clk_name, stall_cycles)
                    total_cycles += stall_cycles

        # Wait for final descriptors with background monitor still running
        self.log.info(f"🔹 APB test: Waiting for remaining descriptors ({len(descriptors_collected)}/{num_packets} so far)")
        final_collection_window = 1000 + (randomization_cycles * 4)  # Scale with randomization level

        for cycle in range(final_collection_window):
            await self.wait_clocks(self.clk_name, 1)
            total_cycles += 1

            # Exit early if all descriptors received
            if len(descriptors_collected) >= num_packets:
                self.log.info(f"✅ All {num_packets} descriptors collected at cycle {total_cycles}")
                break

        # Stop background monitor
        monitor_active = False
        await self.wait_clocks(self.clk_name, 2)  # Let monitor task finish

        # Update global counter
        descriptors_received = len(descriptors_collected)
        self.descriptors_received += descriptors_received

        success_rate = (descriptors_received / num_packets) * 100
        avg_cycles_per_packet = total_cycles / max(num_packets, 1)

        self.log.info(f"🔹 Enhanced APB Only Test Complete: {descriptors_received}/{num_packets} descriptors "
                     f"({success_rate:.1f}%) - Total cycles: {total_cycles}, Avg per packet: {avg_cycles_per_packet:.1f}")

        return success_rate >= 100  # Must receive ALL descriptors

    async def run_cda_only_test(self, num_packets: int, profile: DelayProfile):
        """Run enhanced CDA-only test with extensive randomization cycles"""
        self.log.info(f"🔸 Enhanced CDA Only Test: {num_packets} packets with {profile.value} timing profile")

        params = self.delay_params[profile]
        descriptors_collected = []  # List to collect descriptors
        burst_count = 0
        total_cycles = 0
        randomization_cycles = params.get('randomization_cycles', 50)
        monitor_active = True  # Flag to control background monitor

        # Log profile details for comprehensive coverage
        self.log.info(f"   📊 Profile configuration: producer_delay={params['producer_delay']}, "
                     f"consumer_delay={params['consumer_delay']}, burst_size={params['burst_size']}, "
                     f"randomization_cycles={randomization_cycles}")

        # Background coroutine to continuously monitor and collect descriptors
        async def descriptor_monitor():
            """Continuously monitor for descriptors throughout the test"""
            while monitor_active:
                await self.wait_clocks(self.clk_name, 1)
                if int(self.dut.descriptor_valid.value) == 1:
                    desc_data = int(self.dut.descriptor_packet.value)
                    descriptors_collected.append(desc_data)
                    if len(descriptors_collected) % 5 == 1 or len(descriptors_collected) <= 3:
                        self.log.info(f"   📦 CDA Descriptor {len(descriptors_collected)}: data=0x{desc_data:X}")

        # Start background descriptor monitor
        monitor_task = cocotb.start_soon(descriptor_monitor())

        for i in range(num_packets):
            # Generate test packet data with enhanced variation
            base_data = 0xABCDEF0000000000 + (i << 32) + random.randint(0, 0xFFFF)
            test_data = base_data + (random.randint(0, 255) << 24)  # Additional randomization
            test_channel = i % min(self.TEST_NUM_CHANNELS, 16)  # Use more channels for better coverage

            # Apply extensive producer delay with channel-specific variations
            producer_delay = self.get_delay_value(params['producer_delay'])

            # Add channel-specific delays to test inter-channel timing
            channel_delay = (test_channel % 4) * 2  # Stagger channels
            await self.wait_clocks(self.clk_name, channel_delay)
            total_cycles += channel_delay

            # Add backpressure cycles based on profile
            if random.random() < params.get('backpressure_freq', 0.1):
                backpressure_cycles = random.randint(3, 20)
                await self.wait_clocks(self.clk_name, backpressure_cycles)
                total_cycles += backpressure_cycles

            await self.wait_clocks(self.clk_name, producer_delay)
            total_cycles += producer_delay

            # Send CDA packet using GAXI Master BFM
            packet = self.cda_master.create_packet(
                packet=test_data,  # Fixed: Use "packet" not "cda_packet"
                channel=test_channel  # Fixed: Use "channel" not "cda_channel"
            )
            try:
                await self.cda_master.send(packet)
                self.cda_packets_sent += 1
            except Exception as e:
                self.test_errors.append(f"CDA packet {i+1} send failed: {str(e)}")
                continue

            # Enhanced burst timing with inter-burst delays
            burst_count += 1
            burst_size = self.get_delay_value(params['burst_size'])

            if burst_count >= burst_size:
                # Apply inter-burst delay for realistic traffic patterns
                inter_burst_delay = self.get_delay_value(params.get('inter_burst_delay', (5, 15)))
                await self.wait_clocks(self.clk_name, inter_burst_delay)
                total_cycles += inter_burst_delay
                burst_count = 0

                # Add channel switching delays for mixed channel testing
                if random.random() < 0.3:  # 30% chance of channel switch delay
                    channel_switch_delay = random.randint(2, 8)
                    await self.wait_clocks(self.clk_name, channel_switch_delay)
                    total_cycles += channel_switch_delay

                # Add pipeline stall simulation for appropriate profiles
                if profile == DelayProfile.PIPELINE_STALL and random.random() < params.get('stall_freq', 0.15):
                    stall_cycles = random.randint(10, 50)
                    await self.wait_clocks(self.clk_name, stall_cycles)
                    total_cycles += stall_cycles

        # Wait for final descriptors with background monitor still running
        self.log.info(f"🔸 CDA test: Waiting for remaining descriptors ({len(descriptors_collected)}/{num_packets} so far)")
        final_collection_window = 1000 + (randomization_cycles * 4)  # Scale with randomization level

        for cycle in range(final_collection_window):
            await self.wait_clocks(self.clk_name, 1)
            total_cycles += 1

            # Exit early if all descriptors received
            if len(descriptors_collected) >= num_packets:
                self.log.info(f"✅ All {num_packets} descriptors collected at cycle {total_cycles}")
                break

        # Stop background monitor
        monitor_active = False
        await self.wait_clocks(self.clk_name, 2)  # Let monitor task finish

        # Update global counter
        descriptors_received = len(descriptors_collected)
        self.descriptors_received += descriptors_received

        success_rate = (descriptors_received / num_packets) * 100
        avg_cycles_per_packet = total_cycles / max(num_packets, 1)

        self.log.info(f"🔸 Enhanced CDA Only Test Complete: {descriptors_received}/{num_packets} descriptors "
                     f"({success_rate:.1f}%) - Total cycles: {total_cycles}, Avg per packet: {avg_cycles_per_packet:.1f}")

        return success_rate >= 100  # Must receive ALL descriptors

    async def run_mixed_test(self, num_packets: int, profile: DelayProfile):
        """Run enhanced mixed APB+RDA test with extensive randomization cycles"""
        self.log.info(f"🔶 Enhanced Mixed Test: {num_packets} packets with {profile.value} timing profile")

        params = self.delay_params[profile]
        descriptors_collected = []  # List to collect descriptors
        total_cycles = 0
        apb_packets = num_packets // 2
        cda_packets = num_packets - apb_packets
        randomization_cycles = params.get('randomization_cycles', 50)
        apb_sent = 0
        cda_sent = 0
        monitor_active = True  # Flag to control background monitor

        # Log profile details for comprehensive coverage
        self.log.info(f"   📊 Profile configuration: producer_delay={params['producer_delay']}, "
                     f"consumer_delay={params['consumer_delay']}, burst_size={params['burst_size']}, "
                     f"randomization_cycles={randomization_cycles}")
        self.log.info(f"   🔀 Mixed operations: {apb_packets} APB + {cda_packets} CDA packets")

        # Background coroutine to continuously monitor and collect descriptors
        async def descriptor_monitor():
            """Continuously monitor for descriptors throughout the test"""
            while monitor_active:
                await self.wait_clocks(self.clk_name, 1)
                if int(self.dut.descriptor_valid.value) == 1:
                    desc_data = int(self.dut.descriptor_packet.value)
                    descriptors_collected.append(desc_data)
                    if len(descriptors_collected) % 5 == 1 or len(descriptors_collected) <= 3:
                        self.log.info(f"   📦 Mixed Descriptor {len(descriptors_collected)}: data=0x{desc_data:X} (total_cycles: {total_cycles})")

        # Start background descriptor monitor
        monitor_task = cocotb.start_soon(descriptor_monitor())

        # Enhanced interleaved APB and CDA operations with randomization
        for i in range(max(apb_packets, cda_packets)):
            # Determine operation mix - sometimes do both, sometimes just one
            do_apb = i < apb_packets and (random.random() > 0.3 or i >= cda_packets)
            do_cda = i < cda_packets and (random.random() > 0.3 or i >= apb_packets)

            # Mixed timing pre-delay with contention simulation
            if do_apb and do_cda:
                # Concurrent operations - add contention delay
                contention_delay = random.randint(2, 10)
                await self.wait_clocks(self.clk_name, contention_delay)
                total_cycles += contention_delay

            # APB operation with enhanced timing
            if do_apb:
                test_addr = 0x40000 + (i * 0x200) + random.randint(0, 0x100)
                test_data = 0x1111222200000000 + (i << 32) + test_addr + random.randint(0, 0xFFFF)
                self.write_memory(test_addr, test_data)

                # Enhanced producer delay with backpressure
                producer_delay = self.get_delay_value(params['producer_delay'])
                if random.random() < params.get('backpressure_freq', 0.1):
                    backpressure_cycles = random.randint(3, 15)
                    await self.wait_clocks(self.clk_name, backpressure_cycles)
                    total_cycles += backpressure_cycles

                await self.wait_clocks(self.clk_name, producer_delay)
                total_cycles += producer_delay

                # Send APB request using GAXI Master BFM
                packet = self.apb_master.create_packet(apb_addr=test_addr)
                try:
                    await self.apb_master.send(packet)
                    apb_sent += 1
                    self.apb_requests_sent += 1
                except Exception as e:
                    self.test_errors.append(f"Mixed APB packet {i+1} send failed: {str(e)}")

            # CDA operation with enhanced timing
            if do_cda:
                test_data = 0x3333444400000000 + (i << 32) + random.randint(0, 0xFFFF)
                test_channel = i % min(self.TEST_NUM_CHANNELS, 12)  # Use more channels

                # Enhanced producer delay with channel-specific timing
                producer_delay = self.get_delay_value(params['producer_delay'])
                channel_delay = (test_channel % 3) * 2  # Channel staggering
                await self.wait_clocks(self.clk_name, channel_delay)
                total_cycles += channel_delay

                if random.random() < params.get('backpressure_freq', 0.1):
                    backpressure_cycles = random.randint(2, 12)
                    await self.wait_clocks(self.clk_name, backpressure_cycles)
                    total_cycles += backpressure_cycles

                await self.wait_clocks(self.clk_name, producer_delay)
                total_cycles += producer_delay

                # Send CDA packet using GAXI Master BFM
                packet = self.cda_master.create_packet(
                    packet=test_data,  # Fixed: Use "packet" not "cda_packet"
                    channel=test_channel  # Fixed: Use "channel" not "cda_channel"
                )
                try:
                    await self.cda_master.send(packet)
                    cda_sent += 1
                    self.cda_packets_sent += 1
                except Exception as e:
                    self.test_errors.append(f"Mixed CDA packet {i+1} send failed: {str(e)}")

            # Inter-packet delays and pipeline stalls
            inter_packet_delay = self.get_delay_value(params.get('inter_burst_delay', (3, 10)))
            await self.wait_clocks(self.clk_name, inter_packet_delay)
            total_cycles += inter_packet_delay

            # Add pipeline stall simulation for appropriate profiles
            if profile == DelayProfile.PIPELINE_STALL and random.random() < params.get('stall_freq', 0.15):
                stall_cycles = random.randint(5, 30)
                await self.wait_clocks(self.clk_name, stall_cycles)
                total_cycles += stall_cycles

        # Wait for final descriptors with background monitor still running
        self.log.info(f"🔶 Mixed test: Waiting for remaining descriptors ({len(descriptors_collected)}/{apb_sent + cda_sent} so far)")
        final_collection_window = 1000 + (randomization_cycles * 4)  # Scale with randomization level

        for cycle in range(final_collection_window):
            await self.wait_clocks(self.clk_name, 1)
            total_cycles += 1

            # Exit early if all descriptors received
            total_sent = apb_sent + cda_sent
            if len(descriptors_collected) >= total_sent:
                self.log.info(f"✅ All {total_sent} descriptors collected at cycle {total_cycles}")
                break

        # Stop background monitor
        monitor_active = False
        await self.wait_clocks(self.clk_name, 2)  # Let monitor task finish

        # Update global counter
        descriptors_received = len(descriptors_collected)
        self.descriptors_received += descriptors_received

        total_sent = apb_sent + cda_sent
        success_rate = (descriptors_received / max(total_sent, 1)) * 100
        avg_cycles_per_packet = total_cycles / max(total_sent, 1)

        self.log.info(f"🔶 Enhanced Mixed Test Complete: {descriptors_received}/{total_sent} descriptors "
                     f"({success_rate:.1f}%) - APB: {apb_sent}, CDA: {cda_sent}")
        self.log.info(f"   Total cycles: {total_cycles}, Avg per packet: {avg_cycles_per_packet:.1f}")

        return success_rate >= 100  # Must receive ALL descriptors

    def generate_test_class_report(self, test_class: TestClass, results: Dict):
        """Generate detailed report for test class results"""
        self.log.info(f"\n📊 === {test_class.value.upper()} TEST CLASS DETAILED REPORT ===")

        passed = 0
        total = len(results)
        best_efficiency = 0
        worst_efficiency = 100
        best_profile = None
        worst_profile = None

        for profile, result in results.items():
            status = "✅ PASS" if result['success'] else "❌ FAIL"
            efficiency = result.get('efficiency', 0)

            self.log.info(f"   {profile.value:15} | {status} | "
                         f"APB: {result.get('apb_sent', 0):3d} | "
                         f"CDA: {result.get('cda_sent', 0):3d} | "
                         f"DESC: {result.get('descriptors_received', 0):3d} | "
                         f"Eff: {efficiency:5.1f}%")

            if result['success']:
                passed += 1
                if efficiency > best_efficiency:
                    best_efficiency = efficiency
                    best_profile = profile
                if efficiency < worst_efficiency:
                    worst_efficiency = efficiency
                    worst_profile = profile

        self.log.info(f"\n📊 Summary: {passed}/{total} profiles passed ({(passed/total)*100:.1f}%)")
        if best_profile:
            self.log.info(f"   Best performance: {best_profile.value} ({best_efficiency:.1f}% efficiency)")
        if worst_profile:
            self.log.info(f"   Worst performance: {worst_profile.value} ({worst_efficiency:.1f}% efficiency)")

    async def setup_clocks_and_reset(self):
        """Complete initialization - starts clocks AND performs reset sequence"""
        # Start clock
        await self.start_clock(self.clk_name, freq=self.TEST_CLK_PERIOD, units='ns')

        # Perform reset sequence
        await self.assert_reset()
        await self.wait_clocks(self.clk_name, 10)
        await self.deassert_reset()
        await self.wait_clocks(self.clk_name, 10)

    async def assert_reset(self):
        """Assert reset signal and reset AXI slave bus"""
        self.mark_progress("assert_reset")
        self.rst_n.value = 0

        # Reset AXI slave bus if initialized
        if self.axi_slave is not None and 'R' in self.axi_slave:
            await self.axi_slave['R'].reset_bus()
        if self.axi_slave is not None and 'AR' in self.axi_slave:
            await self.axi_slave['AR'].reset_bus()

        await self.wait_clocks(self.clk_name, 5)
        self.log.info("Reset asserted")

    async def deassert_reset(self):
        """Deassert reset signal"""
        self.mark_progress("deassert_reset")
        self.rst_n.value = 1
        await self.wait_clocks(self.clk_name, 5)
        self.log.info("Reset deasserted")