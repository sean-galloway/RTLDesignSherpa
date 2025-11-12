# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: SchedulerTB
# Purpose: STREAM Scheduler Testbench - v1.0 (Simplified from RAPIDS)
#
# Documentation: projects/components/stream/PRD.md
# Subsystem: stream
#
# Author: sean galloway
# Created: 2025-10-19

"""
STREAM Scheduler Testbench - v1.0 (Simplified from RAPIDS)

Simplified testbench for STREAM's scheduler - focuses on memory-to-memory DMA.

SIMPLIFICATIONS FROM RAPIDS:
- NO credit management (STREAM uses simple transaction limits)
- NO control engines (ctrlrd/ctrlwr - STREAM has direct APB)
- Simpler FSM (no control sequencing states)
- Memory-to-memory only (no network interfaces)

Features:
- Descriptor acceptance and processing
- Read/write data path coordination
- Descriptor chaining
- Error injection and recovery
- Timeout detection
- FSM state transitions
- Backpressure scenarios
"""

import os
import random
import time
from typing import List, Dict, Any, Tuple, Optional
from enum import Enum
from collections import deque

import cocotb
from cocotb.triggers import RisingEdge, ClockCycles
from cocotb.utils import get_sim_time

# Framework imports (shared infrastructure)
from CocoTBFramework.tbclasses.shared.tbbase import TBBase
from CocoTBFramework.components.gaxi.gaxi_factories import create_gaxi_master
from CocoTBFramework.components.shared.field_config import FieldConfig, FieldDefinition
from CocoTBFramework.components.shared.flex_randomizer import FlexRandomizer


class SchedulerState(Enum):
    """STREAM Scheduler FSM states (from stream_pkg.sv) - ONE-HOT ENCODED

    SIMPLIFIED: No credit management, no control sequencing
    """
    CH_IDLE = 0x01        # 7'b0000001 [0]
    CH_FETCH_DESC = 0x02  # 7'b0000010 [1]
    CH_READ_DATA = 0x04   # 7'b0000100 [2]
    CH_WRITE_DATA = 0x08  # 7'b0001000 [3]
    CH_COMPLETE = 0x10    # 7'b0010000 [4]
    CH_NEXT_DESC = 0x20   # 7'b0100000 [5]
    CH_ERROR = 0x40       # 7'b1000000 [6]


class TestMode(Enum):
    """Test mode definitions"""
    DESCRIPTOR_FLOW = "descriptor_flow"      # Test descriptor processing
    DESCRIPTOR_CHAIN = "descriptor_chain"    # Test chained descriptors
    ERROR_HANDLING = "error_handling"        # Test error detection/recovery
    TIMEOUT = "timeout"                      # Test timeout detection
    STRESS_TEST = "stress_test"              # Stress testing with backpressure


class SchedulerTB(TBBase):
    """
    STREAM Scheduler testbench (simplified from RAPIDS).

    Tests:
    - Descriptor acceptance and processing
    - Read/write data path coordination
    - Descriptor chaining
    - FSM state machine validation
    - Error injection and recovery
    - Timeout detection
    - Backpressure scenarios
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

        # Get test parameters from environment
        self.CHANNEL_ID = self.convert_to_int(os.environ.get('STREAM_CHANNEL_ID', '0'))
        self.NUM_CHANNELS = self.convert_to_int(os.environ.get('STREAM_NUM_CHANNELS', '8'))
        self.ADDR_WIDTH = self.convert_to_int(os.environ.get('STREAM_ADDR_WIDTH', '64'))
        self.DATA_WIDTH = self.convert_to_int(os.environ.get('STREAM_DATA_WIDTH', '512'))
        self.TIMEOUT_CYCLES = self.convert_to_int(os.environ.get('STREAM_TIMEOUT_CYCLES', '1000'))
        self.TEST_CLK_PERIOD = self.convert_to_int(os.environ.get('TEST_CLK_PERIOD', '10'))
        self.SEED = self.convert_to_int(os.environ.get('SEED', '12345'))

        # Initialize random generator
        random.seed(self.SEED)

        # Setup clock and reset signals
        self.clk = clk if clk else dut.clk
        self.clk_name = self.clk._name if hasattr(self.clk, '_name') else 'clk'
        self.rst_n = rst_n if rst_n else dut.rst_n

        # Test configuration
        self.test_config = {
            'enable_stress_tests': self.convert_to_int(os.environ.get('ENABLE_STRESS_TESTS', '1')),
            'enable_error_tests': self.convert_to_int(os.environ.get('ENABLE_ERROR_TESTS', '1')),
            'descriptor_backpressure': self.convert_to_int(os.environ.get('DESCRIPTOR_BACKPRESSURE', '1')),
            'data_engine_backpressure': self.convert_to_int(os.environ.get('DATA_ENGINE_BACKPRESSURE', '1'))
        }

        # Test tracking
        self.descriptors_sent = 0
        self.descriptors_completed = 0
        self.read_completions = 0
        self.write_completions = 0
        self.monitor_packets_received = []
        self.test_errors = []

        # FSM tracking
        self.fsm_state_history = []
        self.current_fsm_state = SchedulerState.CH_IDLE

        # Components (initialized after clock setup)
        self.descriptor_master = None

    async def setup_clocks_and_reset(self):
        """Setup clock and perform reset sequence

        This method should be called first in each test to:
        1. Start the clock
        2. Perform reset sequence
        3. Configure the scheduler
        """
        self.log.info("=== Setting up clocks and reset ===")

        # Start clock at 10ns period (100 MHz)
        await self.start_clock(self.clk_name, freq=10, units='ns')
        self.log.info(f"Clock '{self.clk_name}' started at 10ns period")

        # Perform reset sequence
        await self.assert_reset()
        await self.wait_clocks(self.clk_name, 10)
        await self.deassert_reset()
        await self.wait_clocks(self.clk_name, 10)
        self.log.info("Reset released")

        # Configure scheduler after reset
        await self.configure_scheduler()

        # Initialize GAXI components now that clock is running
        await self.initialize_gaxi_components()

        self.log.info("Clocks and reset setup complete")

    async def assert_reset(self):
        """Assert reset signal (active-low)"""
        self.rst_n.value = 0

    async def deassert_reset(self):
        """Deassert reset signal (active-low)"""
        self.rst_n.value = 1

    async def initialize_gaxi_components(self):
        """Initialize GAXI master for descriptor interface"""
        self.log.info("Initializing GAXI descriptor master...")

        # Descriptor field configuration (256-bit packet)
        descriptor_field_config = FieldConfig()
        descriptor_field_config.add_field(FieldDefinition(
            name='packet',
            bits=256,  # Full descriptor packet
            format='hex',
            description='Descriptor packet data'
        ))

        self.descriptor_master = create_gaxi_master(
            dut=self.dut,
            title="DescriptorMaster",
            prefix="descriptor",
            clock=self.clk,
            field_config=descriptor_field_config,
            log=self.log,
            mode='skid',
            multi_sig=True  # Separate signals for each field
        )
        self.log.info("GAXI Descriptor Master initialized successfully")

    async def initialize_test(self):
        """Initialize test components and interfaces

        This method starts background monitors and should be called
        after setup_clocks_and_reset() in each test.
        """
        self.log.info("=== Initializing Scheduler Test ===")

        try:
            # Start background monitors
            cocotb.start_soon(self.monitor_fsm_states())
            cocotb.start_soon(self.monitor_monitor_bus())

            # Start data path responders
            cocotb.start_soon(self.simulate_read_engine())
            cocotb.start_soon(self.simulate_write_engine())

            self.log.info("Background monitors and responders started")

        except Exception as e:
            self.log.error(f"Initialization failed: {str(e)}")
            raise

    async def configure_scheduler(self):
        """Configure the scheduler for testing"""
        self.log.info("Configuring scheduler...")

        # Configuration interface
        self.dut.cfg_channel_enable.value = 1
        self.dut.cfg_channel_reset.value = 0

        # Data engine interfaces (ready by default)
        self.dut.datard_ready.value = 1
        self.dut.datard_done_strobe.value = 0
        self.dut.datard_beats_done.value = 0
        self.dut.datard_error.value = 0

        self.dut.datawr_ready.value = 1
        self.dut.datawr_done_strobe.value = 0
        self.dut.datawr_beats_done.value = 0
        self.dut.datawr_error.value = 0

        # Monitor bus interface
        self.dut.mon_ready.value = 1

        await self.wait_clocks(self.clk_name, 5)
        self.log.info("Scheduler configured and signals initialized")

    def create_descriptor(self, src_addr=0x1000, dst_addr=0x2000, length=0x100,
                         next_desc_ptr=0x0, last=True, gen_irq=False):
        """Create a STREAM descriptor packet (256-bit)

        Args:
            src_addr: Source address (64-bit, must be aligned)
            dst_addr: Destination address (64-bit, must be aligned)
            length: Transfer length in BEATS (not bytes!)
            next_desc_ptr: Next descriptor address (0 = last)
            last: Last descriptor flag
            gen_irq: Generate interrupt on completion

        Returns:
            256-bit descriptor packet value
        """
        descriptor = 0

        # [63:0] - Source address
        descriptor |= (src_addr & 0xFFFFFFFFFFFFFFFF) << 0

        # [127:64] - Destination address
        descriptor |= (dst_addr & 0xFFFFFFFFFFFFFFFF) << 64

        # [159:128] - Length in BEATS
        descriptor |= (length & 0xFFFFFFFF) << 128

        # [191:160] - Next descriptor pointer
        descriptor |= (next_desc_ptr & 0xFFFFFFFF) << 160

        # [255:192] - Control bits
        valid = 1
        error = 0
        channel_id = self.CHANNEL_ID
        priority = 0
        control = (valid << 0) | (gen_irq << 1) | (last << 2) | (error << 3) | \
                 (channel_id << 4) | (priority << 8)
        descriptor |= (control & 0xFFFFFFFFFFFFFFFF) << 192

        return descriptor

    async def send_descriptor(self, descriptor_data):
        """Send a descriptor to the scheduler using GAXI Master BFM

        Args:
            descriptor_data: 256-bit descriptor value

        Returns:
            True if successful, False otherwise
        """
        self.log.info(f"📤 Sending descriptor: length=0x{(descriptor_data >> 128) & 0xFFFFFFFF:x}")

        # Create packet with descriptor data
        packet = self.descriptor_master.create_packet(packet=descriptor_data)

        # Send using GAXI Master BFM
        try:
            await self.descriptor_master.send(packet)
            self.descriptors_sent += 1
            return True
        except Exception as e:
            self.log.error(f"Failed to send descriptor: {str(e)}")
            self.test_errors.append("descriptor_send_failed")
            return False

    async def wait_for_idle(self, timeout_cycles=500):
        """Wait for scheduler to return to idle state

        Args:
            timeout_cycles: Maximum cycles to wait

        Returns:
            True if scheduler returned to idle, False if timeout or error
        """
        for _ in range(timeout_cycles):
            await self.wait_clocks(self.clk_name, 1)
            if int(self.dut.scheduler_idle.value) == 1:
                return True
            # Check for ERROR state
            if int(self.dut.scheduler_state.value) == SchedulerState.CH_ERROR.value:
                fsm_state = int(self.dut.scheduler_state.value)
                self.log.error(f"Scheduler entered ERROR state (0x{fsm_state:02x})")
                return False

        fsm_state = int(self.dut.scheduler_state.value)
        self.log.warning(f"Timeout waiting for idle. State: 0x{fsm_state:02x}")
        return False

    async def monitor_fsm_states(self):
        """Monitor and log FSM state changes"""
        last_state = 0

        self.log.info("🔍 FSM state monitor STARTED")

        while True:
            await self.wait_clocks(self.clk_name, 1)
            current_state = int(self.dut.scheduler_state.value)

            if current_state != last_state:
                try:
                    state_enum = SchedulerState(current_state)
                    self.current_fsm_state = state_enum
                    self.fsm_state_history.append((get_sim_time('ns'), state_enum))

                    self.log.info(f"🔍 FSM: {SchedulerState(last_state).name} → {state_enum.name} (0x{current_state:02x})")
                except ValueError:
                    self.log.warning(f"Unknown FSM state: 0x{current_state:02x}")

                last_state = current_state

    async def simulate_read_engine(self):
        """Simulate read engine behavior - completes reads with minimal delay"""
        while True:
            await self.wait_clocks(self.clk_name, 1)

            # Check if read request is active
            if int(self.dut.datard_valid.value) == 1 and int(self.dut.datard_ready.value) == 1:
                # Read request accepted
                beats_remaining = int(self.dut.datard_beats_remaining.value)
                self.log.info(f"📖 Read engine: Processing {beats_remaining} beats")

                # Simulate read processing time
                await self.wait_clocks(self.clk_name, random.randint(5, 15))

                # Complete read (all beats in one go for simple tests)
                self.dut.datard_done_strobe.value = 1
                self.dut.datard_beats_done.value = beats_remaining
                await self.wait_clocks(self.clk_name, 1)
                self.dut.datard_done_strobe.value = 0
                self.dut.datard_beats_done.value = 0

                self.read_completions += 1
                self.log.info(f"✅ Read engine: Completed {beats_remaining} beats")

    async def simulate_write_engine(self):
        """Simulate write engine behavior - completes writes with minimal delay"""
        while True:
            await self.wait_clocks(self.clk_name, 1)

            # Check if write request is active
            if int(self.dut.datawr_valid.value) == 1 and int(self.dut.datawr_ready.value) == 1:
                # Write request accepted
                beats_remaining = int(self.dut.datawr_beats_remaining.value)
                self.log.info(f"✍️  Write engine: Processing {beats_remaining} beats")

                # Simulate write processing time
                await self.wait_clocks(self.clk_name, random.randint(5, 15))

                # Complete write (all beats in one go for simple tests)
                self.dut.datawr_done_strobe.value = 1
                self.dut.datawr_beats_done.value = beats_remaining
                await self.wait_clocks(self.clk_name, 1)
                self.dut.datawr_done_strobe.value = 0
                self.dut.datawr_beats_done.value = 0

                self.write_completions += 1
                self.log.info(f"✅ Write engine: Completed {beats_remaining} beats")

    async def monitor_monitor_bus(self):
        """Monitor the monitor bus for events"""
        while True:
            await self.wait_clocks(self.clk_name, 1)

            if int(self.dut.mon_valid.value) == 1 and int(self.dut.mon_ready.value) == 1:
                packet = int(self.dut.mon_packet.value)
                self.monitor_packets_received.append(packet)

    # =========================================================================
    # TEST CASES - Descriptor Processing
    # =========================================================================

    async def test_basic_descriptor_flow(self, num_descriptors=5):
        """Test basic descriptor processing flow"""
        self.log.info(f"=== Testing Basic Descriptor Flow: {num_descriptors} descriptors ===")

        completed = 0

        for i in range(num_descriptors):
            descriptor = self.create_descriptor(
                src_addr=0x10000 + i*0x1000,
                dst_addr=0x20000 + i*0x1000,
                length=0x100 + i*0x10,
                last=True
            )

            success = await self.send_descriptor(descriptor)
            if not success:
                self.test_errors.append(f"Failed to send descriptor {i+1}")
                continue

            idle = await self.wait_for_idle(timeout_cycles=300)
            if idle:
                completed += 1

        success_rate = (completed / num_descriptors) * 100
        self.log.info(f"Basic flow test: {completed}/{num_descriptors} completed ({success_rate:.1f}%)")

        return completed == num_descriptors

    async def test_descriptor_chaining(self, chain_length=3):
        """Test sequential descriptor processing (NOT true chaining - that's integration test)

        NOTE: This tests the scheduler's ability to process multiple independent
        descriptors sequentially. True autonomous descriptor chaining (where the
        descriptor engine follows next_descriptor_ptr) is tested at integration level.

        For FUB-level scheduler test, we mark all descriptors as independent (last=True).
        """
        self.log.info(f"=== Testing Sequential Descriptor Processing: {chain_length} descriptors ===")

        completed = 0

        # Send independent descriptors (all marked as last)
        for i in range(chain_length):
            descriptor = self.create_descriptor(
                src_addr=0x30000 + i*0x1000,
                dst_addr=0x40000 + i*0x1000,
                length=0x80,
                next_desc_ptr=0x0,    # Not chained
                last=True              # Each is independent
            )

            self.log.info(f"Sending descriptor {i+1}/{chain_length}")
            success = await self.send_descriptor(descriptor)
            if not success:
                self.log.error(f"Failed to send descriptor {i+1}")
                return False

            # Wait for this descriptor to complete
            idle = await self.wait_for_idle(timeout_cycles=300)
            if idle:
                completed += 1
                self.log.info(f"  ✅ Descriptor {i+1} completed")
            else:
                self.log.error(f"  ❌ Descriptor {i+1} timeout")
                return False

        if completed == chain_length:
            self.log.info(f"✅ Sequential descriptor test passed: {chain_length}/{chain_length} completed")
            return True
        else:
            self.log.error(f"❌ Sequential descriptor test failed: {completed}/{chain_length} completed")
            return False

    # =========================================================================
    # TEST CASES - Error Handling
    # =========================================================================

    async def test_descriptor_error(self):
        """Test descriptor error handling"""
        self.log.info("=== Testing Descriptor Error Handling ===")

        # Send descriptor with error flag set
        descriptor = 0x0  # Invalid descriptor (valid bit = 0)

        await self.send_descriptor(descriptor)
        await self.wait_clocks(self.clk_name, 20)

        # Check if ERROR state was visited
        error_state_seen = any(state == SchedulerState.CH_ERROR for _, state in self.fsm_state_history)

        if error_state_seen:
            self.log.info("  ✅ Scheduler entered ERROR state on invalid descriptor")
            return True
        else:
            self.log.warning("  ⚠️  Scheduler did not enter ERROR state")
            return False

    async def test_read_engine_error(self):
        """Test read engine error handling"""
        self.log.info("=== Testing Read Engine Error ===")

        descriptor = self.create_descriptor(
            src_addr=0x50000,
            dst_addr=0x60000,
            length=0x100
        )
        await self.send_descriptor(descriptor)

        # Inject read error after some delay
        await self.wait_clocks(self.clk_name, 30)
        self.dut.datard_error.value = 1
        await self.wait_clocks(self.clk_name, 5)
        self.dut.datard_error.value = 0

        # Check ERROR state
        await self.wait_clocks(self.clk_name, 10)
        fsm_state = int(self.dut.scheduler_state.value)

        if fsm_state == SchedulerState.CH_ERROR.value:
            self.log.info("  ✅ Scheduler detected read engine error")
            return True
        else:
            self.log.warning("  ⚠️  Scheduler did not detect read engine error")
            return False

    async def test_timeout_detection(self):
        """Test timeout detection"""
        self.log.info("=== Testing Timeout Detection ===")

        # CRITICAL: Force backpressure BEFORE sending descriptor
        # This prevents the read engine mock from completing before we can test timeout
        self.log.info("  Setting datard_ready=0 BEFORE sending descriptor")
        self.dut.datard_ready.value = 0
        await self.wait_clocks(self.clk_name, 2)

        # Send descriptor
        descriptor = self.create_descriptor(
            src_addr=0x70000,
            dst_addr=0x80000,
            length=0x100
        )
        await self.send_descriptor(descriptor)

        # Wait for read request to start
        timeout_wait = 0
        while int(self.dut.datard_valid.value) != 1 and timeout_wait < 50:
            await self.wait_clocks(self.clk_name, 1)
            timeout_wait += 1

        if timeout_wait >= 50:
            self.log.error("  ❌ Scheduler never asserted datard_valid")
            self.dut.datard_ready.value = 1  # Restore before returning
            return False

        self.log.info(f"  ✅ Read request started after {timeout_wait} cycles (with ready=0)")

        # Continue backpressure for TIMEOUT_CYCLES
        self.log.info(f"  Applying backpressure for {self.TIMEOUT_CYCLES + 10} cycles to trigger timeout")
        error_detected = False
        for cycle in range(self.TIMEOUT_CYCLES + 10):
            await self.wait_clocks(self.clk_name, 1)

            # Check if ERROR state reached (scheduler auto-recovers, so must check during backpressure)
            fsm_state = int(self.dut.scheduler_state.value)
            if fsm_state == SchedulerState.CH_ERROR.value:
                error_detected = True
                self.log.info(f"  ✅ Timeout detected at cycle {cycle} - ERROR state reached!")
                break

        # Restore ready (cleanup)
        self.log.info("  Restoring datard_ready=1")
        self.dut.datard_ready.value = 1
        await self.wait_clocks(self.clk_name, 5)

        if error_detected:
            self.log.info("  ✅ Timeout detection test passed")
            return True
        else:
            fsm_state = int(self.dut.scheduler_state.value)
            self.log.error(f"  ❌ Timeout not detected - final state=0x{fsm_state:02x}")
            self.log.error(f"  Note: Scheduler may have completed before timeout threshold")
            return False

    async def test_irq_generation(self, num_descriptors=3):
        """Test IRQ generation via MonBus

        Send descriptors with gen_irq flag and verify STREAM_EVENT_IRQ appears on MonBus.
        """
        self.log.info("=== Testing IRQ Generation via MonBus ===")

        # STREAM_EVENT_IRQ = 0x7 (from stream_pkg.sv)
        STREAM_EVENT_IRQ = 0x7
        STREAM_EVENT_DESC_COMPLETE = 0x1

        # Clear monitor packets
        self.monitor_packets_received.clear()
        irq_count = 0
        non_irq_count = 0

        for i in range(num_descriptors):
            # Alternate: IRQ on odd descriptors, no IRQ on even
            gen_irq = (i % 2 == 1)

            descriptor = self.create_descriptor(
                src_addr=0x10000 + i*0x1000,
                dst_addr=0x20000 + i*0x1000,
                length=0x100 + i*0x10,
                last=True,
                gen_irq=gen_irq
            )

            self.log.info(f"Descriptor {i}: gen_irq={gen_irq}, descriptor=0x{descriptor:064X}")
            await self.send_descriptor(descriptor)

            # Wait for completion
            await self.wait_for_idle(timeout_cycles=500)

        # Wait for any final monitor packets
        await self.wait_clocks(self.clk_name, 20)

        # Analyze MonBus packets
        self.log.info(f"\nAnalyzing {len(self.monitor_packets_received)} MonBus packets:")

        for idx, packet in enumerate(self.monitor_packets_received):
            # Extract fields from MonBus packet format:
            # {packet_type[3:0], protocol[2:0], event_code[3:0], channel_id[5:0], unit_id[3:0], agent_id[7:0], event_data[34:0]}
            # [63:60] packet_type (4 bits)
            # [59:57] protocol (3 bits) ← NOTE: 3 bits, not 2!
            # [56:53] event_code (4 bits)
            # [52:47] channel_id (6 bits)
            # [46:43] unit_id (4 bits)
            # [42:35] agent_id (8 bits)
            # [34:0] event_data (35 bits)
            packet_type = (packet >> 60) & 0xF
            protocol = (packet >> 57) & 0x7      # Bits [59:57] - 3 bits!
            event_code = (packet >> 53) & 0xF    # Bits [56:53]
            channel_id = (packet >> 47) & 0x3F   # Bits [52:47]
            unit_id = (packet >> 43) & 0xF       # Bits [46:43]
            agent_id = (packet >> 35) & 0xFF     # Bits [42:35]
            event_data = packet & 0x7FFFFFFFF    # Bits [34:0] - 35 bits!

            # Log all packets for debugging
            self.log.info(f"  Packet {idx}: event_code=0x{event_code:X}, channel={channel_id}, payload=0x{event_data:08X}, full=0x{packet:016X}")

            if event_code == STREAM_EVENT_IRQ:
                irq_count += 1
                self.log.info(f"    → IRQ event (0x7) - channel={channel_id}, length={event_data}")
            elif event_code == STREAM_EVENT_DESC_COMPLETE:
                non_irq_count += 1
                self.log.info(f"    → Completion event (0x1) - no IRQ")

        # Verify results
        # For (i % 2 == 1) pattern: descriptors 1, 3, 5, ... have IRQ
        expected_irq = sum(1 for i in range(num_descriptors) if i % 2 == 1)
        expected_non_irq = sum(1 for i in range(num_descriptors) if i % 2 == 0)

        self.log.info(f"\nResults:")
        self.log.info(f"  IRQ events:        {irq_count} (expected {expected_irq})")
        self.log.info(f"  Non-IRQ events:    {non_irq_count} (expected {expected_non_irq})")

        if irq_count == expected_irq and non_irq_count == expected_non_irq:
            self.log.info("  ✅ IRQ generation test PASSED")
            return True
        else:
            self.log.error("  ❌ IRQ generation test FAILED - event count mismatch")
            self.test_errors.append(f"IRQ events: got {irq_count}, expected {expected_irq}")
            self.test_errors.append(f"Non-IRQ events: got {non_irq_count}, expected {expected_non_irq}")
            return False

    # =========================================================================
    # Utility Methods
    # =========================================================================

    def generate_test_report(self):
        """Generate comprehensive test report"""
        self.log.info("\n" + "="*70)
        self.log.info("=== STREAM SCHEDULER TEST REPORT ===")
        self.log.info("="*70)
        self.log.info(f"Descriptors sent: {self.descriptors_sent}")
        self.log.info(f"Descriptors completed: {self.descriptors_completed}")
        self.log.info(f"Read completions: {self.read_completions}")
        self.log.info(f"Write completions: {self.write_completions}")
        self.log.info(f"Monitor packets: {len(self.monitor_packets_received)}")
        self.log.info(f"FSM state transitions: {len(self.fsm_state_history)}")

        if self.test_errors:
            self.log.error(f"\nTest errors ({len(self.test_errors)}):")
            for error in self.test_errors:
                self.log.error(f"  - {error}")
            self.log.info("\n" + "="*70)
            return False
        else:
            self.log.info("\n✅ ALL TESTS PASSED SUCCESSFULLY!")
            self.log.info("="*70)
            return True
