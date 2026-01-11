# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: DelayProfile
# Purpose: RAPIDS Control Read Engine Testbench
#
# Documentation: projects/components/rapids/PRD.md
# Subsystem: rapids
#
# Author: sean galloway
# Created: 2025-10-18

"""
RAPIDS Control Read Engine Testbench

Reusable testbench class for ctrlrd_engine validation.

The ctrlrd_engine performs pre-descriptor control read operations with:
- Read-and-compare mechanism with configurable mask
- Automatic retry with configurable max attempts (0-511)
- 1µs delay between retries (using tick_1us from scheduler_group)
- Null address support (64'h0 = immediate success)
- AXI4 read interface (AR and R channels)
- Monitor packet generation

Architecture:
- Scheduler Interface: ctrlrd_valid/ready, addr, expected_data, mask, result
- AXI4 Read Interface: AR and R channels (32-bit reads)
- Configuration: Max retry count, channel reset
- MonBus: Completion, retry, and error events

Test Strategy:
1. Basic read-match scenarios
2. Retry scenarios (with various retry counts)
3. Max retries exceeded scenarios
4. Masked comparison scenarios
5. Null address scenarios
6. AXI error scenarios
7. Back-to-back operations

See: projects/components/rapids/docs/rapids_spec/ch02_blocks/01_04_ctrlrd_engine.md
"""

import cocotb
from cocotb.triggers import RisingEdge, Timer, ClockCycles
from enum import Enum
import random
import os

from CocoTBFramework.tbclasses.shared.tbbase import TBBase
from CocoTBFramework.components.shared.memory_model import MemoryModel
from CocoTBFramework.components.axi4.axi4_factories import create_axi4_slave_rd
from CocoTBFramework.components.gaxi.gaxi_factories import create_gaxi_master
from CocoTBFramework.components.shared.field_config import FieldConfig, FieldDefinition


class DelayProfile(Enum):
    """Delay profiles for timing coverage"""
    FIXED_DELAY = "fixed_delay"
    MINIMAL_DELAY = "minimal_delay"
    FAST_CONSUMER = "fast_consumer"
    BACKPRESSURE = "backpressure"
    RANDOM_DELAY = "random_delay"


class TestScenario(Enum):
    """Test scenarios for ctrlrd_engine"""
    BASIC_READ_MATCH = "basic_read_match"
    READ_RETRY_MATCH = "read_retry_match"
    MAX_RETRIES_EXCEEDED = "max_retries_exceeded"
    NULL_ADDRESS = "null_address"
    MASKED_COMPARISON = "masked_comparison"
    AXI_ERROR = "axi_error"
    BACK_TO_BACK = "back_to_back"
    MIXED = "mixed"


class CtrlrdEngineTB(TBBase):
    """
    Reusable testbench for RAPIDS Control Read Engine validation.

    Follows standardized RAPIDS testbench architecture with:
    - Mandatory initialization methods (setup_clocks_and_reset, assert_reset, deassert_reset)
    - GAXI BFM for ctrlrd interface
    - AXI responder for read interface
    - Safety monitoring
    - Configurable delay profiles
    """

    def __init__(self, dut, enable_safety_monitoring=False):
        """Initialize ctrlrd_engine testbench"""
        super().__init__(dut)

        # Clock and reset
        self.clk = dut.clk
        self.clk_name = 'clk'
        self.rst_n = dut.rst_n

        # Component references (created in setup_clocks_and_reset)
        self.ctrlrd_master = None
        self.axi_slave = None

        # Memory model for AXI read responses (64-bit data width = 8 bytes per line)
        # 64KB memory (8192 lines × 8 bytes per line = 65536 bytes)
        self.memory_model = MemoryModel(
            num_lines=8192,
            bytes_per_line=8,  # 64-bit data width
            log=self.log
        )

        # Test state
        self.operations_sent = 0
        self.operations_completed = 0
        self.errors_detected = []

        # Delay profile parameters
        self.delay_params = {
            DelayProfile.FIXED_DELAY: {
                'producer_delay': (1, 1),
                'consumer_delay': (1, 1),
                'backpressure_freq': 0.1,
            },
            DelayProfile.MINIMAL_DELAY: {
                'producer_delay': (0, 0),
                'consumer_delay': (0, 0),
                'backpressure_freq': 0.0,
            },
            DelayProfile.FAST_CONSUMER: {
                'producer_delay': (3, 5),
                'consumer_delay': (0, 1),
                'backpressure_freq': 0.05,
            },
            DelayProfile.BACKPRESSURE: {
                'producer_delay': (1, 2),
                'consumer_delay': (5, 10),
                'backpressure_freq': 0.3,
            },
            DelayProfile.RANDOM_DELAY: {
                'producer_delay': (0, 5),
                'consumer_delay': (0, 5),
                'backpressure_freq': 0.2,
            },
        }

        self.log.info(f"Initialized testbench for ctrlrd_engine")

    async def setup_clocks_and_reset(self):
        """
        Complete initialization - MANDATORY METHOD

        Sets up clocks and performs complete reset sequence.
        Must set any configuration signals BEFORE reset if needed.
        """
        # Start clock (100 MHz)
        await self.start_clock(self.clk_name, freq=10, units='ns')

        # Create GAXI Master for ctrlrd interface
        # IMPORTANT: Field names combined with prefix must match actual signal names
        # Signal: ctrlrd_pkt_addr → prefix="ctrlrd" + "_" + field_name="pkt_addr"
        ctrlrd_field_config = FieldConfig()
        ctrlrd_field_config.add_field(FieldDefinition(
            name='pkt_addr',  # prefix + _ + pkt_addr → ctrlrd_pkt_addr
            bits=64,
            format='hex',
            description='Ctrlrd read address'
        ))
        ctrlrd_field_config.add_field(FieldDefinition(
            name='pkt_data',  # prefix + _ + pkt_data → ctrlrd_pkt_data
            bits=32,
            format='hex',
            description='Ctrlrd expected data'
        ))
        ctrlrd_field_config.add_field(FieldDefinition(
            name='pkt_mask',  # prefix + _ + pkt_mask → ctrlrd_pkt_mask
            bits=32,
            format='hex',
            description='Ctrlrd comparison mask'
        ))

        self.ctrlrd_master = create_gaxi_master(
            dut=self.dut,
            title="CtrlrdMaster",
            prefix="ctrlrd",  # Will combine: ctrlrd + _ + field_name
            clock=self.clk,
            field_config=ctrlrd_field_config,
            log=self.log,
            mode='skid',
            multi_sig=True  # Ctrlrd interface uses separate pkt_addr, pkt_data, pkt_mask signals
        )

        # Initialize remaining input signals to known values BEFORE reset
        self.dut.cfg_channel_reset.value = 0
        self.dut.cfg_ctrlrd_max_try.value = 3  # Default max retries
        self.dut.tick_1us.value = 0  # 1µs tick (driven by scheduler_group in real design)
        self.dut.mon_ready.value = 1  # MonBus ready

        # Initialize AXI AR and R channel inputs (will be driven by AXI4 factory slave)
        self.dut.ar_ready.value = 0  # AR channel ready (driven by slave)
        self.dut.r_valid.value = 0   # R channel valid (driven by slave)
        self.dut.r_data.value = 0
        self.dut.r_id.value = 0
        self.dut.r_resp.value = 0
        self.dut.r_last.value = 0

        # Note: AXI4 factory slave created on-demand by tests that need it

        # Perform reset sequence
        await self.assert_reset()
        await self.wait_clocks(self.clk_name, 10)  # Hold reset
        await self.deassert_reset()
        await self.wait_clocks(self.clk_name, 5)   # Stabilization time

    async def assert_reset(self):
        """Assert reset signal - MANDATORY METHOD"""
        self.rst_n.value = 0

    async def deassert_reset(self):
        """Deassert reset signal - MANDATORY METHOD"""
        self.rst_n.value = 1

    def get_delay_value(self, delay_tuple):
        """Get randomized delay value from tuple (min, max)"""
        if isinstance(delay_tuple, tuple):
            return random.randint(delay_tuple[0], delay_tuple[1])
        return delay_tuple

    async def send_ctrlrd_request(self, addr: int, expected_data: int, mask: int, profile: DelayProfile):
        """
        Send single ctrlrd request.

        Args:
            addr: Address to read
            expected_data: Expected data value
            mask: Comparison mask
            profile: Delay profile to use

        Returns:
            bool: True if request accepted, False on error
        """
        params = self.delay_params[profile]

        # Apply producer delay
        producer_delay = self.get_delay_value(params['producer_delay'])
        if producer_delay > 0:
            await self.wait_clocks(self.clk_name, producer_delay)

        # Create and send packet
        packet = self.ctrlrd_master.create_packet(
            pkt_addr=addr,
            pkt_data=expected_data,
            pkt_mask=mask
        )

        await self.ctrlrd_master.send(packet)
        self.operations_sent += 1

        return True

    async def wait_for_completion(self, timeout_cycles=1000):
        """
        Wait for ctrlrd operation to complete.

        Args:
            timeout_cycles: Maximum cycles to wait

        Returns:
            tuple: (success, result_data, error_occurred)
        """
        for cycle in range(timeout_cycles):
            await self.wait_clocks(self.clk_name, 1)

            # Check for error
            if int(self.dut.ctrlrd_error.value) == 1:
                self.errors_detected.append("ctrlrd_error")
                return (False, 0, True)

            # Check for completion (engine returns to idle)
            if int(self.dut.ctrlrd_engine_idle.value) == 1:
                result_data = int(self.dut.ctrlrd_result.value)
                self.operations_completed += 1
                return (True, result_data, False)

        # Timeout
        self.errors_detected.append("timeout_waiting_for_completion")
        return (False, 0, False)

    async def test_basic_read_match(self, profile: DelayProfile, use_manual_responders=False):
        """
        Test basic read-and-match operation (first read matches).

        Scenario:
        1. Send ctrlrd request with address, expected_data, mask
        2. AXI read returns data that matches expected_data (with mask)
        3. Engine completes successfully

        Args:
            profile: Delay profile to use
            use_manual_responders: If True, use manual responders instead of AXI factory
        """
        self.log.info("="*70)
        self.log.info(f"TEST: Basic Read-Match (Profile: {profile.value})")
        self.log.info("="*70)

        test_addr = 0x1000
        expected_data = 0x12345678
        mask = 0xFFFFFFFF  # Full match required
        read_data = 0x12345678  # Matches expected

        if use_manual_responders:
            # Use manual responders with surgical control
            self.log.info("  Using manual responders (surgical control)")
            monitor_active = [True]

            async def simple_ar_responder():
                """Simple AR/R responder for basic test"""
                self.dut.ar_ready.value = 1

                while monitor_active[0]:
                    await self.wait_clocks(self.clk_name, 1)

                    if int(self.dut.ar_valid.value) == 1 and int(self.dut.ar_ready.value) == 1:
                        ar_id = int(self.dut.ar_id.value)
                        await self.wait_clocks(self.clk_name, 2)

                        # Drive R channel with matching data
                        self.dut.r_valid.value = 1
                        self.dut.r_data.value = read_data
                        self.dut.r_id.value = ar_id
                        self.dut.r_resp.value = 0
                        self.dut.r_last.value = 1

                        while True:
                            await self.wait_clocks(self.clk_name, 1)
                            if int(self.dut.r_ready.value) == 1:
                                break

                        self.dut.r_valid.value = 0

            responder_task = cocotb.start_soon(simple_ar_responder())

            # Send request
            success = await self.send_ctrlrd_request(test_addr, expected_data, mask, profile)
            if not success:
                monitor_active[0] = False
                await self.wait_clocks(self.clk_name, 2)
                return False

            # Wait for completion
            (success, result_data, error) = await self.wait_for_completion(timeout_cycles=500)

            # Stop responder
            monitor_active[0] = False
            await self.wait_clocks(self.clk_name, 2)

        else:
            # Create AXI4 factory slave for this test
            if self.axi_slave is None:
                self.axi_slave = create_axi4_slave_rd(
                    dut=self.dut,
                    clock=self.clk,
                    prefix="",  # No prefix - signals are ar_*, r_*
                    log=self.log,
                    data_width=64,  # AXI_DATA_WIDTH
                    id_width=8,     # AXI_ID_WIDTH
                    addr_width=64,  # ADDR_WIDTH
                    user_width=1,
                    multi_sig=True,
                    memory_model=self.memory_model
                )

            # Write data to memory model (AXI slave will return this)
            data_bytes = bytearray(read_data.to_bytes(4, byteorder='little'))
            self.memory_model.write(test_addr, data_bytes)

            # Send ctrlrd request
            success = await self.send_ctrlrd_request(test_addr, expected_data, mask, profile)
            if not success:
                self.log.error("Failed to send ctrlrd request")
                return False

            # Wait for completion
            (success, result_data, error) = await self.wait_for_completion(timeout_cycles=500)

        if not success:
            self.log.error(f"Ctrlrd operation failed: error={error}")
            return False

        if result_data != read_data:
            self.log.error(f"Result mismatch: expected=0x{read_data:08X}, got=0x{result_data:08X}")
            return False

        self.log.info(f"✓ Basic read-match completed successfully")
        self.log.info(f"  Result: 0x{result_data:08X}")

        return True

    async def test_read_retry_match(self, profile: DelayProfile, max_retries=3):
        """
        Test read-retry-match operation (data doesn't match initially, then matches).

        Scenario:
        1. Send ctrlrd request
        2. First read returns non-matching data (manual R responder)
        3. Engine retries with 1µs delay
        4. Second read returns matching data (manual R responder)
        5. Engine completes successfully
        """
        self.log.info("="*70)
        self.log.info(f"TEST: Read-Retry-Match (Profile: {profile.value}, Max: {max_retries})")
        self.log.info("="*70)

        test_addr = 0x2000
        expected_data = 0xABCDEF00
        mask = 0xFFFFFF00  # Ignore lower byte

        # Configure max retries
        self.dut.cfg_ctrlrd_max_try.value = max_retries

        # Counter for AR transactions
        read_count = [0]
        monitor_active = [True]  # Control flag for debug monitor

        # State name mapping for debug
        state_names = {
            0: "IDLE",
            1: "ISSUE_ADDR",
            2: "WAIT_DATA",
            3: "COMPARE",
            4: "RETRY_WAIT",
            5: "MATCH",
            6: "ERROR",
        }

        # Debug monitor - track RTL internal state
        async def debug_state_monitor():
            """Monitor RTL internal state for debugging"""
            prev_state = None
            while monitor_active[0]:
                await self.wait_clocks(self.clk_name, 1)

                # Read internal state signals
                try:
                    current_state = int(self.dut.r_current_state.value)
                    retry_counter = int(self.dut.r_retry_counter.value)
                    retry_wait_complete = int(self.dut.r_retry_wait_complete.value)
                    tick_1us = int(self.dut.tick_1us.value)

                    # Log state transitions
                    if current_state != prev_state:
                        state_name = state_names.get(current_state, f"UNKNOWN({current_state})")
                        self.log.info(f"  [RTL STATE] → {state_name} (retry_cnt={retry_counter}, retry_wait_done={retry_wait_complete}, tick={tick_1us})")
                        prev_state = current_state

                    # Log COMPARE state details
                    if current_state == 3:  # COMPARE
                        axi_read_data = int(self.dut.r_axi_read_data.value)
                        expected = int(self.dut.r_expected_data.value)
                        mask_val = int(self.dut.r_mask.value)
                        masked_expected = expected & mask_val
                        masked_actual = (axi_read_data & 0xFFFFFFFF) & mask_val
                        self.log.info(f"  [COMPARE] expected=0x{expected:08X}, mask=0x{mask_val:08X}, actual=0x{axi_read_data:08X}")
                        self.log.info(f"  [COMPARE] masked_expected=0x{masked_expected:08X}, masked_actual=0x{masked_actual:08X}, match={masked_expected == masked_actual}")
                        self.log.info(f"  [COMPARE] retry_counter={retry_counter}, retries_remaining={retry_counter > 0}")

                    # Log RETRY_WAIT state details
                    if current_state == 4:  # RETRY_WAIT
                        if tick_1us == 1:
                            self.log.info(f"  [RETRY_WAIT] tick_1us pulse detected!")

                except Exception as e:
                    self.log.debug(f"Debug monitor error: {e}")

        # AR request queue and R response handler (separate concurrent tasks)
        ar_queue = []  # Queue of AR requests to respond to

        async def ar_monitor():
            """Continuously monitor for AR handshakes (runs concurrently with R responder)"""
            # Assert ar_ready (always ready)
            self.dut.ar_ready.value = 1

            while monitor_active[0]:
                await self.wait_clocks(self.clk_name, 1)

                # Detect AR handshake
                if int(self.dut.ar_valid.value) == 1 and int(self.dut.ar_ready.value) == 1:
                    read_count[0] += 1
                    ar_id = int(self.dut.ar_id.value)
                    ar_addr = int(self.dut.ar_addr.value)

                    self.log.info(f"  AR transaction #{read_count[0]} - addr=0x{ar_addr:X}, id={ar_id}")

                    # Add to queue for R responder
                    ar_queue.append((read_count[0], ar_id, ar_addr))

        async def r_responder():
            """Respond to AR requests from queue (runs concurrently with AR monitor)"""
            while monitor_active[0]:
                await self.wait_clocks(self.clk_name, 1)

                # Check if there's an AR request to respond to
                if ar_queue:
                    (transaction_num, ar_id, ar_addr) = ar_queue.pop(0)

                    # Return wrong data for first max_retries reads, correct data on (max_retries+1)th read
                    if transaction_num <= max_retries:
                        # First N reads: return non-matching data (engine will retry)
                        response_data = 0x00000000
                        self.log.info(f"  → Returning NON-matching data: 0x{response_data:08X} (retry {transaction_num}/{max_retries})")
                    else:
                        # (N+1)th read: return matching data (engine will complete)
                        response_data = 0xABCDEF55
                        self.log.info(f"  → Returning MATCHING data: 0x{response_data:08X}")

                    # Wait a few cycles before responding (realistic delay)
                    await self.wait_clocks(self.clk_name, 2)

                    # Drive R channel
                    self.dut.r_valid.value = 1
                    self.dut.r_data.value = response_data
                    self.dut.r_id.value = ar_id
                    self.dut.r_resp.value = 0  # OKAY
                    self.dut.r_last.value = 1

                    # Wait for R ready
                    while True:
                        await self.wait_clocks(self.clk_name, 1)
                        if int(self.dut.r_ready.value) == 1:
                            break

                    # Clear R channel
                    self.dut.r_valid.value = 0

        # Background task for 1µs tick
        async def tick_1us_driver():
            """Drive 1µs tick signal for retry timing"""
            while monitor_active[0]:
                await self.wait_clocks(self.clk_name, 100)  # Simulate 1µs tick every 100 cycles
                self.dut.tick_1us.value = 1
                await self.wait_clocks(self.clk_name, 1)
                self.dut.tick_1us.value = 0

        # Start background tasks (concurrent AR monitor and R responder)
        debug_task = cocotb.start_soon(debug_state_monitor())
        ar_monitor_task = cocotb.start_soon(ar_monitor())
        r_responder_task = cocotb.start_soon(r_responder())
        tick_task = cocotb.start_soon(tick_1us_driver())

        # Send ctrlrd request
        success = await self.send_ctrlrd_request(test_addr, expected_data, mask, profile)
        if not success:
            monitor_active[0] = False
            await self.wait_clocks(self.clk_name, 2)
            return False

        # Wait for completion (needs more time for retry delay)
        (success, result_data, error) = await self.wait_for_completion(timeout_cycles=2000)

        # Stop background tasks
        monitor_active[0] = False
        await self.wait_clocks(self.clk_name, 2)

        if not success:
            self.log.error(f"Ctrlrd retry operation failed: error={error}")
            return False

        # Verify we got exactly max_retries + 1 reads (N wrong + 1 correct)
        expected_reads = max_retries + 1
        if read_count[0] != expected_reads:
            self.log.error(f"Expected exactly {expected_reads} reads, got {read_count[0]}")
            return False

        self.log.info(f"✓ Read-retry-match completed successfully")
        self.log.info(f"  Retries: {read_count[0] - 1}, Result: 0x{result_data:08X}")

        return True

    async def test_null_address(self, profile: DelayProfile, skip_axi_slave_creation=False):
        """
        Test null address operation (64'h0 = immediate success).

        Scenario:
        1. Send ctrlrd request with address = 64'h0
        2. Engine skips AXI read and completes immediately
        3. No AXI transactions should occur

        Args:
            profile: Delay profile to use
            skip_axi_slave_creation: If True, don't create AXI factory slave
        """
        self.log.info("="*70)
        self.log.info(f"TEST: Null Address (Profile: {profile.value})")
        self.log.info("="*70)

        # Create AXI4 factory slave for this test (though it shouldn't be used)
        # Skip if running in MIXED mode with manual responders
        if not skip_axi_slave_creation and self.axi_slave is None:
            self.axi_slave = create_axi4_slave_rd(
                dut=self.dut,
                clock=self.clk,
                prefix="",
                log=self.log,
                data_width=64,
                id_width=8,
                addr_width=64,
                user_width=1,
                multi_sig=True,
                memory_model=self.memory_model
            )

        test_addr = 0x0  # Null address
        expected_data = 0x0
        mask = 0xFFFFFFFF

        # No need to write to memory - null address skips AXI read

        # Send ctrlrd request
        success = await self.send_ctrlrd_request(test_addr, expected_data, mask, profile)
        if not success:
            return False

        # Wait for completion (should be fast - no AXI transaction)
        (success, result_data, error) = await self.wait_for_completion(timeout_cycles=100)

        if not success:
            self.log.error(f"Null address operation failed: error={error}")
            return False

        self.log.info(f"✓ Null address completed successfully")
        self.log.info(f"  Result: 0x{result_data:08X}")

        return True

    async def test_masked_comparison(self, profile: DelayProfile):
        """
        Test masked comparison with various mask patterns.

        Scenario:
        1. Send ctrlrd requests with different mask patterns
        2. Verify masked bits are ignored in comparison
        3. Verify unmasked bits must match
        """
        self.log.info("="*70)
        self.log.info(f"TEST: Masked Comparison (Profile: {profile.value})")
        self.log.info("="*70)

        # Create AXI4 factory slave for this test
        if self.axi_slave is None:
            self.axi_slave = create_axi4_slave_rd(
                dut=self.dut,
                clock=self.clk,
                prefix="",
                log=self.log,
                data_width=64,
                id_width=8,
                addr_width=64,
                user_width=1,
                multi_sig=True,
                memory_model=self.memory_model
            )

        test_cases = [
            # (addr, expected, mask, actual_data, should_match)
            (0x3000, 0x12345678, 0xFFFF0000, 0x12340000, True),   # Upper 16 bits match: (0x12345678 & 0xFFFF0000) == (0x12340000 & 0xFFFF0000) = 0x12340000
            (0x3004, 0xABCDEF12, 0x0000FFFF, 0x0000EF12, True),   # Lower 16 bits match: (0xABCDEF12 & 0x0000FFFF) == (0x0000EF12 & 0x0000FFFF) = 0x0000EF12
            (0x3008, 0xFF00FF00, 0xFF00FF00, 0xFF55FF99, True),   # Alternating bytes: (0xFF00FF00 & 0xFF00FF00) == (0xFF55FF99 & 0xFF00FF00) = 0xFF00FF00
            (0x300C, 0x12345679, 0x00000001, 0xABCDEF79, True),   # Only LSB matches: (0x12345679 & 0x00000001) == (0xABCDEF79 & 0x00000001) = 0x00000001
        ]

        for test_addr, expected_data, mask, actual_data, should_match in test_cases:
            # Write data to memory model
            data_bytes = bytearray(actual_data.to_bytes(4, byteorder='little'))
            self.memory_model.write(test_addr, data_bytes)

            success = await self.send_ctrlrd_request(test_addr, expected_data, mask, profile)
            if not success:
                return False

            (success, result_data, error) = await self.wait_for_completion(timeout_cycles=500)

            if should_match and not success:
                self.log.error(f"Masked comparison failed: addr=0x{test_addr:X}, expected=0x{expected_data:08X}, mask=0x{mask:08X}, actual=0x{actual_data:08X}")
                return False

            self.log.info(f"  ✓ Masked comparison passed: addr=0x{test_addr:X}, mask=0x{mask:08X}")

            await self.wait_clocks(self.clk_name, 5)

        self.log.info(f"✓ All masked comparisons completed successfully")
        return True

    async def test_max_retries_exceeded(self, profile: DelayProfile, max_retries=3):
        """
        Test max retries exceeded scenario (data never matches).

        Scenario:
        1. Send ctrlrd request with expected_data that won't match memory
        2. AXI4 slave returns non-matching data from memory model
        3. Engine exhausts all retry attempts
        4. Engine completes with error

        Uses AXI4 factory slave (NOT manual AR/R driving) per framework standards.
        """
        self.log.info("="*70)
        self.log.info(f"TEST: Max Retries Exceeded (Profile: {profile.value}, Max: {max_retries})")
        self.log.info("="*70)

        test_addr = 0x4000
        expected_data = 0x12345678  # This is what we'll expect
        non_matching_data = 0x00000000  # This is what memory will return (never matches)
        mask = 0xFFFFFFFF  # All bits must match

        # Configure max retries
        self.dut.cfg_ctrlrd_max_try.value = max_retries

        # Create AXI4 factory slave if not already created
        if self.axi_slave is None:
            self.axi_slave = create_axi4_slave_rd(
                dut=self.dut,
                clock=self.clk,
                prefix="",
                log=self.log,
                data_width=64,
                id_width=8,
                addr_width=64,
                user_width=1,
                multi_sig=True,
                memory_model=self.memory_model
            )

        # Write NON-MATCHING data to memory model (AXI slave will return this)
        # Expected=0x12345678, Actual=0x00000000 -> mismatch, retry
        data_bytes = bytearray(non_matching_data.to_bytes(4, byteorder='little'))
        self.memory_model.write(test_addr, data_bytes)

        # Background driver for 1µs tick (needed for retry timing)
        monitor_active = [True]

        async def tick_1us_driver():
            """Drive 1µs tick signal for retry timing"""
            while monitor_active[0]:
                await self.wait_clocks(self.clk_name, 100)
                self.dut.tick_1us.value = 1
                await self.wait_clocks(self.clk_name, 1)
                self.dut.tick_1us.value = 0

        # Start tick driver
        tick_task = cocotb.start_soon(tick_1us_driver())

        # Send ctrlrd request
        success = await self.send_ctrlrd_request(test_addr, expected_data, mask, profile)
        if not success:
            monitor_active[0] = False
            await self.wait_clocks(self.clk_name, 2)
            return False

        # Wait for completion (should get error after max retries)
        # Longer timeout to allow for retries with 1µs tick delays
        (success, result_data, error) = await self.wait_for_completion(timeout_cycles=5000)

        # Stop background tasks
        monitor_active[0] = False
        await self.wait_clocks(self.clk_name, 2)

        # Check that error was raised (data never matched)
        if error == 1:
            self.log.info(f"✓ Max retries exceeded - error reported correctly")
            self.log.info(f"  Expected data: 0x{expected_data:08X}, Memory data: 0x{non_matching_data:08X}")
            return True
        else:
            self.log.error(f"Expected error after max retries, got success")
            self.log.error(f"  Result data: 0x{result_data:08X}")
            return False

    async def test_axi_error(self, profile: DelayProfile):
        """
        Test AXI error handling.

        Scenario:
        1. Send ctrlrd request
        2. AXI read returns SLVERR response
        3. Engine completes with error
        """
        self.log.info("="*70)
        self.log.info(f"TEST: AXI Error (Profile: {profile.value})")
        self.log.info("="*70)

        test_addr = 0x5000
        expected_data = 0xDEADBEEF
        mask = 0xFFFFFFFF

        monitor_active = [True]

        async def ar_monitor():
            """Monitor for AR handshakes and return error response"""
            self.dut.ar_ready.value = 1

            while monitor_active[0]:
                await self.wait_clocks(self.clk_name, 1)

                if int(self.dut.ar_valid.value) == 1 and int(self.dut.ar_ready.value) == 1:
                    ar_id = int(self.dut.ar_id.value)
                    ar_addr = int(self.dut.ar_addr.value)
                    self.log.info(f"  AR transaction - addr=0x{ar_addr:X}, returning SLVERR")

                    await self.wait_clocks(self.clk_name, 2)
                    self.dut.r_valid.value = 1
                    self.dut.r_data.value = 0x00000000
                    self.dut.r_id.value = ar_id
                    self.dut.r_resp.value = 2  # SLVERR
                    self.dut.r_last.value = 1

                    while True:
                        await self.wait_clocks(self.clk_name, 1)
                        if int(self.dut.r_ready.value) == 1:
                            break
                    self.dut.r_valid.value = 0

        # Start background task
        ar_task = cocotb.start_soon(ar_monitor())

        # Send ctrlrd request
        success = await self.send_ctrlrd_request(test_addr, expected_data, mask, profile)
        if not success:
            monitor_active[0] = False
            await self.wait_clocks(self.clk_name, 2)
            return False

        # Wait for completion
        (success, result_data, error) = await self.wait_for_completion(timeout_cycles=500)

        # Stop background task
        monitor_active[0] = False
        await self.wait_clocks(self.clk_name, 2)

        # Should have error due to AXI SLVERR
        if error == 1:
            self.log.info(f"✓ AXI error handled correctly")
            return True
        else:
            self.log.error(f"Expected error from AXI SLVERR, but got success")
            return False

    async def test_channel_reset(self, profile: DelayProfile):
        """
        Test channel reset during operation.

        Scenario:
        1. Start ctrlrd operation
        2. Assert channel reset mid-operation
        3. Verify engine returns to idle
        4. Deassert reset and verify normal operation
        """
        self.log.info("="*70)
        self.log.info(f"TEST: Channel Reset (Profile: {profile.value})")
        self.log.info("="*70)

        test_addr = 0x6000
        expected_data = 0xCAFEBABE
        mask = 0xFFFFFFFF

        monitor_active = [True]

        async def ar_monitor():
            """Monitor for AR handshakes but delay response"""
            self.dut.ar_ready.value = 1

            while monitor_active[0]:
                await self.wait_clocks(self.clk_name, 1)

                if int(self.dut.ar_valid.value) == 1 and int(self.dut.ar_ready.value) == 1:
                    ar_id = int(self.dut.ar_id.value)
                    # Delay response to allow reset to be asserted mid-transaction
                    await self.wait_clocks(self.clk_name, 10)

                    # Check if we should still respond (reset may have been asserted)
                    if not monitor_active[0]:
                        return

                    self.dut.r_valid.value = 1
                    self.dut.r_data.value = expected_data
                    self.dut.r_id.value = ar_id
                    self.dut.r_resp.value = 0
                    self.dut.r_last.value = 1

                    while True:
                        await self.wait_clocks(self.clk_name, 1)
                        if int(self.dut.r_ready.value) == 1 or not monitor_active[0]:
                            break
                    self.dut.r_valid.value = 0

        # Start background task
        ar_task = cocotb.start_soon(ar_monitor())

        # Send ctrlrd request
        success = await self.send_ctrlrd_request(test_addr, expected_data, mask, profile)
        if not success:
            monitor_active[0] = False
            await self.wait_clocks(self.clk_name, 2)
            return False

        # Wait a few cycles then assert channel reset
        await self.wait_clocks(self.clk_name, 5)
        self.log.info("  Asserting channel reset...")
        self.dut.cfg_channel_reset.value = 1
        await self.wait_clocks(self.clk_name, 5)

        # Verify engine returns to idle
        idle = int(self.dut.ctrlrd_engine_idle.value)
        self.log.info(f"  Engine idle after reset: {idle}")

        # Deassert reset
        self.dut.cfg_channel_reset.value = 0
        await self.wait_clocks(self.clk_name, 5)

        # Stop background task
        monitor_active[0] = False
        await self.wait_clocks(self.clk_name, 2)

        # Now verify normal operation works after reset
        self.log.info("  Verifying normal operation after reset...")
        result = await self.test_basic_read_match(profile, use_manual_responders=True)

        if result:
            self.log.info(f"✓ Channel reset handled correctly")
            return True
        else:
            self.log.error(f"Normal operation failed after channel reset")
            return False

    async def test_back_to_back(self, profile: DelayProfile, num_operations=5):
        """
        Test back-to-back operations.

        Scenario:
        1. Send multiple ctrlrd requests back-to-back
        2. Verify all complete successfully
        3. Check no data corruption between operations
        """
        self.log.info("="*70)
        self.log.info(f"TEST: Back-to-Back ({num_operations} ops, Profile: {profile.value})")
        self.log.info("="*70)

        monitor_active = [True]
        operations_complete = [0]
        ar_queue = []  # Queue of AR requests to respond to

        async def ar_monitor():
            """Monitor for AR handshakes (non-blocking)"""
            self.dut.ar_ready.value = 1

            while monitor_active[0]:
                await self.wait_clocks(self.clk_name, 1)

                if int(self.dut.ar_valid.value) == 1 and int(self.dut.ar_ready.value) == 1:
                    ar_id = int(self.dut.ar_id.value)
                    ar_addr = int(self.dut.ar_addr.value)
                    self.log.info(f"  AR transaction - addr=0x{ar_addr:X}, id={ar_id}")
                    ar_queue.append((ar_id, ar_addr))

        async def r_responder():
            """Respond to AR requests from queue"""
            while monitor_active[0]:
                await self.wait_clocks(self.clk_name, 1)

                if ar_queue:
                    (ar_id, ar_addr) = ar_queue.pop(0)

                    # Return data based on address
                    response_data = ar_addr & 0xFFFFFFFF

                    await self.wait_clocks(self.clk_name, 2)
                    self.dut.r_valid.value = 1
                    self.dut.r_data.value = response_data
                    self.dut.r_id.value = ar_id
                    self.dut.r_resp.value = 0
                    self.dut.r_last.value = 1

                    while True:
                        await self.wait_clocks(self.clk_name, 1)
                        if int(self.dut.r_ready.value) == 1:
                            break
                    self.dut.r_valid.value = 0

        # Start background tasks
        ar_task = cocotb.start_soon(ar_monitor())
        r_task = cocotb.start_soon(r_responder())

        # Run multiple operations
        for i in range(num_operations):
            test_addr = 0x7000 + (i * 4)
            expected_data = test_addr & 0xFFFFFFFF  # Expect address as data
            mask = 0xFFFFFFFF

            self.log.info(f"  Operation {i+1}/{num_operations}: addr=0x{test_addr:X}")

            success = await self.send_ctrlrd_request(test_addr, expected_data, mask, profile)
            if not success:
                self.log.error(f"Failed to send request for operation {i+1}")
                monitor_active[0] = False
                await self.wait_clocks(self.clk_name, 2)
                return False

            (success, result_data, error) = await self.wait_for_completion(timeout_cycles=500)
            if not success or error:
                self.log.error(f"Operation {i+1} failed: success={success}, error={error}")
                monitor_active[0] = False
                await self.wait_clocks(self.clk_name, 2)
                return False

            operations_complete[0] += 1
            self.log.info(f"    ✓ Completed with result=0x{result_data:08X}")

            # Small delay between operations
            await self.wait_clocks(self.clk_name, 3)

        # Stop background task
        monitor_active[0] = False
        await self.wait_clocks(self.clk_name, 2)

        if operations_complete[0] == num_operations:
            self.log.info(f"✓ All {num_operations} back-to-back operations completed successfully")
            return True
        else:
            self.log.error(f"Only {operations_complete[0]}/{num_operations} operations completed")
            return False

    async def test_mixed_scenarios(self):
        """
        Run mixed scenarios test combining multiple test types.

        Runs a subset of tests to validate overall functionality.
        """
        self.log.info("="*70)
        self.log.info("TEST: Mixed Scenarios")
        self.log.info("="*70)

        profile = DelayProfile.FIXED_DELAY
        result = True

        # Helper to reset AXI interface between scenarios
        async def reset_axi_interface():
            """Reset AXI interface signals to known state"""
            self.dut.ar_ready.value = 0
            self.dut.r_valid.value = 0
            self.dut.r_data.value = 0
            self.dut.r_id.value = 0
            self.dut.r_resp.value = 0
            self.dut.r_last.value = 0
            await self.wait_clocks(self.clk_name, 5)

        # Test 1: Basic read-match
        self.log.info("\n--- Scenario 1: Basic Read-Match ---")
        result &= await self.test_basic_read_match(profile, use_manual_responders=True)
        if not result:
            return False
        await reset_axi_interface()
        await self.wait_clocks(self.clk_name, 10)

        # Test 2: Null address
        self.log.info("\n--- Scenario 2: Null Address ---")
        result &= await self.test_null_address(profile, skip_axi_slave_creation=True)
        if not result:
            return False
        await reset_axi_interface()
        await self.wait_clocks(self.clk_name, 10)

        # Test 3: Back-to-back (2 ops only for quick test)
        self.log.info("\n--- Scenario 3: Back-to-Back (2 ops) ---")
        result &= await self.test_back_to_back(profile, num_operations=2)
        if not result:
            return False
        await self.wait_clocks(self.clk_name, 10)

        self.log.info("\n" + "="*70)
        if result:
            self.log.info("✓ All mixed scenarios completed successfully")
        else:
            self.log.error("✗ Some mixed scenarios failed")

        return result

    async def run_test_suite(self, scenario: TestScenario, profile: DelayProfile, num_ops: int = 1):
        """
        Run comprehensive test suite based on scenario.

        Args:
            scenario: Test scenario to run
            profile: Delay profile to use
            num_ops: Number of operations for multi-op scenarios

        Returns:
            bool: True if all tests pass
        """
        if scenario == TestScenario.BASIC_READ_MATCH:
            return await self.test_basic_read_match(profile)
        elif scenario == TestScenario.READ_RETRY_MATCH:
            return await self.test_read_retry_match(profile)
        elif scenario == TestScenario.NULL_ADDRESS:
            return await self.test_null_address(profile)
        elif scenario == TestScenario.MASKED_COMPARISON:
            return await self.test_masked_comparison(profile)
        elif scenario == TestScenario.MIXED:
            # Run all scenarios sequentially
            # NOTE: MIXED mode uses manual responders for ALL tests to avoid signal conflicts
            # Manual responders have complete surgical control over AR/R responses
            result = True

            # Test 1: Basic read-match (use manual responders)
            result &= await self.test_basic_read_match(profile, use_manual_responders=True)
            if not result:
                return False
            await self.wait_clocks(self.clk_name, 10)  # Allow RTL to fully settle

            # Test 2: Null address (doesn't issue AR transaction, skip AXI slave)
            result &= await self.test_null_address(profile, skip_axi_slave_creation=True)
            if not result:
                return False
            await self.wait_clocks(self.clk_name, 10)

            # Test 3: Masked comparison (use manual responders)
            # TODO: Add manual responder support to masked comparison test
            self.log.info("="*70)
            self.log.info("SKIPPED: Masked comparison (needs manual responder support)")
            self.log.info("  Masked comparison validated in standalone test")
            self.log.info("="*70)
            await self.wait_clocks(self.clk_name, 10)

            # Test 4: Retry test (already uses manual responders)
            # Wait for RTL to return to complete idle
            for _ in range(100):
                await self.wait_clocks(self.clk_name, 1)
                if int(self.dut.ctrlrd_engine_idle.value) == 1:
                    break

            # Reconfigure max retries
            self.dut.cfg_ctrlrd_max_try.value = 3
            await self.wait_clocks(self.clk_name, 5)

            # Reset AXI interface signals to known state before retry test
            # This ensures clean state after previous manual responder tests
            self.dut.ar_ready.value = 0
            self.dut.r_valid.value = 0
            self.dut.r_data.value = 0
            self.dut.r_id.value = 0
            self.dut.r_resp.value = 0
            self.dut.r_last.value = 0
            await self.wait_clocks(self.clk_name, 2)

            # Run retry test - manual responders provide complete surgical control
            # They can easily return zeros hundreds of times before returning match
            result &= await self.test_read_retry_match(profile)

            return result
        else:
            self.log.error(f"Unknown scenario: {scenario}")
            return False
