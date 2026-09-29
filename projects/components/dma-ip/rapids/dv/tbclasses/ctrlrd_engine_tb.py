# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: DelayProfile
# Purpose: RAPIDS Control Read Engine Testbench
#
# Documentation: projects/components/dma-ip/rapids/PRD.md
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

See: projects/components/dma-ip/rapids/docs/rapids_spec/ch02_blocks/01_04_ctrlrd_engine.md
"""

import cocotb
from cocotb.triggers import RisingEdge, Timer, ClockCycles
from enum import Enum
import random
import os

from TBClasses.shared.tbbase import TBBase
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

        # The test cell parameterizes the DUT's AXI_DATA_WIDTH; the TB must model
        # the bus it was given rather than assume 64. A ctrlrd is ALWAYS a 4-byte
        # read, so on a wider bus the data rides the address-selected 32-bit lane.
        self.axi_data_width = int(os.environ.get('AXI_DATA_WIDTH', 64))

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

    def _lane_place(self, addr: int, data32: int) -> int:
        """Place a 4-byte read value on the 32-bit lane AXI selects by address.

        A ctrlrd is ALWAYS a 32-bit read at a 32-bit-aligned address -- an
        unaligned address is a malformed descriptor -- so the placement is
        word-granular and everything below addr[2] is zero by contract. On a bus
        wider than 32 bits a real slave returns the word on the addressed lanes,
        which is what ctrlrd_engine's lane select reads. Degenerates to a no-op
        on a 32-bit bus, where the only lane is lane 0.
        """
        words = self.axi_data_width // 32
        if words <= 1:
            return data32 & 0xFFFFFFFF
        sel = (addr >> 2) & (words - 1)
        return (data32 & 0xFFFFFFFF) << (32 * sel)

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

    async def _ensure_axi_slave(self):
        """Create the framework AXI4 read slave once and reset its bus.

        Memory-backed; every test address is a multiple of the bus width so
        the word sits on lane 0 (the shared slave BFM returns narrow reads in
        the low word -- see the narrow-read note in the handbook/memory).
        resp_override lets a test force SLVERR without a hand-rolled R driver:
        set self._forced_resp = 2 for the duration (rapids TASK-013).
        """
        if self.axi_slave is None:
            self.axi_slave = create_axi4_slave_rd(
                dut=self.dut, clock=self.clk, prefix="", log=self.log,
                data_width=self.axi_data_width, id_width=8, addr_width=64,
                user_width=1, multi_sig=True, memory_model=self.memory_model,
                response_delay=getattr(self, '_response_delay', 1),
                resp_override=lambda addr: getattr(self, '_forced_resp', None))
            await self.axi_slave['AR'].reset_bus()
            await self.axi_slave['R'].reset_bus()
            self.axi_slave['AR'].add_callback(self._on_ar)
        return self.axi_slave

    def _on_ar(self, pkt):
        """AR monitor callback (framework hook): count reads, expose the address."""
        self._ar_count = getattr(self, '_ar_count', 0) + 1
        self._last_ar_addr = int(getattr(pkt, 'addr', 0))
        hook = getattr(self, '_ar_hook', None)
        if hook is not None:
            # Runs before the slave generates this AR's response (the framework
            # schedules generation with start_soon from its own AR callback,
            # registered ahead of this one), so a memory swap here is seen by
            # THIS read.
            hook(self._last_ar_addr, self._ar_count)

    def _word(self, value: int) -> bytearray:
        return bytearray((value & 0xFFFFFFFF).to_bytes(4, byteorder='little'))


    async def test_basic_read_match(self, profile: DelayProfile, use_manual_responders=False):
        """
        Test basic read-and-match operation (first read matches).

        Scenario:
        1. Send ctrlrd request with address, expected_data, mask
        2. AXI read returns data that matches expected_data (with mask)
        3. Engine completes successfully

        Args:
            profile: Delay profile to use
            use_manual_responders: accepted for call compatibility; the framework
                AXI4 slave is always used (rapids TASK-013)
        """
        self.log.info("="*70)
        self.log.info(f"TEST: Basic Read-Match (Profile: {profile.value})")
        self.log.info("="*70)

        test_addr = 0x1000
        expected_data = 0x12345678
        mask = 0xFFFFFFFF  # Full match required
        read_data = 0x12345678  # Matches expected

        await self._ensure_axi_slave()

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

        # Framework read slave. Memory holds the NON-matching word; the AR hook
        # swaps the matching word in as read max_retries+1 is accepted, so the
        # engine sees exactly max_retries mismatches and then a match.
        await self._ensure_axi_slave()
        wrong, right = 0x00000000, 0xABCDEF55
        self.memory_model.write(test_addr, self._word(right if max_retries == 0 else wrong))
        self._ar_count = 0

        def _swap_on_nth(addr, count):
            # Count-exact, not time-based: after the first tick the engine
            # retries back-to-back, so read N+1 can follow read N within cycles.
            if count == max_retries + 1:
                self.memory_model.write(test_addr, self._word(right))
                self.log.info(f"  -> matching data 0x{right:08X} armed for read {count}")
        self._ar_hook = _swap_on_nth

        # Background task for 1us tick (paces the engine's retries)
        async def tick_1us_driver():
            while monitor_active[0]:
                await self.wait_clocks(self.clk_name, 100)  # 1us tick every 100 cycles
                self.dut.tick_1us.value = 1
                await self.wait_clocks(self.clk_name, 1)
                self.dut.tick_1us.value = 0

        debug_task = cocotb.start_soon(debug_state_monitor())
        tick_task = cocotb.start_soon(tick_1us_driver())

        # Send ctrlrd request
        success = await self.send_ctrlrd_request(test_addr, expected_data, mask, profile)
        if not success:
            monitor_active[0] = False
            await self.wait_clocks(self.clk_name, 2)
            return False

        # Wait for completion (needs more time for retry delay)
        (success, result_data, error) = await self.wait_for_completion(timeout_cycles=2000)
        self._ar_hook = None

        # Stop background tasks
        monitor_active[0] = False
        await self.wait_clocks(self.clk_name, 2)

        if not success:
            self.log.error(f"Ctrlrd retry operation failed: error={error}")
            return False

        # Verify we got exactly max_retries + 1 reads (N wrong + 1 correct)
        expected_reads = max_retries + 1
        if self._ar_count != expected_reads:
            self.log.error(f"Expected exactly {expected_reads} reads, got {self._ar_count}")
            return False

        self.log.info(f"✓ Read-retry-match completed successfully")
        self.log.info(f"  Retries: {self._ar_count - 1}, Result: 0x{result_data:08X}")

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

        # The framework slave is created if a test needs it; a null address never
        # issues an AR, so MIXED mode may skip creating it here.
        if not skip_axi_slave_creation and self.axi_slave is None:
            self.axi_slave = create_axi4_slave_rd(
                dut=self.dut,
                clock=self.clk,
                prefix="",
                log=self.log,
                data_width=self.axi_data_width,
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

        # The claim under test is "no AXI transaction": count AR handshakes the
        # slave BFM sees while the request runs. Without this the BFM would
        # answer a spurious read of address 0 with 0, which matches
        # expected_data, and the special case could be dropped unnoticed.
        ar_seen = []
        if self.axi_slave is not None:
            self.axi_slave['AR'].add_callback(lambda pkt: ar_seen.append(pkt))

        # Send ctrlrd request
        success = await self.send_ctrlrd_request(test_addr, expected_data, mask, profile)
        if not success:
            return False

        # Wait for completion (should be fast - no AXI transaction)
        (success, result_data, error) = await self.wait_for_completion(timeout_cycles=100)

        if not success:
            self.log.error(f"Null address operation failed: error={error}")
            return False

        await self.wait_clocks(self.clk_name, 5)
        if ar_seen:
            self.log.error(f"Null address issued {len(ar_seen)} AXI read(s); the 64'h0 special case must skip AXI")
            return False

        self.log.info(f"✓ Null address completed successfully with no AXI transaction")
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
                data_width=self.axi_data_width,
                id_width=8,
                addr_width=64,
                user_width=1,
                multi_sig=True,
                memory_model=self.memory_model
            )

        # Strided by the bus width so every case lands on lane 0. This test rides
        # the shared AXI4 slave BFM, which returns a narrow read in the low word
        # instead of on the address-selected lanes (CocoTBFramework
        # axi4_interfaces.py _generate_read_response -- its master/write path DOES
        # lane-position, the slave read path does not). Lane coverage therefore
        # is covered by test_back_to_back, which walks consecutive 4-byte
        # addresses (addr[2] across 0x7000..) against the framework slave; the
        # slave read BFM lane-positions narrow reads since RTLDesignSherpa-DV
        # 593c279 (the gap TASK-013 recorded is closed).
        bus_stride = max(4, self.axi_data_width // 8)
        test_cases = [
            # (addr, expected, mask, actual_data, should_match)
            (0x3000 + 0 * bus_stride, 0x12345678, 0xFFFF0000, 0x12340000, True),   # Upper 16 bits match
            (0x3000 + 1 * bus_stride, 0xABCDEF12, 0x0000FFFF, 0x0000EF12, True),   # Lower 16 bits match
            (0x3000 + 2 * bus_stride, 0xFF00FF00, 0xFF00FF00, 0xFF55FF99, True),   # Alternating bytes
            (0x3000 + 3 * bus_stride, 0x12345679, 0x00000001, 0xABCDEF79, True),   # Only LSB matches
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
                data_width=self.axi_data_width,
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

        # Framework read slave with the response forced to SLVERR through its
        # resp_override hook (no hand-rolled AR/R driving; rapids TASK-013).
        await self._ensure_axi_slave()
        self.memory_model.write(test_addr, self._word(0))
        self._forced_resp = 2

        # Send ctrlrd request
        success = await self.send_ctrlrd_request(test_addr, expected_data, mask, profile)
        if not success:
            self._forced_resp = None
            return False

        # Wait for completion
        (success, result_data, error) = await self.wait_for_completion(timeout_cycles=500)

        self._forced_resp = None

        # Should have error due to AXI SLVERR
        if error == 1:
            self.log.info(f"✓ AXI error handled correctly")
            return True
        else:
            self.log.error(f"Expected error from AXI SLVERR, but got success")
            return False

    async def test_channel_reset(self, profile: DelayProfile):
        """
        Test channel reset as a BETWEEN-OPERATIONS channel clear -- the realistic
        use of cfg_channel_reset (same model as ctrlwr's test_channel_reset).

        The old version asserted reset with a read outstanding and had its
        hand-rolled responder WITHDRAW the R beat afterwards, which a real slave
        cannot do: ctrlrd_engine only raises r_ready in READ_WAIT_DATA, so a
        response landing after the abort would sit on the bus forever. That
        mid-read abort needs engine drain-on-reset (or a fabric-drain model) and
        is tracked in vault/Tasks/projects/components/dma-ip/rapids/CONTROL_ENGINE_INTEGRATION.md; here the framework slave
        stays honest and the reset is applied with the engine idle.

        Scenario:
        1. A read-match at addr A completes.
        2. With the engine idle, assert channel reset; idle reads 0 by design
           while reset is held.
        3. Release reset; the engine must be idle within a few cycles.
        4. A fresh, DISTINCT read-match at addr B completes -> recovery proven.
        """
        self.log.info("="*70)
        self.log.info(f"TEST: Channel Reset (between-ops clear) (Profile: {profile.value})")
        self.log.info("="*70)
        await self._ensure_axi_slave()
        mask = 0xFFFFFFFF
        addr_a, data_a = 0x6000, 0xCAFEBABE
        addr_b, data_b = 0x6100, 0x0BADF00D

        async def _read_and_match(addr: int, data: int, tag: str) -> bool:
            self.memory_model.write(addr, self._word(data))
            if not await self.send_ctrlrd_request(addr, data, mask, profile):
                self.log.error(f"{tag} request was not accepted")
                return False
            ok, got, err = await self.wait_for_completion(timeout_cycles=500)
            if not ok or err or got != data:
                self.log.error(f"{tag} read-match failed: ok={ok} err={err} got=0x{got:08X}")
                return False
            self.log.info(f"  {tag} read-match completed: 0x{got:08X}")
            return True

        if not await _read_and_match(addr_a, data_a, "baseline"):
            return False

        await self.wait_clocks(self.clk_name, 5)
        self.log.info("  Asserting channel reset with the engine idle...")
        self.dut.cfg_channel_reset.value = 1
        await self.wait_clocks(self.clk_name, 5)
        idle = int(self.dut.ctrlrd_engine_idle.value)
        self.log.info(f"  Engine idle while reset held: {idle} (0 expected by design)")
        self.dut.cfg_channel_reset.value = 0
        await self.wait_clocks(self.clk_name, 5)
        if int(self.dut.ctrlrd_engine_idle.value) != 1:
            self.log.error("Engine did not return to idle within 5 cycles of releasing cfg_channel_reset")
            return False

        self.log.info("  Verifying normal operation after reset...")
        if not await _read_and_match(addr_b, data_b, "post-reset"):
            self.log.error("Normal operation failed after channel reset")
            return False
        self.log.info("Channel reset handled correctly")
        return True

    async def test_reset_mid_read(self, profile: DelayProfile) -> bool:
        """Channel reset with a read on the fabric (rapids TASK-014, drain-on-reset).

        AXI cannot cancel a transaction: an AR that is up must stay up until
        accepted, and an accepted AR is owed an R beat. The engine must take and
        discard that beat, report busy and refuse requests until it has, and
        answer the NEXT read with fresh data rather than the stale beat.

        A) reset lands with the AR raised and not yet accepted (slave AR ready
           delayed): ar_valid holds through the reset until the handshake.
        B) reset lands with the AR accepted and the R beat still to come.
        Both end with a fresh read-match that must return its own word.
        """
        from CocoTBFramework.components.shared.flex_randomizer import FlexRandomizer
        self.log.info("=" * 70)
        self.log.info(f"TEST: Channel Reset mid-read, drain-on-reset (Profile: {profile.value})")
        self.log.info("=" * 70)
        self._response_delay = 24                       # R lands well after the reset
        await self._ensure_axi_slave()
        self._ar_count = getattr(self, '_ar_count', 0)
        mask = 0xFFFFFFFF
        stale_addr, stale_data = 0x6200, 0x57A1E000     # the aborted read's word
        fresh_addr, fresh_data = 0x6300, 0xF4E54000
        self.memory_model.write(stale_addr, self._word(stale_data))
        self.memory_model.write(fresh_addr, self._word(fresh_data))

        obs = {'run': True, 'r_hs': 0, 'ar_dropped': 0, 'idle_seen_before_r': 0}

        async def observer():
            """DUT outputs only: R handshakes, an AR withdrawn before its handshake,
            and idle reported while the R beat is still owed."""
            prev_ar_valid = 0
            owed = False
            while obs['run']:
                await RisingEdge(self.clk)
                ar_v, ar_r = int(self.dut.ar_valid.value), int(self.dut.ar_ready.value)
                if prev_ar_valid and not ar_v and not obs.get('ar_hs_last', 0):
                    obs['ar_dropped'] += 1
                obs['ar_hs_last'] = 1 if (ar_v and ar_r) else 0
                if ar_v and ar_r:
                    owed = True
                if int(self.dut.r_valid.value) and int(self.dut.r_ready.value):
                    obs['r_hs'] += 1
                    owed = False
                if owed and int(self.dut.ctrlrd_engine_idle.value):
                    obs['idle_seen_before_r'] += 1
                prev_ar_valid = ar_v

        task = cocotb.start_soon(observer())
        ok = True
        try:
            for scenario, ar_delay in (("A: AR raised, not accepted", 20), ("B: AR accepted, R owed", 0)):
                self.log.info(f"  --- scenario {scenario} ---")
                self.axi_slave['AR'].set_randomizer(FlexRandomizer({'ready_delay': ([(ar_delay, ar_delay)], [1])}))
                r_hs_before, ar_before = obs['r_hs'], self._ar_count
                if not await self.send_ctrlrd_request(stale_addr, stale_data, mask, profile):
                    self.log.error("request not accepted"); return False
                # wait for the AR to be raised (A) or accepted (B)
                for _ in range(100):
                    await self.wait_clocks(self.clk_name, 1)
                    if ar_delay and int(self.dut.ar_valid.value):
                        break
                    if not ar_delay and self._ar_count > ar_before:
                        break
                await self.wait_clocks(self.clk_name, 2)
                self.dut.cfg_channel_reset.value = 1
                await self.wait_clocks(self.clk_name, 10)
                self.dut.cfg_channel_reset.value = 0
                # the owed beat must be taken; idle must not report before it is
                for _ in range(200):
                    await self.wait_clocks(self.clk_name, 1)
                    if obs['r_hs'] > r_hs_before and int(self.dut.ctrlrd_engine_idle.value):
                        break
                if obs['r_hs'] != r_hs_before + 1:
                    self.log.error(f"{scenario}: stale R beat not drained (handshakes {obs['r_hs'] - r_hs_before})")
                    ok = False
                if obs['idle_seen_before_r']:
                    self.log.error(f"{scenario}: idle reported {obs['idle_seen_before_r']} cycle(s) with the R beat still owed")
                    ok = False
                if obs['ar_dropped']:
                    self.log.error(f"{scenario}: AR withdrawn before its handshake ({obs['ar_dropped']}x)")
                    ok = False
                # fresh read after the drain must return its own word
                self.axi_slave['AR'].set_randomizer(FlexRandomizer({'ready_delay': ([(0, 0)], [1])}))
                if not await self.send_ctrlrd_request(fresh_addr, fresh_data, mask, profile):
                    self.log.error(f"{scenario}: fresh request not accepted after the drain"); return False
                success, got, err = await self.wait_for_completion(timeout_cycles=500)
                if not success or err or got != fresh_data:
                    self.log.error(f"{scenario}: fresh read after reset: ok={success} err={err} got=0x{got:08X} "
                                   f"(stale word is 0x{stale_data:08X})")
                    ok = False
                else:
                    self.log.info(f"  {scenario}: drained, idle held, fresh read returned 0x{got:08X}")
        finally:
            obs['run'] = False
            task.kill()
        return ok

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

        # Framework read slave answers from memory: each operation's word is
        # its own address, preloaded here. Consecutive 4-byte addresses walk
        # the byte lanes of a wide bus (addr[2] on 64 bits), which exercises
        # the engine's lane select -- the slave read BFM lane-positions narrow
        # reads since RTLDesignSherpa-DV 593c279 (rapids TASK-013 note).
        await self._ensure_axi_slave()
        operations_complete = [0]
        bus_stride = 4
        for i in range(num_operations):
            a = 0x7000 + i * bus_stride
            self.memory_model.write(a, self._word(a))

        # Run multiple operations
        for i in range(num_operations):
            test_addr = 0x7000 + i * bus_stride
            expected_data = test_addr & 0xFFFFFFFF  # Expect address as data
            mask = 0xFFFFFFFF

            self.log.info(f"  Operation {i+1}/{num_operations}: addr=0x{test_addr:X}")

            success = await self.send_ctrlrd_request(test_addr, expected_data, mask, profile)
            if not success:
                self.log.error(f"Failed to send request for operation {i+1}")
                return False

            (success, result_data, error) = await self.wait_for_completion(timeout_cycles=500)
            if not success or error:
                self.log.error(f"Operation {i+1} failed: success={success}, error={error}")
                return False

            operations_complete[0] += 1
            self.log.info(f"    ✓ Completed with result=0x{result_data:08X}")

            # Small delay between operations
            await self.wait_clocks(self.clk_name, 3)


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
            """Let the framework slave settle between scenarios (it owns AR/R)."""
            await self.wait_clocks(self.clk_name, 5)

        # Test 1: Basic read-match
        self.log.info("\n--- Scenario 1: Basic Read-Match ---")
        result &= await self.test_basic_read_match(profile)
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
            # MIXED mode runs the scenarios back to back on the one framework
            # AXI4 read slave (rapids TASK-013).
            result = True

            # Test 1: Basic read-match
            result &= await self.test_basic_read_match(profile)
            if not result:
                return False
            await self.wait_clocks(self.clk_name, 10)  # Allow RTL to fully settle

            # Test 2: Null address (doesn't issue AR transaction, skip AXI slave)
            result &= await self.test_null_address(profile, skip_axi_slave_creation=True)
            if not result:
                return False
            await self.wait_clocks(self.clk_name, 10)

            # Test 3: Masked comparison
            result &= await self.test_masked_comparison(profile)
            if not result:
                return False
            await self.wait_clocks(self.clk_name, 10)

            # Test 4: Retry test
            # Wait for RTL to return to complete idle
            for _ in range(100):
                await self.wait_clocks(self.clk_name, 1)
                if int(self.dut.ctrlrd_engine_idle.value) == 1:
                    break

            # Reconfigure max retries
            self.dut.cfg_ctrlrd_max_try.value = 3
            await self.wait_clocks(self.clk_name, 5)

            # The framework slave owns AR/R; just let it settle between scenarios.
            await self.wait_clocks(self.clk_name, 2)

            result &= await self.test_read_retry_match(profile)

            return result
        else:
            self.log.error(f"Unknown scenario: {scenario}")
            return False
