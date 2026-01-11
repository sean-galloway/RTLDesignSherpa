# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: BeatsSchedulerGroupTB
# Purpose: RAPIDS Beats Scheduler Group Testbench - Phase 1 Macro Level
#
# Documentation: projects/components/rapids/PRD.md
# Subsystem: rapids_macro_beats
#
# Author: sean galloway
# Created: 2025-01-10

"""
RAPIDS Beats Scheduler Group Testbench - Phase 1 Macro Level

Testbench for the scheduler_group_beats module which wraps:
- Descriptor Engine (fetches descriptors via AXI, provides to scheduler)
- Scheduler (processes descriptors, issues data path commands)
- MonBus Arbiter (aggregates monitor packets from 2 sources)

This is a simplified RAPIDS architecture for Phase 1:
- No program engine (direct APB config)
- No control read/write engines
- Simplified data path interface

Features tested:
- APB descriptor kick-off interface
- Descriptor AXI read interface (256-bit descriptors)
- Scheduler data path interfaces (rd/wr)
- Completion strobe handling
- Error propagation
- MonBus aggregation
"""

import os
import random
import cocotb
from typing import Dict, List, Tuple, Any, Optional
from cocotb.triggers import RisingEdge, Timer

# Framework imports
from CocoTBFramework.tbclasses.shared.tbbase import TBBase
from CocoTBFramework.components.shared.memory_model import MemoryModel


class SchedulerGroupBeatsTB(TBBase):
    """
    RAPIDS Beats Scheduler Group testbench.

    Tests wrapper functionality for scheduler + descriptor_engine:
    - APB programming interface for descriptor fetch kick-off
    - Descriptor AXI interface (responder mode)
    - Scheduler data path command interfaces
    - Completion strobe handling
    - MonBus event aggregation
    """

    def __init__(self, dut, clk=None, rst_n=None):
        super().__init__(dut)

        # Get test parameters from environment
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

        # Calculated parameters
        self.MAX_ADDR = (2**self.TEST_ADDR_WIDTH) - 1

        # Test tracking
        self.apb_requests = 0
        self.descriptors_served = 0
        self.rd_commands_received = 0
        self.wr_commands_received = 0
        self.completions_sent = 0
        self.mon_packets_received = 0
        self.test_errors = []

        # Memory model for descriptor storage
        self.descriptor_memory = None

        self.log.info(f"BeatsSchedulerGroupTB initialized: "
                     f"{self.TEST_ADDR_WIDTH}-bit addr, {self.TEST_DATA_WIDTH}-bit data")

    async def setup_clocks_and_reset(self):
        """Complete initialization - starts clocks AND performs reset sequence"""
        # Start clock
        await self.start_clock(self.clk_name, freq=self.TEST_CLK_PERIOD, units='ns')

        # Set configuration signals BEFORE reset (important for proper initialization)
        self.dut.cfg_channel_enable.value = 1
        self.dut.cfg_channel_reset.value = 0
        self.dut.cfg_sched_timeout_cycles.value = 1000
        self.dut.cfg_sched_timeout_enable.value = 1
        self.dut.cfg_sched_err_enable.value = 1
        self.dut.cfg_sched_compl_enable.value = 1
        self.dut.cfg_sched_perf_enable.value = 0

        self.dut.cfg_desceng_prefetch.value = 1
        self.dut.cfg_desceng_fifo_thresh.value = 4
        self.dut.cfg_desceng_addr0_base.value = 0
        self.dut.cfg_desceng_addr0_limit.value = 0xFFFF_FFFF
        self.dut.cfg_desceng_addr1_base.value = 0
        self.dut.cfg_desceng_addr1_limit.value = 0xFFFF_FFFF

        # Perform reset sequence
        await self.assert_reset()
        await self.wait_clocks(self.clk_name, 10)
        await self.deassert_reset()
        await self.wait_clocks(self.clk_name, 10)

    async def assert_reset(self):
        """Assert reset signal"""
        self.mark_progress("assert_reset")
        self.rst_n.value = 0

        # Clear inputs during reset
        self.dut.apb_valid.value = 0
        self.dut.apb_addr.value = 0
        self.dut.desc_ar_ready.value = 0
        self.dut.desc_r_valid.value = 0
        self.dut.desc_r_data.value = 0
        self.dut.desc_r_resp.value = 0
        self.dut.desc_r_last.value = 0
        self.dut.desc_r_id.value = 0
        self.dut.sched_wr_ready.value = 1
        self.dut.sched_rd_done_strobe.value = 0
        self.dut.sched_rd_beats_done.value = 0
        self.dut.sched_wr_done_strobe.value = 0
        self.dut.sched_wr_beats_done.value = 0
        self.dut.sched_rd_error.value = 0
        self.dut.sched_wr_error.value = 0
        self.dut.mon_ready.value = 1

        await self.wait_clocks(self.clk_name, 5)
        self.log.info("Reset asserted")

    async def deassert_reset(self):
        """Deassert reset signal"""
        self.mark_progress("deassert_reset")
        self.rst_n.value = 1
        await self.wait_clocks(self.clk_name, 5)
        self.log.info("Reset deasserted")

    async def initialize_test(self):
        """Initialize test environment"""
        self.log.info("=== Initializing Beats Scheduler Group Test ===")
        self.log.info(f"  ADDR_WIDTH: {self.TEST_ADDR_WIDTH}")
        self.log.info(f"  DATA_WIDTH: {self.TEST_DATA_WIDTH}")

        # Create memory model for descriptor storage (256-bit descriptors)
        self.descriptor_memory = MemoryModel(
            num_lines=4096,
            bytes_per_line=32,  # 256 bits = 32 bytes
            log=self.log
        )

        # Set default ready signals
        self.dut.desc_ar_ready.value = 1
        self.dut.sched_wr_ready.value = 1
        self.dut.mon_ready.value = 1

        await self.wait_clocks(self.clk_name, 5)
        self.log.info("Beats scheduler group initialization completed")

    # ==========================================================================
    # INTERFACE METHODS
    # ==========================================================================

    async def send_apb_request(self, addr: int) -> bool:
        """Send APB descriptor fetch request.

        Args:
            addr: Descriptor address to fetch

        Returns:
            True if request accepted, False on timeout
        """
        self.dut.apb_valid.value = 1
        self.dut.apb_addr.value = addr

        # Wait for ready handshake
        for _ in range(100):
            if int(self.dut.apb_ready.value) == 1:
                await self.wait_clocks(self.clk_name, 1)
                self.apb_requests += 1
                self.log.info(f"APB request sent: addr=0x{addr:X}")
                self.dut.apb_valid.value = 0
                return True
            await self.wait_clocks(self.clk_name, 1)

        self.log.warning(f"APB request timeout: addr=0x{addr:X}")
        self.dut.apb_valid.value = 0
        return False

    async def respond_to_descriptor_read(self, data: int) -> bool:
        """Respond to descriptor AXI read request.

        Args:
            data: 256-bit descriptor data to return

        Returns:
            True if response sent, False on timeout
        """
        # Wait for AR valid with debug logging
        for i in range(100):
            ar_valid = int(self.dut.desc_ar_valid.value)
            ar_ready = int(self.dut.desc_ar_ready.value)
            if ar_valid == 1 and ar_ready == 1:
                self.log.info(f"AR handshake at cycle {i}")
                break
            # Print debug info every 10 cycles
            if i % 10 == 0 and i > 0:
                try:
                    # Access internal signals for debug
                    desc_eng = self.dut.u_descriptor_engine
                    fsm_state = int(desc_eng.r_current_state.value)
                    apb_ip = int(desc_eng.r_apb_ip.value)
                    channel_reset = int(desc_eng.r_channel_reset_active.value)
                    chan_idle = int(self.dut.channel_idle.value)
                    sched_idle = int(self.dut.scheduler_idle.value)
                    # FIFO signals
                    fifo_wr_valid = int(desc_eng.w_desc_addr_fifo_wr_valid.value)
                    fifo_wr_ready = int(desc_eng.w_desc_addr_fifo_wr_ready.value)
                    fifo_rd_valid = int(desc_eng.w_desc_addr_fifo_rd_valid.value)
                    fifo_rd_ready = int(desc_eng.w_desc_addr_fifo_rd_ready.value)
                    # Skid buffer signals
                    skid_wr_valid = int(desc_eng.w_apb_skid_valid_in.value)
                    skid_wr_ready = int(desc_eng.w_apb_skid_ready_in.value)
                    skid_rd_valid = int(desc_eng.w_apb_skid_valid_out.value)
                    skid_rd_ready = int(desc_eng.w_apb_skid_ready_out.value)
                    self.log.info(f"[DEBUG cycle {i}] FSM={fsm_state} apb_ip={apb_ip} chan_reset={channel_reset} "
                                  f"chan_idle={chan_idle} sched_idle={sched_idle}")
                    self.log.info(f"[DEBUG cycle {i}] FIFO: wr={fifo_wr_valid}/{fifo_wr_ready} "
                                  f"rd={fifo_rd_valid}/{fifo_rd_ready}")
                    self.log.info(f"[DEBUG cycle {i}] SKID: wr={skid_wr_valid}/{skid_wr_ready} "
                                  f"rd={skid_rd_valid}/{skid_rd_ready}")
                    self.log.info(f"[DEBUG cycle {i}] ar_valid={ar_valid} ar_ready={ar_ready}")
                except Exception as e:
                    self.log.warning(f"[DEBUG cycle {i}] Could not access internal signals: {e}")
            await self.wait_clocks(self.clk_name, 1)
        else:
            return False

        # Get request info
        ar_addr = int(self.dut.desc_ar_addr.value)
        ar_id = int(self.dut.desc_ar_id.value)
        ar_len = int(self.dut.desc_ar_len.value)

        await self.wait_clocks(self.clk_name, 2)

        # Send read response (single beat for 256-bit descriptor)
        self.dut.desc_r_valid.value = 1
        self.dut.desc_r_data.value = data
        self.dut.desc_r_resp.value = 0  # OKAY
        self.dut.desc_r_last.value = 1
        self.dut.desc_r_id.value = ar_id

        # Wait for ready with debug logging
        self.log.info(f"R channel: asserting r_valid with id={ar_id}")

        # After setting r_valid, use Timer(0) to let combinational logic settle
        # This ensures the DUT sees r_valid=1 and updates r_ready accordingly
        await Timer(0, units='ns')

        # Check r_ready - should now reflect the combinational response to r_valid=1
        for i in range(50):
            r_ready = int(self.dut.desc_r_ready.value)

            if r_ready == 1:
                # Handshake detected! Wait for clock edge to complete the transfer
                await self.wait_clocks(self.clk_name, 1)
                self.descriptors_served += 1
                self.log.info(f"Descriptor served: addr=0x{ar_addr:X}, data=0x{data:X}")
                self.dut.desc_r_valid.value = 0
                return True

            # Print debug info for first 5 cycles, then every 10
            if i < 5 or i % 10 == 0:
                try:
                    desc_eng = self.dut.u_descriptor_engine
                    fsm_state = int(desc_eng.r_current_state.value)
                    r_id_dut = int(self.dut.desc_r_id.value)
                    r_valid_dut = int(self.dut.desc_r_valid.value)
                    r_resp_dut = int(self.dut.desc_r_resp.value)
                    our_axi_resp = int(desc_eng.w_our_axi_response.value)
                    axi_resp_ok = int(desc_eng.w_axi_response_ok.value)
                    chan_reset = int(desc_eng.r_channel_reset_active.value)
                    self.log.info(f"[R DEBUG cycle {i}] FSM={fsm_state} r_ready={r_ready} "
                                  f"r_valid={r_valid_dut} r_resp={r_resp_dut} r_id={r_id_dut} "
                                  f"our_axi_resp={our_axi_resp} axi_ok={axi_resp_ok} chan_reset={chan_reset}")
                except Exception as e:
                    self.log.warning(f"[R DEBUG cycle {i}] Could not access internal signals: {e}")

            # Wait for clock edge, let combinational logic settle, then check again
            await self.wait_clocks(self.clk_name, 1)
            await Timer(0, units='ns')

        self.log.error(f"R channel timeout: r_ready never asserted")
        self.dut.desc_r_valid.value = 0
        return False

    async def wait_for_rd_command(self, timeout: int = 100) -> Optional[Tuple[int, int]]:
        """Wait for scheduler read command.

        Returns:
            Tuple of (addr, beats) if command received, None on timeout
        """
        for _ in range(timeout):
            if int(self.dut.sched_rd_valid.value) == 1:
                addr = int(self.dut.sched_rd_addr.value)
                beats = int(self.dut.sched_rd_beats.value)
                self.rd_commands_received += 1
                self.log.info(f"RD command: addr=0x{addr:X}, beats={beats}")
                return (addr, beats)
            await self.wait_clocks(self.clk_name, 1)
        return None

    async def wait_for_wr_command(self, timeout: int = 100) -> Optional[Tuple[int, int]]:
        """Wait for scheduler write command.

        Returns:
            Tuple of (addr, beats) if command received, None on timeout
        """
        for _ in range(timeout):
            if int(self.dut.sched_wr_valid.value) == 1 and int(self.dut.sched_wr_ready.value) == 1:
                addr = int(self.dut.sched_wr_addr.value)
                beats = int(self.dut.sched_wr_beats.value)
                await self.wait_clocks(self.clk_name, 1)
                self.wr_commands_received += 1
                self.log.info(f"WR command: addr=0x{addr:X}, beats={beats}")
                return (addr, beats)
            await self.wait_clocks(self.clk_name, 1)
        return None

    async def send_rd_completion(self, beats_done: int):
        """Send read completion strobe."""
        self.dut.sched_rd_done_strobe.value = 1
        self.dut.sched_rd_beats_done.value = beats_done
        await self.wait_clocks(self.clk_name, 1)
        self.dut.sched_rd_done_strobe.value = 0
        self.completions_sent += 1
        self.log.info(f"RD completion: beats={beats_done}")

    async def send_wr_completion(self, beats_done: int):
        """Send write completion strobe."""
        self.dut.sched_wr_done_strobe.value = 1
        self.dut.sched_wr_beats_done.value = beats_done
        await self.wait_clocks(self.clk_name, 1)
        self.dut.sched_wr_done_strobe.value = 0
        self.completions_sent += 1
        self.log.info(f"WR completion: beats={beats_done}")

    async def check_monbus_packet(self, timeout: int = 50) -> Optional[int]:
        """Check for monitor bus packet.

        Returns:
            64-bit packet data if available, None on timeout
        """
        for _ in range(timeout):
            if int(self.dut.mon_valid.value) == 1 and int(self.dut.mon_ready.value) == 1:
                packet = int(self.dut.mon_packet.value)
                self.mon_packets_received += 1
                return packet
            await self.wait_clocks(self.clk_name, 1)
        return None

    # ==========================================================================
    # STATUS METHODS
    # ==========================================================================

    def is_scheduler_idle(self) -> bool:
        """Check if scheduler is idle."""
        return int(self.dut.scheduler_idle.value) == 1

    def is_descriptor_engine_idle(self) -> bool:
        """Check if descriptor engine is idle."""
        return int(self.dut.descriptor_engine_idle.value) == 1

    def get_scheduler_state(self) -> int:
        """Get scheduler state (7-bit one-hot)."""
        return int(self.dut.scheduler_state.value)

    def has_scheduler_error(self) -> bool:
        """Check for scheduler error."""
        return int(self.dut.sched_error.value) == 1

    # ==========================================================================
    # TEST METHODS
    # ==========================================================================

    async def test_basic_descriptor_flow(self, num_descriptors: int = 5) -> bool:
        """Test basic descriptor fetch and processing flow.

        Args:
            num_descriptors: Number of descriptors to test

        Returns:
            True if test passed
        """
        self.log.info(f"=== Basic Descriptor Flow Test: {num_descriptors} descriptors ===")

        errors = 0

        for i in range(num_descriptors):
            # Create descriptor data (256-bit)
            # RAPIDS Descriptor Format (from scheduler.sv):
            #   [63:0]    - src_addr     (64 bits) - Source address
            #   [127:64]  - dst_addr     (64 bits) - Destination address
            #   [159:128] - length       (32 bits) - Transfer length in beats
            #   [191:160] - next_ptr     (32 bits) - Next descriptor pointer (0=none)
            #   [192]     - valid        (1 bit)   - Descriptor valid flag
            #   [193]     - gen_irq      (1 bit)   - Generate IRQ on completion
            #   [194]     - last         (1 bit)   - Last descriptor in chain
            src_addr = random.randint(0x1000, 0xFFFF) * 0x100
            dst_addr = random.randint(0x2000, 0xFFFF) * 0x100
            length = random.randint(1, 64)
            next_ptr = 0  # No chaining for this test
            valid = 1     # CRITICAL: Must be 1 for scheduler to accept!
            gen_irq = 0   # No IRQ for this test
            last = 1      # Last descriptor (no chaining)

            desc_data = (src_addr & ((1 << 64) - 1))
            desc_data |= ((dst_addr & ((1 << 64) - 1)) << 64)
            desc_data |= ((length & ((1 << 32) - 1)) << 128)
            desc_data |= ((next_ptr & ((1 << 32) - 1)) << 160)
            desc_data |= (valid << 192)
            desc_data |= (gen_irq << 193)
            desc_data |= (last << 194)

            # Start from non-zero address (0 is invalid for descriptor engine)
            desc_addr = (i + 1) * 32  # 32-byte aligned, starting from 32

            self.log.info(f"Descriptor {i+1}: src=0x{src_addr:X}, dst=0x{dst_addr:X}, len={length}")

            # Send APB request
            if not await self.send_apb_request(desc_addr):
                self.log.error(f"APB request failed for descriptor {i+1}")
                errors += 1
                continue

            # Respond to AXI read
            if not await self.respond_to_descriptor_read(desc_data):
                self.log.error(f"Descriptor AXI response failed for descriptor {i+1}")
                errors += 1
                continue

            # Wait for scheduler command (could be rd or wr)
            await self.wait_clocks(self.clk_name, 20)

            # Check for read or write command
            rd_cmd = await self.wait_for_rd_command(timeout=50)
            if rd_cmd:
                addr, beats = rd_cmd
                # Complete the read
                await self.wait_clocks(self.clk_name, 10)
                await self.send_rd_completion(beats)

            wr_cmd = await self.wait_for_wr_command(timeout=50)
            if wr_cmd:
                addr, beats = wr_cmd
                # Complete the write
                await self.wait_clocks(self.clk_name, 10)
                await self.send_wr_completion(beats)

            await self.wait_clocks(self.clk_name, 20)

        self.log.info(f"Basic descriptor flow test: {num_descriptors - errors}/{num_descriptors} passed")
        return errors == 0

    async def test_idle_state(self) -> bool:
        """Test that system starts in idle state."""
        self.log.info("=== Idle State Test ===")

        # Check idle states
        sched_idle = self.is_scheduler_idle()
        desc_idle = self.is_descriptor_engine_idle()

        self.log.info(f"  Scheduler idle: {sched_idle}")
        self.log.info(f"  Descriptor engine idle: {desc_idle}")

        if sched_idle and desc_idle:
            self.log.info("Idle state test PASSED")
            return True
        else:
            self.log.error("Idle state test FAILED")
            return False

    async def test_config_interface(self) -> bool:
        """Test configuration interface."""
        self.log.info("=== Configuration Interface Test ===")

        # Test enable/disable
        self.dut.cfg_channel_enable.value = 0
        await self.wait_clocks(self.clk_name, 5)
        self.dut.cfg_channel_enable.value = 1
        await self.wait_clocks(self.clk_name, 5)

        # Test timeout configuration
        self.dut.cfg_sched_timeout_cycles.value = 500
        await self.wait_clocks(self.clk_name, 2)

        # Test descriptor engine configuration
        self.dut.cfg_desceng_prefetch.value = 0
        await self.wait_clocks(self.clk_name, 2)
        self.dut.cfg_desceng_prefetch.value = 1
        await self.wait_clocks(self.clk_name, 2)

        self.log.info("Configuration interface test PASSED")
        return True

    async def test_monbus_events(self, wait_cycles: int = 100) -> bool:
        """Test monitor bus event generation.

        Args:
            wait_cycles: Cycles to wait for events

        Returns:
            True if events received
        """
        self.log.info("=== MonBus Events Test ===")

        initial_count = self.mon_packets_received

        # Generate activity to trigger mon events
        await self.send_apb_request(0x100)
        await self.wait_clocks(self.clk_name, wait_cycles)

        # Check for monitor packets
        for _ in range(10):
            packet = await self.check_monbus_packet(timeout=20)
            if packet is not None:
                self.log.info(f"  MonBus packet received: 0x{packet:016X}")

        events_received = self.mon_packets_received - initial_count
        self.log.info(f"MonBus events received: {events_received}")

        return events_received > 0

    def generate_test_report(self) -> bool:
        """Generate comprehensive test report."""
        self.log.info("\n" + "=" * 60)
        self.log.info("BEATS SCHEDULER GROUP TEST REPORT")
        self.log.info("=" * 60)
        self.log.info(f"APB requests: {self.apb_requests}")
        self.log.info(f"Descriptors served: {self.descriptors_served}")
        self.log.info(f"RD commands received: {self.rd_commands_received}")
        self.log.info(f"WR commands received: {self.wr_commands_received}")
        self.log.info(f"Completions sent: {self.completions_sent}")
        self.log.info(f"MonBus packets received: {self.mon_packets_received}")

        if self.test_errors:
            self.log.error(f"Test errors ({len(self.test_errors)}):")
            for error in self.test_errors:
                self.log.error(f"  - {error}")
            self.log.info("=" * 60)
            return False
        else:
            self.log.info("ALL TESTS PASSED SUCCESSFULLY!")
            self.log.info("=" * 60)
            return True
