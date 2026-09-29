# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: BeatsSchedulerGroupTB
# Purpose: RAPIDS Beats Scheduler Group Testbench - Phase 1 Macro Level
#
# Documentation: projects/components/dmas/rapids/PRD.md
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
from TBClasses.shared.tbbase import TBBase
from CocoTBFramework.components.gaxi.gaxi_factories import create_gaxi_master
from CocoTBFramework.components.axi4.axi4_factories import create_axi4_slave_rd, create_axi4_slave_wr
from CocoTBFramework.components.shared.field_config import FieldConfig, FieldDefinition
from CocoTBFramework.components.shared.flex_randomizer import FlexRandomizer
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
        # GAXI master for the APB descriptor-fetch kick (created end of setup)
        self.apb4_master = None
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
        self.dut.cfg_sched_timeout_limit.value = 1  # escalate after one window (legacy timeout->error)
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

        # Create the GAXI master for the APB descriptor-fetch kick.
        self._create_bfms()

    def _create_bfms(self):
        """Create the GAXI master for the APB kick (apb_valid/ready/addr)."""
        addr_bits = len(self.dut.apb_addr)
        fc = FieldConfig()
        fc.add_field(FieldDefinition(name='addr', bits=addr_bits,
                                     format='hex', description='descriptor address'))
        self.apb4_master = create_gaxi_master(
            dut=self.dut, title='sg_apb', prefix='apb', clock=self.clk,
            field_config=fc, multi_sig=True, log=self.log)
        self.set_gaxi_timing_profile(os.environ.get('GAXI_TIMING_PROFILE', 'backtoback'))

    def set_gaxi_timing_profile(self, profile_name='backtoback'):
        """Apply a GAXI timing profile to the APB-kick master's valid_delay."""
        from TBClasses.amba.amba_random_configs import GAXI_RANDOMIZER_CONFIGS
        if profile_name == 'mixed':
            profile_name = 'gaxi_realistic'
        if profile_name not in GAXI_RANDOMIZER_CONFIGS:
            self.log.warning(f"Unknown GAXI timing profile '{profile_name}', using 'backtoback'")
            profile_name = 'backtoback'
        cfg = GAXI_RANDOMIZER_CONFIGS[profile_name]
        self.apb4_master.randomizer = FlexRandomizer(cfg['master'])
        self.log.info(f"GAXI scheduler_group APB-kick timing profile: {profile_name}")

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
        self.dut.sched_wr_commit_strobe.value = 0
        self.dut.sched_wr_commit_beats.value = 0
        self.dut.sched_rd_error.value = 0
        self.dut.sched_wr_error.value = 0
        # Control engine AXI + config (Phase 2)
        self.dut.ctrlrd_ar_ready.value = 0
        self.dut.ctrlrd_r_valid.value = 0
        self.dut.ctrlrd_r_data.value = 0
        self.dut.ctrlrd_r_id.value = 0
        self.dut.ctrlrd_r_resp.value = 0
        self.dut.ctrlrd_r_last.value = 0
        self.dut.ctrlwr_aw_ready.value = 0
        self.dut.ctrlwr_w_ready.value = 0
        self.dut.ctrlwr_b_valid.value = 0
        self.dut.ctrlwr_b_id.value = 0
        self.dut.ctrlwr_b_resp.value = 0
        self.dut.cfg_ctrlrd_max_try.value = 16
        self.dut.tick_1us.value = 0
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

        # Framework slaves own the three AXI ports the group masters (rapids
        # TASK-013; the TB used to drive AR/R, AW/W/B by hand):
        #   desc_*   256-bit read slave backed by descriptor_memory (register_descriptor)
        #   ctrlrd_* 32-bit read slave backed by ctrlrd_memory (poll values)
        #   ctrlwr_* 32-bit write slave backed by ctrlwr_memory (doorbells)
        self.ctrlrd_memory = MemoryModel(num_lines=4096, bytes_per_line=4, log=self.log)
        self.ctrlwr_memory = MemoryModel(num_lines=4096, bytes_per_line=4, log=self.log)
        self.desc_fetches, self._desc_fetch_seen = 0, 0
        self.ctrlrd_polls, self._ctrlrd_poll_seen = [], 0
        self.ctrlwr_doorbells, self._ctrlwr_seen, self._ctrlwr_pending_aw = [], 0, []
        self.desc_slave = create_axi4_slave_rd(
            dut=self.dut, clock=self.clk, prefix="desc_", log=self.log,
            data_width=256, id_width=self.TEST_AXI_ID_WIDTH, addr_width=self.TEST_ADDR_WIDTH,
            user_width=1, multi_sig=True, memory_model=self.descriptor_memory)
        self.ctrlrd_slave = create_axi4_slave_rd(
            dut=self.dut, clock=self.clk, prefix="ctrlrd_", log=self.log,
            data_width=32, id_width=self.TEST_AXI_ID_WIDTH, addr_width=self.TEST_ADDR_WIDTH,
            user_width=1, multi_sig=True, memory_model=self.ctrlrd_memory)
        self.ctrlwr_slave = create_axi4_slave_wr(
            dut=self.dut, clock=self.clk, prefix="ctrlwr_", log=self.log,
            data_width=32, id_width=self.TEST_AXI_ID_WIDTH, addr_width=self.TEST_ADDR_WIDTH,
            user_width=1, multi_sig=True, memory_model=self.ctrlwr_memory)
        for comp in (self.desc_slave['AR'], self.desc_slave['R'], self.ctrlrd_slave['AR'],
                     self.ctrlrd_slave['R'], self.ctrlwr_slave['AW'], self.ctrlwr_slave['W'],
                     self.ctrlwr_slave['B']):
            await comp.reset_bus()
        self.desc_slave['AR'].add_callback(self._on_desc_ar)
        self.ctrlrd_slave['AR'].add_callback(self._on_ctrlrd_ar)
        self.ctrlwr_slave['AW'].add_callback(self._on_ctrlwr_aw)
        self.ctrlwr_slave['W'].add_callback(self._on_ctrlwr_w)

        # Set default ready signals (scheduler-side consumers the TB models by level)
        self.dut.sched_wr_ready.value = 1
        self.dut.mon_ready.value = 1
        if not getattr(self, '_mon_capture_started', False):
            self._mon_capture_started = True
            cocotb.start_soon(self._capture_monbus())

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
        # Drive the APB kick through the GAXI master; the pipeline performs the
        # apb_valid/ready handshake honoring the active timing profile.
        pkt = self.apb4_master.create_packet(addr=addr)
        await self.apb4_master.send(pkt)

        # send() queues; wait for the handshake to complete.
        await self.wait_clocks(self.clk_name, 1)
        for _ in range(100):
            if not self.apb4_master.transfer_busy and len(self.apb4_master.transmit_queue) == 0:
                self.apb_requests += 1
                self.log.info(f"APB request sent: addr=0x{addr:X}")
                return True
            await self.wait_clocks(self.clk_name, 1)

        self.log.warning(f"APB request timeout: addr=0x{addr:X}")
        return False

    # -- framework-slave hooks (AR/AW/W monitor callbacks) ---------------------
    def _on_desc_ar(self, pkt):
        self.desc_fetches += 1
        self.log.info(f"descriptor fetch #{self.desc_fetches}: addr=0x{int(getattr(pkt, 'addr', 0)):X}")

    def _on_ctrlrd_ar(self, pkt):
        self.ctrlrd_polls.append(int(getattr(pkt, 'addr', 0)))

    def _on_ctrlwr_aw(self, pkt):
        self._ctrlwr_pending_aw.append(int(getattr(pkt, 'addr', 0)))

    def _on_ctrlwr_w(self, pkt):
        addr = self._ctrlwr_pending_aw.pop(0) if self._ctrlwr_pending_aw else None
        self.ctrlwr_doorbells.append((addr, int(getattr(pkt, 'data', 0)) & 0xFFFFFFFF))

    def register_descriptor(self, addr: int, data: int):
        """Place a 256-bit descriptor in the memory the desc_* read slave serves.
        Must precede the APB kick: the engine fetches within a few cycles."""
        self.descriptor_memory.write(addr, bytearray((data & ((1 << 256) - 1)).to_bytes(32, 'little')))

    async def wait_descriptor_fetch(self, timeout: int = 200) -> bool:
        """Wait for the next descriptor AR the read slave serves (one per call)."""
        for _ in range(timeout):
            if self.desc_fetches > self._desc_fetch_seen:
                self._desc_fetch_seen += 1
                return True
            await self.wait_clocks(self.clk_name, 1)
        self.log.error(f"no descriptor fetch within {timeout} cycles")
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
        """Send write completion strobes (issue + commit).

        commit_strobe now gates scheduler completion, so pulse it alongside the
        issue done_strobe (this simulator models issue and commit together).
        """
        self.dut.sched_wr_done_strobe.value = 1
        self.dut.sched_wr_beats_done.value = beats_done
        self.dut.sched_wr_commit_strobe.value = 1
        self.dut.sched_wr_commit_beats.value = beats_done
        await self.wait_clocks(self.clk_name, 1)
        self.dut.sched_wr_done_strobe.value = 0
        self.dut.sched_wr_commit_strobe.value = 0
        self.completions_sent += 1
        self.log.info(f"WR completion: beats={beats_done}")

    async def _capture_monbus(self):
        """Count every packet on the group's monitor bus from initialisation on.
        test_monbus_events used to poll only after the activity that produced
        them and saw nothing (rapids TASK-003)."""
        from TBClasses.monbus import parse
        self.mon_packets = []
        while True:
            await self.wait_clocks(self.clk_name, 1)
            if int(self.dut.mon_valid.value) == 1 and int(self.dut.mon_ready.value) == 1:
                self.mon_packets.append(parse(int(self.dut.mon_packet.value)))
                self.mon_packets_received += 1

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

            # Descriptor in memory first, then the kick; the read slave serves it.
            self.register_descriptor(desc_addr, desc_data)
            if not await self.send_apb_request(desc_addr):
                self.log.error(f"APB request failed for descriptor {i+1}")
                errors += 1
                continue
            if not await self.wait_descriptor_fetch():
                self.log.error(f"Descriptor {i+1} was never fetched")
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

    # ==========================================================================
    # CONTROL-DESCRIPTOR SUPPORT (Phase 2 producer/consumer)
    # ==========================================================================

    @staticmethod
    def _build_descriptor(opcode=0, src=0, dst=0, length=1, valid=1, last=1,
                          next_ptr=0, gen_irq=0):
        """Build a 256-bit descriptor. For control descriptors the ctrl fields
        overlay the data slots: addr = src[63:0]; data = dst[31:0]; mask = dst[63:32];
        opcode at [209:208] (0=DATA, 1=CTRL_READ, 2=CTRL_WRITE)."""
        d = (src & ((1 << 64) - 1))
        d |= ((dst & ((1 << 64) - 1)) << 64)
        d |= ((length & 0xFFFFFFFF) << 128)
        d |= ((next_ptr & 0xFFFFFFFF) << 160)
        d |= (valid << 192)
        d |= (gen_irq << 193)
        d |= (last << 194)
        d |= ((opcode & 0x3) << 208)
        return d

    async def _wait_ctrlwr_doorbell(self, timeout: int = 300):
        """Next doorbell (addr, data) the ctrlwr_* write slave accepted, or None."""
        for _ in range(timeout):
            if len(self.ctrlwr_doorbells) > self._ctrlwr_seen:
                got = self.ctrlwr_doorbells[self._ctrlwr_seen]
                self._ctrlwr_seen += 1
                return got
            await self.wait_clocks(self.clk_name, 1)
        return None

    async def _wait_ctrlrd_poll(self, timeout: int = 300):
        """Address of the next poll the ctrlrd_* read slave served, or None.
        The value returned to the engine is whatever ctrlrd_memory holds."""
        for _ in range(timeout):
            if len(self.ctrlrd_polls) > self._ctrlrd_poll_seen:
                got = self.ctrlrd_polls[self._ctrlrd_poll_seen]
                self._ctrlrd_poll_seen += 1
                return got
            await self.wait_clocks(self.clk_name, 1)
        return None

    def _set_poll_value(self, addr: int, value: int):
        self.ctrlrd_memory.write(addr, bytearray((value & 0xFFFFFFFF).to_bytes(4, 'little')))

    async def _tick_generator(self, period: int = 8):
        """Free-running tick_1us pulse generator (models the periodic 1us tick that
        paces ctrlrd retries). Runs until self._tick_active is cleared."""
        while self._tick_active:
            self.dut.tick_1us.value = 1
            await self.wait_clocks(self.clk_name, 1)
            self.dut.tick_1us.value = 0
            await self.wait_clocks(self.clk_name, period)

    async def test_ctrl_write_doorbell(self) -> bool:
        """CTRL_WRITE descriptor routes through the scheduler to the real ctrlwr
        engine, which posts a doorbell write; verify addr/data and completion."""
        self.log.info("=== Control Write Doorbell Test ===")
        door_addr = 0x2000
        door_data = 0xABCD1234
        desc = self._build_descriptor(opcode=2, src=door_addr, dst=door_data)

        self.register_descriptor(64, desc)
        if not await self.send_apb_request(64):
            self.log.error("APB kick failed")
            return False
        if not await self.wait_descriptor_fetch():
            self.log.error("descriptor was never fetched")
            return False

        captured = await self._wait_ctrlwr_doorbell()
        if captured is None:
            self.log.error("ctrlwr engine never issued a write (routing failed)")
            return False
        addr, data = captured
        if addr != door_addr or data != door_data:
            self.log.error(f"doorbell mismatch: got addr=0x{addr:X} data=0x{data:X}, "
                           f"expected 0x{door_addr:X}/0x{door_data:X}")
            return False
        self.log.info(f"  ✓ Doorbell posted: addr=0x{addr:X} data=0x{data:X}")

        for _ in range(200):
            await self.wait_clocks(self.clk_name, 1)
            if self.is_scheduler_idle():
                self.log.info("✅ CTRL_WRITE doorbell test PASSED")
                return True
        self.log.error("scheduler did not return idle after ctrlwr")
        return False

    async def test_ctrl_read_gate(self) -> bool:
        """CTRL_READ descriptor routes to the real ctrlrd engine, which polls until
        (read & mask)==expected. Verify the gate holds off the chain (data engines
        NOT driven) through a mismatch, then completes on a match."""
        self.log.info("=== Control Read Gate Test ===")
        self.dut.cfg_ctrlrd_max_try.value = 16
        poll_addr = 0x3000
        expected = 0x1
        mask = 0x1
        desc = self._build_descriptor(opcode=1, src=poll_addr, dst=((mask << 32) | expected))

        self._set_poll_value(poll_addr, 0x0)     # first poll must NOT match
        self.register_descriptor(96, desc)
        if not await self.send_apb_request(96):
            self.log.error("APB kick failed")
            return False
        if not await self.wait_descriptor_fetch():
            self.log.error("descriptor was never fetched")
            return False

        # Free-running tick paces the engine's retries.
        self._tick_active = True
        tick_task = cocotb.start_soon(self._tick_generator())
        try:
            # First poll returns a NON-matching value -> engine must retry (gate held).
            addr1 = await self._wait_ctrlrd_poll()
            if addr1 != poll_addr:
                self.log.error(f"ctrlrd poll addr mismatch: 0x{addr1} vs 0x{poll_addr:X}")
                return False
            # Gate must be holding: data engines must NOT be driven for a control descriptor.
            if int(self.dut.sched_rd_valid.value) == 1 or int(self.dut.sched_wr_valid.value) == 1:
                self.log.error("data engine driven during CTRL_READ gate (should be held off)")
                return False
            self.log.info("  ✓ Gate held after mismatch (data engines idle)")

            # Next retry poll returns a MATCHING value -> gate opens.
            self._set_poll_value(poll_addr, 0x1)
            addr2 = await self._wait_ctrlrd_poll()
            if addr2 != poll_addr:
                self.log.error(f"ctrlrd retry poll addr mismatch: 0x{addr2} vs 0x{poll_addr:X}")
                return False

            for _ in range(300):
                await self.wait_clocks(self.clk_name, 1)
                if self.is_scheduler_idle():
                    self.log.info("✅ CTRL_READ gate test PASSED (opened on match)")
                    return True
            self.log.error("scheduler did not complete after ctrlrd match")
            return False
        finally:
            self._tick_active = False
            await self.wait_clocks(self.clk_name, 2)

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
        n0 = len(getattr(self, 'mon_packets', []))
        # A bare APB kick never completes here (nothing answers the descriptor
        # fetch), so no packet could ever appear; run one real descriptor through
        # the group -- the flow helper models the AXI side -- and then look.
        if not await self.test_basic_descriptor_flow(num_descriptors=1):
            self.log.error("MonBus events: the descriptor flow itself failed")
            return False
        await self.wait_clocks(self.clk_name, wait_cycles)
        pkts = list(getattr(self, 'mon_packets', []))[n0:]
        kinds = [p.get_packet_type_name() for p in pkts]
        events_received = len(pkts)
        self.log.info(f"MonBus events received: {events_received} {sorted(set(kinds))}")
        if events_received == 0 or 'PktTypeCompletion' not in kinds:
            self.log.error(f"MonBus events: expected at least one completion after a descriptor fetch, saw {kinds}")
            return False
        return True

    async def test_compl_enable_gate(self, wait_cycles: int = 100) -> bool:
        """SCHED_CONFIG.COMPL_EN (rapids ISSUE-005): with cfg_sched_compl_enable=0
        a descriptor flow completes normally and NO Completion packet reaches the
        group's monitor bus; with it back at 1 the same flow produces one. The
        OFF half is the point -- before the fix the bit did nothing."""
        self.log.info("=== COMPL_EN gate test ===")
        results = {}
        for enable in (0, 1):
            self.dut.cfg_sched_compl_enable.value = enable
            await self.wait_clocks(self.clk_name, 2)
            n0 = len(getattr(self, 'mon_packets', []))
            if not await self.test_basic_descriptor_flow(num_descriptors=1):
                self.log.error(f"COMPL_EN={enable}: the descriptor flow itself failed "
                               f"(a gated emitter must still be acknowledged)")
                return False
            await self.wait_clocks(self.clk_name, wait_cycles)
            pkts = list(getattr(self, 'mon_packets', []))[n0:]
            kinds = [p.get_packet_type_name() for p in pkts]
            n_compl = kinds.count('PktTypeCompletion')
            results[enable] = (len(pkts), n_compl)
            self.log.info(f"COMPL_EN={enable}: {len(pkts)} packet(s) {sorted(set(kinds))}, "
                          f"{n_compl} completion(s)")
        ok = True
        if results[0][1] != 0:
            self.log.error(f"COMPL_EN=0 still passed {results[0][1]} Completion packet(s) to the monitor bus")
            ok = False
        if results[1][1] == 0:
            self.log.error("COMPL_EN=1 produced no Completion packet (the ON state must still report)")
            ok = False
        return ok

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
