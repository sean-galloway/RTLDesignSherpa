"""
Testbench for apbtodescr (APB-to-Descriptor Router)

This testbench verifies the address decode and routing logic for the APB
kick-off registers to descriptor engine APB ports.
"""

import cocotb
from cocotb.triggers import RisingEdge, Timer
from cocotb.clock import Clock
import random

import sys
import os

# Add framework to path
sys.path.append(os.path.join(os.path.dirname(__file__), '../../../../bin'))

from CocoTBFramework.tbclasses.shared.tbbase import TBBase


class APBToDescrTB(TBBase):
    """Testbench for apbtodescr module"""

    def __init__(self, dut):
        """Initialize testbench

        Args:
            dut: DUT instance from cocotb
        """
        super().__init__(dut)

        # Clock and reset
        self.clk = dut.clk
        self.clk_name = 'clk'
        self.rst_n = dut.rst_n

        # Get parameters
        self.ADDR_WIDTH = int(os.environ.get('ADDR_WIDTH', '32'))
        self.DATA_WIDTH = int(os.environ.get('DATA_WIDTH', '32'))
        self.NUM_CHANNELS = int(os.environ.get('NUM_CHANNELS', '8'))

        # APB CMD interface
        self.apb_cmd_valid = dut.apb_cmd_valid
        self.apb_cmd_ready = dut.apb_cmd_ready
        self.apb_cmd_addr = dut.apb_cmd_addr
        self.apb_cmd_wdata = dut.apb_cmd_wdata
        self.apb_cmd_write = dut.apb_cmd_write

        # APB RSP interface
        self.apb_rsp_valid = dut.apb_rsp_valid
        self.apb_rsp_ready = dut.apb_rsp_ready
        self.apb_rsp_rdata = dut.apb_rsp_rdata
        self.apb_rsp_error = dut.apb_rsp_error

        # Descriptor engine APB outputs
        self.desc_apb_valid = dut.desc_apb_valid
        self.desc_apb_ready = dut.desc_apb_ready
        self.desc_apb_addr = dut.desc_apb_addr

        # Integration control signal
        self.apb_descriptor_kickoff_hit = dut.apb_descriptor_kickoff_hit

        self.log.info(f"APBToDescrTB initialized:")
        self.log.info(f"  NUM_CHANNELS = {self.NUM_CHANNELS}")

    async def setup_clocks_and_reset(self):
        """Complete initialization - clocks and reset"""
        # Start clock
        await self.start_clock(self.clk_name, freq=10, units='ns')

        # Initialize all inputs
        self.apb_cmd_valid.value = 0
        self.apb_cmd_addr.value = 0
        self.apb_cmd_wdata.value = 0
        self.apb_cmd_write.value = 0
        self.apb_rsp_ready.value = 1  # Always ready to accept responses

        # Initialize descriptor engine ready signals (all ready)
        self.desc_apb_ready.value = (1 << self.NUM_CHANNELS) - 1

        # Reset sequence
        await self.assert_reset()
        await self.wait_clocks(self.clk_name, 10)
        await self.deassert_reset()
        await self.wait_clocks(self.clk_name, 5)

    async def assert_reset(self):
        """Assert reset signal"""
        self.rst_n.value = 0

    async def deassert_reset(self):
        """Deassert reset signal"""
        self.rst_n.value = 1

    async def apb_write(self, addr, data, expect_error=False):
        """Perform APB write transaction

        Args:
            addr: Target address
            data: Write data (32-bit descriptor address)
            expect_error: If True, expect error response

        Returns:
            Tuple (success, error_flag, cycles, kickoff_hit_asserted)
        """
        await self.wait_clocks(self.clk_name, 1)

        # Verify kickoff_hit initially low
        if int(self.apb_descriptor_kickoff_hit.value) != 0:
            self.log.warning(f"kickoff_hit already asserted before transaction start")

        # Drive CMD interface
        self.apb_cmd_valid.value = 1
        self.apb_cmd_addr.value = addr
        self.apb_cmd_wdata.value = data
        self.apb_cmd_write.value = 1

        # Wait for cmd_ready
        cmd_start_cycle = 0
        while int(self.apb_cmd_ready.value) == 0:
            await self.wait_clocks(self.clk_name, 1)
            cmd_start_cycle += 1
            if cmd_start_cycle > 100:
                raise TimeoutError(f"APB CMD timeout at addr 0x{addr:08X}")

        await self.wait_clocks(self.clk_name, 1)

        # Clear CMD
        self.apb_cmd_valid.value = 0

        # Track if kickoff_hit was asserted during transaction
        kickoff_hit_seen = False

        # Wait for RSP
        rsp_start_cycle = 0
        while int(self.apb_rsp_valid.value) == 0:
            # Check kickoff_hit during ROUTE/RESPOND phases
            if int(self.apb_descriptor_kickoff_hit.value) == 1:
                kickoff_hit_seen = True

            await self.wait_clocks(self.clk_name, 1)
            rsp_start_cycle += 1
            if rsp_start_cycle > 100:
                raise TimeoutError(f"APB RSP timeout at addr 0x{addr:08X}")

        # Capture response and kickoff_hit state
        error_flag = int(self.apb_rsp_error.value)
        kickoff_hit_at_response = int(self.apb_descriptor_kickoff_hit.value)

        if kickoff_hit_at_response == 1:
            kickoff_hit_seen = True

        await self.wait_clocks(self.clk_name, 1)

        # Verify kickoff_hit deasserted after transaction
        kickoff_hit_after = int(self.apb_descriptor_kickoff_hit.value)
        if kickoff_hit_after != 0:
            self.log.warning(f"kickoff_hit still asserted after transaction complete")

        total_cycles = cmd_start_cycle + rsp_start_cycle + 3

        if expect_error:
            success = (error_flag == 1)
        else:
            success = (error_flag == 0)

        self.log.info(f"APB write 0x{data:08X} to 0x{addr:08X}: "
                     f"error={error_flag}, cycles={total_cycles}, kickoff_hit={kickoff_hit_seen}")

        return (success, error_flag, total_cycles, kickoff_hit_seen)

    async def apb_read(self, addr):
        """Perform APB read transaction (should return error)

        Args:
            addr: Target address

        Returns:
            Tuple (error_flag, cycles, kickoff_hit_asserted)
        """
        await self.wait_clocks(self.clk_name, 1)

        # Drive CMD interface
        self.apb_cmd_valid.value = 1
        self.apb_cmd_addr.value = addr
        self.apb_cmd_wdata.value = 0
        self.apb_cmd_write.value = 0  # Read

        # Wait for cmd_ready
        cmd_start_cycle = 0
        while int(self.apb_cmd_ready.value) == 0:
            await self.wait_clocks(self.clk_name, 1)
            cmd_start_cycle += 1
            if cmd_start_cycle > 100:
                raise TimeoutError(f"APB CMD timeout at addr 0x{addr:08X}")

        await self.wait_clocks(self.clk_name, 1)

        # Clear CMD
        self.apb_cmd_valid.value = 0

        # Track if kickoff_hit was asserted during transaction (should NOT be for reads)
        kickoff_hit_seen = False

        # Wait for RSP
        rsp_start_cycle = 0
        while int(self.apb_rsp_valid.value) == 0:
            # Check kickoff_hit during transaction (should remain low for read error)
            if int(self.apb_descriptor_kickoff_hit.value) == 1:
                kickoff_hit_seen = True

            await self.wait_clocks(self.clk_name, 1)
            rsp_start_cycle += 1
            if rsp_start_cycle > 100:
                raise TimeoutError(f"APB RSP timeout at addr 0x{addr:08X}")

        # Capture response
        error_flag = int(self.apb_rsp_error.value)
        kickoff_hit_at_response = int(self.apb_descriptor_kickoff_hit.value)

        if kickoff_hit_at_response == 1:
            kickoff_hit_seen = True

        await self.wait_clocks(self.clk_name, 1)

        total_cycles = cmd_start_cycle + rsp_start_cycle + 3

        self.log.info(f"APB read from 0x{addr:08X}: error={error_flag}, "
                     f"cycles={total_cycles}, kickoff_hit={kickoff_hit_seen}")

        return (error_flag, total_cycles, kickoff_hit_seen)

    async def set_desc_ready(self, channel_mask):
        """Set descriptor engine ready mask

        Args:
            channel_mask: Bit mask for ready channels
        """
        self.desc_apb_ready.value = channel_mask & ((1 << self.NUM_CHANNELS) - 1)
        await self.wait_clocks(self.clk_name, 1)

    async def test_basic_write(self, channel):
        """Test basic write to a single channel

        Args:
            channel: Channel ID (0-7)

        Returns:
            True if test passed
        """
        self.log.info(f"Testing basic write to channel {channel}")

        # Calculate address (channel offset only, no base address)
        addr = channel * 4
        data = 0x1000_0000 + (channel * 0x100)

        # Perform write
        success, error, cycles, kickoff_hit = await self.apb_write(addr, data)

        if not success:
            self.log.error(f"Channel {channel} write failed with error={error}")
            return False

        # Verify kickoff_hit was asserted (valid kick-off transaction)
        if not kickoff_hit:
            self.log.error(f"Channel {channel} kickoff_hit not asserted during transaction")
            return False

        # Note: desc_apb_valid and desc_apb_addr are transient signals during ROUTE state
        # After transaction completes (RESPOND → IDLE), they are deasserted
        # The apb_descriptor_kickoff_hit signal confirms correct routing occurred

        self.log.info(f"✓ Channel {channel} basic write passed (kickoff_hit confirmed)")
        return True

    async def test_backpressure(self, channel, stall_cycles):
        """Test write with descriptor engine back-pressure

        Args:
            channel: Channel ID (0-7)
            stall_cycles: Number of cycles to stall

        Returns:
            True if test passed
        """
        self.log.info(f"Testing back-pressure on channel {channel} ({stall_cycles} cycles)")

        # Make channel not ready
        ready_mask = ((1 << self.NUM_CHANNELS) - 1) & ~(1 << channel)
        await self.set_desc_ready(ready_mask)

        # Start write transaction in background
        addr = channel * 4
        data = 0x2000_0000 + (channel * 0x100)

        # Start write (will block)
        write_task = cocotb.start_soon(self.apb_write(addr, data))

        # Wait for stall cycles
        for i in range(stall_cycles):
            await self.wait_clocks(self.clk_name, 1)
            # Verify still waiting (apb_rsp_valid should be low)
            if int(self.apb_rsp_valid.value) == 1:
                self.log.error(f"Response arrived too early at cycle {i}")
                return False

        # Make channel ready
        await self.set_desc_ready((1 << self.NUM_CHANNELS) - 1)

        # Wait for write to complete
        success, error, total_cycles, kickoff_hit = await write_task

        if not success:
            self.log.error(f"Channel {channel} write with back-pressure failed")
            return False

        # Verify kickoff_hit was asserted (valid kick-off transaction)
        if not kickoff_hit:
            self.log.error(f"Channel {channel} kickoff_hit not asserted during back-pressure test")
            return False

        # Verify total cycles includes stall
        # Cycle breakdown: ~2 cycles overhead (CMD + RESPOND) + stall_cycles
        min_expected = 2 + stall_cycles
        if total_cycles < min_expected:
            self.log.error(f"Back-pressure cycles incorrect: got {total_cycles}, "
                          f"expected >= {min_expected}")
            return False

        self.log.info(f"✓ Channel {channel} back-pressure test passed ({total_cycles} cycles, "
                     f"{total_cycles - 2} cycles stalled)")
        return True

    async def test_out_of_range(self):
        """Test write to out-of-range address (should error)

        Returns:
            True if test passed
        """
        self.log.info("Testing out-of-range address")

        # Try address beyond last channel (0x100 is beyond 0x1C)
        addr = 0x100  # Way beyond CH7
        data = 0xDEAD_BEEF

        success, error, cycles, kickoff_hit = await self.apb_write(addr, data, expect_error=True)

        if not success:
            self.log.error(f"Out-of-range test failed: error flag not set")
            return False

        # Verify kickoff_hit was NOT asserted (error transaction, not valid kick-off)
        if kickoff_hit:
            self.log.error(f"Out-of-range: kickoff_hit should NOT be asserted for error transaction")
            return False

        self.log.info(f"✓ Out-of-range address test passed (error={error})")
        return True

    async def test_read_error(self):
        """Test read request (should return error)

        Returns:
            True if test passed
        """
        self.log.info("Testing read request (not supported)")

        addr = 0x00  # CH0

        error, cycles, kickoff_hit = await self.apb_read(addr)

        if error != 1:
            self.log.error(f"Read error test failed: error flag not set (got {error})")
            return False

        # Verify kickoff_hit was NOT asserted (read error, not valid kick-off)
        if kickoff_hit:
            self.log.error(f"Read error: kickoff_hit should NOT be asserted for read transaction")
            return False

        self.log.info(f"✓ Read error test passed")
        return True

    async def test_all_channels(self):
        """Test writes to all 8 channels sequentially

        Returns:
            True if all passed
        """
        self.log.info("Testing all channels sequentially")

        for ch in range(self.NUM_CHANNELS):
            if not await self.test_basic_write(ch):
                return False
            await self.wait_clocks(self.clk_name, 2)

        self.log.info(f"✓ All {self.NUM_CHANNELS} channels tested successfully")
        return True
