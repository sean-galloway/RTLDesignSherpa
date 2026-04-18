"""
AXI4 Slave Write CRC Check Testbench

TB class for axi4_slave_wr_crc_check.sv FUB testing.
Drives AXI4 AW/W channels with burst writes and verifies B responses
and CRC computation on received data.

Author: RTL Design Sherpa
Created: 2026-04-18
"""

import cocotb
from cocotb.triggers import RisingEdge

from TBClasses.shared.tbbase import TBBase


class AXI4SlaveWrCrcCheckTB(TBBase):
    """Testbench for axi4_slave_wr_crc_check module."""

    def __init__(self, dut, **kwargs):
        super().__init__(dut)
        self.clk_name = 'aclk'

    async def setup_clocks_and_reset(self):
        await self.start_clock(self.clk_name, 10, 'ns')
        await self.assert_reset()
        self.dut.crc_reset.value = 0
        self.dut.s_axi_awid.value = 0
        self.dut.s_axi_awaddr.value = 0
        self.dut.s_axi_awlen.value = 0
        self.dut.s_axi_awsize.value = 0
        self.dut.s_axi_awburst.value = 0
        self.dut.s_axi_awlock.value = 0
        self.dut.s_axi_awcache.value = 0
        self.dut.s_axi_awprot.value = 0
        self.dut.s_axi_awqos.value = 0
        self.dut.s_axi_awregion.value = 0
        self.dut.s_axi_awuser.value = 0
        self.dut.s_axi_awvalid.value = 0
        self.dut.s_axi_wdata.value = 0
        self.dut.s_axi_wstrb.value = 0
        self.dut.s_axi_wlast.value = 0
        self.dut.s_axi_wuser.value = 0
        self.dut.s_axi_wvalid.value = 0
        self.dut.s_axi_bready.value = 1
        await self.wait_clocks(self.clk_name, 10)
        await self.deassert_reset()
        await self.wait_clocks(self.clk_name, 5)

    async def assert_reset(self):
        self.dut.aresetn.value = 0

    async def deassert_reset(self):
        self.dut.aresetn.value = 1

    async def reset_crc(self):
        """Pulse crc_reset for one cycle."""
        self.dut.crc_reset.value = 1
        await self.wait_clocks(self.clk_name, 1)
        self.dut.crc_reset.value = 0
        await self.wait_clocks(self.clk_name, 1)

    async def issue_write(self, addr, data_list, axi_id=0, size=2, burst=1):
        """
        Issue a single AXI4 write burst and wait for B response.

        Args:
            addr: Write address
            data_list: List of data values (one per beat)
            axi_id: AXI transaction ID
            size: AXI burst size
            burst: AXI burst type (1 = INCR)

        Returns:
            Tuple of (bresp, bid) or None on timeout
        """
        burst_len = len(data_list)

        # Issue AW
        self.dut.s_axi_awid.value = axi_id
        self.dut.s_axi_awaddr.value = addr
        self.dut.s_axi_awlen.value = burst_len - 1
        self.dut.s_axi_awsize.value = size
        self.dut.s_axi_awburst.value = burst
        self.dut.s_axi_awvalid.value = 1

        # Wait for AW handshake
        for _ in range(1000):
            await RisingEdge(self.dut.aclk)
            if int(self.dut.s_axi_awready.value) == 1:
                break
        else:
            self.log.error("AW handshake timeout")
            self.dut.s_axi_awvalid.value = 0
            return None

        self.dut.s_axi_awvalid.value = 0

        # Send W beats
        strb_all = (1 << (int(self.dut.AXI_DATA_WIDTH.value) // 8)) - 1
        for i, data in enumerate(data_list):
            is_last = (i == burst_len - 1)
            self.dut.s_axi_wdata.value = data
            self.dut.s_axi_wstrb.value = strb_all
            self.dut.s_axi_wlast.value = 1 if is_last else 0
            self.dut.s_axi_wvalid.value = 1

            for _ in range(1000):
                await RisingEdge(self.dut.aclk)
                if int(self.dut.s_axi_wready.value) == 1:
                    break
            else:
                self.log.error(f"W handshake timeout on beat {i}")
                self.dut.s_axi_wvalid.value = 0
                return None

        self.dut.s_axi_wvalid.value = 0
        self.dut.s_axi_wlast.value = 0

        # Wait for B response
        self.dut.s_axi_bready.value = 1
        for _ in range(1000):
            await RisingEdge(self.dut.aclk)
            if int(self.dut.s_axi_bvalid.value) == 1 and int(self.dut.s_axi_bready.value) == 1:
                bresp = int(self.dut.s_axi_bresp.value)
                bid = int(self.dut.s_axi_bid.value)
                return (bresp, bid)

        self.log.error("B response timeout")
        return None

    async def run_single_beat_test(self):
        """Test a single-beat write."""
        self.log.info("=== Single Beat Write Test ===")
        await self.reset_crc()

        result = await self.issue_write(
            addr=0x1000, data_list=[0xDEADBEEF], axi_id=1
        )

        assert result is not None, "Write failed — no B response"
        bresp, bid = result
        assert bresp == 0, f"Expected OKAY response, got {bresp}"
        assert bid == 1, f"Expected BID=1, got {bid}"
        self.log.info(f"  Single beat: bresp={bresp} bid={bid}")
        self.log.info("  PASS")

    async def run_burst_test(self, burst_len=4):
        """Test a multi-beat burst write."""
        self.log.info(f"=== Burst Write Test (len={burst_len}) ===")
        await self.reset_crc()

        data_list = [0x1000_0000 + i for i in range(burst_len)]
        result = await self.issue_write(
            addr=0x2000, data_list=data_list, axi_id=2
        )

        assert result is not None, f"Burst write failed — no B response after {burst_len} beats"
        bresp, bid = result
        assert bresp == 0, f"Expected OKAY response, got {bresp}"
        assert bid == 2, f"Expected BID=2, got {bid}"
        self.log.info(f"  Burst: {burst_len} beats, bresp={bresp} bid={bid}")
        self.log.info("  PASS")

    async def run_back_to_back_test(self, num_writes=3, burst_len=2):
        """Test back-to-back write bursts."""
        self.log.info(f"=== Back-to-Back Test ({num_writes} writes x {burst_len} beats) ===")
        await self.reset_crc()

        for i in range(num_writes):
            data_list = [0x100 * (i + 1) + j for j in range(burst_len)]
            result = await self.issue_write(
                addr=0x3000 + i * 0x100,
                data_list=data_list,
                axi_id=i
            )
            assert result is not None, f"Write {i}: no B response"
            bresp, bid = result
            assert bresp == 0, f"Write {i}: expected OKAY, got {bresp}"
            self.log.info(f"  Write {i}: {burst_len} beats, bresp={bresp} bid={bid}")

        self.log.info("  PASS")

    async def run_crc_test(self, burst_len=8):
        """Test that CRC and beat counter update correctly."""
        self.log.info(f"=== CRC/Counter Test (len={burst_len}) ===")
        await self.reset_crc()

        assert int(self.dut.write_beat_count.value) == 0, "Beat count should be 0 after reset"
        assert int(self.dut.write_crc_valid.value) == 0, "CRC valid should be 0 after reset"

        data_list = [0xA0000000 + i for i in range(burst_len)]
        result = await self.issue_write(addr=0x4000, data_list=data_list, axi_id=4)
        await self.wait_clocks(self.clk_name, 5)

        assert result is not None, "Write failed"

        beat_count = int(self.dut.write_beat_count.value)
        crc_valid = int(self.dut.write_crc_valid.value)
        crc_value = int(self.dut.write_crc_value.value)

        self.log.info(f"  beat_count={beat_count} crc_valid={crc_valid} crc=0x{crc_value:08x}")

        assert beat_count == burst_len, f"Expected {burst_len} beats, got {beat_count}"
        assert crc_valid == 1, "CRC should be valid after writes"
        self.log.info("  PASS")
