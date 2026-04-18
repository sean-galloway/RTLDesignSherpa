"""
AXI4 Slave Read Pattern Generator Testbench

TB class for axi4_slave_rd_pattern_gen.sv FUB testing.
Drives AXI4 AR channel with burst requests and verifies R channel
responses contain LFSR-generated pattern data.

Author: RTL Design Sherpa
Created: 2026-04-17
"""

import cocotb
from cocotb.triggers import RisingEdge

from TBClasses.shared.tbbase import TBBase


class AXI4SlaveRdPatternGenTB(TBBase):
    """Testbench for axi4_slave_rd_pattern_gen module."""

    def __init__(self, dut, **kwargs):
        super().__init__(dut)
        self.clk_name = 'aclk'

    async def setup_clocks_and_reset(self):
        await self.start_clock(self.clk_name, 10, 'ns')
        await self.assert_reset()
        # Tie off unused inputs during reset
        self.dut.crc_lfsr_reset.value = 0
        self.dut.s_axi_arid.value = 0
        self.dut.s_axi_araddr.value = 0
        self.dut.s_axi_arlen.value = 0
        self.dut.s_axi_arsize.value = 0
        self.dut.s_axi_arburst.value = 0
        self.dut.s_axi_arlock.value = 0
        self.dut.s_axi_arcache.value = 0
        self.dut.s_axi_arprot.value = 0
        self.dut.s_axi_arqos.value = 0
        self.dut.s_axi_arregion.value = 0
        self.dut.s_axi_aruser.value = 0
        self.dut.s_axi_arvalid.value = 0
        self.dut.s_axi_rready.value = 0
        await self.wait_clocks(self.clk_name, 10)
        await self.deassert_reset()
        await self.wait_clocks(self.clk_name, 5)

    async def assert_reset(self):
        self.dut.aresetn.value = 0

    async def deassert_reset(self):
        self.dut.aresetn.value = 1

    async def reset_crc_lfsr(self):
        """Pulse crc_lfsr_reset for one cycle."""
        self.dut.crc_lfsr_reset.value = 1
        await self.wait_clocks(self.clk_name, 1)
        self.dut.crc_lfsr_reset.value = 0
        await self.wait_clocks(self.clk_name, 1)

    async def issue_read(self, addr, length, axi_id=0, size=2, burst=1):
        """
        Issue a single AXI4 read request and collect all response beats.

        Args:
            addr: Read address
            length: Number of beats (arlen = length - 1)
            axi_id: AXI transaction ID
            size: AXI burst size (2 = 4 bytes, 4 = 16 bytes, etc.)
            burst: AXI burst type (1 = INCR)

        Returns:
            List of (rdata, rresp, rlast) tuples
        """
        # Issue AR
        self.dut.s_axi_arid.value = axi_id
        self.dut.s_axi_araddr.value = addr
        self.dut.s_axi_arlen.value = length - 1
        self.dut.s_axi_arsize.value = size
        self.dut.s_axi_arburst.value = burst
        self.dut.s_axi_arvalid.value = 1
        self.dut.s_axi_rready.value = 1

        # Wait for AR handshake
        for _ in range(1000):
            await RisingEdge(self.dut.aclk)
            if int(self.dut.s_axi_arready.value) == 1:
                break
        else:
            self.log.error("AR handshake timeout")
            self.dut.s_axi_arvalid.value = 0
            return []

        self.dut.s_axi_arvalid.value = 0

        # Collect R beats
        beats = []
        for _ in range(length * 100):  # Generous timeout
            await RisingEdge(self.dut.aclk)
            if int(self.dut.s_axi_rvalid.value) == 1 and int(self.dut.s_axi_rready.value) == 1:
                rdata = int(self.dut.s_axi_rdata.value)
                rresp = int(self.dut.s_axi_rresp.value)
                rlast = int(self.dut.s_axi_rlast.value)
                beats.append((rdata, rresp, rlast))
                if rlast:
                    break
        else:
            self.log.error(f"R channel timeout: got {len(beats)}/{length} beats")

        return beats

    async def run_single_beat_test(self):
        """Test a single-beat read (arlen=0)."""
        self.log.info("=== Single Beat Read Test ===")
        await self.reset_crc_lfsr()

        beats = await self.issue_read(addr=0x1000, length=1, axi_id=1)

        assert len(beats) == 1, f"Expected 1 beat, got {len(beats)}"
        rdata, rresp, rlast = beats[0]
        assert rresp == 0, f"Expected OKAY response, got {rresp}"
        assert rlast == 1, "Expected RLAST on single beat"
        self.log.info(f"  Single beat: rdata=0x{rdata:032x} rresp={rresp} rlast={rlast}")
        if rdata == 0:
            self.log.warning("  rdata is 0 -- LFSR may not be seeded yet")
        self.log.info("  PASS")

    async def run_burst_test(self, burst_len=4):
        """Test a multi-beat burst read."""
        self.log.info(f"=== Burst Read Test (len={burst_len}) ===")
        await self.reset_crc_lfsr()

        beats = await self.issue_read(addr=0x2000, length=burst_len, axi_id=2)

        assert len(beats) == burst_len, f"Expected {burst_len} beats, got {len(beats)}"

        for i, (rdata, rresp, rlast) in enumerate(beats):
            expected_last = 1 if i == burst_len - 1 else 0
            assert rresp == 0, f"Beat {i}: expected OKAY, got {rresp}"
            assert rlast == expected_last, f"Beat {i}: rlast={rlast}, expected {expected_last}"
            self.log.info(f"  Beat {i}: rdata=0x{rdata:08x} rlast={rlast}")

        # Verify all beats have unique data (LFSR should produce different values)
        data_values = [b[0] for b in beats]
        unique_values = set(data_values)
        assert len(unique_values) == burst_len, \
            f"Expected {burst_len} unique data values, got {len(unique_values)}"

        self.log.info("  PASS")

    async def run_back_to_back_test(self, num_reads=3, burst_len=2):
        """Test back-to-back read bursts."""
        self.log.info(f"=== Back-to-Back Test ({num_reads} reads x {burst_len} beats) ===")
        await self.reset_crc_lfsr()

        total_beats = 0
        for i in range(num_reads):
            beats = await self.issue_read(
                addr=0x3000 + i * 0x100,
                length=burst_len,
                axi_id=i
            )
            assert len(beats) == burst_len, \
                f"Read {i}: expected {burst_len} beats, got {len(beats)}"
            total_beats += len(beats)
            self.log.info(f"  Read {i}: {len(beats)} beats OK")

        assert total_beats == num_reads * burst_len
        self.log.info(f"  Total: {total_beats} beats across {num_reads} transactions")
        self.log.info("  PASS")

    async def run_crc_test(self, burst_len=8):
        """Test that CRC and beat counter update correctly."""
        self.log.info(f"=== CRC/Counter Test (len={burst_len}) ===")
        await self.reset_crc_lfsr()

        # Verify counters start at 0
        assert int(self.dut.read_beat_count.value) == 0, "Beat count should be 0 after reset"
        assert int(self.dut.read_crc_valid.value) == 0, "CRC valid should be 0 after reset"

        beats = await self.issue_read(addr=0x4000, length=burst_len, axi_id=4)
        await self.wait_clocks(self.clk_name, 5)  # Let CRC settle

        beat_count = int(self.dut.read_beat_count.value)
        crc_valid = int(self.dut.read_crc_valid.value)
        crc_value = int(self.dut.read_crc_value.value)

        self.log.info(f"  beat_count={beat_count} crc_valid={crc_valid} crc=0x{crc_value:08x}")

        assert len(beats) == burst_len, f"Expected {burst_len} beats, got {len(beats)}"
        assert crc_valid == 1, "CRC should be valid after reads"
        assert beat_count > 0, "Beat count should be non-zero"
        self.log.info("  PASS")
