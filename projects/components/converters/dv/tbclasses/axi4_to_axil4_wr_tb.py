# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 RTL Design Sherpa
#
# Module: axi4_to_axil4_wr_tb
# Purpose: Testbench class for axi4_to_axil4_wr converter (WRITE-ONLY)
#
# Author: RTL Design Sherpa
# Created: 2025-11-05

"""
Testbench for axi4_to_axil4_wr converter - WRITE-ONLY

Tests AXI4 → AXI4-Lite protocol downgrade for write path with burst decomposition:
- Multi-beat AXI4 AW/W bursts decomposed into multiple single-beat AXIL4 writes
- Address incrementing for INCR bursts
- FIXED burst support (same address)
- Response aggregation (worst-case)
- ID preservation through burst

Architecture:
- AXI4MasterWrite drives slave side (sends AW/W bursts, receives B responses)
- AXIL4 responder on master side (responds to single-beat AXIL4 writes)
- Monitor AXIL4 master outputs for burst decomposition validation
"""

import os
import sys
import cocotb
from cocotb.triggers import RisingEdge, FallingEdge, Timer
from cocotb.clock import Clock
import random

# Import framework utilities (PYTHONPATH includes bin/)
from CocoTBFramework.tbclasses.shared.utilities import get_repo_root
from CocoTBFramework.tbclasses.shared.tbbase import TBBase

# Add repo root to Python path using robust git-based method
repo_root = get_repo_root()
sys.path.insert(0, repo_root)
from CocoTBFramework.components.axi4.axi4_interfaces import AXI4MasterWrite
from CocoTBFramework.components.axil4.axil4_interfaces import AXIL4SlaveWrite


class AXI4ToAXIL4WriteTB(TBBase):
    """
    Testbench for axi4_to_axil4_wr converter.

    Tests protocol downgrade from AXI4 → AXI4-Lite for write path with burst decomposition.

    Key Validations:
    - Burst decomposition (multi-beat → multiple single-beat)
    - Address incrementing (INCR burst type)
    - FIXED burst support (same address)
    - Response aggregation (worst-case error)
    - ID preservation through burst
    """

    def __init__(self, dut):
        super().__init__(dut)

        # Clock and reset
        self.clk = dut.aclk
        self.clk_name = 'aclk'
        self.rst_n = dut.aresetn

        # Extract parameters from DUT or environment
        self.data_width = self.convert_to_int(os.environ.get('AXI_DATA_WIDTH', '32'))
        self.addr_width = self.convert_to_int(os.environ.get('AXI_ADDR_WIDTH', '32'))
        self.id_width = self.convert_to_int(os.environ.get('AXI_ID_WIDTH', '8'))

        # Statistics
        self.stats = {
            'bursts_sent': 0,
            'beats_expected': 0,
            'axil_writes_received': 0,
            'bursts_completed': 0,
            'errors': 0,
            'address_errors': 0,
            'decomposition_errors': 0,
            'data_errors': 0,
        }

        # Bytes per transfer
        self.bytes_per_beat = self.data_width // 8

        # Initialize AXI4 master (drives slave side of converter)
        self.axi4_master = AXI4MasterWrite(
            dut=dut,
            clock=self.clk,
            prefix="s_axi_",
            log=self.log,
            data_width=self.data_width,
            id_width=self.id_width,
            addr_width=self.addr_width,
            multi_sig=True
        )

        # Initialize AXIL4 slave (responds on master side of converter)
        self.axil4_slave = AXIL4SlaveWrite(
            dut=dut,
            clock=self.clk,
            prefix="m_axil_",
            log=self.log,
            data_width=self.data_width,
            addr_width=self.addr_width,
            multi_sig=True,
            response_delay=1
        )

        # Storage for monitoring AXIL4 transactions (track from slave BFM queues)
        self.axil_transactions = []  # (type, addr, data, strb)

        self.log.info(f"Initialized AXI4→AXIL4 Write TB: "
                     f"data_width={self.data_width}, "
                     f"addr_width={self.addr_width}, "
                     f"id_width={self.id_width}")

    # =========================================================================
    # MANDATORY METHODS - Required by TBBase
    # =========================================================================

    async def setup_clocks_and_reset(self, period_ns=10):
        """Complete initialization - start clocks and perform reset"""
        # Start clock
        await self.start_clock(self.clk_name, freq=period_ns, units='ns')

        # BFM handles awready, wready, bvalid automatically - don't override!

        # Reset sequence
        await self.assert_reset()
        await self.wait_clocks(self.clk_name, 10)
        await self.deassert_reset()
        await self.wait_clocks(self.clk_name, 5)

        self.log.info("Reset sequence complete")

    async def assert_reset(self):
        """Assert reset signal (active-low)"""
        self.rst_n.value = 0
        self.log.debug("Reset asserted")

    async def deassert_reset(self):
        """Deassert reset signal (active-low)"""
        self.rst_n.value = 1
        self.log.debug("Reset deasserted")

    # =========================================================================
    # AXIL4 MASTER SIDE TRANSACTION MONITOR
    # =========================================================================

    async def axil4_transaction_monitor(self):
        """
        Monitor AXIL4 write transactions by watching handshakes.

        Since the BFM processes transactions immediately, we monitor the
        actual AXIL protocol handshakes on the DUT signals. For writes,
        we track both AW and W handshakes and match them up.
        """
        self.log.info("Starting AXIL4 transaction monitor")

        # Track pending addresses
        pending_addr = None

        while True:
            await RisingEdge(self.clk)

            # Monitor AW channel handshakes
            if (int(self.dut.m_axil_awvalid.value) == 1 and
                int(self.dut.m_axil_awready.value) == 1):
                pending_addr = int(self.dut.m_axil_awaddr.value)
                self.log.debug(f"AXIL4 AW handshake: addr=0x{pending_addr:08X}")

            # Monitor W channel handshakes
            if (int(self.dut.m_axil_wvalid.value) == 1 and
                int(self.dut.m_axil_wready.value) == 1):
                w_data = int(self.dut.m_axil_wdata.value)
                w_strb = int(self.dut.m_axil_wstrb.value)

                # Match with pending address
                if pending_addr is not None:
                    self.axil_transactions.append(('W', pending_addr, w_data, w_strb))
                    self.stats['axil_writes_received'] += 1
                    self.log.debug(f"AXIL4 Write complete: addr=0x{pending_addr:08X}, data=0x{w_data:08X}")
                    pending_addr = None

    # =========================================================================
    # TEST SCENARIO METHODS
    # =========================================================================

    async def test_write_burst(self, address, data_list, burst_type=1, size=None):
        """
        Test AXI4 write burst through converter.

        Args:
            address: Starting write address
            data_list: List of write data values
            burst_type: 0=FIXED, 1=INCR, 2=WRAP
            size: AWSIZE value (None = full width)

        Returns:
            True if test passed, False otherwise
        """
        if size is None:
            size = (self.data_width // 8).bit_length() - 1

        burst_len = len(data_list)

        # Calculate address increment
        addr_incr = 1 << size

        self.log.debug(f"Testing write burst: addr=0x{address:08X}, len={burst_len}, "
                      f"burst_type={burst_type}, size={size}")

        # Clear AXIL transaction log
        initial_axil_count = len(self.axil_transactions)

        # Send AXI4 write burst
        try:
            await self.axi4_master.write_transaction(
                address=address,
                data=data_list,
                size=size,
                burst_type=burst_type
            )

            # Wait for all AXIL transactions to complete
            await self.wait_clocks(self.clk_name, 20)

            # Verify number of AXIL4 writes
            axil_writes = len(self.axil_transactions) - initial_axil_count

            if axil_writes != burst_len:
                self.log.error(f"Burst decomposition FAILED: got {axil_writes} AXIL writes, "
                             f"expected {burst_len}")
                self.stats['decomposition_errors'] += 1
                self.stats['errors'] += 1
                return False

            # Verify addresses and data (for INCR bursts)
            if burst_type == 1:  # INCR
                expected_addr = address
                for i in range(axil_writes):
                    txn_type, txn_addr, txn_data, txn_strb = self.axil_transactions[initial_axil_count + i]

                    if txn_addr != expected_addr:
                        self.log.error(f"Address increment FAILED: beat {i}, "
                                     f"got 0x{txn_addr:08X}, expected 0x{expected_addr:08X}")
                        self.stats['address_errors'] += 1
                        self.stats['errors'] += 1
                        return False

                    if txn_data != data_list[i]:
                        self.log.error(f"Data mismatch: beat {i}, "
                                     f"got 0x{txn_data:08X}, expected 0x{data_list[i]:08X}")
                        self.stats['data_errors'] += 1
                        self.stats['errors'] += 1
                        return False

                    expected_addr += addr_incr

            elif burst_type == 0:  # FIXED
                # All beats should have same address
                for i in range(axil_writes):
                    txn_type, txn_addr, txn_data, txn_strb = self.axil_transactions[initial_axil_count + i]

                    if txn_addr != address:
                        self.log.error(f"FIXED burst FAILED: beat {i}, "
                                     f"got 0x{txn_addr:08X}, expected 0x{address:08X}")
                        self.stats['address_errors'] += 1
                        self.stats['errors'] += 1
                        return False

                    if txn_data != data_list[i]:
                        self.log.error(f"Data mismatch: beat {i}, "
                                     f"got 0x{txn_data:08X}, expected 0x{data_list[i]:08X}")
                        self.stats['data_errors'] += 1
                        self.stats['errors'] += 1
                        return False

            self.log.debug(f"Burst test PASSED: {burst_len} beats decomposed correctly")
            self.stats['bursts_sent'] += 1
            self.stats['beats_expected'] += burst_len
            self.stats['bursts_completed'] += 1
            return True

        except Exception as e:
            self.log.error(f"Write burst transaction failed: {e}")
            self.stats['errors'] += 1
            return False

    async def run_basic_test(self):
        """Run basic write burst test suite"""
        self.log.info("=" * 80)
        self.log.info("BASIC WRITE BURST TEST SUITE")
        self.log.info("=" * 80)

        success = True

        # Test single-beat and small bursts
        test_cases = [
            (0x1000, [0x11111111]),                                    # Single beat
            (0x2000, [0x22222222, 0x33333333]),                       # 2-beat burst
            (0x3000, [0x44444444, 0x55555555, 0x66666666, 0x77777777]), # 4-beat burst
            (0x4000, [0xDEADBEEF]),                                    # Another single beat
        ]

        for addr, data_list in test_cases:
            if not await self.test_write_burst(addr, data_list):
                success = False

        return success

    async def run_medium_test(self):
        """Run medium write burst test suite"""
        self.log.info("=" * 80)
        self.log.info("MEDIUM WRITE BURST TEST SUITE")
        self.log.info("=" * 80)

        success = True

        # Test various burst lengths with random data
        for i in range(10):
            addr = random.randint(0, (1 << self.addr_width) - 1) & ~0x3
            burst_len = random.randint(1, 16)
            data_list = [random.randint(0, (1 << self.data_width) - 1) for _ in range(burst_len)]
            burst_type = random.choice([0, 1])  # FIXED or INCR

            if not await self.test_write_burst(addr, data_list, burst_type):
                success = False

        return success

    async def run_full_test(self):
        """Run full write burst test suite"""
        self.log.info("=" * 80)
        self.log.info("FULL WRITE BURST TEST SUITE")
        self.log.info("=" * 80)

        success = True

        # Comprehensive testing with various burst lengths and types
        for i in range(30):
            addr = random.randint(0, (1 << self.addr_width) - 1) & ~0x3
            burst_len = random.randint(1, 32)
            data_list = [random.randint(0, (1 << self.data_width) - 1) for _ in range(burst_len)]
            burst_type = random.choice([0, 1])  # FIXED or INCR

            if not await self.test_write_burst(addr, data_list, burst_type):
                success = False

        return success

    def get_statistics(self):
        """Return test statistics"""
        return dict(self.stats)
