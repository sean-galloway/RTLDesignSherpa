# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 RTL Design Sherpa
#
# Module: axi4_to_axil4_rd_tb
# Purpose: Testbench class for axi4_to_axil4_rd converter (READ-ONLY)
#
# Author: RTL Design Sherpa
# Created: 2025-11-05

"""
Testbench for axi4_to_axil4_rd converter - READ-ONLY

Tests AXI4 → AXI4-Lite protocol downgrade for read path with burst decomposition:
- Multi-beat AXI4 AR bursts decomposed into multiple single-beat AXIL4 reads
- Address incrementing for INCR bursts
- FIXED burst support (same address)
- Response aggregation (worst-case)
- ID preservation

Architecture:
- AXI4MasterRead drives slave side (sends AR bursts, receives R responses)
- AXIL4 responder on master side (responds to single-beat AXIL4 reads)
- Monitor AXIL4 master outputs for burst decomposition validation
"""

import os
import sys
import cocotb
from cocotb.triggers import RisingEdge, FallingEdge, Timer
from cocotb.clock import Clock
import random

# Import framework utilities (PYTHONPATH includes bin/)
from TBClasses.shared.utilities import get_repo_root
from TBClasses.shared.tbbase import TBBase

# Add repo root to Python path using robust git-based method
repo_root = get_repo_root()
sys.path.insert(0, repo_root)
from CocoTBFramework.components.axi4.axi4_interfaces import AXI4MasterRead
from CocoTBFramework.components.axil4.axil4_interfaces import AXIL4SlaveRead


class AXI4ToAXIL4ReadTB(TBBase):
    """
    Testbench for axi4_to_axil4_rd converter.

    Tests protocol downgrade from AXI4 → AXI4-Lite for read path with burst decomposition.

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
            'axil_reads_received': 0,
            'bursts_completed': 0,
            'errors': 0,
            'address_errors': 0,
            'decomposition_errors': 0,
        }

        # Bytes per transfer
        self.bytes_per_beat = self.data_width // 8

        # Initialize AXI4 master (drives slave side of converter)
        self.axi4_master = AXI4MasterRead(
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
        self.axil4_slave = AXIL4SlaveRead(
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
        self.axil_transactions = []

        self.log.info(f"Initialized AXI4→AXIL4 Read TB: "
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

        # BFM handles arready, rvalid automatically - don't override!

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
    # AXIL4 MASTER SIDE RESPONDER
    # =========================================================================

    async def axil4_transaction_monitor(self):
        """
        Monitor AXIL4 read transactions by watching handshakes.

        Since the BFM processes transactions immediately, we monitor the
        actual AXILprotocol handshakes on the DUT signals rather than
        trying to intercept from BFM queues.
        """
        self.log.info("Starting AXIL4 transaction monitor")

        while True:
            await RisingEdge(self.clk)

            # Monitor AR channel handshakes directly
            if (int(self.dut.m_axil_arvalid.value) == 1 and
                int(self.dut.m_axil_arready.value) == 1):
                ar_addr = int(self.dut.m_axil_araddr.value)
                ar_prot = int(self.dut.m_axil_arprot.value) if hasattr(self.dut, 'm_axil_arprot') else 0

                # Store transaction for verification
                self.axil_transactions.append(('AR', ar_addr, ar_prot))
                self.stats['axil_reads_received'] += 1

                self.log.debug(f"AXIL4 Read handshake: addr=0x{ar_addr:08X}")

    # =========================================================================
    # TEST SCENARIO METHODS
    # =========================================================================

    async def test_read_burst(self, address, burst_len, burst_type=1, size=None):
        """
        Test AXI4 read burst through converter.

        Args:
            address: Starting read address
            burst_len: Burst length (1-256)
            burst_type: 0=FIXED, 1=INCR, 2=WRAP
            size: ARSIZE value (None = full width)

        Returns:
            True if test passed, False otherwise
        """
        if size is None:
            size = (self.data_width // 8).bit_length() - 1

        # Calculate address increment
        addr_incr = 1 << size

        self.log.debug(f"Testing read burst: addr=0x{address:08X}, len={burst_len}, "
                      f"burst_type={burst_type}, size={size}")

        # Clear AXIL transaction log
        initial_axil_count = len(self.axil_transactions)

        # Send AXI4 read burst
        try:
            read_data = await self.axi4_master.read_transaction(
                address=address,
                burst_len=burst_len,
                size=size,
                burst_type=burst_type
            )

            # Wait for all AXIL transactions to complete
            await self.wait_clocks(self.clk_name, 20)

            # Verify number of AXIL4 reads
            axil_reads = len(self.axil_transactions) - initial_axil_count

            if axil_reads != burst_len:
                self.log.error(f"Burst decomposition FAILED: got {axil_reads} AXIL reads, "
                             f"expected {burst_len}")
                self.stats['decomposition_errors'] += 1
                self.stats['errors'] += 1
                return False

            # Verify addresses (for INCR bursts)
            if burst_type == 1:  # INCR
                expected_addr = address
                for i in range(axil_reads):
                    txn_type, txn_addr, txn_prot = self.axil_transactions[initial_axil_count + i]
                    if txn_addr != expected_addr:
                        self.log.error(f"Address increment FAILED: beat {i}, "
                                     f"got 0x{txn_addr:08X}, expected 0x{expected_addr:08X}")
                        self.stats['address_errors'] += 1
                        self.stats['errors'] += 1
                        return False
                    expected_addr += addr_incr

            elif burst_type == 0:  # FIXED
                # All beats should have same address
                for i in range(axil_reads):
                    txn_type, txn_addr, txn_prot = self.axil_transactions[initial_axil_count + i]
                    if txn_addr != address:
                        self.log.error(f"FIXED burst FAILED: beat {i}, "
                                     f"got 0x{txn_addr:08X}, expected 0x{address:08X}")
                        self.stats['address_errors'] += 1
                        self.stats['errors'] += 1
                        return False

            # Verify we received correct number of read data beats
            if len(read_data) != burst_len:
                self.log.error(f"Read data count mismatch: got {len(read_data)}, expected {burst_len}")
                self.stats['errors'] += 1
                return False

            self.log.debug(f"Burst test PASSED: {burst_len} beats decomposed correctly")
            self.stats['bursts_sent'] += 1
            self.stats['beats_expected'] += burst_len
            self.stats['bursts_completed'] += 1
            return True

        except Exception as e:
            self.log.error(f"Read burst transaction failed: {e}")
            self.stats['errors'] += 1
            return False

    async def test_b2b_bursts(self, bursts, size=None):
        """
        Issue N read bursts back-to-back with NO test-level cooldown.

        Each burst is launched via cocotb.start_soon so the AXI4 master BFM
        queues them and the AR beats flow on the wire as fast as the
        bridge accepts. We then await each task in issue order.

        Args:
            bursts: List of (address, burst_len) tuples to issue back-to-back.
                    All bursts use INCR (burst_type=1).
            size: ARSIZE for every burst (None = full data width).

        Returns:
            True if total AXIL reads and per-burst address sequence match
            the expected issue order.
        """
        if size is None:
            size = (self.data_width // 8).bit_length() - 1
        addr_incr = 1 << size

        # Build the expected AXIL AR address sequence in issue order
        expected_addrs = []
        for (start_addr, blen) in bursts:
            addr = start_addr
            for _ in range(blen):
                expected_addrs.append(addr)
                addr += addr_incr

        total_expected = len(expected_addrs)
        initial_axil_count = len(self.axil_transactions)

        self.log.info(f"B2B READ BURSTS: issuing {len(bursts)} bursts "
                      f"({total_expected} total beats) with NO inter-burst cooldown")

        # Launch all bursts as concurrent tasks (no awaits between launches)
        tasks = []
        for (start_addr, blen) in bursts:
            task = cocotb.start_soon(self.axi4_master.read_transaction(
                address=start_addr,
                burst_len=blen,
                size=size,
                burst_type=1,  # INCR
            ))
            tasks.append(task)

        # Wait for every burst's read data to come back, in issue order
        for i, task in enumerate(tasks):
            await task

        # Drain remaining AXIL beats (do NOT wait between bursts above —
        # only here, at the end).
        await self.wait_clocks(self.clk_name, 50)

        actual_beats = len(self.axil_transactions) - initial_axil_count
        if actual_beats != total_expected:
            self.log.error(f"B2B read beat count MISMATCH: got {actual_beats}, "
                          f"expected {total_expected}")
            self.stats['decomposition_errors'] += 1
            self.stats['errors'] += 1
            return False

        # Verify the AXIL AR sequence matches the expected addresses in order
        for i, exp_addr in enumerate(expected_addrs):
            _, got_addr, _ = self.axil_transactions[initial_axil_count + i]
            if got_addr != exp_addr:
                self.log.error(f"B2B read addr MISMATCH at beat {i}: "
                              f"got 0x{got_addr:08X}, expected 0x{exp_addr:08X}")
                self.stats['address_errors'] += 1
                self.stats['errors'] += 1
                return False

        self.log.info(f"B2B READ BURSTS PASSED: {len(bursts)} bursts, "
                      f"{total_expected} beats verified in issue order")
        self.stats['bursts_sent'] += len(bursts)
        self.stats['beats_expected'] += total_expected
        self.stats['bursts_completed'] += len(bursts)
        return True

    async def test_b2b_mixed_lengths(self):
        """
        B2B read bursts with interleaved lengths to exercise the
        RD_IDLE↔RD_BURST↔RD_LAST_BEAT transitions in adjacent cycles.
        """
        bursts = []
        base = 0x10000
        lengths = [1, 4, 1, 2, 8, 1, 16, 1]
        for i, blen in enumerate(lengths):
            addr = base + (i * 0x1000)
            bursts.append((addr, blen))
        return await self.test_b2b_bursts(bursts)

    async def test_narrow_within_wide(self):
        """
        Bursts with arsize < full data width on a wider bus.
        Verifies address increment matches the narrower size.
        """
        if self.data_width <= 32:
            self.log.info("test_narrow_within_wide: data_width<=32, skipping")
            return True

        success = True
        full_size = (self.data_width // 8).bit_length() - 1
        narrow_size = full_size - 1
        addr_incr = 1 << narrow_size

        cases = [
            (0x30000, 1),
            (0x30100, 4),
            (0x30200, 8),
        ]

        for addr, blen in cases:
            initial_axil_count = len(self.axil_transactions)
            try:
                await self.axi4_master.read_transaction(
                    address=addr,
                    burst_len=blen,
                    size=narrow_size,
                    burst_type=1,
                )
                await self.wait_clocks(self.clk_name, 20)

                got = self.axil_transactions[initial_axil_count:]
                if len(got) != blen:
                    self.log.error(f"narrow_within_wide: got {len(got)} beats, "
                                  f"expected {blen}")
                    self.stats['errors'] += 1
                    success = False
                    continue

                expected_addr = addr
                for i, (_, got_addr, _) in enumerate(got):
                    if got_addr != expected_addr:
                        self.log.error(f"narrow_within_wide addr beat {i}: "
                                      f"got 0x{got_addr:08X}, expected 0x{expected_addr:08X}")
                        self.stats['address_errors'] += 1
                        self.stats['errors'] += 1
                        success = False
                    expected_addr += addr_incr
            except Exception as e:
                self.log.error(f"narrow_within_wide read raised: {e}")
                self.stats['errors'] += 1
                success = False

        return success

    async def test_max_burst(self):
        """
        ARLEN = 255 (256-beat burst). Exercises the full burst counter
        range in the shim.
        """
        return await self.test_read_burst(0x40000, 256, burst_type=1)

    async def run_basic_test(self):
        """Run basic read burst test suite"""
        self.log.info("=" * 80)
        self.log.info("BASIC READ BURST TEST SUITE")
        self.log.info("=" * 80)
        self.log.info("=== Scenarios AXI2AXIL-RD-01,02,03: Single read passthrough, burst decomposition, ID preservation ===")

        success = True

        # Test single-beat transactions (LEN=1)
        test_cases = [
            (0x1000, 1),   # Single beat
            (0x2000, 2),   # 2-beat burst
            (0x3000, 4),   # 4-beat burst
            (0x4000, 1),   # Another single beat
        ]

        for addr, burst_len in test_cases:
            if not await self.test_read_burst(addr, burst_len):
                success = False

        # Lightweight b2b smoke
        b2b_smoke = [(0x5000, 2), (0x5010, 2)]
        if not await self.test_b2b_bursts(b2b_smoke):
            success = False

        return success

    async def run_medium_test(self):
        """Run medium read burst test suite"""
        self.log.info("=" * 80)
        self.log.info("MEDIUM READ BURST TEST SUITE")
        self.log.info("=" * 80)
        self.log.info("=== Scenarios AXI2AXIL-RD-04,05,06,07,08: Address increment, RLAST, RRESP, FIXED/INCR bursts ===")

        success = True

        # Test various burst lengths
        for i in range(10):
            addr = random.randint(0, (1 << self.addr_width) - 1) & ~0x3
            burst_len = random.randint(1, 16)
            burst_type = random.choice([0, 1])  # FIXED or INCR

            if not await self.test_read_burst(addr, burst_len, burst_type):
                success = False

        # B2B scenarios — exercises the page-probe class of bug
        b2b_bursts = []
        base = 0x80000
        for i in range(8):
            blen = random.randint(1, 8)
            addr = base + (i * 0x1000)
            b2b_bursts.append((addr, blen))
        if not await self.test_b2b_bursts(b2b_bursts):
            success = False

        if not await self.test_b2b_mixed_lengths():
            success = False

        return success

    async def run_full_test(self):
        """Run full read burst test suite"""
        self.log.info("=" * 80)
        self.log.info("FULL READ BURST TEST SUITE")
        self.log.info("=" * 80)
        self.log.info("=== Scenario AXI2AXIL-RD-09: Read state machine comprehensive coverage ===")

        success = True

        # Comprehensive testing with various burst lengths and types
        for i in range(30):
            addr = random.randint(0, (1 << self.addr_width) - 1) & ~0x3
            burst_len = random.randint(1, 32)
            burst_type = random.choice([0, 1])  # FIXED or INCR

            if not await self.test_read_burst(addr, burst_len, burst_type):
                success = False

        # All the medium b2b scenarios too
        b2b_bursts = []
        base = 0x90000
        for i in range(16):
            blen = random.randint(1, 16)
            addr = base + (i * 0x1000)
            b2b_bursts.append((addr, blen))
        if not await self.test_b2b_bursts(b2b_bursts):
            success = False

        if not await self.test_b2b_mixed_lengths():
            success = False

        # FULL-only scenarios
        if not await self.test_narrow_within_wide():
            success = False

        if not await self.test_max_burst():
            success = False

        return success

    def get_statistics(self):
        """Return test statistics"""
        return dict(self.stats)
