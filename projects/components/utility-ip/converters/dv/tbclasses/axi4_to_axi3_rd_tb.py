# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 RTL Design Sherpa
#
# Module: axi4_to_axi3_rd_tb
# Purpose: Testbench class for axi4_to_axi3_rd converter (READ-ONLY)
#
# Author: RTL Design Sherpa
# Created: 2026-10-10

"""
Testbench for axi4_to_axi3_rd converter - READ-ONLY

Tests AXI4 -> AXI3 protocol downgrade for read path with pass-through semantics:
- Single-beat and burst read pass-through
- AXI4 ARLOCK -> AXI3 ARLOCK mapping
- ID preservation
- Data/response identity
"""

import os
import sys
import cocotb
from cocotb.triggers import RisingEdge

# Import framework utilities (PYTHONPATH includes bin/)
from TBClasses.shared.utilities import get_repo_root
from TBClasses.shared.tbbase import TBBase

# Add repo root to Python path using robust git-based method
repo_root = get_repo_root()
sys.path.insert(0, repo_root)
from CocoTBFramework.components.axi4.axi4_interfaces import AXI4MasterRead
from CocoTBFramework.components.axi3.axi3_interfaces import AXI3SlaveRead


class AXI4ToAXI3ReadTB(TBBase):
    """
    Testbench for axi4_to_axi3_rd converter.

    Tests protocol downgrade from AXI4 -> AXI3 for read path with pass-through.

    Key Validations:
    - Single-beat read pass-through
    - 16-beat burst pass-through (no chopping)
    - FIXED burst pass-through
    - ARLOCK mapping (AXI4 1-bit -> AXI3 2-bit)
    - ID preservation
    - Data/response identity
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
            'axi3_reads_received': 0,
            'bursts_completed': 0,
            'errors': 0,
            'arlen_errors': 0,
            'lock_errors': 0,
            'id_errors': 0,
            'data_errors': 0,
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

        # Initialize AXI3 slave (responds on master side of converter)
        self.axi3_slave = AXI3SlaveRead(
            dut=dut,
            clock=self.clk,
            prefix="m_axi3_",
            log=self.log,
            data_width=self.data_width,
            id_width=self.id_width,
            addr_width=self.addr_width,
            multi_sig=True,
            response_delay=1
        )

        # Storage for monitoring AXI3 transactions
        self.axi3_transactions = []

        self.log.info(f"Initialized AXI4->AXI3 Read TB: "
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
    # AXI3 MASTER SIDE MONITOR
    # =========================================================================

    async def axi3_transaction_monitor(self):
        """
        Monitor AXI3 read transactions by watching handshakes.
        """
        self.log.info("Starting AXI3 transaction monitor")

        while True:
            await RisingEdge(self.clk)

            # Monitor AR channel handshakes directly
            if (int(self.dut.m_axi3_arvalid.value) == 1 and
                int(self.dut.m_axi3_arready.value) == 1):
                ar_addr = int(self.dut.m_axi3_araddr.value)
                ar_len = int(self.dut.m_axi3_arlen.value)
                ar_lock = int(self.dut.m_axi3_arlock.value)
                ar_id = int(self.dut.m_axi3_arid.value)

                # Store transaction for verification
                self.axi3_transactions.append(('AR', ar_addr, ar_len, ar_lock, ar_id))
                self.stats['axi3_reads_received'] += 1

                self.log.debug(f"AXI3 AR handshake: addr=0x{ar_addr:08X}, len={ar_len}, lock={ar_lock}, id={ar_id}")

    # =========================================================================
    # TEST SCENARIO METHODS
    # =========================================================================

    async def single_beat_read(self):
        """Single-beat read pass-through."""
        self.log.info("TEST: single_beat_read")
        address = 0x1000
        axid = 7

        initial_count = len(self.axi3_transactions)

        read_data = await self.axi4_master.read_transaction(
            address=address,
            burst_len=1,
            id=axid
        )

        await self.wait_clocks(self.clk_name, 10)

        if len(self.axi3_transactions) - initial_count != 1:
            self.log.error(f"single_beat_read: expected 1 AXI3 AR, got "
                          f"{len(self.axi3_transactions) - initial_count}")
            self.stats['errors'] += 1
            return False

        txn = self.axi3_transactions[initial_count]
        if txn[1] != address:
            self.log.error(f"single_beat_read: address mismatch got 0x{txn[1]:08X}, "
                          f"expected 0x{address:08X}")
            self.stats['errors'] += 1
            return False

        if txn[2] != 0:
            self.log.error(f"single_beat_read: arlen mismatch got {txn[2]}, expected 0")
            self.stats['arlen_errors'] += 1
            self.stats['errors'] += 1
            return False

        if len(read_data) != 1:
            self.log.error(f"single_beat_read: data count mismatch got {len(read_data)}, expected 1")
            self.stats['errors'] += 1
            return False

        self.log.info("single_beat_read PASSED")
        self.stats['bursts_sent'] += 1
        self.stats['beats_expected'] += 1
        self.stats['bursts_completed'] += 1
        return True

    async def incr_burst_len16(self):
        """16-beat INCR burst passes through unchopped."""
        self.log.info("TEST: incr_burst_len16")
        address = 0x2000
        burst_len = 16
        axid = 5
        size = self.bytes_per_beat.bit_length() - 1

        initial_count = len(self.axi3_transactions)

        read_data = await self.axi4_master.read_transaction(
            address=address,
            burst_len=burst_len,
            burst_type=1,
            size=size,
            id=axid
        )

        await self.wait_clocks(self.clk_name, 20)

        expected_ar_count = 1
        actual_ar_count = len(self.axi3_transactions) - initial_count
        if actual_ar_count != expected_ar_count:
            self.log.error(f"incr_burst_len16: expected {expected_ar_count} AXI3 AR, got {actual_ar_count}")
            self.stats['errors'] += 1
            return False

        txn = self.axi3_transactions[initial_count]
        if txn[1] != address:
            self.log.error(f"incr_burst_len16: address mismatch got 0x{txn[1]:08X}, "
                          f"expected 0x{address:08X}")
            self.stats['errors'] += 1
            return False

        if txn[2] != 15:
            self.log.error(f"incr_burst_len16: arlen mismatch got {txn[2]}, expected 15")
            self.stats['arlen_errors'] += 1
            self.stats['errors'] += 1
            return False

        if len(read_data) != burst_len:
            self.log.error(f"incr_burst_len16: data count mismatch got {len(read_data)}, "
                          f"expected {burst_len}")
            self.stats['errors'] += 1
            return False

        # Verify data identity: AXI3 slave with no memory model returns address per beat
        for i, data in enumerate(read_data):
            expected_addr = address + (i * self.bytes_per_beat)
            expected_data = expected_addr & ((1 << self.data_width) - 1)
            if data != expected_data:
                self.log.error(f"incr_burst_len16: data mismatch beat {i} got 0x{data:08X}, "
                              f"expected 0x{expected_data:08X}")
                self.stats['data_errors'] += 1
                self.stats['errors'] += 1
                return False

        self.log.info("incr_burst_len16 PASSED")
        self.stats['bursts_sent'] += 1
        self.stats['beats_expected'] += burst_len
        self.stats['bursts_completed'] += 1
        return True

    async def fixed_burst(self):
        """FIXED burst passes through unchopped."""
        self.log.info("TEST: fixed_burst")
        address = 0x3000
        burst_len = 4
        axid = 3
        size = self.bytes_per_beat.bit_length() - 1

        initial_count = len(self.axi3_transactions)

        read_data = await self.axi4_master.read_transaction(
            address=address,
            burst_len=burst_len,
            burst_type=0,
            size=size,
            id=axid
        )

        await self.wait_clocks(self.clk_name, 20)

        expected_ar_count = 1
        actual_ar_count = len(self.axi3_transactions) - initial_count
        if actual_ar_count != expected_ar_count:
            self.log.error(f"fixed_burst: expected {expected_ar_count} AXI3 AR, got {actual_ar_count}")
            self.stats['errors'] += 1
            return False

        txn = self.axi3_transactions[initial_count]
        if txn[1] != address:
            self.log.error(f"fixed_burst: address mismatch got 0x{txn[1]:08X}, "
                          f"expected 0x{address:08X}")
            self.stats['errors'] += 1
            return False

        if txn[2] != burst_len - 1:
            self.log.error(f"fixed_burst: arlen mismatch got {txn[2]}, expected {burst_len - 1}")
            self.stats['arlen_errors'] += 1
            self.stats['errors'] += 1
            return False

        if len(read_data) != burst_len:
            self.log.error(f"fixed_burst: data count mismatch got {len(read_data)}, "
                          f"expected {burst_len}")
            self.stats['errors'] += 1
            return False

        self.log.info("fixed_burst PASSED")
        self.stats['bursts_sent'] += 1
        self.stats['beats_expected'] += burst_len
        self.stats['bursts_completed'] += 1
        return True

    async def lock_map(self):
        """AXI4 arlock=1 maps to AXI3 arlock=2'b10 (exclusive)."""
        self.log.info("TEST: lock_map")
        address = 0x4000
        axid = 9

        initial_count = len(self.axi3_transactions)

        pkt = self.axi4_master.ar_channel.create_packet(
            addr=address, len=0, id=axid,
            size=self.bytes_per_beat.bit_length() - 1,
            burst=1, lock=1, cache=0, prot=0, qos=0, region=0)
        await self.axi4_master.ar_channel.send(pkt)

        # Wait for response to come back
        id_queue = self.axi4_master._response_by_id[axid]
        cycles_waited = 0
        while len(id_queue) < 1:
            await RisingEdge(self.clk)
            cycles_waited += 1
            if cycles_waited > 5000:
                self.log.error("lock_map: timeout waiting for response")
                self.stats['errors'] += 1
                return False

        await self.wait_clocks(self.clk_name, 5)

        actual_ar_count = len(self.axi3_transactions) - initial_count
        if actual_ar_count != 1:
            self.log.error(f"lock_map: expected 1 AXI3 AR, got {actual_ar_count}")
            self.stats['errors'] += 1
            return False

        txn = self.axi3_transactions[initial_count]
        if txn[3] != 2:
            self.log.error(f"lock_map: arlock mismatch got {txn[3]}, expected 2 (2'b10)")
            self.stats['lock_errors'] += 1
            self.stats['errors'] += 1
            return False

        self.log.info("lock_map PASSED")
        self.stats['bursts_sent'] += 1
        self.stats['beats_expected'] += 1
        self.stats['bursts_completed'] += 1
        return True

    async def id_preserved(self):
        """AXI4 ARID is preserved on AXI3 ARID and returned on RID."""
        self.log.info("TEST: id_preserved")

        # Issue reads on multiple distinct IDs and verify both the AXI3 ARID
        # and the returned RID match the issued AXI4 ARID.
        test_cases = [
            (0x5000, 11),
            (0x5100, 3),
            (0x5200, 7),
        ]

        initial_count = len(self.axi3_transactions)

        for address, axid in test_cases:
            read_data = await self.axi4_master.read_transaction(
                address=address,
                burst_len=1,
                id=axid
            )

            if len(read_data) != 1:
                self.log.error(f"id_preserved: data count mismatch for id={axid} "
                              f"got {len(read_data)}, expected 1")
                self.stats['errors'] += 1
                return False

        await self.wait_clocks(self.clk_name, 10)

        actual_ar_count = len(self.axi3_transactions) - initial_count
        if actual_ar_count != len(test_cases):
            self.log.error(f"id_preserved: expected {len(test_cases)} AXI3 ARs, got {actual_ar_count}")
            self.stats['errors'] += 1
            return False

        for i, (address, axid) in enumerate(test_cases):
            txn = self.axi3_transactions[initial_count + i]
            txn_type, txn_addr, txn_len, txn_lock, txn_id = txn

            if txn_addr != address:
                self.log.error(f"id_preserved: address mismatch for id={axid} "
                              f"got 0x{txn_addr:08X}, expected 0x{address:08X}")
                self.stats['errors'] += 1
                return False

            if txn_id != axid:
                self.log.error(f"id_preserved: AXI3 ARID mismatch got {txn_id}, expected {axid}")
                self.stats['id_errors'] += 1
                self.stats['errors'] += 1
                return False

        # Verify RID for each issued ID by sending AR manually and inspecting
        # the response packet before read_transaction consumes it.
        for address, axid in test_cases:
            # Clear any stale response queue entries
            self.axi4_master._response_by_id[axid].clear()

            size = self.bytes_per_beat.bit_length() - 1
            pkt = self.axi4_master.ar_channel.create_packet(
                addr=address, len=0, id=axid, size=size,
                burst=1, lock=0, cache=0, prot=0, qos=0, region=0)
            await self.axi4_master.ar_channel.send(pkt)

            id_queue = self.axi4_master._response_by_id[axid]
            cycles_waited = 0
            while len(id_queue) < 1:
                await RisingEdge(self.clk)
                cycles_waited += 1
                if cycles_waited > 5000:
                    self.log.error(f"id_preserved: timeout waiting for RID response for id={axid}")
                    self.stats['errors'] += 1
                    return False

            resp_pkt = id_queue[0]
            resp_id = getattr(resp_pkt, 'id', None)
            if resp_id != axid:
                self.log.error(f"id_preserved: RID mismatch got {resp_id}, expected {axid}")
                self.stats['id_errors'] += 1
                self.stats['errors'] += 1
                return False

            # Consume the response
            id_queue.popleft()

        self.log.info("id_preserved PASSED")
        self.stats['bursts_sent'] += len(test_cases) * 2
        self.stats['beats_expected'] += len(test_cases) * 2
        self.stats['bursts_completed'] += len(test_cases) * 2
        return True

    async def run_basic_test(self):
        """Run basic read pass-through test suite"""
        self.log.info("=" * 80)
        self.log.info("BASIC READ PASS-THROUGH TEST SUITE")
        self.log.info("=" * 80)

        success = True

        if not await self.single_beat_read():
            success = False

        if not await self.incr_burst_len16():
            success = False

        if not await self.fixed_burst():
            success = False

        if not await self.lock_map():
            success = False

        if not await self.id_preserved():
            success = False

        return success

    async def run_medium_test(self):
        """Run medium read pass-through test suite"""
        self.log.info("=" * 80)
        self.log.info("MEDIUM READ PASS-THROUGH TEST SUITE")
        self.log.info("=" * 80)

        success = True

        if not await self.run_basic_test():
            success = False

        return success

    async def run_full_test(self):
        """Run full read pass-through test suite"""
        self.log.info("=" * 80)
        self.log.info("FULL READ PASS-THROUGH TEST SUITE")
        self.log.info("=" * 80)

        success = True

        if not await self.run_basic_test():
            success = False

        return success

    def get_statistics(self):
        """Return test statistics"""
        return dict(self.stats)
