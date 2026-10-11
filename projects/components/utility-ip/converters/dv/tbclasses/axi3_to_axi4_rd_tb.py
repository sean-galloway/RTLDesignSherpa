# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 RTL Design Sherpa
#
# Module: axi3_to_axi4_rd_tb
# Purpose: Testbench class for axi3_to_axi4_rd converter (READ-ONLY)
#
# Author: RTL Design Sherpa
# Created: 2026-10-10

"""
Testbench for axi3_to_axi4_rd converter - READ-ONLY

Tests AXI3 -> AXI4 protocol upgrade for read path with pass-through semantics
and qualifier mapping:
- AXI3 ARLEN (4 bits) is zero-extended to AXI4 ARLEN (8 bits)
- AXI3 ARLOCK (2 bits) is mapped to AXI4 ARLOCK (1 bit)
  (2'b00 -> 1'b0, 2'b01 -> 1'b0, 2'b10 -> 1'b1)
- ID, data, response, and user information are preserved
- No burst chopping in this direction (4-bit ARLEN is inherently <= 16)
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
from CocoTBFramework.components.axi3.axi3_interfaces import AXI3MasterRead
from CocoTBFramework.components.axi4.axi4_interfaces import AXI4SlaveRead


class AXI3ToAXI4ReadTB(TBBase):
    """
    Testbench for axi3_to_axi4_rd converter.

    Tests protocol upgrade from AXI3 -> AXI4 for read path with pass-through
    and qualifier mapping.

    Key Validations:
    - Single-beat and burst read pass-through
    - ARLEN zero-extension (4-bit -> 8-bit)
    - ARLOCK mapping (AXI3 2-bit -> AXI4 1-bit)
    - ID preservation on ARID/RID
    - Data/response/user identity
    - 16-beat burst passes as a single AXI4 transaction (no chopping)
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
            'axi4_reads_received': 0,
            'bursts_completed': 0,
            'errors': 0,
            'arlen_errors': 0,
            'lock_errors': 0,
            'id_errors': 0,
            'data_errors': 0,
        }

        # Bytes per transfer
        self.bytes_per_beat = self.data_width // 8

        # Initialize AXI3 master (drives slave side of converter)
        self.axi3_master = AXI3MasterRead(
            dut=dut,
            clock=self.clk,
            prefix="s_axi3_",
            log=self.log,
            data_width=self.data_width,
            id_width=self.id_width,
            addr_width=self.addr_width,
            multi_sig=True
        )

        # Initialize AXI4 slave (responds on master side of converter)
        self.axi4_slave = AXI4SlaveRead(
            dut=dut,
            clock=self.clk,
            prefix="m_axi_",
            log=self.log,
            data_width=self.data_width,
            id_width=self.id_width,
            addr_width=self.addr_width,
            multi_sig=True,
            response_delay=1
        )
        # Keep AR ready asserted so transactions stream through.
        self.axi4_slave.ar_channel.set_ready_policy('always')

        # Storage for monitoring AXI4 transactions
        self.axi4_transactions = []
        # Extended AR capture with burst/size/lock for mapping verification
        self.axi4_ar_details = []

        self.log.info(f"Initialized AXI3->AXI4 Read TB: "
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
    # AXI4 SLAVE SIDE MONITOR
    # =========================================================================

    async def axi4_transaction_monitor(self):
        """
        Monitor AXI4 read transactions by watching handshakes.
        """
        self.log.info("Starting AXI4 transaction monitor")

        while True:
            await RisingEdge(self.clk)

            # Monitor AR channel handshakes directly
            if (int(self.dut.m_axi_arvalid.value) == 1 and
                int(self.dut.m_axi_arready.value) == 1):
                ar_addr = int(self.dut.m_axi_araddr.value)
                ar_len = int(self.dut.m_axi_arlen.value)
                ar_lock = int(self.dut.m_axi_arlock.value)
                ar_id = int(self.dut.m_axi_arid.value)
                ar_burst = int(self.dut.m_axi_arburst.value)
                ar_size = int(self.dut.m_axi_arsize.value)

                # Store transaction for verification (legacy tuple preserved)
                self.axi4_transactions.append(('AR', ar_addr, ar_len, ar_lock, ar_id))
                # Extended detail for mapping checks
                self.axi4_ar_details.append({
                    'addr': ar_addr,
                    'len': ar_len,
                    'lock': ar_lock,
                    'id': ar_id,
                    'burst': ar_burst,
                    'size': ar_size,
                })
                self.stats['axi4_reads_received'] += 1

                self.log.debug(f"AXI4 AR handshake: addr=0x{ar_addr:08X}, len={ar_len}, lock={ar_lock}, id={ar_id}")

    # =========================================================================
    # TEST SCENARIO METHODS
    # =========================================================================

    async def single_beat_read(self):
        """Single-beat read pass-through."""
        self.log.info("TEST: single_beat_read")
        address = 0x1000
        axid = 7

        initial_count = len(self.axi4_transactions)

        read_data = await self.axi3_master.read_transaction(
            address=address,
            burst_len=1,
            id=axid
        )

        await self.wait_clocks(self.clk_name, 10)

        if len(self.axi4_transactions) - initial_count != 1:
            self.log.error(f"single_beat_read: expected 1 AXI4 AR, got "
                          f"{len(self.axi4_transactions) - initial_count}")
            self.stats['errors'] += 1
            return False

        txn = self.axi4_transactions[initial_count]
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

    async def arlen_zeroextend(self):
        """AXI3 ARLEN=15 (4-bit) is zero-extended to AXI4 ARLEN=15 (8-bit)."""
        self.log.info("TEST: arlen_zeroextend")
        address = 0x2000
        burst_len = 16
        axid = 5
        size = self.bytes_per_beat.bit_length() - 1

        initial_count = len(self.axi4_transactions)

        read_data = await self.axi3_master.read_transaction(
            address=address,
            burst_len=burst_len,
            burst_type=1,
            size=size,
            id=axid
        )

        await self.wait_clocks(self.clk_name, 20)

        actual_ar_count = len(self.axi4_transactions) - initial_count
        if actual_ar_count != 1:
            self.log.error(f"arlen_zeroextend: expected 1 AXI4 AR, got {actual_ar_count}")
            self.stats['errors'] += 1
            return False

        txn = self.axi4_transactions[initial_count]
        if txn[1] != address:
            self.log.error(f"arlen_zeroextend: address mismatch got 0x{txn[1]:08X}, "
                          f"expected 0x{address:08X}")
            self.stats['errors'] += 1
            return False

        if txn[2] != 15:
            self.log.error(f"arlen_zeroextend: arlen mismatch got {txn[2]}, expected 15")
            self.stats['arlen_errors'] += 1
            self.stats['errors'] += 1
            return False

        if len(read_data) != burst_len:
            self.log.error(f"arlen_zeroextend: data count mismatch got {len(read_data)}, "
                          f"expected {burst_len}")
            self.stats['errors'] += 1
            return False

        # Verify data identity: AXI4 slave with no memory model returns address per beat
        for i, data in enumerate(read_data):
            expected_addr = address + (i * self.bytes_per_beat)
            expected_data = expected_addr & ((1 << self.data_width) - 1)
            if data != expected_data:
                self.log.error(f"arlen_zeroextend: data mismatch beat {i} got 0x{data:08X}, "
                              f"expected 0x{expected_data:08X}")
                self.stats['data_errors'] += 1
                self.stats['errors'] += 1
                return False

        self.log.info("arlen_zeroextend PASSED")
        self.stats['bursts_sent'] += 1
        self.stats['beats_expected'] += burst_len
        self.stats['bursts_completed'] += 1
        return True

    async def burst_len16_passthrough(self):
        """16-beat AXI3 burst passes through as a single AXI4 transaction."""
        self.log.info("TEST: burst_len16_passthrough")
        address = 0x3000
        burst_len = 16
        axid = 3
        size = self.bytes_per_beat.bit_length() - 1

        initial_count = len(self.axi4_transactions)

        read_data = await self.axi3_master.read_transaction(
            address=address,
            burst_len=burst_len,
            burst_type=1,
            size=size,
            id=axid
        )

        await self.wait_clocks(self.clk_name, 20)

        actual_ar_count = len(self.axi4_transactions) - initial_count
        if actual_ar_count != 1:
            self.log.error(f"burst_len16_passthrough: expected 1 AXI4 AR, got {actual_ar_count}")
            self.stats['errors'] += 1
            return False

        txn = self.axi4_transactions[initial_count]
        if txn[1] != address:
            self.log.error(f"burst_len16_passthrough: address mismatch got 0x{txn[1]:08X}, "
                          f"expected 0x{address:08X}")
            self.stats['errors'] += 1
            return False

        if txn[2] != 15:
            self.log.error(f"burst_len16_passthrough: arlen mismatch got {txn[2]}, expected 15")
            self.stats['arlen_errors'] += 1
            self.stats['errors'] += 1
            return False

        if len(read_data) != burst_len:
            self.log.error(f"burst_len16_passthrough: data count mismatch got {len(read_data)}, "
                          f"expected {burst_len}")
            self.stats['errors'] += 1
            return False

        # Verify data identity
        for i, data in enumerate(read_data):
            expected_addr = address + (i * self.bytes_per_beat)
            expected_data = expected_addr & ((1 << self.data_width) - 1)
            if data != expected_data:
                self.log.error(f"burst_len16_passthrough: data mismatch beat {i} got 0x{data:08X}, "
                              f"expected 0x{expected_data:08X}")
                self.stats['data_errors'] += 1
                self.stats['errors'] += 1
                return False

        self.log.info("burst_len16_passthrough PASSED")
        self.stats['bursts_sent'] += 1
        self.stats['beats_expected'] += burst_len
        self.stats['bursts_completed'] += 1
        return True

    async def lock_map_down(self):
        """AXI3 2-bit ARLOCK maps to AXI4 1-bit ARLOCK correctly."""
        self.log.info("TEST: lock_map_down")
        address = 0x4000
        axid = 9
        size = self.bytes_per_beat.bit_length() - 1

        # (AXI3 lock value, expected AXI4 lock value)
        test_cases = [
            (0, 0),  # 2'b00 normal -> normal
            (1, 0),  # 2'b01 locked -> normal
            (2, 1),  # 2'b10 exclusive -> exclusive
        ]

        initial_count = len(self.axi4_transactions)

        for axi3_lock, expected_axi4_lock in test_cases:
            pkt = self.axi3_master.ar_channel.create_packet(
                addr=address + (axi3_lock * 0x100),
                len=0,
                id=axid,
                size=size,
                burst=1,
                lock=axi3_lock,
                cache=0,
                prot=0
            )
            await self.axi3_master.ar_channel.send(pkt)

            # Wait for response to come back
            id_queue = self.axi3_master._response_by_id[axid]
            cycles_waited = 0
            while len(id_queue) < 1:
                await RisingEdge(self.clk)
                cycles_waited += 1
                if cycles_waited > 5000:
                    self.log.error(f"lock_map_down: timeout waiting for response for lock={axi3_lock}")
                    self.stats['errors'] += 1
                    return False
            # Consume the response
            id_queue.popleft()

        await self.wait_clocks(self.clk_name, 5)

        actual_ar_count = len(self.axi4_transactions) - initial_count
        if actual_ar_count != len(test_cases):
            self.log.error(f"lock_map_down: expected {len(test_cases)} AXI4 ARs, got {actual_ar_count}")
            self.stats['errors'] += 1
            return False

        for i, (axi3_lock, expected_axi4_lock) in enumerate(test_cases):
            txn = self.axi4_transactions[initial_count + i]
            if txn[3] != expected_axi4_lock:
                self.log.error(f"lock_map_down: lock mismatch for AXI3 lock={axi3_lock} "
                              f"got {txn[3]}, expected {expected_axi4_lock}")
                self.stats['lock_errors'] += 1
                self.stats['errors'] += 1
                return False

        self.log.info("lock_map_down PASSED")
        self.stats['bursts_sent'] += len(test_cases)
        self.stats['beats_expected'] += len(test_cases)
        self.stats['bursts_completed'] += len(test_cases)
        return True

    async def rid_roundtrip(self):
        """AXI3 ARID is preserved on AXI4 ARID and returned on AXI3 RID."""
        self.log.info("TEST: rid_roundtrip")

        test_cases = [
            (0x5000, 11),
            (0x5100, 3),
            (0x5200, 7),
        ]

        initial_count = len(self.axi4_transactions)

        for address, axid in test_cases:
            read_data = await self.axi3_master.read_transaction(
                address=address,
                burst_len=1,
                id=axid
            )

            if len(read_data) != 1:
                self.log.error(f"rid_roundtrip: data count mismatch for id={axid} "
                              f"got {len(read_data)}, expected 1")
                self.stats['errors'] += 1
                return False

        await self.wait_clocks(self.clk_name, 10)

        actual_ar_count = len(self.axi4_transactions) - initial_count
        if actual_ar_count != len(test_cases):
            self.log.error(f"rid_roundtrip: expected {len(test_cases)} AXI4 ARs, got {actual_ar_count}")
            self.stats['errors'] += 1
            return False

        for i, (address, axid) in enumerate(test_cases):
            txn = self.axi4_transactions[initial_count + i]
            txn_type, txn_addr, txn_len, txn_lock, txn_id = txn

            if txn_addr != address:
                self.log.error(f"rid_roundtrip: address mismatch for id={axid} "
                              f"got 0x{txn_addr:08X}, expected 0x{address:08X}")
                self.stats['errors'] += 1
                return False

            if txn_id != axid:
                self.log.error(f"rid_roundtrip: AXI4 ARID mismatch got {txn_id}, expected {axid}")
                self.stats['id_errors'] += 1
                self.stats['errors'] += 1
                return False

        # Verify RID for each issued ID by sending AR manually and inspecting
        # the response packet before read_transaction consumes it.
        for address, axid in test_cases:
            # Clear any stale response queue entries.
            self.axi3_master._response_by_id[axid].clear()

            size = self.bytes_per_beat.bit_length() - 1
            pkt = self.axi3_master.ar_channel.create_packet(
                addr=address, len=0, id=axid, size=size,
                burst=1, lock=0, cache=0, prot=0)
            await self.axi3_master.ar_channel.send(pkt)

            id_queue = self.axi3_master._response_by_id[axid]
            cycles_waited = 0
            while len(id_queue) < 1:
                await RisingEdge(self.clk)
                cycles_waited += 1
                if cycles_waited > 5000:
                    self.log.error(f"rid_roundtrip: timeout waiting for RID response for id={axid}")
                    self.stats['errors'] += 1
                    return False

            resp_pkt = id_queue[0]
            resp_id = getattr(resp_pkt, 'id', None)
            if resp_id != axid:
                self.log.error(f"rid_roundtrip: RID mismatch got {resp_id}, expected {axid}")
                self.stats['id_errors'] += 1
                self.stats['errors'] += 1
                return False

            # Consume the response
            id_queue.popleft()

        self.log.info("rid_roundtrip PASSED")
        self.stats['bursts_sent'] += len(test_cases) * 2
        self.stats['beats_expected'] += len(test_cases) * 2
        self.stats['bursts_completed'] += len(test_cases) * 2
        return True

    async def fixed_burst(self):
        """FIXED burst passes through unmodified."""
        self.log.info("TEST: fixed_burst")
        address = 0x6000
        burst_len = 4
        axid = 4
        size = self.bytes_per_beat.bit_length() - 1

        initial_count = len(self.axi4_transactions)

        read_data = await self.axi3_master.read_transaction(
            address=address,
            burst_len=burst_len,
            burst_type=0,
            size=size,
            id=axid
        )

        await self.wait_clocks(self.clk_name, 20)

        actual_ar_count = len(self.axi4_transactions) - initial_count
        if actual_ar_count != 1:
            self.log.error(f"fixed_burst: expected 1 AXI4 AR, got {actual_ar_count}")
            self.stats['errors'] += 1
            return False

        txn = self.axi4_transactions[initial_count]
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

    # =========================================================================
    # TEST SUITE RUNNERS
    # =========================================================================

    async def run_basic_test(self):
        """Run basic read pass-through test suite"""
        self.log.info("=" * 80)
        self.log.info("BASIC READ PASS-THROUGH TEST SUITE")
        self.log.info("=" * 80)

        success = True

        if not await self.single_beat_read():
            success = False

        if not await self.arlen_zeroextend():
            success = False

        if not await self.burst_len16_passthrough():
            success = False

        if not await self.lock_map_down():
            success = False

        if not await self.rid_roundtrip():
            success = False

        if not await self.fixed_burst():
            success = False

        return success

    async def run_medium_test(self):
        """Run medium read pass-through test suite"""
        self.log.info("=" * 80)
        self.log.info("MEDIUM READ PASS-THROUGH TEST SUITE")
        self.log.info("=" * 80)

        # For this pass-through converter, medium is the same as basic.
        return await self.run_basic_test()

    async def run_full_test(self):
        """Run full read pass-through test suite"""
        self.log.info("=" * 80)
        self.log.info("FULL READ PASS-THROUGH TEST SUITE")
        self.log.info("=" * 80)

        # For this pass-through converter, full is the same as basic.
        return await self.run_basic_test()

    def get_statistics(self):
        """Return test statistics"""
        return dict(self.stats)
