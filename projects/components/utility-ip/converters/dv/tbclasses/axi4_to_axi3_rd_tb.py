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

Tests AXI4 -> AXI3 protocol downgrade for read path with pass-through semantics
and burst chopping:
- Single-beat and burst read pass-through
- AXI4 ARLOCK -> AXI3 ARLOCK mapping
- ID preservation
- Data/response identity
- Burst chopping for AXI4 bursts longer than 16 beats
- Worst-response merging across chunks
- Per-ID merge state isolation
"""

import os
import sys
import cocotb
from cocotb.triggers import RisingEdge
from cocotb.utils import get_sim_time

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

    Tests protocol downgrade from AXI4 -> AXI3 for read path with pass-through
    and burst chopping.

    Key Validations:
    - Single-beat read pass-through
    - 16-beat INCR burst pass-through (no chopping)
    - FIXED burst pass-through and long FIXED burst repeat-address chopping
    - ARLOCK mapping (AXI4 1-bit -> AXI3 2-bit)
    - ID preservation
    - Data/response identity
    - Bursts longer than 16 beats are chopped into <=16-beat AXI3 bursts
    - Worst-rank response merge across chunks (DECERR > SLVERR > OKAY/EXOKAY)
    - Per-ID merge state never crosses between IDs
    - Back-to-back AR chunk handshakes can occur while R beats stream
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
            'chop_errors': 0,
            'merge_errors': 0,
        }

        # Bytes per transfer
        self.bytes_per_beat = self.data_width // 8
        self.axi3_max_beats = 16

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
        # Keep AR ready asserted so chunk handshakes can stream back-to-back.
        self.axi3_slave.ar_channel.set_ready_policy('always')

        # Storage for monitoring AXI3 transactions
        self.axi3_transactions = []
        # Extended AR capture with burst/size for chopping verification
        self.axi3_ar_details = []
        self.axi3_ar_handshake_cycles = []
        self.first_r_beat_cycle = None

        # Free-running cycle counter (started after reset)
        self.cycle_count = 0
        self.cycle_counter_task = None

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

        # Start free-running cycle counter after reset
        self.cycle_counter_task = cocotb.start_soon(self._cycle_counter())

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
    # CYCLE COUNTER
    # =========================================================================

    async def _cycle_counter(self):
        """Free-running cycle counter used for pipeline timing checks."""
        while True:
            await RisingEdge(self.clk)
            self.cycle_count += 1

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
                ar_burst = int(self.dut.m_axi3_arburst.value)
                ar_size = int(self.dut.m_axi3_arsize.value)

                # Store transaction for verification (legacy tuple preserved)
                self.axi3_transactions.append(('AR', ar_addr, ar_len, ar_lock, ar_id))
                # Extended detail for chopping checks
                self.axi3_ar_details.append({
                    'addr': ar_addr,
                    'len': ar_len,
                    'lock': ar_lock,
                    'id': ar_id,
                    'burst': ar_burst,
                    'size': ar_size,
                    'cycle': self.cycle_count,
                })
                self.axi3_ar_handshake_cycles.append(self.cycle_count)
                self.stats['axi3_reads_received'] += 1

                self.log.debug(f"AXI3 AR handshake: addr=0x{ar_addr:08X}, len={ar_len}, lock={ar_lock}, id={ar_id}")

    async def r_channel_monitor(self):
        """Record the first slave R beat cycle for pipeline checks."""
        while True:
            await RisingEdge(self.clk)
            if (int(self.dut.s_axi_rvalid.value) == 1 and
                int(self.dut.s_axi_rready.value) == 1 and
                self.first_r_beat_cycle is None):
                self.first_r_beat_cycle = self.cycle_count

    # =========================================================================
    # LOW-LEVEL READ HELPERS
    # =========================================================================

    async def read_with_responses(self, address, burst_len, axid=0, burst_type=1, size=None):
        """
        Issue a read and return a list of (data, resp, last, rid) tuples.

        Unlike read_transaction(), this does not raise on non-OKAY responses,
        so merge tests can inspect per-beat RRESP and RID.
        """
        if size is None:
            size = self.bytes_per_beat.bit_length() - 1

        pkt = self.axi4_master.ar_channel.create_packet(
            addr=address,
            len=burst_len - 1,
            id=axid,
            size=size,
            burst=burst_type,
            lock=0,
            cache=0,
            prot=0,
            qos=0,
            region=0
        )
        await self.axi4_master.ar_channel.send(pkt)

        # Private member access: test-only introspection of AXI4MasterRead's
        # per-ID response deque. No public accessor exists in this framework version.
        id_queue = self.axi4_master._response_by_id[axid]
        cycles_waited = 0
        while len(id_queue) < burst_len:
            await RisingEdge(self.clk)
            cycles_waited += 1
            if cycles_waited > 5000:
                raise TimeoutError(f"read_with_responses timeout waiting for {burst_len} beats")

        responses = []
        for _ in range(burst_len):
            packet = id_queue.popleft()
            data = getattr(packet, 'data', 0)
            resp = getattr(packet, 'resp', 0)
            last = getattr(packet, 'last', 0)
            rid = getattr(packet, 'id', 0)
            responses.append((data, resp, last, rid))
        return responses

    def set_resp_override(self, override_fn):
        """Install a response override on the AXI3 slave BFM."""
        self.axi3_slave.resp_override = override_fn

    def clear_resp_override(self):
        """Remove the AXI3 slave response override."""
        self.axi3_slave.resp_override = None

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
        """AXI4 arlock=1 (exclusive) maps to AXI3 arlock=2'b01 (exclusive)."""
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
        if txn[3] != 1:
            self.log.error(f"lock_map: arlock mismatch got {txn[3]}, expected 1 (2'b01)")
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
            # Clear any stale response queue entries.
            # Private member access: test-only introspection of AXI4MasterRead's
            # per-ID response deque. No public accessor exists in this version.
            self.axi4_master._response_by_id[axid].clear()

            size = self.bytes_per_beat.bit_length() - 1
            pkt = self.axi4_master.ar_channel.create_packet(
                addr=address, len=0, id=axid, size=size,
                burst=1, lock=0, cache=0, prot=0, qos=0, region=0)
            await self.axi4_master.ar_channel.send(pkt)

            # Private member access: see comment above.
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

    # -------------------------------------------------------------------------
    # Chopping tests
    # -------------------------------------------------------------------------

    async def incr_burst_len17(self):
        """17-beat INCR burst is chopped into len15 + len0 AXI3 bursts."""
        self.log.info("TEST: incr_burst_len17")
        address = 0x6000
        burst_len = 17
        axid = 1
        size = self.bytes_per_beat.bit_length() - 1
        addr_step = 16 << size

        initial_count = len(self.axi3_transactions)

        read_data = await self.axi4_master.read_transaction(
            address=address,
            burst_len=burst_len,
            burst_type=1,
            size=size,
            id=axid
        )

        await self.wait_clocks(self.clk_name, 20)

        actual_ar_count = len(self.axi3_transactions) - initial_count
        if actual_ar_count != 2:
            self.log.error(f"incr_burst_len17: expected 2 AXI3 ARs, got {actual_ar_count}")
            self.stats['chop_errors'] += 1
            self.stats['errors'] += 1
            return False

        chunk0 = self.axi3_ar_details[initial_count]
        chunk1 = self.axi3_ar_details[initial_count + 1]

        if chunk0['len'] != 15 or chunk0['addr'] != address:
            self.log.error(f"incr_burst_len17: chunk0 mismatch len={chunk0['len']} addr=0x{chunk0['addr']:08X}")
            self.stats['chop_errors'] += 1
            self.stats['errors'] += 1
            return False

        if chunk1['len'] != 0 or chunk1['addr'] != address + addr_step:
            self.log.error(f"incr_burst_len17: chunk1 mismatch len={chunk1['len']} addr=0x{chunk1['addr']:08X}")
            self.stats['chop_errors'] += 1
            self.stats['errors'] += 1
            return False

        if len(read_data) != burst_len:
            self.log.error(f"incr_burst_len17: data count mismatch got {len(read_data)}, expected {burst_len}")
            self.stats['errors'] += 1
            return False

        for i, data in enumerate(read_data):
            expected_addr = address + (i * self.bytes_per_beat)
            expected_data = expected_addr & ((1 << self.data_width) - 1)
            if data != expected_data:
                self.log.error(f"incr_burst_len17: data mismatch beat {i} got 0x{data:08X}, "
                              f"expected 0x{expected_data:08X}")
                self.stats['data_errors'] += 1
                self.stats['errors'] += 1
                return False

        self.log.info("incr_burst_len17 PASSED")
        self.stats['bursts_sent'] += 1
        self.stats['beats_expected'] += burst_len
        self.stats['bursts_completed'] += 1
        return True

    async def incr_burst_len64(self):
        """64-beat INCR burst is chopped into four 16-beat AXI3 bursts."""
        self.log.info("TEST: incr_burst_len64")
        address = 0x7000
        burst_len = 64
        axid = 2
        size = self.bytes_per_beat.bit_length() - 1
        addr_step = 16 << size

        initial_count = len(self.axi3_transactions)

        read_data = await self.axi4_master.read_transaction(
            address=address,
            burst_len=burst_len,
            burst_type=1,
            size=size,
            id=axid
        )

        await self.wait_clocks(self.clk_name, 30)

        actual_ar_count = len(self.axi3_transactions) - initial_count
        if actual_ar_count != 4:
            self.log.error(f"incr_burst_len64: expected 4 AXI3 ARs, got {actual_ar_count}")
            self.stats['chop_errors'] += 1
            self.stats['errors'] += 1
            return False

        for i in range(4):
            chunk = self.axi3_ar_details[initial_count + i]
            expected_addr = address + (i * addr_step)
            if chunk['len'] != 15 or chunk['addr'] != expected_addr:
                self.log.error(f"incr_burst_len64: chunk {i} mismatch len={chunk['len']} "
                              f"addr=0x{chunk['addr']:08X}, expected 0x{expected_addr:08X}")
                self.stats['chop_errors'] += 1
                self.stats['errors'] += 1
                return False

        if len(read_data) != burst_len:
            self.log.error(f"incr_burst_len64: data count mismatch got {len(read_data)}, expected {burst_len}")
            self.stats['errors'] += 1
            return False

        for i, data in enumerate(read_data):
            expected_addr = address + (i * self.bytes_per_beat)
            expected_data = expected_addr & ((1 << self.data_width) - 1)
            if data != expected_data:
                self.log.error(f"incr_burst_len64: data mismatch beat {i} got 0x{data:08X}, "
                              f"expected 0x{expected_data:08X}")
                self.stats['data_errors'] += 1
                self.stats['errors'] += 1
                return False

        self.log.info("incr_burst_len64 PASSED")
        self.stats['bursts_sent'] += 1
        self.stats['beats_expected'] += burst_len
        self.stats['bursts_completed'] += 1
        return True

    async def incr_burst_len256(self):
        """256-beat INCR burst (max legal AXI4) is chopped into sixteen 16-beat chunks."""
        self.log.info("TEST: incr_burst_len256")
        address = 0xE000
        burst_len = 256
        axid = 14
        size = self.bytes_per_beat.bit_length() - 1
        addr_step = 16 << size

        initial_count = len(self.axi3_transactions)

        read_data = await self.axi4_master.read_transaction(
            address=address,
            burst_len=burst_len,
            burst_type=1,
            size=size,
            id=axid
        )

        await self.wait_clocks(self.clk_name, 30)

        actual_ar_count = len(self.axi3_transactions) - initial_count
        if actual_ar_count != 16:
            self.log.error(f"incr_burst_len256: expected 16 AXI3 ARs, got {actual_ar_count}")
            self.stats['chop_errors'] += 1
            self.stats['errors'] += 1
            return False

        for i in range(16):
            chunk = self.axi3_ar_details[initial_count + i]
            expected_addr = address + (i * addr_step)
            if chunk['len'] != 15 or chunk['addr'] != expected_addr:
                self.log.error(f"incr_burst_len256: chunk {i} mismatch len={chunk['len']} "
                              f"addr=0x{chunk['addr']:08X}, expected 0x{expected_addr:08X}")
                self.stats['chop_errors'] += 1
                self.stats['errors'] += 1
                return False

        if len(read_data) != burst_len:
            self.log.error(f"incr_burst_len256: data count mismatch got {len(read_data)}, expected {burst_len}")
            self.stats['errors'] += 1
            return False

        for i, data in enumerate(read_data):
            expected_addr = address + (i * self.bytes_per_beat)
            expected_data = expected_addr & ((1 << self.data_width) - 1)
            if data != expected_data:
                self.log.error(f"incr_burst_len256: data mismatch beat {i} got 0x{data:08X}, "
                              f"expected 0x{expected_data:08X}")
                self.stats['data_errors'] += 1
                self.stats['errors'] += 1
                return False

        self.log.info("incr_burst_len256 PASSED")
        self.stats['bursts_sent'] += 1
        self.stats['beats_expected'] += burst_len
        self.stats['bursts_completed'] += 1
        return True

    async def fixed_burst_long(self):
        """Long FIXED burst repeats the same address on every chunk."""
        self.log.info("TEST: fixed_burst_long")
        address = 0x8000
        burst_len = 33
        axid = 4
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

        actual_ar_count = len(self.axi3_transactions) - initial_count
        if actual_ar_count != 3:
            self.log.error(f"fixed_burst_long: expected 3 AXI3 ARs, got {actual_ar_count}")
            self.stats['chop_errors'] += 1
            self.stats['errors'] += 1
            return False

        for i in range(3):
            chunk = self.axi3_ar_details[initial_count + i]
            expected_len = 15 if i < 2 else 0
            if chunk['addr'] != address or chunk['len'] != expected_len:
                self.log.error(f"fixed_burst_long: chunk {i} mismatch len={chunk['len']} "
                              f"addr=0x{chunk['addr']:08X}, expected 0x{address:08X}")
                self.stats['chop_errors'] += 1
                self.stats['errors'] += 1
                return False

        if len(read_data) != burst_len:
            self.log.error(f"fixed_burst_long: data count mismatch got {len(read_data)}, expected {burst_len}")
            self.stats['errors'] += 1
            return False

        # The BFM returns address + beat_offset within each chunk even for FIXED,
        # so the merged data repeats the first-chunk pattern across chunks.
        for i, data in enumerate(read_data):
            beat_in_chunk = i % self.axi3_max_beats
            expected_addr = address + (beat_in_chunk * self.bytes_per_beat)
            expected_data = expected_addr & ((1 << self.data_width) - 1)
            if data != expected_data:
                self.log.error(f"fixed_burst_long: data mismatch beat {i} got 0x{data:08X}, "
                              f"expected 0x{expected_data:08X}")
                self.stats['data_errors'] += 1
                self.stats['errors'] += 1
                return False

        self.log.info("fixed_burst_long PASSED")
        self.stats['bursts_sent'] += 1
        self.stats['beats_expected'] += burst_len
        self.stats['bursts_completed'] += 1
        return True

    async def chop_pipelined(self):
        """
        Back-to-back chopped ARs handshaking while R beats stream.

        Verifies that chunk n+1's AR handshake occurs before chunk n's R beats
        have finished returning.
        """
        self.log.info("TEST: chop_pipelined")
        address = 0x9000
        burst_len = 33
        axid = 6
        size = self.bytes_per_beat.bit_length() - 1
        expected_chunks = 3

        # Snapshot before issuing
        initial_ar_count = len(self.axi3_ar_handshake_cycles)
        self.first_r_beat_cycle = None

        # Start the read in the background so we can observe progress
        read_task = cocotb.start_soon(self.read_with_responses(address, burst_len, axid=axid, burst_type=1, size=size))

        # Wait until all expected AR handshakes have occurred
        cycles_waited = 0
        while len(self.axi3_ar_handshake_cycles) - initial_ar_count < expected_chunks:
            await RisingEdge(self.clk)
            cycles_waited += 1
            if cycles_waited > 5000:
                self.log.error("chop_pipelined: timeout waiting for AR handshakes")
                self.stats['chop_errors'] += 1
                self.stats['errors'] += 1
                return False

        ar_cycles = self.axi3_ar_handshake_cycles[initial_ar_count:initial_ar_count + expected_chunks]
        self.log.info(f"chop_pipelined: AR handshake cycles: {ar_cycles}")

        # Wait for read to complete and verify the ARs issued before any R beat
        responses = await read_task
        if self.first_r_beat_cycle is None:
            self.log.error("chop_pipelined: no R beat observed")
            self.stats['chop_errors'] += 1
            self.stats['errors'] += 1
            return False

        # The critical pipelining check: all chunk ARs must have handshaked
        # before the first R beat returns, proving chunk issuance does not wait
        # for R completion.
        if self.first_r_beat_cycle <= ar_cycles[-1]:
            self.log.error(f"chop_pipelined: first R beat at cycle {self.first_r_beat_cycle} "
                          f"before/together with last AR handshake at cycle {ar_cycles[-1]}")
            self.stats['chop_errors'] += 1
            self.stats['errors'] += 1
            return False

        if len(responses) != burst_len:
            self.log.error(f"chop_pipelined: response count mismatch got {len(responses)}, expected {burst_len}")
            self.stats['errors'] += 1
            return False

        self.log.info("chop_pipelined PASSED")
        self.stats['bursts_sent'] += 1
        self.stats['beats_expected'] += burst_len
        self.stats['bursts_completed'] += 1
        return True

    # -------------------------------------------------------------------------
    # Response-merge tests
    # -------------------------------------------------------------------------

    async def resp_merge_slverr_middle(self):
        """SLVERR on a middle chunk propagates to the final R beat."""
        self.log.info("TEST: resp_merge_slverr_middle")
        address = 0xA000
        burst_len = 33
        axid = 10
        size = self.bytes_per_beat.bit_length() - 1

        # Three chunks: chunk0 [0xA000,0xA03F], chunk1 [0xA040,0xA07F], chunk2 [0xA080,0xA080]
        chunk1_start = address + (16 << size)
        chunk1_end = chunk1_start + (16 << size)

        def override(addr):
            if chunk1_start <= addr < chunk1_end:
                return 2  # SLVERR
            return None

        self.set_resp_override(override)

        try:
            responses = await self.read_with_responses(address, burst_len, axid=axid, burst_type=1, size=size)
        finally:
            self.clear_resp_override()

        if len(responses) != burst_len:
            self.log.error(f"resp_merge_slverr_middle: response count mismatch got {len(responses)}, expected {burst_len}")
            self.stats['merge_errors'] += 1
            self.stats['errors'] += 1
            return False

        # Only the final beat may assert RLAST; non-final chunk boundaries have
        # RLAST suppressed by the converter.
        last_high_beats = [i for i, (_, _, last, _) in enumerate(responses) if last]
        if len(last_high_beats) != 1 or last_high_beats[0] != burst_len - 1:
            self.log.error(f"resp_merge_slverr_middle: RLAST only on final beat expected, "
                          f"got last-high beats {last_high_beats}")
            self.stats['merge_errors'] += 1
            self.stats['errors'] += 1
            return False

        # Per-beat RRESP passthrough: every non-final beat must match the slave's
        # forced response for that beat's address.
        for i, (data, resp, last, rid) in enumerate(responses[:-1]):
            beat_addr = address + (i * self.bytes_per_beat)
            expected_resp = 2 if chunk1_start <= beat_addr < chunk1_end else 0
            if resp != expected_resp:
                self.log.error(f"resp_merge_slverr_middle: beat {i} resp={resp}, expected {expected_resp}")
                self.stats['merge_errors'] += 1
                self.stats['errors'] += 1
                return False

        # The final beat must carry the merged worst response (SLVERR).
        final_data, final_resp, final_last, final_rid = responses[-1]
        if final_resp != 2:
            self.log.error(f"resp_merge_slverr_middle: final resp={final_resp}, expected 2 (SLVERR)")
            self.stats['merge_errors'] += 1
            self.stats['errors'] += 1
            return False

        self.log.info("resp_merge_slverr_middle PASSED")
        self.stats['bursts_sent'] += 1
        self.stats['beats_expected'] += burst_len
        self.stats['bursts_completed'] += 1
        return True

    async def resp_merge_decerr_wins(self):
        """DECERR on a middle chunk wins over SLVERR on the final chunk."""
        self.log.info("TEST: resp_merge_decerr_wins")
        address = 0xB000
        burst_len = 33
        axid = 11
        size = self.bytes_per_beat.bit_length() - 1

        chunk1_start = address + (16 << size)
        chunk1_end = chunk1_start + (16 << size)
        chunk2_start = chunk1_end
        chunk2_end = chunk2_start + (1 << size)

        def override(addr):
            if chunk1_start <= addr < chunk1_end:
                return 3  # DECERR
            if chunk2_start <= addr < chunk2_end:
                return 2  # SLVERR
            return None

        self.set_resp_override(override)

        try:
            responses = await self.read_with_responses(address, burst_len, axid=axid, burst_type=1, size=size)
        finally:
            self.clear_resp_override()

        if len(responses) != burst_len:
            self.log.error(f"resp_merge_decerr_wins: response count mismatch got {len(responses)}, expected {burst_len}")
            self.stats['merge_errors'] += 1
            self.stats['errors'] += 1
            return False

        last_high_beats = [i for i, (_, _, last, _) in enumerate(responses) if last]
        if len(last_high_beats) != 1 or last_high_beats[0] != burst_len - 1:
            self.log.error(f"resp_merge_decerr_wins: RLAST only on final beat expected, "
                          f"got last-high beats {last_high_beats}")
            self.stats['merge_errors'] += 1
            self.stats['errors'] += 1
            return False

        final_data, final_resp, final_last, final_rid = responses[-1]
        if final_resp != 3:
            self.log.error(f"resp_merge_decerr_wins: final resp={final_resp}, expected 3 (DECERR)")
            self.stats['merge_errors'] += 1
            self.stats['errors'] += 1
            return False

        self.log.info("resp_merge_decerr_wins PASSED")
        self.stats['bursts_sent'] += 1
        self.stats['beats_expected'] += burst_len
        self.stats['bursts_completed'] += 1
        return True

    # -------------------------------------------------------------------------
    # Multi-ID concurrency test
    # -------------------------------------------------------------------------

    async def multi_id_outstanding(self):
        """Two IDs chopped concurrently; per-ID data/response/RLAST must not cross."""
        self.log.info("TEST: multi_id_outstanding")
        address0 = 0xC000
        address1 = 0xD000
        burst_len = 33
        id0 = 12
        id1 = 13
        size = self.bytes_per_beat.bit_length() - 1

        initial_count = len(self.axi3_transactions)

        # Force SLVERR on every beat of id0's transaction; id1 must stay OKAY
        # to prove per-ID response isolation.
        def override(addr):
            if address0 <= addr < address0 + (burst_len * self.bytes_per_beat):
                return 2  # SLVERR
            return None

        self.set_resp_override(override)

        try:
            # Launch both reads concurrently
            task0 = cocotb.start_soon(self.read_with_responses(address0, burst_len, axid=id0, burst_type=1, size=size))
            task1 = cocotb.start_soon(self.read_with_responses(address1, burst_len, axid=id1, burst_type=1, size=size))

            responses0 = await task0
            responses1 = await task1
        finally:
            self.clear_resp_override()

        await self.wait_clocks(self.clk_name, 10)

        actual_ar_count = len(self.axi3_transactions) - initial_count
        if actual_ar_count != 6:
            self.log.error(f"multi_id_outstanding: expected 6 AXI3 ARs, got {actual_ar_count}")
            self.stats['chop_errors'] += 1
            self.stats['errors'] += 1
            return False

        # Verify each ID got its own data sequence and isolated RID/RLAST/RRESP.
        for i, (data, resp, last, rid) in enumerate(responses0):
            expected_addr = address0 + (i * self.bytes_per_beat)
            expected_data = expected_addr & ((1 << self.data_width) - 1)
            if data != expected_data:
                self.log.error(f"multi_id_outstanding: id0 data mismatch beat {i} got 0x{data:08X}, "
                              f"expected 0x{expected_data:08X}")
                self.stats['merge_errors'] += 1
                self.stats['errors'] += 1
                return False
            if rid != id0:
                self.log.error(f"multi_id_outstanding: id0 RID mismatch beat {i} got {rid}, expected {id0}")
                self.stats['id_errors'] += 1
                self.stats['errors'] += 1
                return False
            is_final = (i == burst_len - 1)
            if last != (1 if is_final else 0):
                self.log.error(f"multi_id_outstanding: id0 RLAST mismatch beat {i} got {last}, expected {1 if is_final else 0}")
                self.stats['merge_errors'] += 1
                self.stats['errors'] += 1
                return False
            if resp != 2:
                self.log.error(f"multi_id_outstanding: id0 RRESP mismatch beat {i} got {resp}, expected SLVERR")
                self.stats['merge_errors'] += 1
                self.stats['errors'] += 1
                return False

        for i, (data, resp, last, rid) in enumerate(responses1):
            expected_addr = address1 + (i * self.bytes_per_beat)
            expected_data = expected_addr & ((1 << self.data_width) - 1)
            if data != expected_data:
                self.log.error(f"multi_id_outstanding: id1 data mismatch beat {i} got 0x{data:08X}, "
                              f"expected 0x{expected_data:08X}")
                self.stats['merge_errors'] += 1
                self.stats['errors'] += 1
                return False
            if rid != id1:
                self.log.error(f"multi_id_outstanding: id1 RID mismatch beat {i} got {rid}, expected {id1}")
                self.stats['id_errors'] += 1
                self.stats['errors'] += 1
                return False
            is_final = (i == burst_len - 1)
            if last != (1 if is_final else 0):
                self.log.error(f"multi_id_outstanding: id1 RLAST mismatch beat {i} got {last}, expected {1 if is_final else 0}")
                self.stats['merge_errors'] += 1
                self.stats['errors'] += 1
                return False
            if resp != 0:
                self.log.error(f"multi_id_outstanding: id1 RRESP mismatch beat {i} got {resp}, expected OKAY")
                self.stats['merge_errors'] += 1
                self.stats['errors'] += 1
                return False

        # Per-ID ARID check
        for i in range(6):
            detail = self.axi3_ar_details[initial_count + i]
            if detail['id'] not in (id0, id1):
                self.log.error(f"multi_id_outstanding: unexpected ARID {detail['id']}")
                self.stats['id_errors'] += 1
                self.stats['errors'] += 1
                return False

        self.log.info("multi_id_outstanding PASSED")
        self.stats['bursts_sent'] += 2
        self.stats['beats_expected'] += burst_len * 2
        self.stats['bursts_completed'] += 2
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
        """Run medium read pass-through + chopping test suite"""
        self.log.info("=" * 80)
        self.log.info("MEDIUM READ CHOPPING TEST SUITE")
        self.log.info("=" * 80)

        success = True

        if not await self.run_basic_test():
            success = False

        if not await self.incr_burst_len17():
            success = False

        if not await self.incr_burst_len64():
            success = False

        if not await self.incr_burst_len256():
            success = False

        if not await self.fixed_burst_long():
            success = False

        if not await self.chop_pipelined():
            success = False

        if not await self.resp_merge_slverr_middle():
            success = False

        if not await self.resp_merge_decerr_wins():
            success = False

        if not await self.multi_id_outstanding():
            success = False

        return success

    async def run_full_test(self):
        """Run full read pass-through + chopping test suite"""
        self.log.info("=" * 80)
        self.log.info("FULL READ CHOPPING TEST SUITE")
        self.log.info("=" * 80)

        success = True

        if not await self.run_medium_test():
            success = False

        return success

    def get_statistics(self):
        """Return test statistics"""
        return dict(self.stats)
