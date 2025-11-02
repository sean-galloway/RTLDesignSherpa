# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: BridgeAXI4FlatTB
# Purpose: Reusable testbench class for AXI4 Bridge Crossbar validation
#
# Documentation: projects/components/bridge/PRD.md
# Subsystem: bridge
#
# Author: sean galloway
# Created: 2025-10-18

"""
Reusable Testbench for AXI4 Bridge Crossbar

This testbench provides infrastructure for testing AXI4 Bridge crossbars
with configurable masters and slaves. Uses queue-based verification with
proper AXI4 interface components (AXI4MasterWrite/Read, AXI4SlaveWrite/Read).
"""

import os
import sys
import cocotb
from cocotb.clock import Clock
from cocotb.triggers import RisingEdge, Timer

# Add framework to path
repo_root = os.path.abspath(os.path.join(os.path.dirname(__file__), '../../../../..'))
sys.path.insert(0, os.path.join(repo_root, 'bin'))

from CocoTBFramework.tbclasses.shared.tbbase import TBBase
from CocoTBFramework.components.axi4.axi4_factories import (
    create_axi4_master_wr, create_axi4_master_rd,
    create_axi4_slave_wr, create_axi4_slave_rd
)
from CocoTBFramework.components.shared.memory_model import MemoryModel


class BridgeAXI4FlatTB(TBBase):
    """
    Reusable Testbench for AXI4 Bridge Crossbar Validation

    Provides infrastructure for testing NxM bridge crossbars with:
    - AXI4MasterWrite/Read components for master ports (drives AW/W/AR, receives B/R)
    - AXI4SlaveWrite/Read components for slave ports (receives AW/W/AR, drives B/R)
    - Queue-based verification (no memory models for simple tests)
    - Automatic response generation via AXI4 framework callbacks
    - Configurable address map

    Architecture:
    - Master-side: AXI4MasterWrite handles AW/W→B, AXI4MasterRead handles AR→R
    - Slave-side: AXI4SlaveWrite handles AW/W→B, AXI4SlaveRead handles AR→R

    Usage:
        tb = BridgeAXI4FlatTB(dut, num_masters=2, num_slaves=2)
        await tb.setup_clocks_and_reset()
        await tb.write_transaction(master_idx=0, address=0x1000, data=0xDEADBEEF)
    """

    def __init__(self, dut, num_masters=2, num_slaves=2,
                 data_width=32, addr_width=32, id_width=4):
        """
        Initialize Bridge testbench

        Args:
            dut: Device under test
            num_masters: Number of master ports
            num_slaves: Number of slave ports
            data_width: AXI data width (32, 64, 128, etc.)
            addr_width: AXI address width (32, 64)
            id_width: AXI ID width (4, 8, etc.)
        """
        super().__init__(dut)

        # Bridge configuration
        self.num_masters = num_masters
        self.num_slaves = num_slaves
        self.data_width = data_width
        self.addr_width = addr_width
        self.id_width = id_width

        # Clock configuration
        self.clk = dut.aclk
        self.clk_name = 'aclk'
        self.rst_n = dut.aresetn

        # Address map (configurable per slave)
        self.slave_base_addrs = []
        self.slave_addr_range = 0x10000000
        for s in range(num_slaves):
            self.slave_base_addrs.append(s * self.slave_addr_range)

        # AXI4 Interface Components
        self.master_write_if = []  # AXI4MasterWrite for each master port
        self.master_read_if = []   # AXI4MasterRead for each master port
        self.slave_write_if = []   # AXI4SlaveWrite for each slave port
        self.slave_read_if = []    # AXI4SlaveRead for each slave port

        # Statistics tracking - one set per slave for route verification
        self.slave_stats = []
        for s in range(num_slaves):
            self.slave_stats.append({
                'aw_received': 0,
                'w_received': 0,
                'b_sent': 0,
                'ar_received': 0,
                'r_sent': 0,
                # Capture actual values for verification
                'addresses': [],      # List of addresses received
                'data_values': [],    # List of data values received
                'write_ids': [],      # List of transaction IDs
                'read_addresses': [], # List of read addresses
                'read_ids': [],       # List of read transaction IDs
            })

        # Global statistics
        self.stats = {
            'writes_sent': 0,
            'reads_sent': 0,
            'b_responses_received': 0,
            'r_responses_received': 0,
        }

        # Initialize components
        self._init_master_side_components()
        self._init_slave_side_components()

        self.log.info(f"Initialized {num_masters}x{num_slaves} Bridge testbench with AXI4 framework")
        self.log.info(f"  Data Width: {data_width}, Addr Width: {addr_width}, ID Width: {id_width}")
        self.log.info(f"  Statistics-based verification with {num_slaves} slave counters")

    def _init_master_side_components(self):
        """Initialize master-side AXI4 interface components using factory functions"""
        for m in range(self.num_masters):
            # Master write interface (handles AW/W channels, receives B responses)
            master_write = create_axi4_master_wr(
                dut=self.dut,
                clock=self.clk,
                prefix=f"s{m}_axi_",  # s0_axi_, s1_axi_, etc.
                log=self.log,
                data_width=self.data_width,
                id_width=self.id_width,
                addr_width=self.addr_width,
                user_width=1,
                multi_sig=True
            )
            self.master_write_if.append(master_write)

            # Master read interface (handles AR channel, receives R responses)
            master_read = create_axi4_master_rd(
                dut=self.dut,
                clock=self.clk,
                prefix=f"s{m}_axi_",  # s0_axi_, s1_axi_, etc.
                log=self.log,
                data_width=self.data_width,
                id_width=self.id_width,
                addr_width=self.addr_width,
                user_width=1,
                multi_sig=True
            )
            self.master_read_if.append(master_read)

    def _init_slave_side_components(self):
        """Initialize slave-side AXI4 interface components using factory functions with stat tracking"""
        for s in range(self.num_slaves):
            # Slave write interface (receives AW/W channels, drives B responses)
            # No memory model - use statistics for verification
            slave_write = create_axi4_slave_wr(
                dut=self.dut,
                clock=self.clk,
                prefix=f"m{s}_axi_",  # m0_axi_, m1_axi_, etc.
                log=self.log,
                data_width=self.data_width,
                id_width=self.id_width,
                addr_width=self.addr_width,
                user_width=1,
                multi_sig=True,
                memory_model=None,  # Statistics-based verification, no memory model
                response_delay=1     # 1 cycle delay for B responses
            )
            self.slave_write_if.append(slave_write)

            # Set up callback to track AW packets (capture address and ID)
            def make_aw_callback(slave_idx):
                def aw_callback(pkt):
                    self.slave_stats[slave_idx]['aw_received'] += 1
                    self.slave_stats[slave_idx]['addresses'].append(pkt.addr)
                    self.slave_stats[slave_idx]['write_ids'].append(pkt.id)
                return aw_callback
            slave_write['AW'].add_callback(make_aw_callback(s))

            # Set up callback to track W packets (capture data)
            def make_w_callback(slave_idx):
                def w_callback(pkt):
                    self.slave_stats[slave_idx]['w_received'] += 1
                    self.slave_stats[slave_idx]['data_values'].append(pkt.data)
                return w_callback
            slave_write['W'].add_callback(make_w_callback(s))

            # Slave read interface (receives AR channel, drives R responses)
            slave_read = create_axi4_slave_rd(
                dut=self.dut,
                clock=self.clk,
                prefix=f"m{s}_axi_",  # m0_axi_, m1_axi_, etc.
                log=self.log,
                data_width=self.data_width,
                id_width=self.id_width,
                addr_width=self.addr_width,
                user_width=1,
                multi_sig=True,
                memory_model=None,  # Statistics-based verification
                response_delay=1     # 1 cycle delay for R responses
            )
            self.slave_read_if.append(slave_read)

            # Set up callback to track AR packets (capture read address and ID)
            def make_ar_callback(slave_idx):
                def ar_callback(pkt):
                    self.slave_stats[slave_idx]['ar_received'] += 1
                    self.slave_stats[slave_idx]['read_addresses'].append(pkt.addr)
                    self.slave_stats[slave_idx]['read_ids'].append(pkt.id)
                return ar_callback
            slave_read['AR'].add_callback(make_ar_callback(s))

    # =========================================================================
    # MANDATORY METHODS - Required by TBBase
    # =========================================================================

    async def setup_clocks_and_reset(self):
        """
        Complete initialization - start clocks and perform reset sequence

        This is the main entry point called by test runners.
        """
        # Start clock
        await self.start_clock(self.clk_name, freq=10, units='ns')
        self.log.info("Clock started")

        # Reset sequence
        await self.assert_reset()
        await self.wait_clocks(self.clk_name, 10)  # Hold reset for 10 cycles
        await self.deassert_reset()
        await self.wait_clocks(self.clk_name, 5)   # Stabilization time

        self.log.info("Reset sequence complete")
        self.log.info("AXI4 framework will handle all ready signals and response generation automatically")

    async def assert_reset(self):
        """Assert reset signal (active-low)"""
        self.rst_n.value = 0
        self.log.debug("Reset asserted")

    async def deassert_reset(self):
        """Deassert reset signal (active-low)"""
        self.rst_n.value = 1
        self.log.debug("Reset deasserted")

    # =========================================================================
    # TEST UTILITY METHODS
    # =========================================================================

    def get_slave_index(self, address):
        """Determine which slave based on address"""
        for s in range(self.num_slaves):
            if self.slave_base_addrs[s] <= address < (self.slave_base_addrs[s] + self.slave_addr_range):
                return s
        return 0  # Default to slave 0

    async def write_transaction(self, master_idx, address, data, txn_id=0):
        """
        Send write transaction (AW + W) using AXI4 framework

        Args:
            master_idx: Master port index (0 to num_masters-1)
            address: Transaction address
            data: Write data
            txn_id: Transaction ID

        Returns:
            Tuple of (aw_pkt, w_pkt)
        """
        # Get channel references from factory dictionary
        aw_channel = self.master_write_if[master_idx]['AW']
        w_channel = self.master_write_if[master_idx]['W']

        # Send AW
        aw_pkt = aw_channel.create_packet(
            addr=address,
            id=txn_id,
            len=0,  # Single beat
            size=2,  # 4 bytes
            burst=1
        )
        await aw_channel.send(aw_pkt)

        # Send W
        w_pkt = w_channel.create_packet(
            data=data,
            last=1,
            strb=0xF
        )
        await w_channel.send(w_pkt)

        self.log.debug(f"M{master_idx} write: addr=0x{address:X}, data=0x{data:X}, id={txn_id}")
        return aw_pkt, w_pkt

    async def read_transaction(self, master_idx, address, txn_id=0):
        """
        Send read transaction (AR) using AXI4 framework

        Args:
            master_idx: Master port index (0 to num_masters-1)
            address: Transaction address
            txn_id: Transaction ID

        Returns:
            ar_pkt
        """
        # Get channel reference from factory dictionary
        ar_channel = self.master_read_if[master_idx]['AR']

        ar_pkt = ar_channel.create_packet(
            addr=address,
            id=txn_id,
            len=0,  # Single beat
            size=2,  # 4 bytes
            burst=1
        )
        await ar_channel.send(ar_pkt)

        self.log.debug(f"M{master_idx} read: addr=0x{address:X}, id={txn_id}")
        return ar_pkt

    # =========================================================================
    # TEST SCENARIO METHODS
    # =========================================================================

    async def test_basic_routing(self, num_transactions=10):
        """
        Test basic address routing from masters to slaves with address/data verification

        Args:
            num_transactions: Number of transactions to send

        Returns:
            True if test passes, False otherwise
        """
        self.log.info(f"Starting basic routing test ({num_transactions} transactions)")

        # Track expected transactions per slave
        expected_writes = [[] for _ in range(self.num_slaves)]  # List of (address, data, id) per slave

        # Send writes to alternating slaves
        for i in range(num_transactions):
            slave_idx = i % self.num_slaves
            master_idx = i % self.num_masters
            address = self.slave_base_addrs[slave_idx] + (i * 4)
            data = 0xA0000000 + i

            # Record expected values
            expected_writes[slave_idx].append((address, data, i))

            # Send write transaction (callbacks capture actual values)
            await self.write_transaction(master_idx, address, data, txn_id=i)
            self.stats['writes_sent'] += 1

        # Wait for all transactions to complete
        await self.wait_clocks(self.clk_name, 50)

        # Verify routing using captured addresses and data
        success = True
        for s in range(self.num_slaves):
            # Check transaction count
            actual_count = self.slave_stats[s]['aw_received']
            expected_count = len(expected_writes[s])

            if actual_count != expected_count:
                self.log.error(f"Slave {s}: Expected {expected_count} AW transactions, got {actual_count}")
                success = False
                continue

            # Verify addresses and data
            for idx, (expected_addr, expected_data, expected_id) in enumerate(expected_writes[s]):
                actual_addr = self.slave_stats[s]['addresses'][idx]
                actual_data = self.slave_stats[s]['data_values'][idx]
                actual_id = self.slave_stats[s]['write_ids'][idx]

                # Check address
                if actual_addr != expected_addr:
                    self.log.error(f"Slave {s} Transaction {idx}: Address mismatch - "
                                   f"expected 0x{expected_addr:X}, got 0x{actual_addr:X}")
                    success = False

                # Check data
                if actual_data != expected_data:
                    self.log.error(f"Slave {s} Transaction {idx}: Data mismatch - "
                                   f"expected 0x{expected_data:X}, got 0x{actual_data:X}")
                    success = False

                # Check ID
                if actual_id != expected_id:
                    self.log.error(f"Slave {s} Transaction {idx}: ID mismatch - "
                                   f"expected {expected_id}, got {actual_id}")
                    success = False

            if success:
                self.log.info(f"✓ Slave {s}: Received {actual_count} transactions with correct addresses/data")

        if success:
            self.log.info(f"✓ All {num_transactions} writes routed correctly with matching addresses and data")

        return success

    async def test_id_routing(self, num_transactions=10):
        """
        Test transaction ID routing with address/data verification

        Args:
            num_transactions: Number of transactions to send

        Returns:
            True if test passes, False otherwise
        """
        self.log.info(f"Starting ID routing test ({num_transactions} transactions)")

        # Track expected writes per slave
        expected_writes = [[] for _ in range(self.num_slaves)]  # List of (address, data, id) per slave

        # Send transactions with different IDs
        for i in range(num_transactions):
            master_idx = 0  # Use first master
            slave_idx = i % self.num_slaves
            address = self.slave_base_addrs[slave_idx] + (i * 4)
            data = 0xB0000000 + i
            txn_id = i % (2 ** self.id_width)  # Cycle through IDs

            # Record expected values
            expected_writes[slave_idx].append((address, data, txn_id))

            await self.write_transaction(master_idx, address, data, txn_id=txn_id)
            self.stats['writes_sent'] += 1

        # Wait for all responses
        await self.wait_clocks(self.clk_name, 50)

        # Verify all writes routed correctly with address/data/ID matching
        success = True
        total_aw = 0
        for s in range(self.num_slaves):
            actual_count = self.slave_stats[s]['aw_received']
            expected_count = len(expected_writes[s])
            total_aw += actual_count

            if actual_count != expected_count:
                self.log.error(f"Slave {s}: Expected {expected_count} AW transactions, got {actual_count}")
                success = False
                continue

            # Verify each transaction's address, data, and ID
            for idx, (expected_addr, expected_data, expected_id) in enumerate(expected_writes[s]):
                actual_addr = self.slave_stats[s]['addresses'][idx]
                actual_data = self.slave_stats[s]['data_values'][idx]
                actual_id = self.slave_stats[s]['write_ids'][idx]

                if actual_addr != expected_addr:
                    self.log.error(f"Slave {s} Transaction {idx}: Address mismatch - "
                                   f"expected 0x{expected_addr:X}, got 0x{actual_addr:X}")
                    success = False

                if actual_data != expected_data:
                    self.log.error(f"Slave {s} Transaction {idx}: Data mismatch - "
                                   f"expected 0x{expected_data:X}, got 0x{actual_data:X}")
                    success = False

                if actual_id != expected_id:
                    self.log.error(f"Slave {s} Transaction {idx}: ID mismatch - "
                                   f"expected {expected_id}, got {actual_id}")
                    success = False

        if success and total_aw == num_transactions:
            self.log.info(f"✓ All {num_transactions} transactions routed correctly with matching IDs, addresses, and data")
        else:
            if total_aw != num_transactions:
                self.log.error(f"Expected {num_transactions} total AW transactions, got {total_aw}")
            success = False

        return success

    async def test_concurrent_masters(self, transactions_per_master=5):
        """
        Test concurrent transactions from multiple masters with address/data verification

        Args:
            transactions_per_master: Number of transactions from each master

        Returns:
            True if test passes, False otherwise
        """
        self.log.info(f"Starting concurrent masters test ({transactions_per_master} per master)")

        # Track expected writes - use dictionary keyed by (address, data, id)
        # to handle concurrent non-deterministic ordering
        expected_txns = {}  # {slave_idx: set of (address, data, id)}
        for s in range(self.num_slaves):
            expected_txns[s] = set()

        # Send transactions from all masters concurrently
        tasks = []
        for m in range(self.num_masters):
            async def send_from_master(master_idx):
                for i in range(transactions_per_master):
                    slave_idx = i % self.num_slaves
                    address = self.slave_base_addrs[slave_idx] + (master_idx * 1024) + (i * 4)
                    data = 0xC0000000 + (master_idx << 16) + i
                    txn_id = i

                    # Record expected transaction (before sending to avoid race)
                    expected_txns[slave_idx].add((address, data, txn_id))

                    await self.write_transaction(master_idx, address, data, txn_id=txn_id)

            tasks.append(cocotb.start_soon(send_from_master(m)))

        # Wait for all tasks
        for task in tasks:
            await task

        # Wait for completion
        await self.wait_clocks(self.clk_name, 100)

        # Verify total transactions and address/data correctness
        total_expected = self.num_masters * transactions_per_master
        total_actual = sum(self.slave_stats[s]['aw_received'] for s in range(self.num_slaves))

        success = True
        if total_actual != total_expected:
            self.log.error(f"Expected {total_expected} total AW transactions, got {total_actual}")
            success = False
        else:
            self.log.info(f"✓ All {total_expected} concurrent transactions completed")

        # Verify each slave's transactions match expectations (unordered)
        for s in range(self.num_slaves):
            actual_count = self.slave_stats[s]['aw_received']
            expected_count = len(expected_txns[s])

            if actual_count != expected_count:
                self.log.error(f"Slave {s}: Expected {expected_count} transactions, got {actual_count}")
                success = False
                continue

            # Build set of actual transactions
            actual_txns = set()
            for idx in range(actual_count):
                addr = self.slave_stats[s]['addresses'][idx]
                data = self.slave_stats[s]['data_values'][idx]
                txn_id = self.slave_stats[s]['write_ids'][idx]
                actual_txns.add((addr, data, txn_id))

            # Compare sets (order doesn't matter for concurrent test)
            if actual_txns != expected_txns[s]:
                missing = expected_txns[s] - actual_txns
                extra = actual_txns - expected_txns[s]
                if missing:
                    self.log.error(f"Slave {s}: Missing transactions: {missing}")
                if extra:
                    self.log.error(f"Slave {s}: Extra transactions: {extra}")
                success = False
            else:
                self.log.info(f"  ✓ Slave {s}: {actual_count} transactions with correct addresses/data/IDs")

        return success
