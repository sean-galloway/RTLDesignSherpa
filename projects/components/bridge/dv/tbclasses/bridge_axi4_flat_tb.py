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
GAXI components for protocol handling.
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
from CocoTBFramework.components.gaxi.gaxi_master import GAXIMaster
from CocoTBFramework.components.gaxi.gaxi_slave import GAXISlave
from CocoTBFramework.components.axi4.axi4_field_configs import AXI4FieldConfigHelper


class BridgeAXI4FlatTB(TBBase):
    """
    Reusable Testbench for AXI4 Bridge Crossbar Validation

    Provides infrastructure for testing NxM bridge crossbars with:
    - GAXI Master/Slave components for all 5 AXI4 channels
    - Queue-based verification (no memory models)
    - Automatic response generation
    - Configurable address map

    Architecture:
    - Master-side: AW/W masters send, B/R slaves receive
    - Slave-side: AW/W slaves receive, B/R masters send

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

        # Component lists
        self.aw_masters = []  # Master-side AW transmitters
        self.w_masters = []   # Master-side W transmitters
        self.b_slaves = []    # Master-side B receivers
        self.ar_masters = []  # Master-side AR transmitters
        self.r_slaves = []    # Master-side R receivers

        self.aw_slaves = []   # Slave-side AW receivers
        self.w_slaves = []    # Slave-side W receivers
        self.b_masters = []   # Slave-side B transmitters
        self.ar_slaves = []   # Slave-side AR receivers
        self.r_masters = []   # Slave-side R transmitters

        # Initialize components
        self._init_master_side_components()
        self._init_slave_side_components()

        self.log.info(f"Initialized {num_masters}x{num_slaves} Bridge testbench")
        self.log.info(f"  Data Width: {data_width}, Addr Width: {addr_width}, ID Width: {id_width}")

    def _init_master_side_components(self):
        """Initialize master-side GAXI components (masters drive AW/W/AR, slaves receive B/R)"""
        for m in range(self.num_masters):
            # AW channel - master drives
            aw_master = GAXIMaster(
                dut=self.dut,
                title=f"AW_M{m}",
                prefix=f"s{m}_axi4_",
                clock=self.clk,
                field_config=AXI4FieldConfigHelper.create_aw_field_config(
                    self.id_width, self.addr_width, 1
                ),
                pkt_prefix="aw",
                multi_sig=True,
                log=self.log
            )
            self.aw_masters.append(aw_master)

            # W channel - master drives
            w_master = GAXIMaster(
                dut=self.dut,
                title=f"W_M{m}",
                prefix=f"s{m}_axi4_",
                clock=self.clk,
                field_config=AXI4FieldConfigHelper.create_w_field_config(
                    self.data_width, 1
                ),
                pkt_prefix="w",
                multi_sig=True,
                log=self.log
            )
            self.w_masters.append(w_master)

            # B channel - master receives responses
            b_slave = GAXISlave(
                dut=self.dut,
                title=f"B_M{m}",
                prefix=f"s{m}_axi4_",
                clock=self.clk,
                field_config=AXI4FieldConfigHelper.create_b_field_config(
                    self.id_width, 1
                ),
                pkt_prefix="b",
                multi_sig=True,
                log=self.log
            )
            self.b_slaves.append(b_slave)

            # AR channel - master drives
            ar_master = GAXIMaster(
                dut=self.dut,
                title=f"AR_M{m}",
                prefix=f"s{m}_axi4_",
                clock=self.clk,
                field_config=AXI4FieldConfigHelper.create_ar_field_config(
                    self.id_width, self.addr_width, 1
                ),
                pkt_prefix="ar",
                multi_sig=True,
                log=self.log
            )
            self.ar_masters.append(ar_master)

            # R channel - master receives responses
            r_slave = GAXISlave(
                dut=self.dut,
                title=f"R_M{m}",
                prefix=f"s{m}_axi4_",
                clock=self.clk,
                field_config=AXI4FieldConfigHelper.create_r_field_config(
                    self.id_width, self.data_width, 1
                ),
                pkt_prefix="r",
                multi_sig=True,
                log=self.log
            )
            self.r_slaves.append(r_slave)

    def _init_slave_side_components(self):
        """Initialize slave-side GAXI components (slaves receive AW/W/AR, masters send B/R)"""
        for s in range(self.num_slaves):
            # AW channel - slave receives
            aw_slave = GAXISlave(
                dut=self.dut,
                title=f"AW_S{s}",
                prefix=f"m{s}_axi4_",
                clock=self.clk,
                field_config=AXI4FieldConfigHelper.create_aw_field_config(
                    self.id_width, self.addr_width, 1
                ),
                pkt_prefix="aw",
                multi_sig=True,
                log=self.log
            )
            # Add callback to generate B response
            aw_slave.add_callback(self._create_b_responder(s))
            self.aw_slaves.append(aw_slave)

            # W channel - slave receives
            w_slave = GAXISlave(
                dut=self.dut,
                title=f"W_S{s}",
                prefix=f"m{s}_axi4_",
                clock=self.clk,
                field_config=AXI4FieldConfigHelper.create_w_field_config(
                    self.data_width, 1
                ),
                pkt_prefix="w",
                multi_sig=True,
                log=self.log
            )
            self.w_slaves.append(w_slave)

            # B channel - slave sends responses
            b_master = GAXIMaster(
                dut=self.dut,
                title=f"B_S{s}",
                prefix=f"m{s}_axi4_",
                clock=self.clk,
                field_config=AXI4FieldConfigHelper.create_b_field_config(
                    self.id_width, 1
                ),
                pkt_prefix="b",
                multi_sig=True,
                log=self.log
            )
            self.b_masters.append(b_master)

            # AR channel - slave receives
            ar_slave = GAXISlave(
                dut=self.dut,
                title=f"AR_S{s}",
                prefix=f"m{s}_axi4_",
                clock=self.clk,
                field_config=AXI4FieldConfigHelper.create_ar_field_config(
                    self.id_width, self.addr_width, 1
                ),
                pkt_prefix="ar",
                multi_sig=True,
                log=self.log
            )
            # Add callback to generate R response
            ar_slave.add_callback(self._create_r_responder(s))
            self.ar_slaves.append(ar_slave)

            # R channel - slave sends responses
            r_master = GAXIMaster(
                dut=self.dut,
                title=f"R_S{s}",
                prefix=f"m{s}_axi4_",
                clock=self.clk,
                field_config=AXI4FieldConfigHelper.create_r_field_config(
                    self.id_width, self.data_width, 1
                ),
                pkt_prefix="r",
                multi_sig=True,
                log=self.log
            )
            self.r_masters.append(r_master)

    def _create_b_responder(self, slave_idx):
        """Create callback to send B response when AW received"""
        def b_responder(aw_pkt):
            cocotb.start_soon(self._send_b_response(slave_idx, aw_pkt))
        return b_responder

    async def _send_b_response(self, slave_idx, aw_pkt):
        """Send B response for received AW"""
        await RisingEdge(self.clk)
        b_pkt = self.b_masters[slave_idx].create_packet(
            id=aw_pkt.id,
            resp=0
        )
        await self.b_masters[slave_idx].send(b_pkt)

    def _create_r_responder(self, slave_idx):
        """Create callback to send R response when AR received"""
        def r_responder(ar_pkt):
            cocotb.start_soon(self._send_r_response(slave_idx, ar_pkt))
        return r_responder

    async def _send_r_response(self, slave_idx, ar_pkt):
        """Send R response for received AR"""
        await RisingEdge(self.clk)
        burst_len = ar_pkt.len + 1
        for i in range(burst_len):
            # Echo address as data for easy verification
            data = ar_pkt.addr + (i * 4)
            r_pkt = self.r_masters[slave_idx].create_packet(
                id=ar_pkt.id,
                data=data,
                resp=0,
                last=1 if i == burst_len - 1 else 0
            )
            await self.r_masters[slave_idx].send(r_pkt)

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
        Send write transaction (AW + W)

        Args:
            master_idx: Master port index (0 to num_masters-1)
            address: Transaction address
            data: Write data
            txn_id: Transaction ID

        Returns:
            Tuple of (aw_pkt, w_pkt)
        """
        # Send AW
        aw_pkt = self.aw_masters[master_idx].create_packet(
            addr=address,
            id=txn_id,
            len=0,  # Single beat
            size=2,  # 4 bytes
            burst=1
        )
        await self.aw_masters[master_idx].send(aw_pkt)

        # Send W
        w_pkt = self.w_masters[master_idx].create_packet(
            data=data,
            last=1,
            strb=0xF
        )
        await self.w_masters[master_idx].send(w_pkt)

        self.log.debug(f"M{master_idx} write: addr=0x{address:X}, data=0x{data:X}, id={txn_id}")
        return aw_pkt, w_pkt

    async def read_transaction(self, master_idx, address, txn_id=0):
        """
        Send read transaction (AR)

        Args:
            master_idx: Master port index (0 to num_masters-1)
            address: Transaction address
            txn_id: Transaction ID

        Returns:
            ar_pkt
        """
        ar_pkt = self.ar_masters[master_idx].create_packet(
            addr=address,
            id=txn_id,
            len=0,  # Single beat
            size=2,  # 4 bytes
            burst=1
        )
        await self.ar_masters[master_idx].send(ar_pkt)

        self.log.debug(f"M{master_idx} read: addr=0x{address:X}, id={txn_id}")
        return ar_pkt

    # =========================================================================
    # TEST SCENARIO METHODS
    # =========================================================================

    async def test_basic_routing(self, num_transactions=10):
        """
        Test basic address routing from masters to slaves

        Args:
            num_transactions: Number of transactions to send

        Returns:
            True if test passes, False otherwise
        """
        self.log.info(f"Starting basic routing test ({num_transactions} transactions)")

        # Send writes to alternating slaves
        for i in range(num_transactions):
            slave_idx = i % self.num_slaves
            master_idx = i % self.num_masters
            address = self.slave_base_addrs[slave_idx] + (i * 4)
            data = 0xA0000000 + i

            await self.write_transaction(master_idx, address, data, txn_id=i)

        # Wait for all transactions to complete
        await self.wait_clocks(self.clk_name, 50)

        # Verify routing
        success = True
        for s in range(self.num_slaves):
            expected_count = (num_transactions + self.num_slaves - 1 - s) // self.num_slaves
            actual_count = len(self.aw_slaves[s]._recvQ)

            if actual_count != expected_count:
                self.log.error(f"Slave {s}: Expected {expected_count} transactions, got {actual_count}")
                success = False
            else:
                self.log.info(f"✓ Slave {s}: Received {actual_count} transactions as expected")

        return success

    async def test_id_routing(self, num_transactions=10):
        """
        Test transaction ID routing through B and R channels

        Args:
            num_transactions: Number of transactions to send

        Returns:
            True if test passes, False otherwise
        """
        self.log.info(f"Starting ID routing test ({num_transactions} transactions)")

        # Send transactions with different IDs
        for i in range(num_transactions):
            master_idx = 0  # Use first master
            slave_idx = i % self.num_slaves
            address = self.slave_base_addrs[slave_idx] + (i * 4)
            data = 0xB0000000 + i
            txn_id = i % (2 ** self.id_width)  # Cycle through IDs

            await self.write_transaction(master_idx, address, data, txn_id=txn_id)

        # Wait for all responses
        await self.wait_clocks(self.clk_name, 50)

        # Verify all B responses received
        b_count = len(self.b_slaves[0]._recvQ)
        if b_count != num_transactions:
            self.log.error(f"Expected {num_transactions} B responses, got {b_count}")
            return False

        self.log.info(f"✓ All {num_transactions} B responses received")
        return True

    async def test_concurrent_masters(self, transactions_per_master=5):
        """
        Test concurrent transactions from multiple masters

        Args:
            transactions_per_master: Number of transactions from each master

        Returns:
            True if test passes, False otherwise
        """
        self.log.info(f"Starting concurrent masters test ({transactions_per_master} per master)")

        # Send transactions from all masters concurrently
        tasks = []
        for m in range(self.num_masters):
            async def send_from_master(master_idx):
                for i in range(transactions_per_master):
                    address = self.slave_base_addrs[i % self.num_slaves] + (i * 4)
                    data = 0xC0000000 + (master_idx << 16) + i
                    await self.write_transaction(master_idx, address, data, txn_id=i)

            tasks.append(cocotb.start_soon(send_from_master(m)))

        # Wait for all tasks
        for task in tasks:
            await task

        # Wait for completion
        await self.wait_clocks(self.clk_name, 100)

        # Verify total transactions
        total_expected = self.num_masters * transactions_per_master
        total_actual = sum(len(slave._recvQ) for slave in self.aw_slaves)

        if total_actual != total_expected:
            self.log.error(f"Expected {total_expected} total transactions, got {total_actual}")
            return False

        self.log.info(f"✓ All {total_expected} concurrent transactions completed")
        return True
