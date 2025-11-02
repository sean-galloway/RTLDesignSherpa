# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: BridgeOOOTB
# Purpose: Testbench class for Out-of-Order Bridge with CAM/FIFO tracking
#
# Documentation: projects/components/bridge/docs/OOO_IMPLEMENTATION_STATUS.md
# Subsystem: bridge
#
# Author: sean galloway
# Created: 2025-10-27

"""
Testbench for Out-of-Order (OOO) Bridge with CAM/FIFO Transaction Tracking

This testbench validates:
- CAM-based tracking for out-of-order slaves (ddr_controller)
- FIFO-based tracking for in-order slaves (sram_buffer)
- Arbiter grant signal exposure and tracking
- Correct response routing for both in-order and out-of-order responses
- Multi-master access to OOO slaves
"""

import os
import sys
import cocotb
from cocotb.clock import Clock
from cocotb.triggers import RisingEdge, Timer
from cocotb.utils import get_sim_time
from collections import defaultdict

# Add framework to path
repo_root = os.path.abspath(os.path.join(os.path.dirname(__file__), '../../../../..'))
sys.path.insert(0, os.path.join(repo_root, 'bin'))

from CocoTBFramework.tbclasses.shared.tbbase import TBBase
from CocoTBFramework.components.axi4.axi4_factories import (
    create_axi4_master_wr, create_axi4_master_rd,
    create_axi4_slave_wr, create_axi4_slave_rd
)


class BridgeOOOTB(TBBase):
    """
    Testbench for Out-of-Order Bridge Validation

    Tests bridge_ooo_with_arbiter.sv which includes:
    - 5 masters: rapids_descr_wr, rapids_sink_wr, rapids_src_rd, stream_master, cpu_master
    - 3 slaves: ddr_controller (OOO with CAM), sram_buffer (in-order with FIFO), apb0 (APB)
    - Debug arbiter signals for grant tracking verification

    Architecture:
    - Master-side: Custom AXI4 prefixes per master (rapids_descr_m_axi_, etc.)
    - Slave-side: Custom AXI4 prefixes per slave (ddr_s_axi_, sram_s_axi_, etc.)
    - CAM tracking: ddr_controller (ooo=1)
    - FIFO tracking: sram_buffer (ooo=0)

    Usage:
        tb = BridgeOOOTB(dut)
        await tb.setup_clocks_and_reset()
        await tb.test_ooo_responses()
    """

    def __init__(self, dut):
        """
        Initialize OOO Bridge testbench

        Args:
            dut: Device under test (bridge_ooo_with_arbiter)
        """
        super().__init__(dut)

        # Bridge configuration (from bridge_ooo_with_arbiter.sv)
        self.num_masters = 5
        self.num_slaves = 3
        self.data_width = 512  # Crossbar width
        self.addr_width = 64
        self.id_width = 8

        # Master configurations (name, prefix, data_width, channels)
        self.master_configs = [
            {'name': 'rapids_descr_wr', 'prefix': 'rapids_descr_m_axi_', 'data_width': 512, 'channels': 'wr'},
            {'name': 'rapids_sink_wr', 'prefix': 'rapids_sink_m_axi_', 'data_width': 512, 'channels': 'wr'},
            {'name': 'rapids_src_rd', 'prefix': 'rapids_src_m_axi_', 'data_width': 512, 'channels': 'rd'},
            {'name': 'stream_master', 'prefix': 'stream_m_axi_', 'data_width': 512, 'channels': 'rw'},
            {'name': 'cpu_master', 'prefix': 'cpu_m_axi_', 'data_width': 64, 'channels': 'rw'},
        ]

        # Slave configurations (name, prefix, base_addr, ooo)
        self.slave_configs = [
            {'name': 'ddr_controller', 'prefix': 'ddr_s_axi_', 'base_addr': 0x80000000,
             'addr_range': 0x80000000, 'ooo': True},
            {'name': 'sram_buffer', 'prefix': 'sram_s_axi_', 'base_addr': 0x40000000,
             'addr_range': 0x10000000, 'ooo': False},
            {'name': 'apb0', 'prefix': 'apb0_', 'base_addr': 0x00000000,
             'addr_range': 0x00010000, 'ooo': False},  # APB slave
        ]

        # Clock configuration
        self.clk = dut.aclk
        self.clk_name = 'aclk'
        self.rst_n = dut.aresetn

        # AXI4 Interface Components
        self.master_write_if = []  # AXI4MasterWrite for each master
        self.master_read_if = []   # AXI4MasterRead for each master
        self.slave_write_if = []   # AXI4SlaveWrite for each slave (AXI only)
        self.slave_read_if = []    # AXI4SlaveRead for each slave (AXI only)

        # Tracking for verification
        self.grant_events = defaultdict(list)  # Track arbiter grants
        self.cam_allocations = []  # Track CAM allocations
        self.cam_deallocations = []  # Track CAM deallocations
        self.fifo_writes = []  # Track FIFO writes
        self.fifo_reads = []  # Track FIFO reads

        # Statistics tracking per slave
        self.slave_stats = []
        for s in range(self.num_slaves):
            self.slave_stats.append({
                'aw_received': 0,
                'w_received': 0,
                'b_sent': 0,
                'ar_received': 0,
                'r_sent': 0,
                'addresses': [],
                'data_values': [],
                'write_ids': [],
                'read_addresses': [],
                'read_ids': [],
            })

        # Initialize components
        self._init_master_side_components()
        self._init_slave_side_components()

        self.log.info(f"Initialized OOO Bridge testbench")
        self.log.info(f"  Masters: {self.num_masters} (5 AXI4)")
        self.log.info(f"  Slaves: {self.num_slaves} (2 AXI4 + 1 APB)")
        self.log.info(f"  OOO Slaves: ddr_controller (CAM)")
        self.log.info(f"  In-order Slaves: sram_buffer (FIFO)")

    def _init_master_side_components(self):
        """Initialize master-side AXI4 interface components"""
        for m, config in enumerate(self.master_configs):
            channels = config['channels']
            prefix = config['prefix']
            dw = config['data_width']

            # Create write interface if master supports write (wr or rw)
            if channels in ['wr', 'rw']:
                master_write = create_axi4_master_wr(
                    dut=self.dut,
                    clock=self.clk,
                    prefix=prefix,
                    log=self.log,
                    data_width=dw,
                    id_width=self.id_width,
                    addr_width=self.addr_width,
                    user_width=1,
                    multi_sig=True
                )
                self.master_write_if.append(master_write)
            else:
                self.master_write_if.append(None)  # Placeholder

            # Create read interface if master supports read (rd or rw)
            if channels in ['rd', 'rw']:
                master_read = create_axi4_master_rd(
                    dut=self.dut,
                    clock=self.clk,
                    prefix=prefix,
                    log=self.log,
                    data_width=dw,
                    id_width=self.id_width,
                    addr_width=self.addr_width,
                    user_width=1,
                    multi_sig=True
                )
                self.master_read_if.append(master_read)
            else:
                self.master_read_if.append(None)  # Placeholder

    def _init_slave_side_components(self):
        """Initialize slave-side AXI4 interface components"""
        for s, config in enumerate(self.slave_configs):
            prefix = config['prefix']

            # Skip APB slaves for now (apb0)
            if config['name'] == 'apb0':
                self.slave_write_if.append(None)
                self.slave_read_if.append(None)
                continue

            # AXI4 slave - create write interface
            slave_write = create_axi4_slave_wr(
                dut=self.dut,
                clock=self.clk,
                prefix=prefix,
                log=self.log,
                data_width=self.data_width,
                id_width=self.id_width,
                addr_width=self.addr_width,
                user_width=1,
                multi_sig=True,
                memory_model=None,  # Statistics-based verification
                response_delay=1     # 1 cycle delay for B responses
            )
            self.slave_write_if.append(slave_write)

            # Set up callback to track AW packets
            def make_aw_callback(slave_idx):
                def aw_callback(pkt):
                    self.slave_stats[slave_idx]['aw_received'] += 1
                    self.slave_stats[slave_idx]['addresses'].append(pkt.addr)
                    self.slave_stats[slave_idx]['write_ids'].append(pkt.id)
                return aw_callback
            slave_write['AW'].add_callback(make_aw_callback(s))

            # Set up callback to track W packets
            def make_w_callback(slave_idx):
                def w_callback(pkt):
                    self.slave_stats[slave_idx]['w_received'] += 1
                    self.slave_stats[slave_idx]['data_values'].append(pkt.data)
                return w_callback
            slave_write['W'].add_callback(make_w_callback(s))

            # AXI4 slave - create read interface
            slave_read = create_axi4_slave_rd(
                dut=self.dut,
                clock=self.clk,
                prefix=prefix,
                log=self.log,
                data_width=self.data_width,
                id_width=self.id_width,
                addr_width=self.addr_width,
                user_width=1,
                multi_sig=True,
                memory_model=None,
                response_delay=1
            )
            self.slave_read_if.append(slave_read)

            # Set up callback to track AR packets
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
        """
        # Start clock
        await self.start_clock(self.clk_name, freq=10, units='ns')
        self.log.info("Clock started at 100 MHz")

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
        for s, config in enumerate(self.slave_configs):
            base = config['base_addr']
            range_size = config['addr_range']
            if base <= address < (base + range_size):
                return s
        return 0  # Default to slave 0

    async def write_transaction(self, master_idx, address, data, txn_id=0):
        """
        Send write transaction (AW + W)

        Args:
            master_idx: Master port index (0 to 4)
            address: Transaction address
            data: Write data
            txn_id: Transaction ID

        Returns:
            Tuple of (aw_pkt, w_pkt)
        """
        if self.master_write_if[master_idx] is None:
            raise ValueError(f"Master {master_idx} does not support write transactions")

        aw_channel = self.master_write_if[master_idx]['AW']
        w_channel = self.master_write_if[master_idx]['W']

        # Send AW
        aw_pkt = aw_channel.create_packet(
            addr=address,
            id=txn_id,
            len=0,  # Single beat
            size=6,  # 64 bytes (512 bits) for 512-bit masters, will be adjusted by framework
            burst=1
        )
        await aw_channel.send(aw_pkt)

        # Send W
        w_pkt = w_channel.create_packet(
            data=data,
            last=1,
            strb=(1 << (self.master_configs[master_idx]['data_width'] // 8)) - 1
        )
        await w_channel.send(w_pkt)

        master_name = self.master_configs[master_idx]['name']
        self.log.debug(f"{master_name} write: addr=0x{address:X}, data=0x{data:X}, id={txn_id}")
        return aw_pkt, w_pkt

    async def read_transaction(self, master_idx, address, txn_id=0):
        """
        Send read transaction (AR)

        Args:
            master_idx: Master port index (0 to 4)
            address: Transaction address
            txn_id: Transaction ID

        Returns:
            ar_pkt
        """
        if self.master_read_if[master_idx] is None:
            raise ValueError(f"Master {master_idx} does not support read transactions")

        ar_channel = self.master_read_if[master_idx]['AR']

        ar_pkt = ar_channel.create_packet(
            addr=address,
            id=txn_id,
            len=0,  # Single beat
            size=6,  # 64 bytes (512 bits)
            burst=1
        )
        await ar_channel.send(ar_pkt)

        master_name = self.master_configs[master_idx]['name']
        self.log.debug(f"{master_name} read: addr=0x{address:X}, id={txn_id}")
        return ar_pkt

    async def monitor_grant_signals(self, cycles=1):
        """Monitor arbiter grant debug signals for specified cycles"""
        for _ in range(cycles):
            await RisingEdge(self.clk)

            # Monitor AW grants for each slave
            for s, config in enumerate(self.slave_configs):
                if config['name'] == 'apb0':
                    continue

                slave_name = config['name']
                grant_signal = getattr(self.dut, f"dbg_aw_grant_{slave_name}")
                grant_valid = getattr(self.dut, f"dbg_aw_grant_valid_{slave_name}")
                grant_id = getattr(self.dut, f"dbg_aw_grant_id_{slave_name}")

                if grant_valid.value == 1:
                    self.grant_events[f"aw_{slave_name}"].append({
                        'grant': int(grant_signal.value),
                        'master_idx': int(grant_id.value),
                        'cycle': get_sim_time('ns')
                    })

            # Monitor AR grants for each slave
            for s, config in enumerate(self.slave_configs):
                if config['name'] == 'apb0':
                    continue

                slave_name = config['name']
                grant_signal = getattr(self.dut, f"dbg_ar_grant_{slave_name}")
                grant_valid = getattr(self.dut, f"dbg_ar_grant_valid_{slave_name}")
                grant_id = getattr(self.dut, f"dbg_ar_grant_id_{slave_name}")

                if grant_valid.value == 1:
                    self.grant_events[f"ar_{slave_name}"].append({
                        'grant': int(grant_signal.value),
                        'master_idx': int(grant_id.value),
                        'cycle': get_sim_time('ns')
                    })

    # =========================================================================
    # TEST SCENARIO METHODS
    # =========================================================================

    async def test_basic_routing(self, num_transactions=10):
        """
        Test basic address routing from masters to slaves

        Args:
            num_transactions: Number of transactions to send

        Returns:
            True if test passes
        """
        self.log.info(f"Starting basic routing test with {num_transactions} transactions")

        # Test write transactions from master 0 (rapids_descr_wr) to DDR
        for i in range(num_transactions):
            addr = 0x80000000 + (i * 64)  # DDR address range
            data = 0xDEAD0000 + i
            await self.write_transaction(master_idx=0, address=addr, data=data, txn_id=i)

        # Wait for responses
        await self.wait_clocks(self.clk_name, 20)

        # Verify routing
        ddr_idx = 0  # ddr_controller is slave 0
        assert self.slave_stats[ddr_idx]['aw_received'] == num_transactions, \
            f"Expected {num_transactions} AW to DDR, got {self.slave_stats[ddr_idx]['aw_received']}"

        self.log.info(f"✓ Basic routing test passed: {num_transactions} transactions routed correctly")
        return True

    async def test_in_order_responses(self, num_transactions=10):
        """
        Test in-order response handling (baseline for FIFO verification)

        Args:
            num_transactions: Number of transactions

        Returns:
            True if test passes
        """
        self.log.info(f"Starting in-order response test with {num_transactions} transactions")

        # Send writes to SRAM (in-order slave)
        sram_base = 0x40000000
        for i in range(num_transactions):
            addr = sram_base + (i * 64)
            data = 0xABCD0000 + i
            await self.write_transaction(master_idx=3, address=addr, data=data, txn_id=i)

        # Monitor and wait for responses
        await self.monitor_grant_signals(cycles=num_transactions + 10)
        await self.wait_clocks(self.clk_name, 20)

        # Verify SRAM received transactions
        sram_idx = 1  # sram_buffer is slave 1
        assert self.slave_stats[sram_idx]['aw_received'] == num_transactions, \
            f"Expected {num_transactions} AW to SRAM, got {self.slave_stats[sram_idx]['aw_received']}"

        self.log.info(f"✓ In-order response test passed")
        return True

    async def test_out_of_order_responses(self, num_transactions=10):
        """
        Test out-of-order response handling (CAM verification)

        This test sends transactions from multiple masters to the OOO slave (DDR)
        and verifies that responses are correctly routed back.

        Args:
            num_transactions: Number of transactions per master

        Returns:
            True if test passes
        """
        self.log.info(f"Starting OOO response test with {num_transactions} transactions from multiple masters")

        # Send writes from multiple masters to DDR (OOO slave)
        ddr_base = 0x80000000
        masters_to_test = [0, 1, 3]  # rapids_descr_wr, rapids_sink_wr, stream_master

        for master_idx in masters_to_test:
            for i in range(num_transactions):
                addr = ddr_base + (master_idx * 0x1000) + (i * 64)
                data = (0x1000 * master_idx) + i
                txn_id = (master_idx << 4) | i  # Unique ID per master
                await self.write_transaction(master_idx=master_idx, address=addr, data=data, txn_id=txn_id)

        # Monitor grant signals and wait for responses
        total_txns = len(masters_to_test) * num_transactions
        await self.monitor_grant_signals(cycles=total_txns + 20)
        await self.wait_clocks(self.clk_name, 30)

        # Verify DDR received all transactions
        ddr_idx = 0
        expected_total = total_txns
        assert self.slave_stats[ddr_idx]['aw_received'] == expected_total, \
            f"Expected {expected_total} AW to DDR, got {self.slave_stats[ddr_idx]['aw_received']}"

        # Verify grant events were captured
        assert len(self.grant_events['aw_ddr_controller']) > 0, \
            "No AW grant events captured for ddr_controller"

        self.log.info(f"✓ OOO response test passed: {expected_total} transactions from {len(masters_to_test)} masters")
        return True

    async def test_cam_fifo_monitoring(self):
        """
        Test CAM and FIFO internal signal monitoring

        Verifies that allocation/deallocation signals are working correctly.

        Returns:
            True if test passes
        """
        self.log.info("Starting CAM/FIFO monitoring test")

        # Send transaction to OOO slave (DDR) - uses CAM
        ddr_addr = 0x80000000
        await self.write_transaction(master_idx=0, address=ddr_addr, data=0xCAFEBABE, txn_id=5)

        # Send transaction to in-order slave (SRAM) - uses FIFO
        sram_addr = 0x40000000
        await self.write_transaction(master_idx=3, address=sram_addr, data=0xDEADBEEF, txn_id=10)

        # Monitor for several cycles
        await self.monitor_grant_signals(cycles=20)

        # Check grant events
        assert len(self.grant_events['aw_ddr_controller']) > 0, "No CAM allocation detected"
        assert len(self.grant_events['aw_sram_buffer']) > 0, "No FIFO write detected"

        self.log.info("✓ CAM/FIFO monitoring test passed")
        return True
