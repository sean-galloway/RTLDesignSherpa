# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 RTL Design Sherpa
#
# Module: axil4_to_axi4_rd_tb
# Purpose: Testbench class for axil4_to_axi4_rd converter (READ-ONLY)
#
# Author: RTL Design Sherpa
# Created: 2025-11-05

"""
Testbench for axil4_to_axi4_rd converter - READ-ONLY

Tests AXI4-Lite → AXI4 protocol upgrade for read path:
- Single-beat AXI4-Lite AR requests converted to AXI4 format
- Addition of AXI4-only fields (ID, LEN=0, SIZE, BURST, etc.)
- Data passthrough verification
- Response propagation

Architecture:
- AXIL4MasterRead drives slave side (AR channel, receives R channel)
- Simple AXI4 responder on master side (provides R responses)
- Monitor AXI4 master outputs for field validation
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
from CocoTBFramework.components.axil4.axil4_interfaces import AXIL4MasterRead
from CocoTBFramework.components.axi4.axi4_interfaces import AXI4SlaveRead


class AXIL4ToAXI4ReadTB(TBBase):
    """
    Testbench for axil4_to_axi4_rd converter.

    Tests protocol upgrade from AXI4-Lite → AXI4 for read path.

    Key Validations:
    - AXI4-Lite AR fields pass through correctly
    - AXI4-only fields have correct defaults (ID, LEN=0, SIZE, etc.)
    - Read data passes through correctly
    - Response codes maintained
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
        self.default_id = self.convert_to_int(os.environ.get('DEFAULT_ID', '0'))
        self.default_region = self.convert_to_int(os.environ.get('DEFAULT_REGION', '0'))
        self.default_qos = self.convert_to_int(os.environ.get('DEFAULT_QOS', '0'))

        # Statistics
        self.stats = {
            'reads_sent': 0,
            'reads_received': 0,
            'errors': 0,
            'field_mismatches': 0,
            'data_mismatches': 0,
        }

        # Expected SIZE value based on data width
        self.expected_size = (self.data_width // 8).bit_length() - 1

        # Initialize AXIL4 master (drives slave side of converter)
        self.axil4_master = AXIL4MasterRead(
            dut=dut,
            clock=self.clk,
            prefix="s_axil_",
            log=self.log,
            data_width=self.data_width,
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

        # Storage for AXI4 master side monitoring (track from slave BFM queues)
        self.pending_reads = {}  # addr -> expected_data
        self.received_reads = []

        self.log.info(f"Initialized AXIL4→AXI4 Read TB: "
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
    # AXI4 MASTER SIDE RESPONDER
    # =========================================================================

    async def axi4_transaction_monitor(self):
        """
        Monitor completed AXI4 read transactions from BFM.

        The AXI4SlaveRead BFM handles all protocol details (AR channel,
        R response generation, etc.). We monitor transactions and validate
        AXI4 fields for protocol upgrade verification.
        """
        self.log.info("Starting AXI4 transaction monitor")

        while True:
            await RisingEdge(self.clk)

            # Check for completed AR transactions
            if self.axi4_slave.ar_channel._recvQ:
                ar_pkt = self.axi4_slave.ar_channel._recvQ.popleft()

                # Extract AXI4 fields
                ar_addr = getattr(ar_pkt, 'addr', 0)
                ar_id = getattr(ar_pkt, 'id', 0)
                ar_len = getattr(ar_pkt, 'len', 0)
                ar_size = getattr(ar_pkt, 'size', 0)
                ar_burst = getattr(ar_pkt, 'burst', 0)
                ar_prot = getattr(ar_pkt, 'prot', 0)
                ar_qos = getattr(ar_pkt, 'qos', 0)
                ar_region = getattr(ar_pkt, 'region', 0)

                self.log.debug(f"AXI4 AR: addr=0x{ar_addr:08X}, id={ar_id}, len={ar_len}")

                # Validate AXI4 fields for protocol upgrade
                field_errors = []
                if ar_id != self.default_id:
                    field_errors.append(f"ARID={ar_id} (expected {self.default_id})")
                if ar_len != 0:
                    field_errors.append(f"ARLEN={ar_len} (expected 0)")
                if ar_size != self.expected_size:
                    field_errors.append(f"ARSIZE={ar_size} (expected {self.expected_size})")
                if ar_burst != 1:  # INCR
                    field_errors.append(f"ARBURST={ar_burst} (expected 1)")
                if ar_qos != self.default_qos:
                    field_errors.append(f"ARQOS={ar_qos} (expected {self.default_qos})")
                if ar_region != self.default_region:
                    field_errors.append(f"ARREGION={ar_region} (expected {self.default_region})")

                if field_errors:
                    self.log.error(f"AXI4 field validation FAILED: {', '.join(field_errors)}")
                    self.stats['field_mismatches'] += 1
                    self.stats['errors'] += 1

                self.stats['reads_received'] += 1

    # =========================================================================
    # TEST SCENARIO METHODS
    # =========================================================================

    async def test_single_read(self, address, expected_prot=0):
        """
        Test single AXI4-Lite read through converter.

        Args:
            address: Read address
            expected_prot: Expected ARPROT value

        Returns:
            True if test passed, False otherwise
        """
        # Store expected data (address-based for determinism)
        expected_data = address & ((1 << self.data_width) - 1)

        self.log.debug(f"Testing single read: addr=0x{address:08X}")

        # Send AXIL4 read via master interface
        try:
            # read_transaction returns when R response is received
            read_data = await self.axil4_master.read_transaction(address, prot=expected_prot)

            # Verify data (read_transaction returns single int, not list)
            if read_data == expected_data:
                self.log.debug(f"Read data matched: 0x{read_data:08X}")
                self.stats['reads_sent'] += 1
                self.stats['reads_received'] += 1
                return True
            else:
                self.log.error(f"Data mismatch: got 0x{read_data:08X}, expected 0x{expected_data:08X}")
                self.stats['data_mismatches'] += 1
                self.stats['errors'] += 1
                return False

        except Exception as e:
            self.log.error(f"Read transaction failed: {e}")
            self.stats['errors'] += 1
            return False

    async def run_basic_test(self):
        """Run basic read test suite"""
        self.log.info("=" * 80)
        self.log.info("BASIC READ TEST SUITE")
        self.log.info("=" * 80)

        success = True

        # Test a few simple reads
        test_addresses = [0x1000, 0x2000, 0x3000, 0x4000, 0x5000]

        for addr in test_addresses:
            if not await self.test_single_read(addr):
                success = False

        return success

    async def run_medium_test(self):
        """Run medium read test suite"""
        self.log.info("=" * 80)
        self.log.info("MEDIUM READ TEST SUITE")
        self.log.info("=" * 80)

        success = True

        # Test more reads with random addresses
        for i in range(20):
            addr = random.randint(0, (1 << self.addr_width) - 1) & ~0x3  # Word-aligned
            prot = random.randint(0, 7)

            if not await self.test_single_read(addr, expected_prot=prot):
                success = False

        return success

    async def run_full_test(self):
        """Run full read test suite"""
        self.log.info("=" * 80)
        self.log.info("FULL READ TEST SUITE")
        self.log.info("=" * 80)

        success = True

        # Comprehensive testing with many reads
        for i in range(50):
            addr = random.randint(0, (1 << self.addr_width) - 1) & ~0x3
            prot = random.randint(0, 7)

            if not await self.test_single_read(addr, expected_prot=prot):
                success = False

        return success

    def get_statistics(self):
        """Return test statistics"""
        return dict(self.stats)
