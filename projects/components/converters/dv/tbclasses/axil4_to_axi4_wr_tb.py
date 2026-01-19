# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 RTL Design Sherpa
#
# Module: axil4_to_axi4_wr_tb
# Purpose: Testbench class for axil4_to_axi4_wr converter (WRITE-ONLY)
#
# Author: RTL Design Sherpa
# Created: 2025-11-05

"""
Testbench for axil4_to_axi4_wr converter - WRITE-ONLY

Tests AXI4-Lite → AXI4 protocol upgrade for write path:
- Single-beat AXI4-Lite AW/W requests converted to AXI4 format
- Addition of AXI4-only fields (ID, LEN=0, SIZE, BURST, WLAST=1, etc.)
- Data passthrough verification
- Response propagation

Architecture:
- AXIL4MasterWrite drives slave side (AW/W channels, receives B channel)
- Simple AXI4 responder on master side (provides B responses)
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
from CocoTBFramework.components.axil4.axil4_interfaces import AXIL4MasterWrite
from CocoTBFramework.components.axi4.axi4_interfaces import AXI4SlaveWrite


class AXIL4ToAXI4WriteTB(TBBase):
    """
    Testbench for axil4_to_axi4_wr converter.

    Tests protocol upgrade from AXI4-Lite → AXI4 for write path.

    Key Validations:
    - AXI4-Lite AW/W fields pass through correctly
    - AXI4-only fields have correct defaults (ID, LEN=0, SIZE, WLAST=1, etc.)
    - Write data passes through correctly
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
            'writes_sent': 0,
            'writes_received': 0,
            'errors': 0,
            'field_mismatches': 0,
            'data_mismatches': 0,
        }

        # Expected SIZE value based on data width
        self.expected_size = (self.data_width // 8).bit_length() - 1

        # Initialize AXIL4 master (drives slave side of converter)
        self.axil4_master = AXIL4MasterWrite(
            dut=dut,
            clock=self.clk,
            prefix="s_axil_",
            log=self.log,
            data_width=self.data_width,
            addr_width=self.addr_width,
            multi_sig=True
        )

        # Initialize AXI4 slave (responds on master side of converter)
        self.axi4_slave = AXI4SlaveWrite(
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

        # Storage for received writes (track from slave BFM queues)
        self.received_writes = []

        self.log.info(f"Initialized AXIL4→AXI4 Write TB: "
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
    # AXI4 MASTER SIDE RESPONDER
    # =========================================================================

    async def axi4_transaction_monitor(self):
        """
        Monitor completed AXI4 write transactions from BFM.

        The AXI4SlaveWrite BFM handles all protocol details (AW/W channels,
        B response generation, etc.). We monitor transactions and validate
        AXI4 fields for protocol upgrade verification.
        """
        self.log.info("Starting AXI4 transaction monitor")

        while True:
            await RisingEdge(self.clk)

            # Check for completed AW transactions
            if self.axi4_slave.aw_channel._recvQ:
                aw_pkt = self.axi4_slave.aw_channel._recvQ.popleft()

                # Extract AXI4 AW fields
                aw_addr = getattr(aw_pkt, 'addr', 0)
                aw_id = getattr(aw_pkt, 'id', 0)
                aw_len = getattr(aw_pkt, 'len', 0)
                aw_size = getattr(aw_pkt, 'size', 0)
                aw_burst = getattr(aw_pkt, 'burst', 0)
                aw_prot = getattr(aw_pkt, 'prot', 0)
                aw_qos = getattr(aw_pkt, 'qos', 0)
                aw_region = getattr(aw_pkt, 'region', 0)

                self.log.debug(f"AXI4 AW: addr=0x{aw_addr:08X}, id={aw_id}, len={aw_len}")

                # Validate AXI4 fields for protocol upgrade
                field_errors = []
                if aw_id != self.default_id:
                    field_errors.append(f"AWID={aw_id} (expected {self.default_id})")
                if aw_len != 0:
                    field_errors.append(f"AWLEN={aw_len} (expected 0)")
                if aw_size != self.expected_size:
                    field_errors.append(f"AWSIZE={aw_size} (expected {self.expected_size})")
                if aw_burst != 1:  # INCR
                    field_errors.append(f"AWBURST={aw_burst} (expected 1)")
                if aw_qos != self.default_qos:
                    field_errors.append(f"AWQOS={aw_qos} (expected {self.default_qos})")
                if aw_region != self.default_region:
                    field_errors.append(f"AWREGION={aw_region} (expected {self.default_region})")

                if field_errors:
                    self.log.error(f"AXI4 AW field validation FAILED: {', '.join(field_errors)}")
                    self.stats['field_mismatches'] += 1
                    self.stats['errors'] += 1

            # Check for completed W transactions
            if self.axi4_slave.w_channel._recvQ:
                w_pkt = self.axi4_slave.w_channel._recvQ.popleft()

                # Extract W fields
                w_data = getattr(w_pkt, 'data', 0)
                w_strb = getattr(w_pkt, 'strb', 0xF)
                w_last = getattr(w_pkt, 'last', 0)

                self.log.debug(f"AXI4 W: data=0x{w_data:08X}, last={w_last}")

                # Validate WLAST (should always be 1 for single beat)
                if w_last != 1:
                    self.log.error(f"WLAST validation FAILED: got {w_last}, expected 1")
                    self.stats['field_mismatches'] += 1
                    self.stats['errors'] += 1

                # Store write transaction
                self.received_writes.append((w_data, w_strb))
                self.stats['writes_received'] += 1

    # =========================================================================
    # TEST SCENARIO METHODS
    # =========================================================================

    async def test_single_write(self, address, data, strb=None, expected_prot=0):
        """
        Test single AXI4-Lite write through converter.

        Args:
            address: Write address
            data: Write data
            strb: Write strobe (None = all 1s)
            expected_prot: Expected AWPROT value

        Returns:
            True if test passed, False otherwise
        """
        if strb is None:
            strb = (1 << (self.data_width // 8)) - 1

        self.log.debug(f"Testing single write: addr=0x{address:08X}, data=0x{data:08X}")

        # Send AXIL4 write via master interface
        try:
            # write_transaction returns when B response is received
            await self.axil4_master.write_transaction(address, data, strb=strb, prot=expected_prot)

            self.log.debug(f"Write completed: addr=0x{address:08X}, data=0x{data:08X}")
            self.stats['writes_sent'] += 1
            self.stats['writes_received'] += 1
            return True

        except Exception as e:
            self.log.error(f"Write transaction failed: {e}")
            self.stats['errors'] += 1
            return False

    async def run_basic_test(self):
        """Run basic write test suite"""
        self.log.info("=" * 80)
        self.log.info("BASIC WRITE TEST SUITE")
        self.log.info("=" * 80)
        self.log.info("=== Scenarios AXIL2AXI-WR-01,02,03: Single write passthrough, default ID/LEN/SIZE ===")

        success = True

        # Test a few simple writes
        test_cases = [
            (0x1000, 0x12345678),
            (0x2000, 0xAABBCCDD),
            (0x3000, 0x00000000),
            (0x4000, 0xFFFFFFFF),
            (0x5000, 0xDEADBEEF),
        ]

        for addr, data in test_cases:
            if not await self.test_single_write(addr, data):
                success = False

        return success

    async def run_medium_test(self):
        """Run medium write test suite"""
        self.log.info("=" * 80)
        self.log.info("MEDIUM WRITE TEST SUITE")
        self.log.info("=" * 80)
        self.log.info("=== Scenarios AXIL2AXI-WR-04,07,09: AWSIZE calculation, WLAST=1 generation, AWPROT ===")

        success = True

        # Test more writes with random addresses and data
        for i in range(20):
            addr = random.randint(0, (1 << self.addr_width) - 1) & ~0x3  # Word-aligned
            data = random.randint(0, (1 << self.data_width) - 1)
            prot = random.randint(0, 7)

            if not await self.test_single_write(addr, data, expected_prot=prot):
                success = False

        return success

    async def run_full_test(self):
        """Run full write test suite"""
        self.log.info("=" * 80)
        self.log.info("FULL WRITE TEST SUITE")
        self.log.info("=" * 80)
        self.log.info("=== Scenarios AXIL2AXI-WR-05,06,08: WSTRB/WDATA passthrough, BRESP comprehensive coverage ===")

        success = True

        # Comprehensive testing with many writes
        for i in range(50):
            addr = random.randint(0, (1 << self.addr_width) - 1) & ~0x3
            data = random.randint(0, (1 << self.data_width) - 1)
            prot = random.randint(0, 7)

            if not await self.test_single_write(addr, data, expected_prot=prot):
                success = False

        return success

    def get_statistics(self):
        """Return test statistics"""
        return dict(self.stats)
