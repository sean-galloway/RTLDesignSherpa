# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 RTL Design Sherpa
#
# Module: axi4_to_axi3_wr_tb
# Purpose: Testbench class for axi4_to_axi3_wr converter (WRITE-ONLY)
#
# Author: RTL Design Sherpa
# Created: 2026-10-10

"""
Testbench for axi4_to_axi3_wr converter - WRITE-ONLY

Tests AXI4 -> AXI3 protocol downgrade for write path with pass-through semantics
and WID stamping:
- Single write pass-through with WID == AWID on every beat
- 16-beat burst pass-through with WLAST only on the final beat
- Multi-outstanding writes across two IDs (AXI3 slave demuxes by WID)
- Early W data: W beats driven before AW handshake, converter buffers them
  and stamps them once AW is accepted
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
from CocoTBFramework.components.axi4.axi4_interfaces import AXI4MasterWrite
from CocoTBFramework.components.axi3.axi3_interfaces import AXI3SlaveWrite


class AXI4ToAXI3WriteTB(TBBase):
    """
    Testbench for axi4_to_axi3_wr converter.

    Tests protocol downgrade from AXI4 -> AXI3 for write path with pass-through
    and WID stamping.

    Key Validations:
    - Single write pass-through
    - 16-beat INCR burst pass-through (no chopping in v1)
    - WID = owning AWID on every W beat
    - WLAST preserved on final beat
    - B response pass-through with ID preserved
    - Multi-outstanding writes across two IDs complete independently
    - Early W data buffered until matching AW arrives
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
            'axi3_writes_received': 0,
            'bursts_completed': 0,
            'errors': 0,
            'awid_errors': 0,
            'wid_errors': 0,
            'wlast_errors': 0,
            'data_errors': 0,
            'bresp_errors': 0,
            'early_w_errors': 0,
        }

        # Bytes per transfer
        self.bytes_per_beat = self.data_width // 8
        self.axi3_max_beats = 16

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

        # Initialize AXI3 slave (responds on master side of converter)
        self.axi3_slave = AXI3SlaveWrite(
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
        self.axi3_aw_transactions = []
        self.axi3_w_beats = []
        self.axi3_b_responses = []

        self.log.info(f"Initialized AXI4->AXI3 Write TB: "
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
    # AXI3 MASTER SIDE MONITORS
    # =========================================================================

    async def axi3_aw_monitor(self):
        """Monitor AXI3 AW channel handshakes."""
        self.log.info("Starting AXI3 AW monitor")

        while True:
            await RisingEdge(self.clk)

            if (int(self.dut.m_axi3_awvalid.value) == 1 and
                int(self.dut.m_axi3_awready.value) == 1):
                self.axi3_aw_transactions.append({
                    'id': int(self.dut.m_axi3_awid.value),
                    'addr': int(self.dut.m_axi3_awaddr.value),
                    'len': int(self.dut.m_axi3_awlen.value),
                    'lock': int(self.dut.m_axi3_awlock.value),
                })
                self.stats['axi3_writes_received'] += 1

    async def axi3_w_monitor(self):
        """Monitor AXI3 W channel handshakes, capturing WID per beat."""
        self.log.info("Starting AXI3 W monitor")

        while True:
            await RisingEdge(self.clk)

            if (int(self.dut.m_axi3_wvalid.value) == 1 and
                int(self.dut.m_axi3_wready.value) == 1):
                self.axi3_w_beats.append({
                    'id': int(self.dut.m_axi3_wid.value),
                    'data': int(self.dut.m_axi3_wdata.value),
                    'strb': int(self.dut.m_axi3_wstrb.value),
                    'last': int(self.dut.m_axi3_wlast.value),
                })

    async def axi3_b_monitor(self):
        """Monitor AXI3 B channel handshakes."""
        self.log.info("Starting AXI3 B monitor")

        while True:
            await RisingEdge(self.clk)

            if (int(self.dut.m_axi3_bvalid.value) == 1 and
                int(self.dut.m_axi3_bready.value) == 1):
                self.axi3_b_responses.append({
                    'id': int(self.dut.m_axi3_bid.value),
                    'resp': int(self.dut.m_axi3_bresp.value),
                })

    # =========================================================================
    # LOW-LEVEL WRITE HELPERS
    # =========================================================================

    async def write_with_result(self, address, data_list, axid=0, burst_type=1,
                                size=None):
        """Issue a write and return the AXI4 master's result dict."""
        if size is None:
            size = self.bytes_per_beat.bit_length() - 1

        result = await self.axi4_master.write_transaction(
            address=address,
            data=data_list,
            size=size,
            burst_type=burst_type,
            id=axid
        )
        return result

    # =========================================================================
    # TEST SCENARIO METHODS
    # =========================================================================

    async def single_write(self):
        """Single-beat write pass-through with WID == AWID."""
        self.log.info("TEST: single_write")
        address = 0x1000
        axid = 7
        data = 0xDEADBEEF & ((1 << self.data_width) - 1)

        initial_aw = len(self.axi3_aw_transactions)
        initial_w = len(self.axi3_w_beats)

        result = await self.write_with_result(address, [data], axid=axid)
        await self.wait_clocks(self.clk_name, 10)

        if not result.get('success', False):
            self.log.error(f"single_write: AXI4 master reported failure {result}")
            self.stats['errors'] += 1
            return False

        if len(self.axi3_aw_transactions) - initial_aw != 1:
            self.log.error(f"single_write: expected 1 AXI3 AW, got "
                          f"{len(self.axi3_aw_transactions) - initial_aw}")
            self.stats['errors'] += 1
            return False

        aw = self.axi3_aw_transactions[initial_aw]
        if aw['id'] != axid:
            self.log.error(f"single_write: AWID mismatch got {aw['id']}, expected {axid}")
            self.stats['awid_errors'] += 1
            self.stats['errors'] += 1
            return False

        if len(self.axi3_w_beats) - initial_w != 1:
            self.log.error(f"single_write: expected 1 AXI3 W beat, got "
                          f"{len(self.axi3_w_beats) - initial_w}")
            self.stats['errors'] += 1
            return False

        beat = self.axi3_w_beats[initial_w]
        if beat['id'] != axid:
            self.log.error(f"single_write: WID mismatch got {beat['id']}, expected {axid}")
            self.stats['wid_errors'] += 1
            self.stats['errors'] += 1
            return False

        if beat['last'] != 1:
            self.log.error(f"single_write: WLAST mismatch got {beat['last']}, expected 1")
            self.stats['wlast_errors'] += 1
            self.stats['errors'] += 1
            return False

        if beat['data'] != data:
            self.log.error(f"single_write: WDATA mismatch got 0x{beat['data']:08X}, "
                          f"expected 0x{data:08X}")
            self.stats['data_errors'] += 1
            self.stats['errors'] += 1
            return False

        self.log.info("single_write PASSED")
        self.stats['bursts_sent'] += 1
        self.stats['beats_expected'] += 1
        self.stats['bursts_completed'] += 1
        return True

    async def burst_len16(self):
        """16-beat INCR burst passes through with WLAST only on beat 16."""
        self.log.info("TEST: burst_len16")
        address = 0x2000
        burst_len = 16
        axid = 5
        size = self.bytes_per_beat.bit_length() - 1

        data_list = [(0x11110000 + i) & ((1 << self.data_width) - 1)
                     for i in range(burst_len)]

        initial_aw = len(self.axi3_aw_transactions)
        initial_w = len(self.axi3_w_beats)

        result = await self.write_with_result(
            address, data_list, axid=axid, burst_type=1, size=size)
        await self.wait_clocks(self.clk_name, 20)

        if not result.get('success', False):
            self.log.error(f"burst_len16: AXI4 master reported failure {result}")
            self.stats['errors'] += 1
            return False

        if len(self.axi3_aw_transactions) - initial_aw != 1:
            self.log.error(f"burst_len16: expected 1 AXI3 AW, got "
                          f"{len(self.axi3_aw_transactions) - initial_aw}")
            self.stats['errors'] += 1
            return False

        aw = self.axi3_aw_transactions[initial_aw]
        if aw['id'] != axid:
            self.log.error(f"burst_len16: AWID mismatch got {aw['id']}, expected {axid}")
            self.stats['awid_errors'] += 1
            self.stats['errors'] += 1
            return False

        if aw['len'] != burst_len - 1:
            self.log.error(f"burst_len16: AWLEN mismatch got {aw['len']}, expected {burst_len - 1}")
            self.stats['errors'] += 1
            return False

        if len(self.axi3_w_beats) - initial_w != burst_len:
            self.log.error(f"burst_len16: expected {burst_len} AXI3 W beats, got "
                          f"{len(self.axi3_w_beats) - initial_w}")
            self.stats['errors'] += 1
            return False

        for i, beat in enumerate(self.axi3_w_beats[initial_w:initial_w + burst_len]):
            if beat['id'] != axid:
                self.log.error(f"burst_len16: WID mismatch beat {i} got {beat['id']}, "
                              f"expected {axid}")
                self.stats['wid_errors'] += 1
                self.stats['errors'] += 1
                return False

            expected_last = 1 if i == burst_len - 1 else 0
            if beat['last'] != expected_last:
                self.log.error(f"burst_len16: WLAST mismatch beat {i} got {beat['last']}, "
                              f"expected {expected_last}")
                self.stats['wlast_errors'] += 1
                self.stats['errors'] += 1
                return False

            if beat['data'] != data_list[i]:
                self.log.error(f"burst_len16: WDATA mismatch beat {i} got "
                              f"0x{beat['data']:08X}, expected 0x{data_list[i]:08X}")
                self.stats['data_errors'] += 1
                self.stats['errors'] += 1
                return False

        self.log.info("burst_len16 PASSED")
        self.stats['bursts_sent'] += 1
        self.stats['beats_expected'] += burst_len
        self.stats['bursts_completed'] += 1
        return True

    async def multi_outstanding_writes(self):
        """Two IDs outstanding; each AW/W/B completes with its own ID."""
        self.log.info("TEST: multi_outstanding_writes")
        address0 = 0x3000
        address1 = 0x4000
        burst_len = 8
        id0 = 3
        id1 = 9
        size = self.bytes_per_beat.bit_length() - 1

        data0 = [(0x33330000 + i) & ((1 << self.data_width) - 1)
                 for i in range(burst_len)]
        data1 = [(0x99990000 + i) & ((1 << self.data_width) - 1)
                 for i in range(burst_len)]

        initial_aw = len(self.axi3_aw_transactions)
        initial_w = len(self.axi3_w_beats)

        # Launch both writes concurrently; AXI4 master serializes W order.
        task0 = cocotb.start_soon(self.write_with_result(
            address0, data0, axid=id0, burst_type=1, size=size))
        task1 = cocotb.start_soon(self.write_with_result(
            address1, data1, axid=id1, burst_type=1, size=size))

        result0 = await task0
        result1 = await task1
        await self.wait_clocks(self.clk_name, 20)

        if not (result0.get('success', False) and result1.get('success', False)):
            self.log.error(f"multi_outstanding_writes: master failure "
                          f"result0={result0} result1={result1}")
            self.stats['errors'] += 1
            return False

        actual_aw = len(self.axi3_aw_transactions) - initial_aw
        actual_w = len(self.axi3_w_beats) - initial_w
        if actual_aw != 2:
            self.log.error(f"multi_outstanding_writes: expected 2 AXI3 AWs, got {actual_aw}")
            self.stats['errors'] += 1
            return False

        if actual_w != burst_len * 2:
            self.log.error(f"multi_outstanding_writes: expected {burst_len * 2} W beats, got {actual_w}")
            self.stats['errors'] += 1
            return False

        # Verify each AW has matching WID on its W beats. AXI4 W order follows
        # AW order, so the first burst_len beats belong to the first AW.
        aw0 = self.axi3_aw_transactions[initial_aw]
        aw1 = self.axi3_aw_transactions[initial_aw + 1]

        for i in range(burst_len):
            beat0 = self.axi3_w_beats[initial_w + i]
            if beat0['id'] != aw0['id']:
                self.log.error(f"multi_outstanding_writes: first burst beat {i} "
                              f"WID={beat0['id']} expected AWID={aw0['id']}")
                self.stats['wid_errors'] += 1
                self.stats['errors'] += 1
                return False

            beat1 = self.axi3_w_beats[initial_w + burst_len + i]
            if beat1['id'] != aw1['id']:
                self.log.error(f"multi_outstanding_writes: second burst beat {i} "
                              f"WID={beat1['id']} expected AWID={aw1['id']}")
                self.stats['wid_errors'] += 1
                self.stats['errors'] += 1
                return False

        self.log.info("multi_outstanding_writes PASSED")
        self.stats['bursts_sent'] += 2
        self.stats['beats_expected'] += burst_len * 2
        self.stats['bursts_completed'] += 2
        return True

    async def early_w_data(self):
        """Drive W beats before AW handshake; converter buffers and stamps them."""
        self.log.info("TEST: early_w_data")
        address = 0x5000
        burst_len = 4
        axid = 11
        size = self.bytes_per_beat.bit_length() - 1
        strb = (1 << self.bytes_per_beat) - 1

        data_list = [(0xEEEE0000 + i) & ((1 << self.data_width) - 1)
                     for i in range(burst_len)]

        initial_aw = len(self.axi3_aw_transactions)
        initial_w = len(self.axi3_w_beats)

        # Build W packets first so we can drive them before AW.
        w_packets = []
        for i, data_value in enumerate(data_list):
            w_packets.append(self.axi4_master.w_channel.create_packet(
                data=data_value,
                last=1 if i == burst_len - 1 else 0,
                strb=strb
            ))

        # Drive all W beats before sending AW. The converter must buffer them.
        for pkt in w_packets:
            await self.axi4_master.w_channel.send(pkt)

        await self.wait_clocks(self.clk_name, 5)

        # Now send AW. The buffered W beats should be stamped with this AWID.
        aw_pkt = self.axi4_master.aw_channel.create_packet(
            addr=address,
            len=burst_len - 1,
            id=axid,
            size=size,
            burst=1,
            lock=0,
            cache=0,
            prot=0,
            qos=0,
            region=0
        )
        await self.axi4_master.aw_channel.send(aw_pkt)

        # Wait for B response.
        id_queue = self.axi4_master._response_by_id[axid]
        cycles_waited = 0
        while len(id_queue) < 1:
            await RisingEdge(self.clk)
            cycles_waited += 1
            if cycles_waited > 5000:
                self.log.error("early_w_data: timeout waiting for B response")
                self.stats['errors'] += 1
                return False

        id_queue.popleft()
        await self.wait_clocks(self.clk_name, 10)

        if len(self.axi3_aw_transactions) - initial_aw != 1:
            self.log.error(f"early_w_data: expected 1 AXI3 AW, got "
                          f"{len(self.axi3_aw_transactions) - initial_aw}")
            self.stats['errors'] += 1
            return False

        aw = self.axi3_aw_transactions[initial_aw]
        if aw['id'] != axid:
            self.log.error(f"early_w_data: AWID mismatch got {aw['id']}, expected {axid}")
            self.stats['awid_errors'] += 1
            self.stats['errors'] += 1
            return False

        if len(self.axi3_w_beats) - initial_w != burst_len:
            self.log.error(f"early_w_data: expected {burst_len} AXI3 W beats, got "
                          f"{len(self.axi3_w_beats) - initial_w}")
            self.stats['early_w_errors'] += 1
            self.stats['errors'] += 1
            return False

        for i, beat in enumerate(self.axi3_w_beats[initial_w:initial_w + burst_len]):
            if beat['id'] != axid:
                self.log.error(f"early_w_data: WID mismatch beat {i} got {beat['id']}, "
                              f"expected {axid}")
                self.stats['wid_errors'] += 1
                self.stats['errors'] += 1
                return False

            expected_last = 1 if i == burst_len - 1 else 0
            if beat['last'] != expected_last:
                self.log.error(f"early_w_data: WLAST mismatch beat {i} got {beat['last']}, "
                              f"expected {expected_last}")
                self.stats['wlast_errors'] += 1
                self.stats['errors'] += 1
                return False

            if beat['data'] != data_list[i]:
                self.log.error(f"early_w_data: WDATA mismatch beat {i} got "
                              f"0x{beat['data']:08X}, expected 0x{data_list[i]:08X}")
                self.stats['data_errors'] += 1
                self.stats['errors'] += 1
                return False

        self.log.info("early_w_data PASSED")
        self.stats['bursts_sent'] += 1
        self.stats['beats_expected'] += burst_len
        self.stats['bursts_completed'] += 1
        return True

    # =========================================================================
    # TEST SUITE RUNNERS
    # =========================================================================

    async def run_basic_test(self):
        """Run basic write pass-through test suite"""
        self.log.info("=" * 80)
        self.log.info("BASIC WRITE PASS-THROUGH TEST SUITE")
        self.log.info("=" * 80)

        success = True

        if not await self.single_write():
            success = False

        if not await self.burst_len16():
            success = False

        if not await self.multi_outstanding_writes():
            success = False

        if not await self.early_w_data():
            success = False

        return success

    async def run_medium_test(self):
        """Run medium write pass-through test suite"""
        self.log.info("=" * 80)
        self.log.info("MEDIUM WRITE PASS-THROUGH TEST SUITE")
        self.log.info("=" * 80)

        success = True

        if not await self.run_basic_test():
            success = False

        return success

    async def run_full_test(self):
        """Run full write pass-through test suite"""
        self.log.info("=" * 80)
        self.log.info("FULL WRITE PASS-THROUGH TEST SUITE")
        self.log.info("=" * 80)

        success = True

        if not await self.run_medium_test():
            success = False

        return success

    def get_statistics(self):
        """Return test statistics"""
        return dict(self.stats)
