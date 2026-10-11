# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 RTL Design Sherpa
#
# Module: axi3_to_axi4_wr_tb
# Purpose: Testbench class for axi3_to_axi4_wr converter (WRITE-ONLY)
#
# Author: RTL Design Sherpa
# Created: 2026-10-10

"""
Testbench for axi3_to_axi4_wr converter - WRITE-ONLY

Tests AXI3 -> AXI4 protocol upgrade for write path under a single-active-write
contract:
- AXI3 WID is stripped on the AXI4 W channel
- AW, W data/strb/last, and B response are passed through
- AWLEN is zero-extended from 4-bit AXI3 to 8-bit AXI4
- AWLOCK is mapped from AXI3 2-bit to AXI4 1-bit
  (2'b00 -> 1'b0, 2'b01 -> 1'b0, 2'b10 -> 1'b1)
- Only one write transaction is active at a time (AW -> W run -> B -> next AW)
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
from CocoTBFramework.components.axi3.axi3_interfaces import AXI3MasterWrite
from CocoTBFramework.components.axi4.axi4_interfaces import AXI4SlaveWrite
from CocoTBFramework.components.shared.memory_model import MemoryModel


class AXI3ToAXI4WriteTB(TBBase):
    """
    Testbench for axi3_to_axi4_wr converter.

    Tests protocol upgrade from AXI3 -> AXI4 for write path with WID stripping
    under a single-active-write contract.

    Key Validations:
    - Single-beat and burst write pass-through
    - WID stripped (AXI4 W has no id concept)
    - W data, strb, and last integrity on AXI4 side
    - B response pass-through with ID preserved
    - AWLEN zero-extension (4-bit -> 8-bit)
    - AWLOCK mapping (AXI3 2-bit -> AXI4 1-bit)
    - Single-active-write backpressure on second AW
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
            'axi4_writes_received': 0,
            'bursts_completed': 0,
            'errors': 0,
            'awid_errors': 0,
            'wid_errors': 0,
            'wlast_errors': 0,
            'data_errors': 0,
            'bresp_errors': 0,
            'buser_errors': 0,
            'backpressure_errors': 0,
            'early_w_errors': 0,
            'awqual_errors': 0,
        }

        # Bytes per transfer
        self.bytes_per_beat = self.data_width // 8

        # Initialize AXI3 master (drives slave side of converter)
        self.axi3_master = AXI3MasterWrite(
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
        self.axi4_slave = AXI4SlaveWrite(
            dut=dut,
            clock=self.clk,
            prefix="m_axi_",
            log=self.log,
            data_width=self.data_width,
            id_width=self.id_width,
            addr_width=self.addr_width,
            multi_sig=True,
            response_delay=1,
            memory_model=MemoryModel(
                num_lines=4096,
                bytes_per_line=self.bytes_per_beat,
                log=self.log
            ),
            base_addr=0
        )
        # Keep AW and W ready asserted so transactions stream through.
        self.axi4_slave.aw_channel.set_ready_policy('always')
        self.axi4_slave.w_channel.set_ready_policy('always')

        # The AXI4SlaveWrite BFM does not natively drive a programmable BUSER,
        # so wrap its B-channel send to allow tests to inject a buser pattern.
        self.axi4_slave.buser_override = None
        self._orig_b_send = self.axi4_slave.b_channel.send
        async def _b_send_with_user(packet):
            if self.axi4_slave.buser_override is not None:
                packet.user = self.axi4_slave.buser_override
            await self._orig_b_send(packet)
        self.axi4_slave.b_channel.send = _b_send_with_user

        # Storage for monitoring AXI4 transactions
        self.axi4_aw_transactions = []
        self.axi4_w_beats = []
        self.axi4_b_responses = []

        self.log.info(f"Initialized AXI3->AXI4 Write TB: "
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
    # AXI4 SLAVE SIDE MONITORS
    # =========================================================================

    async def axi4_aw_monitor(self):
        """Monitor AXI4 AW channel handshakes."""
        self.log.info("Starting AXI4 AW monitor")

        while True:
            await RisingEdge(self.clk)

            if (int(self.dut.m_axi_awvalid.value) == 1 and
                int(self.dut.m_axi_awready.value) == 1):
                self.axi4_aw_transactions.append({
                    'id': int(self.dut.m_axi_awid.value),
                    'addr': int(self.dut.m_axi_awaddr.value),
                    'len': int(self.dut.m_axi_awlen.value),
                    'lock': int(self.dut.m_axi_awlock.value),
                    'cache': int(self.dut.m_axi_awcache.value),
                    'prot': int(self.dut.m_axi_awprot.value),
                    'user': int(self.dut.m_axi_awuser.value),
                })
                self.stats['axi4_writes_received'] += 1

    async def axi4_w_monitor(self):
        """Monitor AXI4 W channel handshakes (no id on AXI4 W)."""
        self.log.info("Starting AXI4 W monitor")

        while True:
            await RisingEdge(self.clk)

            if (int(self.dut.m_axi_wvalid.value) == 1 and
                int(self.dut.m_axi_wready.value) == 1):
                self.axi4_w_beats.append({
                    'data': int(self.dut.m_axi_wdata.value),
                    'strb': int(self.dut.m_axi_wstrb.value),
                    'last': int(self.dut.m_axi_wlast.value),
                })

    async def axi4_b_monitor(self):
        """Monitor AXI4 B channel handshakes."""
        self.log.info("Starting AXI4 B monitor")

        while True:
            await RisingEdge(self.clk)

            if (int(self.dut.m_axi_bvalid.value) == 1 and
                int(self.dut.m_axi_bready.value) == 1):
                self.axi4_b_responses.append({
                    'id': int(self.dut.m_axi_bid.value),
                    'resp': int(self.dut.m_axi_bresp.value),
                    'user': int(self.dut.m_axi_buser.value),
                })

    # =========================================================================
    # LOW-LEVEL WRITE HELPERS
    # =========================================================================

    async def write_with_result(self, address, data_list, axid=0, burst_type=1,
                                size=None, lock=0, cache=0, prot=0, user=None):
        """Issue a write and return the AXI3 master's result dict."""
        if size is None:
            size = self.bytes_per_beat.bit_length() - 1

        kwargs = {
            'address': address,
            'data': data_list,
            'size': size,
            'burst_type': burst_type,
            'id': axid,
            'lock': lock,
            'cache': cache,
            'prot': prot,
        }
        if user is not None:
            kwargs['user'] = user

        result = await self.axi3_master.write_transaction(**kwargs)
        return result

    # =========================================================================
    # TEST SCENARIO METHODS
    # =========================================================================

    async def wid_stripped(self):
        """AXI4 W channel has no id; data/strb/last are forwarded intact."""
        self.log.info("TEST: wid_stripped")
        address = 0x1000
        burst_len = 4
        axid = 5
        size = self.bytes_per_beat.bit_length() - 1

        data_list = [(0xAABB0000 + i) & ((1 << self.data_width) - 1)
                     for i in range(burst_len)]

        initial_aw = len(self.axi4_aw_transactions)
        initial_w = len(self.axi4_w_beats)
        initial_b = len(self.axi4_b_responses)

        result = await self.write_with_result(
            address, data_list, axid=axid, burst_type=1, size=size)
        await self.wait_clocks(self.clk_name, 10)

        if not result.get('success', False):
            self.log.error(f"wid_stripped: AXI3 master reported failure {result}")
            self.stats['errors'] += 1
            return False

        if len(self.axi4_aw_transactions) - initial_aw != 1:
            self.log.error(f"wid_stripped: expected 1 AXI4 AW, got "
                          f"{len(self.axi4_aw_transactions) - initial_aw}")
            self.stats['errors'] += 1
            return False

        aw = self.axi4_aw_transactions[initial_aw]
        if aw['id'] != axid:
            self.log.error(f"wid_stripped: AWID mismatch got {aw['id']}, expected {axid}")
            self.stats['awid_errors'] += 1
            self.stats['errors'] += 1
            return False

        if aw['len'] != burst_len - 1:
            self.log.error(f"wid_stripped: AWLEN mismatch got {aw['len']}, expected {burst_len - 1}")
            self.stats['errors'] += 1
            return False

        if len(self.axi4_w_beats) - initial_w != burst_len:
            self.log.error(f"wid_stripped: expected {burst_len} AXI4 W beats, got "
                          f"{len(self.axi4_w_beats) - initial_w}")
            self.stats['errors'] += 1
            return False

        for i, beat in enumerate(self.axi4_w_beats[initial_w:initial_w + burst_len]):
            if beat['data'] != data_list[i]:
                self.log.error(f"wid_stripped: WDATA mismatch beat {i} got "
                              f"0x{beat['data']:08X}, expected 0x{data_list[i]:08X}")
                self.stats['data_errors'] += 1
                self.stats['errors'] += 1
                return False

            expected_strb = (1 << self.bytes_per_beat) - 1
            if beat['strb'] != expected_strb:
                self.log.error(f"wid_stripped: WSTRB mismatch beat {i} got "
                              f"0x{beat['strb']:X}, expected 0x{expected_strb:X}")
                self.stats['data_errors'] += 1
                self.stats['errors'] += 1
                return False

            expected_last = 1 if i == burst_len - 1 else 0
            if beat['last'] != expected_last:
                self.log.error(f"wid_stripped: WLAST mismatch beat {i} got {beat['last']}, "
                              f"expected {expected_last}")
                self.stats['wlast_errors'] += 1
                self.stats['errors'] += 1
                return False

        if len(self.axi4_b_responses) - initial_b != 1:
            self.log.error(f"wid_stripped: expected 1 AXI4 B response, got "
                          f"{len(self.axi4_b_responses) - initial_b}")
            self.stats['bresp_errors'] += 1
            self.stats['errors'] += 1
            return False

        b = self.axi4_b_responses[initial_b]
        if b['id'] != axid:
            self.log.error(f"wid_stripped: BID mismatch got {b['id']}, expected {axid}")
            self.stats['bresp_errors'] += 1
            self.stats['errors'] += 1
            return False

        self.log.info("wid_stripped PASSED")
        self.stats['bursts_sent'] += 1
        self.stats['beats_expected'] += burst_len
        self.stats['bursts_completed'] += 1
        return True

    async def single_active_backpressure(self):
        """Second AW is held until the first transaction's B response completes."""
        self.log.info("TEST: single_active_backpressure")
        address0 = 0x2000
        address1 = 0x3000
        burst_len = 8
        id0 = 3
        id1 = 7
        size = self.bytes_per_beat.bit_length() - 1

        data0 = [(0x22220000 + i) & ((1 << self.data_width) - 1)
                 for i in range(burst_len)]
        data1 = [(0x77770000 + i) & ((1 << self.data_width) - 1)
                 for i in range(1)]

        initial_aw = len(self.axi4_aw_transactions)
        initial_w = len(self.axi4_w_beats)
        initial_b = len(self.axi4_b_responses)

        # Launch the first burst.
        task0 = cocotb.start_soon(self.write_with_result(
            address0, data0, axid=id0, burst_type=1, size=size))

        # Wait until the first AW handshake has been observed.
        cycles_waited = 0
        while len(self.axi4_aw_transactions) - initial_aw < 1:
            await RisingEdge(self.clk)
            cycles_waited += 1
            if cycles_waited > 5000:
                self.log.error("single_active_backpressure: timeout waiting for first AW")
                self.stats['errors'] += 1
                return False

        # Launch the second write while the first burst is still active.
        task1 = cocotb.start_soon(self.write_with_result(
            address1, data1, axid=id1, burst_type=1, size=size))

        # Give the second write a chance to be accepted, then verify it was not.
        await self.wait_clocks(self.clk_name, 10)
        if len(self.axi4_aw_transactions) - initial_aw != 1:
            self.log.error("single_active_backpressure: second AW was accepted while first burst active")
            self.stats['backpressure_errors'] += 1
            self.stats['errors'] += 1
            return False

        if int(self.dut.s_axi3_awready.value) != 0:
            self.log.error("single_active_backpressure: s_axi3_awready not deasserted during active burst")
            self.stats['backpressure_errors'] += 1
            self.stats['errors'] += 1
            return False

        # Wait for the final W beat of the first burst to be accepted.
        cycles_waited = 0
        while len(self.axi4_w_beats) - initial_w < burst_len:
            await RisingEdge(self.clk)
            cycles_waited += 1
            if cycles_waited > 5000:
                self.log.error("single_active_backpressure: timeout waiting for WLAST")
                self.stats['errors'] += 1
                return False

        # From WLAST acceptance until the first B response, awready must stay low.
        if int(self.dut.s_axi3_awready.value) != 0:
            self.log.error("single_active_backpressure: s_axi3_awready high right after WLAST")
            self.stats['backpressure_errors'] += 1
            self.stats['errors'] += 1
            return False

        cycles_waited = 0
        while len(self.axi4_b_responses) - initial_b < 1:
            if int(self.dut.s_axi3_awready.value) != 0:
                self.log.error("single_active_backpressure: s_axi3_awready went high between WLAST and B")
                self.stats['backpressure_errors'] += 1
                self.stats['errors'] += 1
                return False
            await RisingEdge(self.clk)
            cycles_waited += 1
            if cycles_waited > 5000:
                self.log.error("single_active_backpressure: timeout waiting for first B")
                self.stats['errors'] += 1
                return False

        # Now the second transaction should eventually complete.
        cycles_waited = 0
        while len(self.axi4_aw_transactions) - initial_aw < 2:
            await RisingEdge(self.clk)
            cycles_waited += 1
            if cycles_waited > 5000:
                self.log.error("single_active_backpressure: second AW never accepted after first B")
                self.stats['backpressure_errors'] += 1
                self.stats['errors'] += 1
                return False

        result0 = await task0
        result1 = await task1
        await self.wait_clocks(self.clk_name, 10)

        if not (result0.get('success', False) and result1.get('success', False)):
            self.log.error(f"single_active_backpressure: master failure "
                          f"result0={result0} result1={result1}")
            self.stats['errors'] += 1
            return False

        aw0 = self.axi4_aw_transactions[initial_aw]
        aw1 = self.axi4_aw_transactions[initial_aw + 1]
        if aw0['id'] != id0 or aw1['id'] != id1:
            self.log.error("single_active_backpressure: AWID order mismatch")
            self.stats['awid_errors'] += 1
            self.stats['errors'] += 1
            return False

        self.log.info("single_active_backpressure PASSED")
        self.stats['bursts_sent'] += 2
        self.stats['beats_expected'] += burst_len + 1
        self.stats['bursts_completed'] += 2
        return True

    async def wid_mismatch_asserts(self):
        """Inject a wrong WID mid-burst; the DUT assertion must fire."""
        self.log.info("TEST: wid_mismatch_asserts")
        address = 0x4000
        burst_len = 4
        axid = 9
        wrong_id = axid + 1
        size = self.bytes_per_beat.bit_length() - 1
        strb = (1 << self.bytes_per_beat) - 1

        data_list = [(0xBAD00000 + i) & ((1 << self.data_width) - 1)
                     for i in range(burst_len)]

        # Build W packets; corrupt the second beat's id.
        w_packets = []
        for i, data_value in enumerate(data_list):
            beat_id = wrong_id if i == 1 else axid
            w_packets.append(self.axi3_master.w_channel.create_packet(
                id=beat_id,
                data=data_value,
                last=1 if i == burst_len - 1 else 0,
                strb=strb
            ))

        # Send AW first.
        aw_pkt = self.axi3_master.aw_channel.create_packet(
            addr=address,
            len=burst_len - 1,
            id=axid,
            size=size,
            burst=1,
            lock=0,
            cache=0,
            prot=0
        )
        await self.axi3_master.aw_channel.send(aw_pkt)

        # Stream the corrupted W burst.
        await self.axi3_master.w_channel.send_burst(w_packets)

        # Wait long enough for the assertion to fire; if it does not, fail
        # internally so the negative test cannot silently pass.
        await self.wait_clocks(self.clk_name, 20)
        self.log.error("wid_mismatch_asserts: simulation reached end without firing ASSERT_A3_WID_STABLE")
        self.stats['errors'] += 1
        assert False, "ASSERT_A3_WID_STABLE did not fire on injected WID mismatch"

    async def b_passthrough(self):
        """B channel id/resp/user are forwarded from AXI4 slave to AXI3 master."""
        self.log.info("TEST: b_passthrough")
        address = 0x1000
        axid = 11
        expected_buser = 1

        initial_b = len(self.axi4_b_responses)

        # Inject a non-zero BUSER pattern on the AXI4 slave side.
        self.axi4_slave.buser_override = expected_buser
        try:
            result = await self.write_with_result(
                address, [0xBEEF0000 & ((1 << self.data_width) - 1)], axid=axid)
        finally:
            self.axi4_slave.buser_override = None

        await self.wait_clocks(self.clk_name, 10)

        if not result.get('success', False):
            self.log.error(f"b_passthrough: AXI3 master reported failure {result}")
            self.stats['errors'] += 1
            return False

        if len(self.axi4_b_responses) - initial_b != 1:
            self.log.error(f"b_passthrough: expected 1 AXI4 B response, got "
                          f"{len(self.axi4_b_responses) - initial_b}")
            self.stats['bresp_errors'] += 1
            self.stats['errors'] += 1
            return False

        b = self.axi4_b_responses[initial_b]
        if b['id'] != axid:
            self.log.error(f"b_passthrough: BID mismatch got {b['id']}, expected {axid}")
            self.stats['bresp_errors'] += 1
            self.stats['errors'] += 1
            return False

        if b['resp'] != 0:
            self.log.error(f"b_passthrough: BRESP mismatch got {b['resp']}, expected 0")
            self.stats['bresp_errors'] += 1
            self.stats['errors'] += 1
            return False

        if b['user'] != expected_buser:
            self.log.error(f"b_passthrough: BUSER mismatch got {b['user']}, expected {expected_buser}")
            self.stats['buser_errors'] += 1
            self.stats['errors'] += 1
            return False

        if result.get('response', 0) != 0:
            self.log.error(f"b_passthrough: AXI3 result response mismatch got {result.get('response')}, expected 0")
            self.stats['bresp_errors'] += 1
            self.stats['errors'] += 1
            return False

        self.log.info("b_passthrough PASSED")
        self.stats['bursts_sent'] += 1
        self.stats['beats_expected'] += 1
        self.stats['bursts_completed'] += 1
        return True

    async def early_w_before_aw(self):
        """W beats driven before AW are held and forwarded once AW is accepted."""
        self.log.info("TEST: early_w_before_aw")
        address = 0x800
        burst_len = 4
        axid = 15
        size = self.bytes_per_beat.bit_length() - 1
        strb = (1 << self.bytes_per_beat) - 1

        data_list = [(0xE1110000 + i) & ((1 << self.data_width) - 1)
                     for i in range(burst_len)]

        initial_aw = len(self.axi4_aw_transactions)
        initial_w = len(self.axi4_w_beats)

        # Build W packets with the correct AWID.
        w_packets = []
        for i, data_value in enumerate(data_list):
            w_packets.append(self.axi3_master.w_channel.create_packet(
                id=axid,
                data=data_value,
                last=1 if i == burst_len - 1 else 0,
                strb=strb
            ))

        # Launch the W burst before the AW handshake. It must be backpressured
        # until the converter accepts the AW.
        w_task = cocotb.start_soon(self.axi3_master.w_channel.send_burst(w_packets))

        # Give the W channel a cycle to attempt transfer, then confirm backpressure.
        await RisingEdge(self.clk)
        if int(self.dut.s_axi3_wready.value) != 0:
            self.log.error("early_w_before_aw: s_axi3_wready was not low before AW acceptance")
            self.stats['early_w_errors'] += 1
            self.stats['errors'] += 1
            return False

        # Now send the matching AW. The buffered W beats should be accepted.
        aw_pkt = self.axi3_master.aw_channel.create_packet(
            addr=address,
            len=burst_len - 1,
            id=axid,
            size=size,
            burst=1,
            lock=0,
            cache=0,
            prot=0
        )
        await self.axi3_master.aw_channel.send(aw_pkt)

        # Wait for the W burst to drain.
        cycles_waited = 0
        while not w_task.done():
            await RisingEdge(self.clk)
            cycles_waited += 1
            if cycles_waited > 5000:
                self.log.error("early_w_before_aw: timeout waiting for W burst to complete")
                self.stats['early_w_errors'] += 1
                self.stats['errors'] += 1
                return False

        # Wait for the B response.
        id_queue = self.axi3_master._response_by_id[axid]
        cycles_waited = 0
        while len(id_queue) < 1:
            await RisingEdge(self.clk)
            cycles_waited += 1
            if cycles_waited > 5000:
                self.log.error("early_w_before_aw: timeout waiting for B response")
                self.stats['early_w_errors'] += 1
                self.stats['errors'] += 1
                return False
        id_queue.popleft()
        await self.wait_clocks(self.clk_name, 10)

        if len(self.axi4_aw_transactions) - initial_aw != 1:
            self.log.error(f"early_w_before_aw: expected 1 AXI4 AW, got "
                          f"{len(self.axi4_aw_transactions) - initial_aw}")
            self.stats['early_w_errors'] += 1
            self.stats['errors'] += 1
            return False

        aw = self.axi4_aw_transactions[initial_aw]
        if aw['id'] != axid:
            self.log.error(f"early_w_before_aw: AWID mismatch got {aw['id']}, expected {axid}")
            self.stats['awid_errors'] += 1
            self.stats['errors'] += 1
            return False

        if len(self.axi4_w_beats) - initial_w != burst_len:
            self.log.error(f"early_w_before_aw: expected {burst_len} AXI4 W beats, got "
                          f"{len(self.axi4_w_beats) - initial_w}")
            self.stats['early_w_errors'] += 1
            self.stats['errors'] += 1
            return False

        for i, beat in enumerate(self.axi4_w_beats[initial_w:initial_w + burst_len]):
            if beat['data'] != data_list[i]:
                self.log.error(f"early_w_before_aw: WDATA mismatch beat {i} got "
                              f"0x{beat['data']:08X}, expected 0x{data_list[i]:08X}")
                self.stats['data_errors'] += 1
                self.stats['errors'] += 1
                return False

            expected_last = 1 if i == burst_len - 1 else 0
            if beat['last'] != expected_last:
                self.log.error(f"early_w_before_aw: WLAST mismatch beat {i} got {beat['last']}, "
                              f"expected {expected_last}")
                self.stats['wlast_errors'] += 1
                self.stats['errors'] += 1
                return False

        self.log.info("early_w_before_aw PASSED")
        self.stats['bursts_sent'] += 1
        self.stats['beats_expected'] += burst_len
        self.stats['bursts_completed'] += 1
        return True

    async def aw_qualifier_passthrough(self):
        """AW cache/prot/user qualifiers are forwarded to the AXI4 master side."""
        self.log.info("TEST: aw_qualifier_passthrough")
        address = 0x900
        axid = 17
        size = self.bytes_per_beat.bit_length() - 1

        expected_cache = 0b1111
        expected_prot = 0b101
        expected_user = 0b1

        initial_aw = len(self.axi4_aw_transactions)

        result = await self.write_with_result(
            address,
            [0xCAFE0000 & ((1 << self.data_width) - 1)],
            axid=axid,
            size=size,
            cache=expected_cache,
            prot=expected_prot,
            user=expected_user
        )
        await self.wait_clocks(self.clk_name, 10)

        if not result.get('success', False):
            self.log.error(f"aw_qualifier_passthrough: AXI3 master reported failure {result}")
            self.stats['errors'] += 1
            return False

        if len(self.axi4_aw_transactions) - initial_aw != 1:
            self.log.error(f"aw_qualifier_passthrough: expected 1 AXI4 AW, got "
                          f"{len(self.axi4_aw_transactions) - initial_aw}")
            self.stats['awqual_errors'] += 1
            self.stats['errors'] += 1
            return False

        aw = self.axi4_aw_transactions[initial_aw]
        if aw['id'] != axid:
            self.log.error(f"aw_qualifier_passthrough: AWID mismatch got {aw['id']}, expected {axid}")
            self.stats['awqual_errors'] += 1
            self.stats['errors'] += 1
            return False

        if aw['cache'] != expected_cache:
            self.log.error(f"aw_qualifier_passthrough: AWCACHE mismatch got {aw['cache']}, "
                          f"expected {expected_cache}")
            self.stats['awqual_errors'] += 1
            self.stats['errors'] += 1
            return False

        if aw['prot'] != expected_prot:
            self.log.error(f"aw_qualifier_passthrough: AWPROT mismatch got {aw['prot']}, "
                          f"expected {expected_prot}")
            self.stats['awqual_errors'] += 1
            self.stats['errors'] += 1
            return False

        if aw['user'] != expected_user:
            self.log.error(f"aw_qualifier_passthrough: AWUSER mismatch got {aw['user']}, "
                          f"expected {expected_user}")
            self.stats['awqual_errors'] += 1
            self.stats['errors'] += 1
            return False

        self.log.info("aw_qualifier_passthrough PASSED")
        self.stats['bursts_sent'] += 1
        self.stats['beats_expected'] += 1
        self.stats['bursts_completed'] += 1
        return True

    async def lock_map_up(self):
        """AXI3 2-bit AWLOCK maps to AXI4 1-bit AWLOCK correctly."""
        self.log.info("TEST: lock_map_up")
        address = 0x100
        axid = 13
        size = self.bytes_per_beat.bit_length() - 1

        # (AXI3 lock value, expected AXI4 lock value)
        test_cases = [
            (0, 0),  # 2'b00 normal -> normal
            (1, 0),  # 2'b01 locked -> normal
            (2, 1),  # 2'b10 exclusive -> exclusive
        ]

        initial_aw = len(self.axi4_aw_transactions)

        for axi3_lock, expected_axi4_lock in test_cases:
            result = await self.write_with_result(
                address + (axi3_lock * 0x100),
                [0xC0DE0000 & ((1 << self.data_width) - 1)],
                axid=axid,
                lock=axi3_lock,
                size=size
            )
            if not result.get('success', False):
                self.log.error(f"lock_map_up: write failed for lock={axi3_lock}: {result}")
                self.stats['errors'] += 1
                return False

        await self.wait_clocks(self.clk_name, 10)

        actual_aw_count = len(self.axi4_aw_transactions) - initial_aw
        if actual_aw_count != len(test_cases):
            self.log.error(f"lock_map_up: expected {len(test_cases)} AXI4 AWs, got {actual_aw_count}")
            self.stats['errors'] += 1
            return False

        for i, (axi3_lock, expected_axi4_lock) in enumerate(test_cases):
            aw = self.axi4_aw_transactions[initial_aw + i]
            if aw['lock'] != expected_axi4_lock:
                self.log.error(f"lock_map_up: lock mismatch for AXI3 lock={axi3_lock} "
                              f"got {aw['lock']}, expected {expected_axi4_lock}")
                self.stats['errors'] += 1
                return False

        self.log.info("lock_map_up PASSED")
        self.stats['bursts_sent'] += len(test_cases)
        self.stats['beats_expected'] += len(test_cases)
        self.stats['bursts_completed'] += len(test_cases)
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

        if not await self.wid_stripped():
            success = False

        if not await self.b_passthrough():
            success = False

        if not await self.single_active_backpressure():
            success = False

        return success

    async def run_medium_test(self):
        """Run medium write pass-through test suite"""
        self.log.info("=" * 80)
        self.log.info("MEDIUM WRITE PASS-THROUGH TEST SUITE")
        self.log.info("=" * 80)

        success = await self.run_basic_test()

        if not await self.early_w_before_aw():
            success = False

        if not await self.aw_qualifier_passthrough():
            success = False

        if not await self.lock_map_up():
            success = False

        return success

    async def run_full_test(self):
        """Run full write pass-through test suite"""
        self.log.info("=" * 80)
        self.log.info("FULL WRITE PASS-THROUGH TEST SUITE")
        self.log.info("=" * 80)

        # For this pass-through converter, full is the same as medium.
        return await self.run_medium_test()

    def get_statistics(self):
        """Return test statistics"""
        return dict(self.stats)
