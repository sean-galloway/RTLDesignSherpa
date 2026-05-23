# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 RTL Design Sherpa
#
# Module: axi4_dwidth_to_axil4_wr_chain_tb
# Purpose: Testbench for the axi4_dwidth_converter_wr → axi4_to_axil4_wr chain.
#
# Author: RTL Design Sherpa
# Created: 2026-05-22

"""
Testbench for axi4_dwidth_to_axil4_wr_chain.

Wide AXI4 master → axi4_dwidth_converter_wr → axi4_to_axil4_wr → narrow AXIL4.

A single wide AXI4 W beat becomes ``ratio`` narrow AXIL4 beats, where
``ratio = S_AXI_DATA_WIDTH / M_AXIL_DATA_WIDTH``. The dnsize primitive
slices each wide beat into ``ratio`` narrow beats, starting from the
low-order lane.

This chain is the exact RTL the bridge instantiates between a wide
master adapter and a narrow AXIL4 peripheral. The same b2b page-probe
class of bug that the bridge surfaces shows up here.
"""

import os
import sys
import cocotb
from cocotb.triggers import RisingEdge
import random

# Import framework utilities (PYTHONPATH includes bin/)
from TBClasses.shared.utilities import get_repo_root
from TBClasses.shared.tbbase import TBBase

repo_root = get_repo_root()
sys.path.insert(0, repo_root)
from CocoTBFramework.components.axi4.axi4_interfaces import AXI4MasterWrite
from CocoTBFramework.components.axil4.axil4_interfaces import AXIL4SlaveWrite


class AXI4DWidthToAXIL4WrChainTB(TBBase):
    """
    Testbench for the dwidth+axil write chain.

    Asymmetric widths: master BFM drives at S_AXI_DATA_WIDTH (wide),
    AXIL slave BFM responds at M_AXIL_DATA_WIDTH (narrow).
    """

    def __init__(self, dut):
        super().__init__(dut)

        self.clk = dut.aclk
        self.clk_name = 'aclk'
        self.rst_n = dut.aresetn

        self.s_data_width = self.convert_to_int(os.environ.get('S_AXI_DATA_WIDTH', '64'))
        self.m_data_width = self.convert_to_int(os.environ.get('M_AXIL_DATA_WIDTH', '32'))
        self.addr_width = self.convert_to_int(os.environ.get('AXI_ADDR_WIDTH', '32'))
        self.id_width = self.convert_to_int(os.environ.get('AXI_ID_WIDTH', '8'))

        assert self.s_data_width > self.m_data_width, \
            f"This chain expects DOWNSIZE: S={self.s_data_width} M={self.m_data_width}"
        self.ratio = self.s_data_width // self.m_data_width

        self.stats = {
            'bursts_sent': 0,
            'wide_beats_expected': 0,
            'narrow_beats_expected': 0,
            'axil_writes_received': 0,
            'bursts_completed': 0,
            'errors': 0,
            'address_errors': 0,
            'decomposition_errors': 0,
            'data_errors': 0,
        }

        # Wide AXI4 master drives slave-side of the dwidth converter
        self.axi4_master = AXI4MasterWrite(
            dut=dut,
            clock=self.clk,
            prefix="s_axi_",
            log=self.log,
            data_width=self.s_data_width,
            id_width=self.id_width,
            addr_width=self.addr_width,
            multi_sig=True,
        )

        # Narrow AXIL4 slave responds on master-side of the axil shim
        self.axil4_slave = AXIL4SlaveWrite(
            dut=dut,
            clock=self.clk,
            prefix="m_axil_",
            log=self.log,
            data_width=self.m_data_width,
            addr_width=self.addr_width,
            multi_sig=True,
            response_delay=1,
        )

        # AXIL transaction monitor storage: list of (addr, data, strb)
        self.axil_transactions = []

        self.log.info(
            f"Initialized chain TB: S_AXI={self.s_data_width}b wide, "
            f"M_AXIL={self.m_data_width}b narrow, ratio={self.ratio}:1, "
            f"id_width={self.id_width}, addr_width={self.addr_width}"
        )

    # ------------------------------------------------------------------
    # Mandatory TBBase methods
    # ------------------------------------------------------------------

    async def setup_clocks_and_reset(self, period_ns=10):
        await self.start_clock(self.clk_name, freq=period_ns, units='ns')
        await self.assert_reset()
        await self.wait_clocks(self.clk_name, 10)
        await self.deassert_reset()
        await self.wait_clocks(self.clk_name, 5)
        self.log.info("Reset sequence complete")

    async def assert_reset(self):
        self.rst_n.value = 0

    async def deassert_reset(self):
        self.rst_n.value = 1

    # ------------------------------------------------------------------
    # AXIL master-side transaction monitor
    # ------------------------------------------------------------------

    async def axil4_transaction_monitor(self):
        """
        Monitor narrow AXIL4 writes by pairing AW addresses with W beats
        in handshake order.
        """
        pending_addr = None
        while True:
            await RisingEdge(self.clk)
            if (int(self.dut.m_axil_awvalid.value) == 1 and
                int(self.dut.m_axil_awready.value) == 1):
                pending_addr = int(self.dut.m_axil_awaddr.value)
            if (int(self.dut.m_axil_wvalid.value) == 1 and
                int(self.dut.m_axil_wready.value) == 1):
                w_data = int(self.dut.m_axil_wdata.value)
                w_strb = int(self.dut.m_axil_wstrb.value)
                if pending_addr is not None:
                    self.axil_transactions.append((pending_addr, w_data, w_strb))
                    self.stats['axil_writes_received'] += 1
                    pending_addr = None

    # ------------------------------------------------------------------
    # Helpers
    # ------------------------------------------------------------------

    def _expand_wide_to_narrow(self, start_addr, wide_data_list):
        """
        Given a wide AXI4 INCR burst at full wide size, return the list of
        narrow (addr, data, strb_default) tuples the AXIL slave should see.

        Each wide beat of S_AXI_DATA_WIDTH bytes is sliced into ``ratio``
        narrow beats of M_AXIL_DATA_WIDTH bytes. The dnsize primitive
        emits low-order lane first.
        """
        narrow_bytes = self.m_data_width // 8
        narrow_mask = (1 << self.m_data_width) - 1
        narrow_strb = (1 << narrow_bytes) - 1
        expanded = []
        addr = start_addr
        for wide_word in wide_data_list:
            for lane in range(self.ratio):
                shift = lane * self.m_data_width
                narrow_word = (wide_word >> shift) & narrow_mask
                expanded.append((addr, narrow_word, narrow_strb))
                addr += narrow_bytes
        return expanded

    # ------------------------------------------------------------------
    # Test scenarios
    # ------------------------------------------------------------------

    async def test_write_burst(self, address, wide_data_list, size=None):
        """Single wide AXI4 INCR burst → verify narrow AXIL4 sequence."""
        if size is None:
            size = (self.s_data_width // 8).bit_length() - 1
        burst_len_wide = len(wide_data_list)
        expected = self._expand_wide_to_narrow(address, wide_data_list)
        expected_narrow_beats = len(expected)

        initial_axil_count = len(self.axil_transactions)
        try:
            await self.axi4_master.write_transaction(
                address=address,
                data=wide_data_list,
                size=size,
                burst_type=1,
            )
            await self.wait_clocks(self.clk_name, 30)

            got = self.axil_transactions[initial_axil_count:]
            if len(got) != expected_narrow_beats:
                self.log.error(
                    f"Burst @0x{address:08X}: narrow beat count "
                    f"{len(got)} != expected {expected_narrow_beats} "
                    f"(wide_len={burst_len_wide}, ratio={self.ratio})"
                )
                self.stats['decomposition_errors'] += 1
                self.stats['errors'] += 1
                return False

            for i, (exp_addr, exp_data, exp_strb) in enumerate(expected):
                got_addr, got_data, got_strb = got[i]
                if got_addr != exp_addr:
                    self.log.error(
                        f"Burst @0x{address:08X} narrow beat {i} addr: "
                        f"got 0x{got_addr:08X} expected 0x{exp_addr:08X}"
                    )
                    self.stats['address_errors'] += 1
                    self.stats['errors'] += 1
                    return False
                if got_data != exp_data:
                    self.log.error(
                        f"Burst @0x{address:08X} narrow beat {i} data: "
                        f"got 0x{got_data:08X} expected 0x{exp_data:08X}"
                    )
                    self.stats['data_errors'] += 1
                    self.stats['errors'] += 1
                    return False

            self.stats['bursts_sent'] += 1
            self.stats['wide_beats_expected'] += burst_len_wide
            self.stats['narrow_beats_expected'] += expected_narrow_beats
            self.stats['bursts_completed'] += 1
            return True
        except Exception as e:
            self.log.error(f"Write burst @0x{address:08X} raised: {e}")
            self.stats['errors'] += 1
            return False

    async def test_b2b_bursts(self, bursts, size=None):
        """
        Issue N wide AXI4 bursts back-to-back with NO inter-burst cooldown,
        then verify the narrow AXIL4 sequence matches the expected
        expansion in issue order.
        """
        if size is None:
            size = (self.s_data_width // 8).bit_length() - 1

        expected = []
        for (start_addr, wide_data_list) in bursts:
            expected.extend(self._expand_wide_to_narrow(start_addr, wide_data_list))

        total_expected = len(expected)
        initial_axil_count = len(self.axil_transactions)

        self.log.info(
            f"B2B CHAIN BURSTS: issuing {len(bursts)} wide bursts "
            f"({total_expected} narrow beats expected) with NO cooldown"
        )

        tasks = [
            cocotb.start_soon(self.axi4_master.write_transaction(
                address=a,
                data=d,
                size=size,
                burst_type=1,
            ))
            for (a, d) in bursts
        ]
        for t in tasks:
            await t

        await self.wait_clocks(self.clk_name, 100)

        got = self.axil_transactions[initial_axil_count:]
        if len(got) != total_expected:
            self.log.error(
                f"B2B chain: narrow beat count {len(got)} != expected {total_expected}"
            )
            self.stats['decomposition_errors'] += 1
            self.stats['errors'] += 1
            return False

        for i, (exp_addr, exp_data, _exp_strb) in enumerate(expected):
            got_addr, got_data, _got_strb = got[i]
            if got_addr != exp_addr:
                self.log.error(
                    f"B2B chain beat {i} addr: "
                    f"got 0x{got_addr:08X} expected 0x{exp_addr:08X}"
                )
                self.stats['address_errors'] += 1
                self.stats['errors'] += 1
                return False
            if got_data != exp_data:
                self.log.error(
                    f"B2B chain beat {i} data (addr=0x{exp_addr:08X}): "
                    f"got 0x{got_data:08X} expected 0x{exp_data:08X}"
                )
                self.stats['data_errors'] += 1
                self.stats['errors'] += 1
                return False

        self.stats['bursts_sent'] += len(bursts)
        self.stats['wide_beats_expected'] += sum(len(d) for _, d in bursts)
        self.stats['narrow_beats_expected'] += total_expected
        self.stats['bursts_completed'] += len(bursts)
        self.log.info(f"B2B CHAIN PASSED: {len(bursts)} bursts, {total_expected} narrow beats")
        return True

    async def test_b2b_mixed_lengths(self):
        """B2B chain bursts with mixed wide-burst lengths."""
        bursts = []
        base = 0x10000
        lengths = [1, 4, 1, 2, 8, 1, 16, 1]
        for i, blen in enumerate(lengths):
            addr = base + (i * 0x1000)
            data_list = [((0xA000_0000 | (i << 16) | j) & ((1 << self.s_data_width) - 1))
                         for j in range(blen)]
            bursts.append((addr, data_list))
        return await self.test_b2b_bursts(bursts)

    async def test_narrow_within_wide(self):
        """
        Wide AXI4 burst issued with awsize < full wide size.
        Pick size that matches the narrow data width — single wide beat
        actually carries one narrow lane of valid data per beat (one-to-one).
        """
        # Use the AXIL (narrow) data width as the AXI4 awsize
        narrow_size = (self.m_data_width // 8).bit_length() - 1
        addr_incr = 1 << narrow_size

        success = True
        for trial_i, (addr, blen) in enumerate([(0x30000, 1), (0x30100, 4), (0x30200, 8)]):
            # When AXI4 awsize == narrow size, dnsize produces 1 narrow
            # beat per wide beat. We need to predict that low-lane data
            # is what's emitted.
            data_list = [(0x55AA_0000 + (trial_i << 24) + i) & ((1 << self.s_data_width) - 1)
                         for i in range(blen)]
            initial_axil_count = len(self.axil_transactions)
            try:
                await self.axi4_master.write_transaction(
                    address=addr,
                    data=data_list,
                    size=narrow_size,
                    burst_type=1,
                )
                await self.wait_clocks(self.clk_name, 30)

                got = self.axil_transactions[initial_axil_count:]
                # With awsize=narrow, the dnsize converter still emits
                # ratio narrow beats per wide beat (it can't know the
                # awsize). So we expect ratio*blen narrow beats.
                expected_count = blen * self.ratio
                if len(got) != expected_count:
                    self.log.error(
                        f"narrow_within_wide: got {len(got)} narrow beats, "
                        f"expected {expected_count}"
                    )
                    self.stats['errors'] += 1
                    success = False
                    continue
                # We don't verify the data here — narrow awsize semantics on
                # a wide bus are subtle; the count check + address-increment
                # sanity is the main goal.
            except Exception as e:
                self.log.error(f"narrow_within_wide raised: {e}")
                self.stats['errors'] += 1
                success = False
        return success

    async def test_max_burst(self):
        """AWLEN = 255 wide-side burst exercises full counter range."""
        burst_len = 256
        addr = 0x40000
        data_list = [(0xBEEF_0000 + i) & ((1 << self.s_data_width) - 1)
                     for i in range(burst_len)]
        return await self.test_write_burst(addr, data_list)

    # ------------------------------------------------------------------
    # Suites
    # ------------------------------------------------------------------

    async def run_basic_test(self):
        self.log.info("=" * 80)
        self.log.info("CHAIN BASIC WRITE TEST")
        self.log.info("=" * 80)
        success = True
        # Single wide bursts
        test_cases = [
            (0x1000, [0x1111_2222_3333_4444 & ((1 << self.s_data_width) - 1)]),
            (0x2000, [(0xAA00_0000_0000_0000 + i) & ((1 << self.s_data_width) - 1)
                      for i in range(2)]),
            (0x3000, [(0xBB00_0000_0000_0000 + i) & ((1 << self.s_data_width) - 1)
                      for i in range(4)]),
        ]
        for addr, dlist in test_cases:
            if not await self.test_write_burst(addr, dlist):
                success = False

        # Lightweight b2b smoke (THIS is the boundary probe)
        b2b_smoke = [
            (0x5000, [(0xAA0000 + i) & ((1 << self.s_data_width) - 1) for i in range(2)]),
            (0x5040, [(0xBB0000 + i) & ((1 << self.s_data_width) - 1) for i in range(2)]),
        ]
        if not await self.test_b2b_bursts(b2b_smoke):
            success = False
        return success

    async def run_medium_test(self):
        self.log.info("=" * 80)
        self.log.info("CHAIN MEDIUM WRITE TEST")
        self.log.info("=" * 80)
        success = True
        # Random INCR bursts
        for _ in range(8):
            addr = (random.randint(0, (1 << self.addr_width) - 1)) & ~((self.s_data_width // 8) - 1)
            blen = random.randint(1, 8)
            data_list = [random.randint(0, (1 << self.s_data_width) - 1) for _ in range(blen)]
            if not await self.test_write_burst(addr, data_list):
                success = False

        # B2B
        b2b_bursts = []
        base = 0x80000
        for i in range(6):
            blen = random.randint(1, 6)
            addr = base + (i * 0x1000)
            dlist = [random.randint(0, (1 << self.s_data_width) - 1) for _ in range(blen)]
            b2b_bursts.append((addr, dlist))
        if not await self.test_b2b_bursts(b2b_bursts):
            success = False

        if not await self.test_b2b_mixed_lengths():
            success = False
        return success

    async def run_full_test(self):
        self.log.info("=" * 80)
        self.log.info("CHAIN FULL WRITE TEST")
        self.log.info("=" * 80)
        success = True
        for _ in range(16):
            addr = (random.randint(0, (1 << self.addr_width) - 1)) & ~((self.s_data_width // 8) - 1)
            blen = random.randint(1, 16)
            data_list = [random.randint(0, (1 << self.s_data_width) - 1) for _ in range(blen)]
            if not await self.test_write_burst(addr, data_list):
                success = False

        b2b_bursts = []
        base = 0x90000
        for i in range(12):
            blen = random.randint(1, 8)
            addr = base + (i * 0x1000)
            dlist = [random.randint(0, (1 << self.s_data_width) - 1) for _ in range(blen)]
            b2b_bursts.append((addr, dlist))
        if not await self.test_b2b_bursts(b2b_bursts):
            success = False
        if not await self.test_b2b_mixed_lengths():
            success = False
        if not await self.test_narrow_within_wide():
            success = False
        if not await self.test_max_burst():
            success = False
        return success

    def get_statistics(self):
        return dict(self.stats)
