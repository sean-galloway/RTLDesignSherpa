# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 RTL Design Sherpa
#
# Module: axi4_dwidth_to_apb_chain_tb
# Purpose: Testbench for the axi4_dwidth_converter_rd → axi4_to_apb_shim chain.
#
# Author: RTL Design Sherpa
# Created: 2026-05-22

"""
Testbench for axi4_dwidth_to_apb_chain.

Wide AXI4 master → axi4_dwidth_converter_rd → axi4_to_apb_shim → narrow APB.

A single wide AXI4 R beat is composed from ``ratio`` narrow APB reads,
where ``ratio = S_AXI_DATA_WIDTH / APB_DATA_WIDTH``. The dnsize side
of the rd converter rewrites the slave-side wide AR into a narrow
AR (arlen scaled by ratio, arsize down to APB size), and the APB
shim decomposes each narrow AXI4 beat into one APB read.

This chain is the exact RTL the bridge instantiates between a wide
master adapter and a narrow APB peripheral. The same b2b page-probe
class of bug that the bridge surfaces (1x5_rd_boundary_probe) should
show up here.
"""

import os
import sys
import cocotb
from cocotb.clock import Clock
from cocotb.triggers import RisingEdge
import random

from TBClasses.shared.utilities import get_repo_root
from TBClasses.shared.tbbase import TBBase

repo_root = get_repo_root()
sys.path.insert(0, repo_root)
from CocoTBFramework.components.axi4.axi4_interfaces import AXI4MasterRead
from CocoTBFramework.components.apb.apb_factories import create_apb_slave
from CocoTBFramework.components.shared.flex_randomizer import FlexRandomizer


class AXI4DWidthToAPBChainTB(TBBase):
    """
    Testbench for the dwidth+apb read chain.

    Asymmetric widths: master BFM drives at S_AXI_DATA_WIDTH (wide),
    APB slave BFM responds at APB_DATA_WIDTH (narrow).
    """

    def __init__(self, dut):
        super().__init__(dut)

        self.clk = dut.aclk
        self.clk_name = 'aclk'
        self.pclk = dut.pclk
        self.pclk_name = 'pclk'
        self.rst_n = dut.aresetn
        self.prst_n = dut.presetn

        self.s_data_width = self.convert_to_int(os.environ.get('S_AXI_DATA_WIDTH', '64'))
        self.apb_data_width = self.convert_to_int(os.environ.get('APB_DATA_WIDTH', '32'))
        self.addr_width = self.convert_to_int(os.environ.get('AXI_ADDR_WIDTH', '32'))
        self.apb_addr_width = self.convert_to_int(os.environ.get('APB_ADDR_WIDTH', '32'))
        self.id_width = self.convert_to_int(os.environ.get('AXI_ID_WIDTH', '8'))

        assert self.s_data_width > self.apb_data_width, \
            f"This chain expects DOWNSIZE: S={self.s_data_width} APB={self.apb_data_width}"
        self.ratio = self.s_data_width // self.apb_data_width

        self.stats = {
            'bursts_sent': 0,
            'wide_beats_expected': 0,
            'narrow_beats_expected': 0,
            'apb_reads_observed': 0,
            'bursts_completed': 0,
            'errors': 0,
            'data_errors': 0,
            'count_errors': 0,
            'timeouts': 0,
        }

        # Wide AXI4 master drives slave-side of the dwidth converter
        self.axi4_master = AXI4MasterRead(
            dut=dut,
            clock=self.clk,
            prefix="s_axi_",
            log=self.log,
            data_width=self.s_data_width,
            id_width=self.id_width,
            addr_width=self.addr_width,
            multi_sig=True,
        )

        # Seed the APB slave memory with a deterministic pattern so reads
        # return predictable values. registers is a flat byte list of
        # length num_words * (APB_DATA_WIDTH / 8). Pattern: byte at
        # absolute byte-address B is (B & 0xFF) — equivalent to a
        # ramp — so a wide read assembling ratio narrow words yields
        # an easy-to-check increasing byte pattern.
        apb_bytes_per_word = self.apb_data_width // 8
        # Provide enough memory to cover the test address ranges. Tests
        # use addresses up to ~0x1000 + small per-burst offsets.
        # 64 KiB is plenty.
        num_apb_words = 0x10000 // apb_bytes_per_word
        registers = []
        for w in range(num_apb_words):
            for b in range(apb_bytes_per_word):
                byte_addr = w * apb_bytes_per_word + b
                registers.append(byte_addr & 0xFF)

        # APB slave responds on master-side of the shim. It uses pclk.
        # Use a non-zero ready/error randomizer light enough to keep the
        # test fast but not zero-cycle ready (which can mask shim bugs).
        self.apb_slave_randomizer = FlexRandomizer({
            'ready': ([(0, 0), (1, 2)], [9, 1]),
            'error': ([(0, 0), (1, 1)], [10, 0]),
        })

        self.apb_slave = create_apb_slave(
            dut,
            'APB Slave',
            'm_apb',
            self.pclk,
            registers=registers,
            addr_width=self.apb_addr_width,
            data_width=self.apb_data_width,
            randomizer=self.apb_slave_randomizer,
            log=self.log,
        )

        # APB transaction monitor storage: list of (addr, rdata)
        self.apb_reads = []

        self.log.info(
            f"Initialized chain TB: S_AXI={self.s_data_width}b wide, "
            f"APB={self.apb_data_width}b narrow, ratio={self.ratio}:1, "
            f"id_width={self.id_width}, addr_width={self.addr_width}"
        )

    # ------------------------------------------------------------------
    # Mandatory TBBase methods
    # ------------------------------------------------------------------

    async def setup_clocks_and_reset(self, period_ns=10):
        # Single-clock test configuration: pclk = aclk, presetn = aresetn.
        # Drive both via Clock so cocotb's clock model is consistent for
        # both clocking domains (the APB slave uses pclk, the AXI master
        # uses aclk, but they're the same period and edge-aligned).
        await self.start_clock(self.clk_name, freq=period_ns, units='ns')
        await self.start_clock(self.pclk_name, freq=period_ns, units='ns')
        await self.assert_reset()
        await self.wait_clocks(self.clk_name, 10)
        await self.deassert_reset()
        await self.wait_clocks(self.clk_name, 5)
        self.log.info("Reset sequence complete")

    async def assert_reset(self):
        self.rst_n.value = 0
        self.prst_n.value = 0

    async def deassert_reset(self):
        self.rst_n.value = 1
        self.prst_n.value = 1

    # ------------------------------------------------------------------
    # APB master-side transaction monitor
    # ------------------------------------------------------------------

    async def apb_transaction_monitor(self):
        """Observe APB read setup→access cycles for diagnostics."""
        while True:
            await RisingEdge(self.pclk)
            psel = int(self.dut.m_apb_PSEL.value)
            penable = int(self.dut.m_apb_PENABLE.value)
            pready = int(self.dut.m_apb_PREADY.value)
            pwrite = int(self.dut.m_apb_PWRITE.value)
            if psel and penable and pready and not pwrite:
                paddr = int(self.dut.m_apb_PADDR.value)
                prdata = int(self.dut.m_apb_PRDATA.value)
                self.apb_reads.append((paddr, prdata))
                self.stats['apb_reads_observed'] += 1

    # ------------------------------------------------------------------
    # Helpers
    # ------------------------------------------------------------------

    def _expected_wide_word(self, start_addr_bytes, wide_beat_index):
        """
        Compute the expected wide-beat data for a wide AXI4 read at
        ``start_addr_bytes``, beat number ``wide_beat_index``. The APB
        memory pattern is (byte_addr & 0xFF) per byte, little-endian.
        """
        wide_bytes = self.s_data_width // 8
        beat_base = start_addr_bytes + wide_beat_index * wide_bytes
        word = 0
        for i in range(wide_bytes):
            word |= ((beat_base + i) & 0xFF) << (i * 8)
        return word

    # ------------------------------------------------------------------
    # Test scenarios
    # ------------------------------------------------------------------

    async def test_read_burst(self, address, wide_burst_len, size=None):
        """Single wide AXI4 INCR read burst; verify R data matches APB memory."""
        if size is None:
            size = (self.s_data_width // 8).bit_length() - 1

        try:
            read_data = await self.axi4_master.read_transaction(
                address=address,
                burst_len=wide_burst_len,
                size=size,
                burst_type=1,
            )
            if read_data is None:
                self.log.error(f"Read @0x{address:08X}: got None")
                self.stats['errors'] += 1
                self.stats['timeouts'] += 1
                return False
            if len(read_data) != wide_burst_len:
                self.log.error(
                    f"Read @0x{address:08X}: got {len(read_data)} beats, "
                    f"expected {wide_burst_len}"
                )
                self.stats['count_errors'] += 1
                self.stats['errors'] += 1
                return False

            mask = (1 << self.s_data_width) - 1
            for i, got in enumerate(read_data):
                expected = self._expected_wide_word(address, i)
                if (got & mask) != (expected & mask):
                    self.log.error(
                        f"Read @0x{address:08X} beat {i}: "
                        f"got 0x{got:0{self.s_data_width//4}X} "
                        f"expected 0x{expected:0{self.s_data_width//4}X}"
                    )
                    self.stats['data_errors'] += 1
                    self.stats['errors'] += 1
                    return False

            self.stats['bursts_sent'] += 1
            self.stats['wide_beats_expected'] += wide_burst_len
            self.stats['narrow_beats_expected'] += wide_burst_len * self.ratio
            self.stats['bursts_completed'] += 1
            return True
        except Exception as e:
            self.log.error(f"Read burst @0x{address:08X} raised: {e}")
            self.stats['errors'] += 1
            self.stats['timeouts'] += 1
            return False

    async def test_b2b_burst_reads(self, bursts, size=None):
        """
        Issue N wide AXI4 read bursts back-to-back (sequential awaits;
        no inter-burst cooldown). This is the bridge's
        ``1x5_rd_boundary_probe`` pattern at the FUB level.

        Each ``burst`` is a tuple of (address, wide_burst_len).
        """
        if size is None:
            size = (self.s_data_width // 8).bit_length() - 1

        self.log.info(
            f"B2B CHAIN READ BURSTS: issuing {len(bursts)} wide bursts "
            f"with NO inter-burst cooldown"
        )

        success = True
        for i, (addr, wlen) in enumerate(bursts):
            self.log.info(f"  burst {i+1}/{len(bursts)}: addr=0x{addr:08X}, wide_len={wlen}")
            ok = await self.test_read_burst(addr, wlen, size=size)
            if not ok:
                self.log.error(f"B2B chain burst {i+1} FAILED at addr=0x{addr:08X}")
                success = False
                break
        if success:
            self.log.info(f"B2B CHAIN READ BURSTS PASSED: {len(bursts)} bursts")
        return success

    async def test_b2b_page_probe(self):
        """
        Mirror the bridge's boundary_probe pattern: page-aligned probes
        at bottom / mid / top of multiple "pages" walked sequentially.
        This is the configuration that surfaces the bridge's
        1x5_rd_boundary_probe hang at slave-3 (APB).
        """
        wide_bytes = self.s_data_width // 8
        burst_len = 2  # 2-beat wide bursts == the bridge's typical decomposition
        # In-page offsets matching the bridge's probe pattern, but kept
        # aligned to wide-beat × burst-length so we don't 4K-cross.
        in_page_offs = [0x0, 0x80, 0xF0]
        page_bases = [0x000, 0x100, 0x180, 0x200, 0x280]
        bursts = []
        for p in page_bases:
            for off in in_page_offs:
                addr = p + off
                # Align to wide-beat boundary
                addr = addr & ~(wide_bytes - 1)
                bursts.append((addr, burst_len))
        return await self.test_b2b_burst_reads(bursts)

    # ------------------------------------------------------------------
    # Suites
    # ------------------------------------------------------------------

    async def run_basic_test(self):
        self.log.info("=" * 80)
        self.log.info("CHAIN BASIC READ TEST")
        self.log.info("=" * 80)
        success = True
        # Single wide bursts
        wide_bytes = self.s_data_width // 8
        smoke = [
            (0x000, 1),
            (0x040, 2),
            (0x080, 4),
        ]
        for addr, blen in smoke:
            addr_aligned = addr & ~(wide_bytes - 1)
            if not await self.test_read_burst(addr_aligned, blen):
                success = False

        # Lightweight b2b smoke (page-probe pattern, scaled down)
        smoke_b2b = [
            (0x100, 2),
            (0x140, 2),
        ]
        if not await self.test_b2b_burst_reads(smoke_b2b):
            success = False
        return success

    async def run_medium_test(self):
        self.log.info("=" * 80)
        self.log.info("CHAIN MEDIUM READ TEST")
        self.log.info("=" * 80)
        success = True

        # B2B page-probe pattern — this is the boundary probe that
        # reproduces the bridge bug.
        if not await self.test_b2b_page_probe():
            success = False
            # Don't early-return: still run a few random checks to gather
            # more diagnostic info in the log.

        # Random INCR bursts
        wide_bytes = self.s_data_width // 8
        for _ in range(6):
            addr = (random.randint(0, 0x800) & ~(wide_bytes - 1))
            blen = random.choice([1, 2, 4])
            if not await self.test_read_burst(addr, blen):
                success = False

        return success

    async def run_full_test(self):
        self.log.info("=" * 80)
        self.log.info("CHAIN FULL READ TEST")
        self.log.info("=" * 80)
        success = True

        # B2B page-probe pattern — bridge boundary reproduction
        if not await self.test_b2b_page_probe():
            success = False

        # Larger random INCR bursts
        wide_bytes = self.s_data_width // 8
        for _ in range(16):
            addr = (random.randint(0, 0x2000) & ~(wide_bytes - 1))
            blen = random.choice([1, 2, 4, 8])
            if not await self.test_read_burst(addr, blen):
                success = False

        # Larger b2b sweep
        big_b2b = []
        for i in range(8):
            big_b2b.append((0x2000 + i * 0x100, 4))
        if not await self.test_b2b_burst_reads(big_b2b):
            success = False

        return success

    def get_statistics(self):
        return dict(self.stats)
