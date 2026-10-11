# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 RTL Design Sherpa
#
# Module: axi4_to_axi3_tb
# Purpose: Testbench class for axi4_to_axi3 top wrapper (READ + WRITE)
#
# Author: RTL Design Sherpa
# Created: 2026-10-10

"""Testbench for axi4_to_axi3 top wrapper.

A thin combined smoke testbench that instantiates the read and write AXI4
masters on the slave side and the read/write AXI3 slaves on the master side.
The deep protocol tests live in the submodule suites; this class only checks
that the wrapper wires both sub-converters together correctly.
"""

import os
import sys

import cocotb
from cocotb.triggers import RisingEdge

from TBClasses.shared.utilities import get_repo_root
from TBClasses.shared.tbbase import TBBase

repo_root = get_repo_root()
sys.path.insert(0, repo_root)
from CocoTBFramework.components.axi4.axi4_interfaces import AXI4MasterRead, AXI4MasterWrite
from CocoTBFramework.components.axi3.axi3_interfaces import AXI3SlaveRead, AXI3SlaveWrite


class AXI4ToAXI3TB(TBBase):
    """Combined smoke testbench for the AXI4 -> AXI3 top wrapper."""

    def __init__(self, dut):
        super().__init__(dut)

        self.clk = dut.aclk
        self.clk_name = 'aclk'
        self.rst_n = dut.aresetn

        self.data_width = self.convert_to_int(os.environ.get('AXI_DATA_WIDTH', '32'))
        self.addr_width = self.convert_to_int(os.environ.get('AXI_ADDR_WIDTH', '32'))
        self.id_width = self.convert_to_int(os.environ.get('AXI_ID_WIDTH', '8'))
        self.bytes_per_beat = self.data_width // 8

        self.stats = {
            'errors': 0,
            'read_errors': 0,
            'write_errors': 0,
            'read_bursts': 0,
            'write_bursts': 0,
            'read_beats': 0,
            'write_beats': 0,
        }

        self.axi4_rd = AXI4MasterRead(
            dut=dut,
            clock=self.clk,
            prefix="s_axi_",
            log=self.log,
            data_width=self.data_width,
            id_width=self.id_width,
            addr_width=self.addr_width,
            multi_sig=True,
        )

        self.axi4_wr = AXI4MasterWrite(
            dut=dut,
            clock=self.clk,
            prefix="s_axi_",
            log=self.log,
            data_width=self.data_width,
            id_width=self.id_width,
            addr_width=self.addr_width,
            multi_sig=True,
        )

        self.axi3_rd = AXI3SlaveRead(
            dut=dut,
            clock=self.clk,
            prefix="m_axi3_",
            log=self.log,
            data_width=self.data_width,
            id_width=self.id_width,
            addr_width=self.addr_width,
            multi_sig=True,
            response_delay=1,
        )
        self.axi3_rd.ar_channel.set_ready_policy('always')

        self.axi3_wr = AXI3SlaveWrite(
            dut=dut,
            clock=self.clk,
            prefix="m_axi3_",
            log=self.log,
            data_width=self.data_width,
            id_width=self.id_width,
            addr_width=self.addr_width,
            multi_sig=True,
            response_delay=1,
        )

        self.axi3_aw_beats = []
        self.axi3_w_beats = []
        self.axi3_ar_beats = []
        self.axi3_r_beats = []
        self.axi3_b_beats = []

        self.log.info(
            f"AXI4->AXI3 top TB: dw={self.data_width} aw={self.addr_width} id={self.id_width}"
        )

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

    async def axi3_monitor(self):
        """Record every AXI3-side handshake."""
        self.log.info("Starting AXI3 combined monitor")
        while True:
            await RisingEdge(self.clk)

            if (int(self.dut.m_axi3_arvalid.value) == 1 and
                    int(self.dut.m_axi3_arready.value) == 1):
                self.axi3_ar_beats.append({
                    'id': int(self.dut.m_axi3_arid.value),
                    'addr': int(self.dut.m_axi3_araddr.value),
                    'len': int(self.dut.m_axi3_arlen.value),
                })

            if (int(self.dut.m_axi3_rvalid.value) == 1 and
                    int(self.dut.m_axi3_rready.value) == 1):
                self.axi3_r_beats.append({
                    'id': int(self.dut.m_axi3_rid.value),
                    'data': int(self.dut.m_axi3_rdata.value),
                    'resp': int(self.dut.m_axi3_rresp.value),
                    'last': int(self.dut.m_axi3_rlast.value),
                })

            if (int(self.dut.m_axi3_awvalid.value) == 1 and
                    int(self.dut.m_axi3_awready.value) == 1):
                self.axi3_aw_beats.append({
                    'id': int(self.dut.m_axi3_awid.value),
                    'addr': int(self.dut.m_axi3_awaddr.value),
                    'len': int(self.dut.m_axi3_awlen.value),
                })

            if (int(self.dut.m_axi3_wvalid.value) == 1 and
                    int(self.dut.m_axi3_wready.value) == 1):
                self.axi3_w_beats.append({
                    'id': int(self.dut.m_axi3_wid.value),
                    'data': int(self.dut.m_axi3_wdata.value),
                    'last': int(self.dut.m_axi3_wlast.value),
                })

            if (int(self.dut.m_axi3_bvalid.value) == 1 and
                    int(self.dut.m_axi3_bready.value) == 1):
                self.axi3_b_beats.append({
                    'id': int(self.dut.m_axi3_bid.value),
                    'resp': int(self.dut.m_axi3_bresp.value),
                })

    async def run_smoke_test(self, burst_len=8):
        """Issue one read burst and one write burst concurrently."""
        self.log.info("=" * 80)
        self.log.info(f"SMOKE TEST: concurrent read + write burst (len={burst_len})")
        self.log.info("=" * 80)

        read_addr = 0x1000
        write_addr = 0x2000
        read_id = 5
        write_id = 7
        size = self.bytes_per_beat.bit_length() - 1

        write_data = [
            (0xBEEF0000 + i) & ((1 << self.data_width) - 1)
            for i in range(burst_len)
        ]

        initial_ar = len(self.axi3_ar_beats)
        initial_aw = len(self.axi3_aw_beats)
        initial_w = len(self.axi3_w_beats)

        read_task = cocotb.start_soon(self.axi4_rd.read_transaction(
            address=read_addr,
            burst_len=burst_len,
            burst_type=1,
            size=size,
            id=read_id,
        ))
        write_task = cocotb.start_soon(self.axi4_wr.write_transaction(
            address=write_addr,
            data=write_data,
            burst_type=1,
            size=size,
            id=write_id,
        ))

        read_result = await read_task
        write_result = await write_task
        await self.wait_clocks('aclk', 20)

        success = True

        # ---- read checks ----
        if len(read_result) != burst_len:
            self.log.error(f"read: expected {burst_len} beats, got {len(read_result)}")
            self.stats['read_errors'] += 1
            self.stats['errors'] += 1
            success = False
        else:
            for i, data in enumerate(read_result):
                expected_addr = read_addr + (i * self.bytes_per_beat)
                expected_data = expected_addr & ((1 << self.data_width) - 1)
                if data != expected_data:
                    self.log.error(
                        f"read: data mismatch beat {i} got 0x{data:08X}, "
                        f"expected 0x{expected_data:08X}"
                    )
                    self.stats['read_errors'] += 1
                    self.stats['errors'] += 1
                    success = False

        ar_count = len(self.axi3_ar_beats) - initial_ar
        expected_chunks = (burst_len + 15) // 16
        if ar_count != expected_chunks:
            self.log.error(
                f"read: expected {expected_chunks} AXI3 ARs, got {ar_count}"
            )
            self.stats['read_errors'] += 1
            self.stats['errors'] += 1
            success = False

        # ---- write checks ----
        if not write_result.get('success', False):
            self.log.error(f"write: AXI4 master reported failure {write_result}")
            self.stats['write_errors'] += 1
            self.stats['errors'] += 1
            success = False

        aw_count = len(self.axi3_aw_beats) - initial_aw
        if aw_count != expected_chunks:
            self.log.error(
                f"write: expected {expected_chunks} AXI3 AWs, got {aw_count}"
            )
            self.stats['write_errors'] += 1
            self.stats['errors'] += 1
            success = False

        w_count = len(self.axi3_w_beats) - initial_w
        if w_count != burst_len:
            self.log.error(f"write: expected {burst_len} W beats, got {w_count}")
            self.stats['write_errors'] += 1
            self.stats['errors'] += 1
            success = False
        else:
            for i, beat in enumerate(self.axi3_w_beats[initial_w:initial_w + burst_len]):
                if beat['id'] != write_id:
                    self.log.error(
                        f"write: WID mismatch beat {i} got {beat['id']}, expected {write_id}"
                    )
                    self.stats['write_errors'] += 1
                    self.stats['errors'] += 1
                    success = False
                if beat['data'] != write_data[i]:
                    self.log.error(
                        f"write: WDATA mismatch beat {i} got 0x{beat['data']:08X}, "
                        f"expected 0x{write_data[i]:08X}"
                    )
                    self.stats['write_errors'] += 1
                    self.stats['errors'] += 1
                    success = False

        self.stats['read_bursts'] += 1
        self.stats['write_bursts'] += 1
        self.stats['read_beats'] += burst_len
        self.stats['write_beats'] += burst_len

        if success:
            self.log.info("SMOKE TEST PASSED")
        else:
            self.log.error("SMOKE TEST FAILED")

        return success

    def get_statistics(self):
        return dict(self.stats)
