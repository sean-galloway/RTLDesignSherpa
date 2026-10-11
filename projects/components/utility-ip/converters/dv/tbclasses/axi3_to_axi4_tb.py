# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 RTL Design Sherpa
#
# Module: axi3_to_axi4_tb
# Purpose: Testbench class for axi3_to_axi4 top wrapper (READ + WRITE)
#
# Author: RTL Design Sherpa
# Created: 2026-10-10

"""Testbench for axi3_to_axi4 top wrapper.

A thin combined smoke testbench that instantiates the read and write AXI3
masters on the slave side and the read/write AXI4 slaves on the master side.
The deep protocol tests live in the submodule suites; this class only checks
that the wrapper wires both sub-converters together correctly.
"""

import os
import sys
from collections import deque

import cocotb
from cocotb.triggers import RisingEdge

from TBClasses.shared.utilities import get_repo_root
from TBClasses.shared.tbbase import TBBase

repo_root = get_repo_root()
sys.path.insert(0, repo_root)
from CocoTBFramework.components.axi3.axi3_interfaces import AXI3MasterRead, AXI3MasterWrite
from CocoTBFramework.components.axi4.axi4_interfaces import AXI4SlaveRead, AXI4SlaveWrite
from CocoTBFramework.components.shared.memory_model import MemoryModel


class AXI3ToAXI4TB(TBBase):
    """Combined smoke testbench for the AXI3 -> AXI4 top wrapper."""

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

        self.axi3_rd = AXI3MasterRead(
            dut=dut,
            clock=self.clk,
            prefix="s_axi3_",
            log=self.log,
            data_width=self.data_width,
            id_width=self.id_width,
            addr_width=self.addr_width,
            multi_sig=True,
        )

        self.axi3_wr = AXI3MasterWrite(
            dut=dut,
            clock=self.clk,
            prefix="s_axi3_",
            log=self.log,
            data_width=self.data_width,
            id_width=self.id_width,
            addr_width=self.addr_width,
            multi_sig=True,
        )

        self.axi4_rd = AXI4SlaveRead(
            dut=dut,
            clock=self.clk,
            prefix="m_axi_",
            log=self.log,
            data_width=self.data_width,
            id_width=self.id_width,
            addr_width=self.addr_width,
            multi_sig=True,
            response_delay=1,
        )
        self.axi4_rd.ar_channel.set_ready_policy('always')

        self.axi4_wr = AXI4SlaveWrite(
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
        self.axi4_wr.aw_channel.set_ready_policy('always')
        self.axi4_wr.w_channel.set_ready_policy('always')

        self.axi4_aw_beats = []
        self.axi4_w_beats = []
        self.axi4_ar_beats = []
        self.axi4_r_beats = []
        self.axi4_b_beats = []

        self.outstanding_reads  = deque()
        self.outstanding_writes = deque()
        self.pending_b_responses = deque()

        self.log.info(
            f"AXI3->AXI4 top TB: dw={self.data_width} aw={self.addr_width} id={self.id_width}"
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

    async def axi4_monitor(self):
        """Record every AXI4-side handshake and assert protocol basics."""
        self.log.info("Starting AXI4 combined monitor")
        while True:
            await RisingEdge(self.clk)

            if (int(self.dut.m_axi_arvalid.value) == 1 and
                    int(self.dut.m_axi_arready.value) == 1):
                ar_id = int(self.dut.m_axi_arid.value)
                ar_len = int(self.dut.m_axi_arlen.value)
                self.axi4_ar_beats.append({
                    'id': ar_id,
                    'addr': int(self.dut.m_axi_araddr.value),
                    'len': ar_len,
                })
                self.outstanding_reads.append({
                    'id': ar_id,
                    'beats_remaining': ar_len + 1,
                })

            if (int(self.dut.m_axi_rvalid.value) == 1 and
                    int(self.dut.m_axi_rready.value) == 1):
                r_id = int(self.dut.m_axi_rid.value)
                r_last = int(self.dut.m_axi_rlast.value)
                self.axi4_r_beats.append({
                    'id': r_id,
                    'data': int(self.dut.m_axi_rdata.value),
                    'resp': int(self.dut.m_axi_rresp.value),
                    'last': r_last,
                })

                if not self.outstanding_reads:
                    self.log.error(
                        f"R channel beat with no outstanding read (rid={r_id})"
                    )
                    self.stats['read_errors'] += 1
                    self.stats['errors'] += 1
                else:
                    expected = self.outstanding_reads[0]
                    if r_id != expected['id']:
                        self.log.error(
                            f"RID mismatch: got {r_id}, expected {expected['id']}"
                        )
                        self.stats['read_errors'] += 1
                        self.stats['errors'] += 1
                    expected_last = 1 if expected['beats_remaining'] == 1 else 0
                    if r_last != expected_last:
                        self.log.error(
                            f"RLAST mismatch for id={r_id}: "
                            f"got {r_last}, expected {expected_last} "
                            f"(beats_remaining={expected['beats_remaining']})"
                        )
                        self.stats['read_errors'] += 1
                        self.stats['errors'] += 1
                    expected['beats_remaining'] -= 1
                    if expected['beats_remaining'] == 0:
                        self.outstanding_reads.popleft()

            if (int(self.dut.m_axi_awvalid.value) == 1 and
                    int(self.dut.m_axi_awready.value) == 1):
                aw_id = int(self.dut.m_axi_awid.value)
                aw_len = int(self.dut.m_axi_awlen.value)
                self.axi4_aw_beats.append({
                    'id': aw_id,
                    'addr': int(self.dut.m_axi_awaddr.value),
                    'len': aw_len,
                })
                self.outstanding_writes.append({
                    'id': aw_id,
                    'beats_remaining': aw_len + 1,
                })
                self.pending_b_responses.append({
                    'id': aw_id,
                })

            if (int(self.dut.m_axi_wvalid.value) == 1 and
                    int(self.dut.m_axi_wready.value) == 1):
                w_last = int(self.dut.m_axi_wlast.value)
                self.axi4_w_beats.append({
                    'data': int(self.dut.m_axi_wdata.value),
                    'strb': int(self.dut.m_axi_wstrb.value),
                    'last': w_last,
                })
                if not self.outstanding_writes:
                    self.log.error(
                        "W channel beat with no outstanding write"
                    )
                    self.stats['write_errors'] += 1
                    self.stats['errors'] += 1
                else:
                    expected = self.outstanding_writes[0]
                    expected_last = 1 if expected['beats_remaining'] == 1 else 0
                    if w_last != expected_last:
                        self.log.error(
                            f"WLAST mismatch: got {w_last}, expected {expected_last} "
                            f"(beats_remaining={expected['beats_remaining']})"
                        )
                        self.stats['write_errors'] += 1
                        self.stats['errors'] += 1
                    expected['beats_remaining'] -= 1
                    if expected['beats_remaining'] == 0:
                        self.outstanding_writes.popleft()

            if (int(self.dut.m_axi_bvalid.value) == 1 and
                    int(self.dut.m_axi_bready.value) == 1):
                b_id = int(self.dut.m_axi_bid.value)
                b_resp = int(self.dut.m_axi_bresp.value)
                self.axi4_b_beats.append({
                    'id': b_id,
                    'resp': b_resp,
                })
                if not self.pending_b_responses:
                    self.log.error(
                        f"B channel response with no outstanding write (bid={b_id})"
                    )
                    self.stats['write_errors'] += 1
                    self.stats['errors'] += 1
                else:
                    expected = self.pending_b_responses.popleft()
                    if b_id != expected['id']:
                        self.log.error(
                            f"BID mismatch: got {b_id}, expected {expected['id']}"
                        )
                        self.stats['write_errors'] += 1
                        self.stats['errors'] += 1
                    if b_resp != 0:
                        self.log.error(
                            f"BRESP mismatch for id={b_id}: got {b_resp}, expected 0"
                        )
                        self.stats['write_errors'] += 1
                        self.stats['errors'] += 1

    async def run_smoke_test(self, burst_len=8, bursts=1):
        """Issue concurrent read + write bursts, optionally repeated.

        Each iteration issues one read burst and one write burst concurrently,
        using incrementing addresses and IDs to avoid collisions. burst_len is
        capped at 16 because the AXI3 slave interface uses 4-bit ARLEN/AWLEN.
        """
        if burst_len > 16:
            self.log.warning(
                f"burst_len {burst_len} exceeds AXI3 legal maximum (16); capping at 16"
            )
            burst_len = 16

        self.log.info("=" * 80)
        self.log.info(
            f"SMOKE TEST: {bursts} concurrent read+write burst(s) (len={burst_len})"
        )
        self.log.info("=" * 80)

        size = self.bytes_per_beat.bit_length() - 1
        success = True

        for burst_idx in range(bursts):
            read_addr = 0x1000 + (burst_idx * 0x1000)
            write_addr = 0x2000 + (burst_idx * 0x1000)
            read_id = 5 + burst_idx
            write_id = 7 + burst_idx

            write_data = [
                (0xBEEF0000 + i) & ((1 << self.data_width) - 1)
                for i in range(burst_len)
            ]

            initial_ar = len(self.axi4_ar_beats)
            initial_aw = len(self.axi4_aw_beats)
            initial_w = len(self.axi4_w_beats)

            read_task = cocotb.start_soon(self.axi3_rd.read_transaction(
                address=read_addr,
                burst_len=burst_len,
                burst_type=1,
                size=size,
                id=read_id,
            ))
            write_task = cocotb.start_soon(self.axi3_wr.write_transaction(
                address=write_addr,
                data=write_data,
                burst_type=1,
                size=size,
                id=write_id,
            ))

            read_result = await read_task
            write_result = await write_task
            await self.wait_clocks('aclk', 10)

            # ---- read checks ----
            if len(read_result) != burst_len:
                self.log.error(
                    f"burst {burst_idx}: expected {burst_len} read beats, "
                    f"got {len(read_result)}"
                )
                self.stats['read_errors'] += 1
                self.stats['errors'] += 1
                success = False
            else:
                for i, data in enumerate(read_result):
                    expected_addr = read_addr + (i * self.bytes_per_beat)
                    expected_data = expected_addr & ((1 << self.data_width) - 1)
                    if data != expected_data:
                        self.log.error(
                            f"burst {burst_idx} read: data mismatch beat {i} "
                            f"got 0x{data:08X}, expected 0x{expected_data:08X}"
                        )
                        self.stats['read_errors'] += 1
                        self.stats['errors'] += 1
                        success = False

            ar_count = len(self.axi4_ar_beats) - initial_ar
            if ar_count != 1:
                self.log.error(
                    f"burst {burst_idx}: expected 1 AXI4 AR, got {ar_count}"
                )
                self.stats['read_errors'] += 1
                self.stats['errors'] += 1
                success = False

            # ---- write checks ----
            if not write_result.get('success', False):
                self.log.error(
                    f"burst {burst_idx}: write reported failure {write_result}"
                )
                self.stats['write_errors'] += 1
                self.stats['errors'] += 1
                success = False

            aw_count = len(self.axi4_aw_beats) - initial_aw
            if aw_count != 1:
                self.log.error(
                    f"burst {burst_idx}: expected 1 AXI4 AW, got {aw_count}"
                )
                self.stats['write_errors'] += 1
                self.stats['errors'] += 1
                success = False

            w_count = len(self.axi4_w_beats) - initial_w
            if w_count != burst_len:
                self.log.error(
                    f"burst {burst_idx}: expected {burst_len} W beats, got {w_count}"
                )
                self.stats['write_errors'] += 1
                self.stats['errors'] += 1
                success = False
            else:
                for i, beat in enumerate(
                        self.axi4_w_beats[initial_w:initial_w + burst_len]):
                    if beat['data'] != write_data[i]:
                        self.log.error(
                            f"burst {burst_idx} write: WDATA mismatch beat {i} "
                            f"got 0x{beat['data']:08X}, expected 0x{write_data[i]:08X}"
                        )
                        self.stats['write_errors'] += 1
                        self.stats['errors'] += 1
                        success = False

            self.stats['read_bursts'] += 1
            self.stats['write_bursts'] += 1
            self.stats['read_beats'] += burst_len
            self.stats['write_beats'] += burst_len

        await self.wait_clocks('aclk', 20)

        if success:
            self.log.info("SMOKE TEST PASSED")
        else:
            self.log.error("SMOKE TEST FAILED")

        return success

    def get_statistics(self):
        return dict(self.stats)
