# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# Module: dma_slave_monitors_tb
# Purpose: FUB testbench for dma_slave_monitors — drives the wrapper's AXI4
#          slave interface with an AXI4 master BFM (RDS-DV), and validates that
#          the internal monitors observe the traffic and the tally counts it.
#
# Follows the repo FUB method: RDS-DV AXI4 master BFM on the DUT's s_axi, the
# three-method reset contract, and a golden expectation (completion packets
# must land in the tally's COMPLETION bin).

import os

import cocotb
from cocotb.triggers import RisingEdge, ReadOnly

from TBClasses.shared.tbbase import TBBase
from CocoTBFramework.components.axi4.axi4_factories import (
    create_axi4_master_wr, create_axi4_master_rd)
from CocoTBFramework.components.shared.memory_model import MemoryModel

PKT_COMPLETION = 1


def bin_of(protocol: int, pkt_type: int, event_code: int) -> int:
    """monbus_pkt_tally bin address = {protocol[3:0], pkt_type[3:0], evcode[7:0]}."""
    return ((protocol & 0xF) << 12) | ((pkt_type & 0xF) << 8) | (event_code & 0xFF)


class DmaSlaveMonitorsTB(TBBase):
    def __init__(self, dut):
        super().__init__(dut)
        self.dut = dut
        self.ID_W   = int(os.environ.get('PARAM_AXI_ID_WIDTH', '8'))
        self.ADDR_W = int(os.environ.get('PARAM_AXI_ADDR_WIDTH', '32'))
        self.DATA_W = int(os.environ.get('PARAM_AXI_DATA_WIDTH', '64'))
        self.USER_W = int(os.environ.get('PARAM_AXI_USER_WIDTH', '1'))

        self.mem = MemoryModel(num_lines=65536,
                               bytes_per_line=max(4, (self.DATA_W + 7) // 8),
                               log=self.log)
        self.wr = create_axi4_master_wr(
            dut=dut, clock=dut.aclk, prefix="s_axi", log=self.log,
            data_width=self.DATA_W, id_width=self.ID_W, addr_width=self.ADDR_W,
            user_width=self.USER_W, multi_sig=True, memory_model=self.mem)
        self.rd = create_axi4_master_rd(
            dut=dut, clock=dut.aclk, prefix="s_axi", log=self.log,
            data_width=self.DATA_W, id_width=self.ID_W, addr_width=self.ADDR_W,
            user_width=self.USER_W, multi_sig=True, memory_model=self.mem)
        self.wr_if = self.wr['interface']
        self.rd_if = self.rd['interface']

    # ---- three-method reset contract ----
    async def assert_reset(self):
        self.dut.aresetn.value = 0

    async def deassert_reset(self):
        self.dut.aresetn.value = 1

    async def setup_clocks_and_reset(self):
        await self.start_clock('aclk', 10, 'ns')
        self.dut.read_lfsr_reset.value = 0
        self.dut.write_crc_reset.value = 0
        # ALL monitor packet classes enabled (monitor-validation env).
        self.dut.cfg_monitor_enable.value = 1
        self.dut.cfg_error_enable.value = 1
        self.dut.cfg_compl_enable.value = 1
        self.dut.cfg_timeout_enable.value = 1
        self.dut.cfg_perf_enable.value = 1
        self.dut.cfg_threshold_enable.value = 1
        self.dut.cfg_debug_enable.value = 1
        self.dut.cfg_timeout_cycles.value = 0xFFFF
        self.dut.tally_freeze.value = 0
        self.dut.tally_flush.value = 0
        self.dut.tally_clear.value = 0
        self.dut.tally_rd_addr.value = 0
        self.dut.tally_watch_arm.value = 0
        self.dut.tally_watch_pkttype_mask.value = 0
        self.dut.tally_latch_sel.value = 0
        await self.assert_reset()
        await self.wait_clocks('aclk', 10)
        await self.deassert_reset()
        await self.wait_clocks('aclk', 10)
        for ch in ('AW', 'W', 'B'):
            if ch in self.wr:
                await self.wr[ch].reset_bus()
        for ch in ('AR', 'R'):
            if ch in self.rd:
                await self.rd[ch].reset_bus()
        await self.wait_clocks('aclk', 5)

    # ---- tally readback ----
    async def read_bin(self, b: int) -> int:
        self.dut.tally_rd_addr.value = b
        await self.wait_clocks('aclk', 3)
        await ReadOnly()
        v = int(self.dut.tally_rd_count.value)
        await RisingEdge(self.dut.aclk)
        return v

    async def freeze_flush(self):
        self.dut.tally_freeze.value = 1
        await self.wait_clocks('aclk', 3)
        self.dut.tally_flush.value = 1
        await self.wait_clocks('aclk', 1)
        self.dut.tally_flush.value = 0
        for _ in range(400):
            await ReadOnly()
            busy = int(self.dut.tally_flush_busy.value)
            await RisingEdge(self.dut.aclk)
            if busy == 0:
                break
        assert int(self.dut.tally_flush_busy.value) == 0, "tally flush never completed"

    # ---- traffic ----
    async def run_traffic(self, n_writes=8, n_reads=8, burst_len=4):
        for i in range(n_writes):
            data = [(i * 7 + b + 1) & ((1 << self.DATA_W) - 1) for b in range(burst_len)]
            await self.wr_if.write_transaction(0x1000 + i * 0x100, data, burst_len=burst_len)
        for i in range(n_reads):
            await self.rd_if.read_transaction(0x2000 + i * 0x100, burst_len=burst_len)
        await self.wait_clocks('aclk', 100)
