# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# Module: dma_slave_monitors_tb
# Purpose: FUB testbench for dma_slave_monitors — drives the wrapper's AXI4
#          slave interface with an AXI4 master BFM (RDS-DV), and validates that
#          the internal monitors observe the traffic and emit monbus packets on
#          the group's master-write port.
#
# The DUT's output contract is the monbus group: slave-side rd/wr monitors ->
# monbus_arbiter -> monbus_axil_axil_group -> m_axil_* (bulk trace writes) plus
# s_axil_* (err-FIFO reads) and irq_out. There is NO tally inside this module --
# the tally memories live one level up in stream_mon_harness, so this TB checks
# what the wrapper actually produces: decoded packets on the wire.
#
# Wire-level orchestration of that group is NOT hand-rolled here: it is the
# shared MonbusGroupHarness (drain/trace/fifo/irq + TBClasses.monbus decode).

import os

import cocotb
from cocotb.triggers import RisingEdge, ReadOnly

from TBClasses.shared.tbbase import TBBase
from TBClasses.scoreboards.monbus_group import MonbusGroupHarness
from CocoTBFramework.components.axi4.axi4_factories import (
    create_axi4_master_wr, create_axi4_master_rd)
from CocoTBFramework.components.shared.memory_model import MemoryModel

PKT_COMPLETION = 1

# Monbus group bulk-write window. The group only issues m_axil writes for
# addresses inside [base, limit]; leave it wide so every packet drains.
MON_BASE  = 0x0004_0000
MON_LIMIT = 0x0007_FFFF


class DmaSlaveMonitorsTB(TBBase):
    def __init__(self, dut):
        super().__init__(dut)
        self.dut = dut
        self.ID_W   = int(os.environ.get('PARAM_AXI_ID_WIDTH', '8'))
        self.ADDR_W = int(os.environ.get('PARAM_AXI_ADDR_WIDTH', '32'))
        self.DATA_W = int(os.environ.get('PARAM_AXI_DATA_WIDTH', '64'))
        self.USER_W = int(os.environ.get('PARAM_AXI_USER_WIDTH', '1'))
        # Drain port width: monbus_axil_axil_group S_AXIL_DATA_WIDTH. At 32 a
        # 64-bit record slice arrives as two beats, so a record is 6 drain beats.
        self.DRAIN_W = int(os.environ.get('PARAM_S_AXIL_DATA_WIDTH', '32'))

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

        # Shared monbus-group collateral: err-drain read side on s_axil_, bulk
        # trace master-write side on m_axil_, fifo counters on the group node.
        self.mon = MonbusGroupHarness(
            dut, dut.aclk,
            drain_proto="axil", trace_proto="axil",
            drain_prefix="s_axil_", trace_prefix="m_axil_",
            drain_data_width=self.DRAIN_W,
            group_node=dut.u_monbus_group, irq_sig=dut.irq_out,
            addr_width=self.ADDR_W, log=self.log)

    # ---- three-method reset contract ----
    async def assert_reset(self):
        self.dut.aresetn.value = 0

    async def deassert_reset(self):
        self.dut.aresetn.value = 1

    async def setup_clocks_and_reset(self):
        await self.start_clock('aclk', 10, 'ns')
        self.dut.cam_clear.value = 0
        self.dut.read_lfsr_reset.value = 0
        self.dut.write_crc_reset.value = 0
        # ALL monitor packet classes enabled (monitor-validation env). The rd and
        # wr monitors take SEPARATE cfg_rd_*/cfg_wr_* inputs -- there are no
        # unsplit cfg_* ports on this wrapper.
        for side in ('rd', 'wr'):
            for cone in ('monitor', 'error', 'compl', 'timeout',
                         'perf', 'threshold', 'debug'):
                getattr(self.dut, f'cfg_{side}_{cone}_enable').value = 1
            getattr(self.dut, f'cfg_{side}_timeout_cycles').value = 0xFFFF
        self.dut.cfg_base_addr.value = MON_BASE
        self.dut.cfg_limit_addr.value = MON_LIMIT
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
        # Sink the bulk trace writes from here on, so packets drain as they are
        # produced instead of backing the write FIFO up.
        self.mon.start_trace_consumer(ready_prob=1.0)

    # ---- traffic ----
    async def run_traffic(self, n_writes=8, n_reads=8, burst_len=4):
        for i in range(n_writes):
            data = [(i * 7 + b + 1) & ((1 << self.DATA_W) - 1) for b in range(burst_len)]
            await self.wr_if.write_transaction(0x1000 + i * 0x100, data, burst_len=burst_len)
        for i in range(n_reads):
            await self.rd_if.read_transaction(0x2000 + i * 0x100, burst_len=burst_len)
        await self.wait_clocks('aclk', 400)

    # ---- observation ----
    def beat_counts(self):
        """(read, write) total beats the DUT's own counters observed."""
        return (int(self.dut.read_beat_count_total.value),
                int(self.dut.write_beat_count_total.value))

    def packets(self):
        """Decode everything captured on the bulk-trace port."""
        self.mon.parse_trace_records()
        return list(self.mon.received_packets)
