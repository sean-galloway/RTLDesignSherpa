# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway

"""Testbench for `andesite_dfi_layer` (TASK-016 t6).

Drives the controller-side command and write-data streams, models a trivial
DFI PHY on the dfi_clk side, and checks that the DFI 4.0 pin surface and
DBI-vs-strobe mask behaviour come out of the composed layer correctly.
"""

import cocotb
from cocotb.triggers import RisingEdge, Timer

import os
import subprocess
import sys

_repo_root = subprocess.check_output(
    ['git', 'rev-parse', '--show-toplevel']
).decode().strip()
if _repo_root not in sys.path:
    sys.path.insert(0, _repo_root)
_BIN = os.path.join(_repo_root, "bin")
if _BIN not in sys.path:
    sys.path.insert(0, _BIN)

from TBClasses.shared.tbbase import TBBase    # noqa: E402

# dram_op_e (andesite_pkg)
OP_NOP, OP_ACT, OP_RD, OP_RDA, OP_WR, OP_WRA = 0x0, 0x1, 0x2, 0x3, 0x4, 0x5
OP_PRE, OP_PREA, OP_REF, OP_REFPB = 0x6, 0x7, 0x8, 0x9
OP_MRS, OP_ZQCS, OP_ZQCL = 0xA, 0xB, 0xC

MEMTYPE_DDR4 = 0b010


class AndesiteDfiLayerTB(TBBase):
    def __init__(self, dut):
        super().__init__(dut)
        self.NUM_BANKS = 8
        self.NUM_BG = 4
        self.ROW_WIDTH = 14
        self.COL_WIDTH = 10
        self.ADDR_WIDTH = 18
        self.RKW = 1
        self.BKW = 3
        self.BGW = 2
        self.OP_W = 5
        self.CMD_DW = (self.OP_W + self.RKW + self.BKW + self.BGW
                       + self.ROW_WIDTH + self.COL_WIDTH + 1)
        self.DFI_DATA_WIDTH = 128
        self.DFI_RATE = 2
        self.STRB_W = self.DFI_DATA_WIDTH // 8
        self.BL_WORDS = 2

    async def setup(self):
        await self.start_clock('ctl_clk', freq=10, units='ns')
        await self.start_clock('dfi_clk', freq=10, units='ns')
        d = self.dut
        d.ctl_rstn.value = 0
        d.dfi_rstn.value = 0

        d.cmd_valid_i.value = 0
        d.cmd_data_i.value = 0
        d.wd_valid_i.value = 0
        d.wd_data_i.value = 0
        d.wd_strb_i.value = 0
        d.wd_dbi_i.value = 0
        d.wd_last_i.value = 0
        d.rd_ready_i.value = 1

        d.init_busy_i.value = 0
        d.init_done_i.value = 0
        d.rd_dbi_en_i.value = 0
        d.wr_dbi_en_i.value = 0

        d.memtype_i.value = MEMTYPE_DDR4
        d.parity_en_i.value = 0
        d.gear_i.value = 1           # DFI_RATE=2 -> active_rate=2 -> all phases
        d.rd_phase_i.value = 0
        d.wr_phase_i.value = 0
        d.t_phy_wrlat_i.value = 2
        d.t_rddata_en_i.value = 2
        d.cke_i.value = 1

        d.dfi_rddata_i.value = 0
        d.dfi_rddata_valid_i.value = 0
        d.dfi_rddata_dbi_i.value = 0

        await self.wait_clocks('ctl_clk', 5)
        await self.wait_clocks('dfi_clk', 5)
        d.ctl_rstn.value = 1
        d.dfi_rstn.value = 1
        await self.wait_clocks('ctl_clk', 2)
        await self.wait_clocks('dfi_clk', 2)

    def pack_cmd(self, op, bank=0, bg=0, row=0, col=0, ap=0, rank=0):
        word = (ap & 1)
        word = (word << self.COL_WIDTH) | (col & ((1 << self.COL_WIDTH) - 1))
        word = (word << self.ROW_WIDTH) | (row & ((1 << self.ROW_WIDTH) - 1))
        word = (word << self.BGW) | (bg & ((1 << self.BGW) - 1))
        word = (word << self.BKW) | (bank & ((1 << self.BKW) - 1))
        word = (word << self.RKW) | (rank & ((1 << self.RKW) - 1))
        word = (word << self.OP_W) | (op & ((1 << self.OP_W) - 1))
        return word

    async def push_cmd(self, op, bank=0, bg=0, row=0, col=0, ap=0):
        d = self.dut
        d.cmd_data_i.value = self.pack_cmd(op, bank, bg, row, col, ap)
        d.cmd_valid_i.value = 1
        while True:
            await RisingEdge(d.ctl_clk)
            await Timer(1, 'ns')
            if int(d.cmd_ready_o.value):
                break
        d.cmd_valid_i.value = 0
        d.cmd_data_i.value = 0

    async def push_wd(self, data, strb, dbi, last=1):
        d = self.dut
        d.wd_valid_i.value = 1
        d.wd_data_i.value = data
        d.wd_strb_i.value = strb
        d.wd_dbi_i.value = dbi
        d.wd_last_i.value = last
        while True:
            await RisingEdge(d.ctl_clk)
            await Timer(1, 'ns')
            if int(d.wd_ready_o.value):
                break
        d.wd_valid_i.value = 0
        d.wd_data_i.value = 0
        d.wd_strb_i.value = 0
        d.wd_dbi_i.value = 0
        d.wd_last_i.value = 0

    async def dfi_cmd_monitor(self, samples, count=40):
        d = self.dut
        for _ in range(count):
            await RisingEdge(d.dfi_clk)
            await Timer(1, 'ns')
            cs = int(d.dfi_cs_o.value)
            if cs == 0:
                samples.append({
                    'cs': cs,
                    'act': int(d.dfi_act_n_o.value),
                    'ras': int(d.dfi_ras_n_o.value),
                    'cas': int(d.dfi_cas_n_o.value),
                    'we': int(d.dfi_we_n_o.value),
                    'bank': int(d.dfi_bank_o.value),
                    'bg': int(d.dfi_bg_o.value),
                    'address': int(d.dfi_address_o.value),
                })

    async def sample_wr_drive(self, timeout=30):
        d = self.dut
        for i in range(timeout):
            await RisingEdge(d.dfi_clk)
            await Timer(1, 'ns')
            en = int(d.dfi_wrdata_en_o.value)
            if en != 0:
                mask = int(d.dfi_wrdata_mask_o.value)
                data = int(d.dfi_wrdata_o.value)
                self.log.info(f"sample_wr_drive HIT +{i}: en={en} "
                              f"mask={mask:#x} data={data:#x}")
                return mask, data
        self.log.info(f"sample_wr_drive MISS after {timeout} dfi cycles")
        return None, None

    async def return_rd_data(self, words, dbi=0):
        d = self.dut
        # Wait for the aligner to assert dfi_rddata_en_o.
        while True:
            await RisingEdge(d.dfi_clk)
            await Timer(1, 'ns')
            if int(d.dfi_rddata_en_o.value) != 0:
                break
        for w in words:
            d.dfi_rddata_i.value = w
            d.dfi_rddata_valid_i.value = (1 << self.DFI_RATE) - 1
            d.dfi_rddata_dbi_i.value = dbi
            await RisingEdge(d.dfi_clk)
            await Timer(1, 'ns')
        d.dfi_rddata_valid_i.value = 0
        d.dfi_rddata_i.value = 0
        d.dfi_rddata_dbi_i.value = 0

    async def drain_rd(self, limit=30):
        d = self.dut
        words = []
        for _ in range(limit):
            await RisingEdge(d.ctl_clk)
            await Timer(1, 'ns')
            if int(d.rd_valid_o.value):
                words.append((int(d.rd_data_o.value), int(d.rd_dbi_o.value)))
        return words
