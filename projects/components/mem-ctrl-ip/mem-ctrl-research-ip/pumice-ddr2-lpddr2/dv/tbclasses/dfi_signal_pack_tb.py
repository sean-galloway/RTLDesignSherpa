# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway
#
# Module: DfiSignalPackTB
# Purpose: Unit-level testbench for dfi_signal_pack.

"""
Testbench class for `dfi_signal_pack`.

The FUB is a pure 1-cycle registered pipeline on every DFI bus signal.
The TB drives the input ports, advances one clock, and checks the output
matches the previous cycle's input. Reset values are also verified.

Reset values (from the FUB's reset block):
  dfi_address       = '0
  dfi_bank          = '0
  dfi_cas_n         = '1
  dfi_ras_n         = '1
  dfi_we_n          = '1
  dfi_cs_n          = '1
  dfi_cke           = '0
  dfi_odt           = '0
  dfi_wrdata        = '0
  dfi_wrdata_en     = '0
  dfi_wrdata_mask   = '1
  dfi_rddata_en     = '0
  dfi_dram_clk_dis  = '0
"""

import os
import sys
import random
import subprocess
from dataclasses import dataclass, field
from typing import Dict, List

import cocotb
from cocotb.triggers import RisingEdge, Timer

_NBA_SETTLE_PS = 1

_repo_root = subprocess.check_output(
    ['git', 'rev-parse', '--show-toplevel']
).decode().strip()
if _repo_root not in sys.path:
    sys.path.insert(0, _repo_root)

from TBClasses.shared.tbbase import TBBase  # noqa: E402


@dataclass
class DfiBus:
    """One snapshot of the full DFI bus."""
    address:        int = 0
    bank:           int = 0
    cas_n:          int = 0
    ras_n:          int = 0
    we_n:           int = 0
    cs_n:           int = 0
    cke:            int = 0
    odt:            int = 0
    wrdata:         int = 0
    wrdata_en:      int = 0
    wrdata_mask:    int = 0
    rddata_en:      int = 0


class DfiSignalPackTB(TBBase):
    CLK_PERIOD_NS = 10

    def __init__(self, dut) -> None:
        super().__init__(dut)
        self.SEED = self.convert_to_int(os.environ.get('SEED', '12345'))
        random.seed(self.SEED)
        self.TEST_LEVEL = os.environ.get('TEST_LEVEL', 'gate').lower()

        self.NUM_RANKS      = self.convert_to_int(os.environ.get('NUM_RANKS',      '1'))
        self.DFI_RATE       = self.convert_to_int(os.environ.get('DFI_RATE',       '2'))
        self.DFI_ADDR_WIDTH = self.convert_to_int(os.environ.get('DFI_ADDR_WIDTH','14'))
        self.DFI_BANK_WIDTH = self.convert_to_int(os.environ.get('DFI_BANK_WIDTH','3'))
        self.DFI_CTRL_WIDTH = self.convert_to_int(os.environ.get('DFI_CTRL_WIDTH','1'))
        self.DFI_CS_WIDTH   = self.convert_to_int(os.environ.get('DFI_CS_WIDTH',
                                                                 str(self.NUM_RANKS)))
        self.DFI_DATA_WIDTH = self.convert_to_int(os.environ.get('DFI_DATA_WIDTH','128'))
        self.DFI_STRB_WIDTH = self.DFI_DATA_WIDTH // 8
        self.DFI_EN_WIDTH   = self.convert_to_int(os.environ.get('DFI_EN_WIDTH',   '1'))

        self.ADDR_BUS_W = self.DFI_ADDR_WIDTH * self.DFI_RATE
        self.BANK_BUS_W = self.DFI_BANK_WIDTH * self.DFI_RATE
        self.CTRL_BUS_W = self.DFI_CTRL_WIDTH * self.DFI_RATE
        self.CS_BUS_W   = self.DFI_CS_WIDTH   * self.DFI_RATE

        self.MASK_ADDR = (1 << self.ADDR_BUS_W) - 1
        self.MASK_BANK = (1 << self.BANK_BUS_W) - 1
        self.MASK_CTRL = (1 << self.CTRL_BUS_W) - 1
        self.MASK_CS   = (1 << self.CS_BUS_W)   - 1
        self.MASK_DATA = (1 << self.DFI_DATA_WIDTH) - 1
        self.MASK_STRB = (1 << self.DFI_STRB_WIDTH) - 1
        self.MASK_EN   = (1 << self.DFI_EN_WIDTH)   - 1

    # ---------------- setup ----------------

    async def setup_clocks_and_reset(self):
        self._drive_idle()
        await self.start_clock('mc_clk', freq=self.CLK_PERIOD_NS, units='ns')
        self.dut.mc_rst_n.value = 0
        await self.wait_clocks('mc_clk', 5)
        self.dut.mc_rst_n.value = 1
        await self.wait_clocks('mc_clk', 5)

    def _drive_idle(self):
        self.dut.i_address.value       = 0
        self.dut.i_bank.value          = 0
        self.dut.i_cas_n.value         = self.MASK_CTRL
        self.dut.i_ras_n.value         = self.MASK_CTRL
        self.dut.i_we_n.value          = self.MASK_CTRL
        self.dut.i_cs_n.value          = self.MASK_CS
        self.dut.i_cke.value           = 0
        self.dut.i_odt.value           = 0
        self.dut.i_wrdata.value        = 0
        self.dut.i_wrdata_en.value     = 0
        self.dut.i_wrdata_mask.value   = self.MASK_STRB
        self.dut.i_rddata_en.value     = 0

    # ---------------- ops ----------------

    def drive(self, b: DfiBus):
        self.dut.i_address.value     = b.address     & self.MASK_ADDR
        self.dut.i_bank.value        = b.bank        & self.MASK_BANK
        self.dut.i_cas_n.value       = b.cas_n       & self.MASK_CTRL
        self.dut.i_ras_n.value       = b.ras_n       & self.MASK_CTRL
        self.dut.i_we_n.value        = b.we_n        & self.MASK_CTRL
        self.dut.i_cs_n.value        = b.cs_n        & self.MASK_CS
        self.dut.i_cke.value         = b.cke         & self.MASK_CS
        self.dut.i_odt.value         = b.odt         & self.MASK_CS
        self.dut.i_wrdata.value      = b.wrdata      & self.MASK_DATA
        self.dut.i_wrdata_en.value   = b.wrdata_en   & self.MASK_EN
        self.dut.i_wrdata_mask.value = b.wrdata_mask & self.MASK_STRB
        self.dut.i_rddata_en.value   = b.rddata_en   & self.MASK_EN

    def check(self, expected: DfiBus, label: str = ""):
        got = self.read_outputs()
        for fname in ('address', 'bank', 'cas_n', 'ras_n', 'we_n', 'cs_n',
                      'cke', 'odt', 'wrdata', 'wrdata_en', 'wrdata_mask',
                      'rddata_en'):
            g = getattr(got, fname)
            e = getattr(expected, fname)
            assert g == e, (
                f"{label}: {fname} got {g:#x} want {e:#x}"
            )

    def read_outputs(self) -> DfiBus:
        return DfiBus(
            address     = int(self.dut.dfi_address_o.value),
            bank        = int(self.dut.dfi_bank_o.value),
            cas_n       = int(self.dut.dfi_cas_n_o.value),
            ras_n       = int(self.dut.dfi_ras_n_o.value),
            we_n        = int(self.dut.dfi_we_n_o.value),
            cs_n        = int(self.dut.dfi_cs_n_o.value),
            cke         = int(self.dut.dfi_cke_o.value),
            odt         = int(self.dut.dfi_odt_o.value),
            wrdata      = int(self.dut.dfi_wrdata_o.value),
            wrdata_en   = int(self.dut.dfi_wrdata_en_o.value),
            wrdata_mask = int(self.dut.dfi_wrdata_mask_o.value),
            rddata_en   = int(self.dut.dfi_rddata_en_o.value),
        )

    def reset_expected(self) -> DfiBus:
        """Reset-snapshot expected values (post-reset, all inputs idle)."""
        return DfiBus(
            address=0, bank=0,
            cas_n=self.MASK_CTRL, ras_n=self.MASK_CTRL, we_n=self.MASK_CTRL,
            cs_n=self.MASK_CS,
            cke=0, odt=0,
            wrdata=0, wrdata_en=0, wrdata_mask=self.MASK_STRB,
            rddata_en=0,
        )

    def random_bus(self, rng: random.Random) -> DfiBus:
        return DfiBus(
            address     = rng.randint(0, self.MASK_ADDR),
            bank        = rng.randint(0, self.MASK_BANK),
            cas_n       = rng.randint(0, self.MASK_CTRL),
            ras_n       = rng.randint(0, self.MASK_CTRL),
            we_n        = rng.randint(0, self.MASK_CTRL),
            cs_n        = rng.randint(0, self.MASK_CS),
            cke         = rng.randint(0, self.MASK_CS),
            odt         = rng.randint(0, self.MASK_CS),
            wrdata      = rng.randint(0, self.MASK_DATA),
            wrdata_en   = rng.randint(0, self.MASK_EN),
            wrdata_mask = rng.randint(0, self.MASK_STRB),
            rddata_en   = rng.randint(0, self.MASK_EN),
        )
