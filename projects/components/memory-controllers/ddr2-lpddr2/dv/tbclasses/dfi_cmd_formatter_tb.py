# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway
#
# Module: DfiCmdFormatterTB
# Purpose: Unit-level testbench for dfi_cmd_formatter_fub.

"""
Testbench class for `dfi_cmd_formatter_fub`.

The FUB is a pure combinational truth-table decode of `dram_op_e` to the
DFI v2.1 control bus (multi-phase). The TB drives op/rank/bank/row/col
and verifies the per-phase output against a Python reference model.

Scoreboard rules:
  * Phase 0 carries the issued command per the DDR2 JEDEC truth table.
  * Phases 1..DFI_RATE-1 ALWAYS emit NOP (cs_n=1, ras_n=cas_n=we_n=1).
  * cs_n[rank] = 0 for the targeted rank; '1 elsewhere.
  * A10 = 1 for RDA/WRA/PREA (auto-precharge or all-bank precharge).
  * When memtype = LPDDR2, phase 0 should also be NOP (TODO marker in
    the FUB — LPDDR2 CA encoding not yet implemented).
"""

import os
import sys
import random
import subprocess
from dataclasses import dataclass
from typing import Optional

import cocotb
from cocotb.triggers import RisingEdge, Timer

_NBA_SETTLE_PS = 1

_repo_root = subprocess.check_output(
    ['git', 'rev-parse', '--show-toplevel']
).decode().strip()
if _repo_root not in sys.path:
    sys.path.insert(0, _repo_root)

from TBClasses.shared.tbbase import TBBase  # noqa: E402


# ---------------------------------------------------------------------------
# Constants — must match ddr2_lpddr2_pkg.sv
# ---------------------------------------------------------------------------

# dram_op_e
OP_NOP   = 0x0
OP_ACT   = 0x1
OP_RD    = 0x2
OP_RDA   = 0x3
OP_WR    = 0x4
OP_WRA   = 0x5
OP_PRE   = 0x6
OP_PREA  = 0x7
OP_REF   = 0x8
OP_REFPB = 0x9
OP_MRS   = 0xA
OP_ZQCS  = 0xB
OP_ZQCL  = 0xC
OP_SREFE = 0xD
OP_SREFX = 0xE
OP_DPDE  = 0xF

# memtype_e
MEMTYPE_DDR2   = 0
MEMTYPE_LPDDR2 = 1


# ---------------------------------------------------------------------------
# Reference model — produces the expected per-phase DFI bus values.
# ---------------------------------------------------------------------------

@dataclass
class PhaseDecoded:
    addr:  int
    bank:  int
    cas_n: int
    ras_n: int
    we_n:  int
    cs_n:  int   # per-rank, '1 = all-deselected
    odt:   int

    @staticmethod
    def nop(dfi_cs_w: int) -> 'PhaseDecoded':
        return PhaseDecoded(addr=0, bank=0,
                            cas_n=1, ras_n=1, we_n=1,
                            cs_n=(1 << dfi_cs_w) - 1,
                            odt=0)


def _selected_rank_mask(rank: int, dfi_cs_w: int) -> int:
    """cs_n with the targeted rank's bit cleared."""
    all_ones = (1 << dfi_cs_w) - 1
    return all_ones & ~(1 << rank)


def decode_p0_ddr2(op: int, rank: int, bank: int, row: int, col: int,
                   dfi_addr_w: int, dfi_bank_w: int,
                   dfi_cs_w: int) -> PhaseDecoded:
    """Compute the expected phase-0 DFI signals for a DDR2 command."""
    base = PhaseDecoded.nop(dfi_cs_w)
    base.cs_n = _selected_rank_mask(rank, dfi_cs_w)
    bank_mask = (1 << dfi_bank_w) - 1
    addr_mask = (1 << dfi_addr_w) - 1
    a10 = 1 << 10

    if op == OP_NOP:
        # selected NOP — cs_n active for targeted rank, ctrl bits all 1
        return base
    if op == OP_ACT:
        base.ras_n = 0
        base.cas_n = 1
        base.we_n  = 1
        base.bank  = bank & bank_mask
        base.addr  = row & addr_mask
        return base
    if op == OP_RD:
        base.ras_n = 1
        base.cas_n = 0
        base.we_n  = 1
        base.bank  = bank & bank_mask
        base.addr  = col & addr_mask    # A10 = 0
        return base
    if op == OP_RDA:
        base.ras_n = 1
        base.cas_n = 0
        base.we_n  = 1
        base.bank  = bank & bank_mask
        base.addr  = (col | a10) & addr_mask
        return base
    if op == OP_WR:
        base.ras_n = 1
        base.cas_n = 0
        base.we_n  = 0
        base.bank  = bank & bank_mask
        base.addr  = col & addr_mask
        return base
    if op == OP_WRA:
        base.ras_n = 1
        base.cas_n = 0
        base.we_n  = 0
        base.bank  = bank & bank_mask
        base.addr  = (col | a10) & addr_mask
        return base
    if op == OP_PRE:
        base.ras_n = 0
        base.cas_n = 1
        base.we_n  = 0
        base.bank  = bank & bank_mask
        # A10 = 0 — single-bank PRE
        return base
    if op == OP_PREA:
        base.ras_n = 0
        base.cas_n = 1
        base.we_n  = 0
        base.addr  = a10 & addr_mask
        return base
    if op == OP_REF:
        base.ras_n = 0
        base.cas_n = 0
        base.we_n  = 1
        return base
    if op == OP_MRS:
        base.ras_n = 0
        base.cas_n = 0
        base.we_n  = 0
        base.bank  = bank & bank_mask
        base.addr  = col & addr_mask
        return base
    # Other ops: drive NOP (defaults)
    base.cs_n = _selected_rank_mask(rank, dfi_cs_w)
    return base


# ---------------------------------------------------------------------------
# TB
# ---------------------------------------------------------------------------

class DfiCmdFormatterTB(TBBase):
    CLK_PERIOD_NS = 10

    def __init__(self, dut) -> None:
        super().__init__(dut)
        self.SEED = self.convert_to_int(os.environ.get('SEED', '12345'))
        random.seed(self.SEED)
        self.TEST_LEVEL = os.environ.get('TEST_LEVEL', 'gate').lower()

        # Parameters — must match the verilator -G overrides
        self.NUM_RANKS      = self.convert_to_int(os.environ.get('NUM_RANKS',      '1'))
        self.NUM_BANKS      = self.convert_to_int(os.environ.get('NUM_BANKS',      '8'))
        self.ROW_WIDTH      = self.convert_to_int(os.environ.get('ROW_WIDTH',     '14'))
        self.COL_WIDTH      = self.convert_to_int(os.environ.get('COL_WIDTH',     '10'))
        self.BLW            = self.convert_to_int(os.environ.get('BURST_LEN_WIDTH','8'))
        self.DFI_RATE       = self.convert_to_int(os.environ.get('DFI_RATE',       '2'))
        self.DFI_ADDR_WIDTH = self.convert_to_int(os.environ.get('DFI_ADDR_WIDTH','14'))
        self.DFI_BANK_WIDTH = self.convert_to_int(os.environ.get('DFI_BANK_WIDTH','3'))
        self.DFI_CTRL_WIDTH = self.convert_to_int(os.environ.get('DFI_CTRL_WIDTH','1'))
        self.DFI_CS_WIDTH   = self.convert_to_int(os.environ.get('DFI_CS_WIDTH',
                                                                 str(self.NUM_RANKS)))

        self.RKW = max(1, (self.NUM_RANKS - 1).bit_length()) if self.NUM_RANKS > 1 else 1
        self.BKW = max(1, (self.NUM_BANKS - 1).bit_length())

    # ---------------- setup ----------------

    async def setup_clocks_and_reset(self):
        self._drive_idle()
        await self.start_clock('mc_clk', freq=self.CLK_PERIOD_NS, units='ns')
        self.dut.mc_rst_n.value = 0
        await self.wait_clocks('mc_clk', 5)
        self.dut.mc_rst_n.value = 1
        await self.wait_clocks('mc_clk', 5)

    def _drive_idle(self):
        self.dut.memtype_i.value  = MEMTYPE_DDR2
        self.dut.cmd_valid_i.value = 0
        self.dut.cmd_op_i.value    = OP_NOP
        self.dut.cmd_rank_i.value  = 0
        self.dut.cmd_bank_i.value  = 0
        self.dut.cmd_row_i.value   = 0
        self.dut.cmd_col_i.value   = 0
        self.dut.cmd_len_i.value   = 0

    # ---------------- driver / scoreboard ----------------

    async def drive_and_check(self, *, op: int, rank: int = 0, bank: int = 0,
                              row: int = 0, col: int = 0, length: int = 0,
                              memtype: int = MEMTYPE_DDR2,
                              valid: bool = True) -> None:
        """Drive a (op, rank, bank, row, col) combination and verify the
        full multi-phase output against the reference model."""
        self.dut.memtype_i.value   = memtype
        self.dut.cmd_valid_i.value = 1 if valid else 0
        self.dut.cmd_op_i.value    = op
        self.dut.cmd_rank_i.value  = rank   & ((1 << self.RKW) - 1)
        self.dut.cmd_bank_i.value  = bank   & ((1 << self.BKW) - 1)
        self.dut.cmd_row_i.value   = row    & ((1 << self.ROW_WIDTH) - 1)
        self.dut.cmd_col_i.value   = col    & ((1 << self.COL_WIDTH) - 1)
        self.dut.cmd_len_i.value   = length & ((1 << self.BLW) - 1)

        # Let combinational outputs settle.
        await Timer(_NBA_SETTLE_PS, units='ps')

        # Build expected — phase 0 = decoded; phase 1..N-1 = NOP.
        if valid and memtype == MEMTYPE_DDR2:
            expected_p0 = decode_p0_ddr2(op, rank, bank, row, col,
                                          self.DFI_ADDR_WIDTH,
                                          self.DFI_BANK_WIDTH,
                                          self.DFI_CS_WIDTH)
        else:
            expected_p0 = PhaseDecoded.nop(self.DFI_CS_WIDTH)

        self._check_phase(0, expected_p0)
        for p in range(1, self.DFI_RATE):
            self._check_phase(p, PhaseDecoded.nop(self.DFI_CS_WIDTH))

    def _check_phase(self, phase: int, expected: PhaseDecoded) -> None:
        addr = self._slice(self.dut.dfi_address_o, phase,
                           self.DFI_ADDR_WIDTH)
        bank = self._slice(self.dut.dfi_bank_o,    phase, self.DFI_BANK_WIDTH)
        cas  = self._slice(self.dut.dfi_cas_n_o,   phase, self.DFI_CTRL_WIDTH)
        ras  = self._slice(self.dut.dfi_ras_n_o,   phase, self.DFI_CTRL_WIDTH)
        we   = self._slice(self.dut.dfi_we_n_o,    phase, self.DFI_CTRL_WIDTH)
        csn  = self._slice(self.dut.dfi_cs_n_o,    phase, self.DFI_CS_WIDTH)
        odt  = self._slice(self.dut.dfi_odt_o,     phase, self.DFI_CS_WIDTH)

        assert addr == expected.addr & ((1 << self.DFI_ADDR_WIDTH) - 1), (
            f"phase {phase}: dfi_address got {addr:#x} want {expected.addr:#x}"
        )
        assert bank == expected.bank, (
            f"phase {phase}: dfi_bank got {bank:#x} want {expected.bank:#x}"
        )
        assert cas == expected.cas_n, (
            f"phase {phase}: dfi_cas_n got {cas} want {expected.cas_n}"
        )
        assert ras == expected.ras_n, (
            f"phase {phase}: dfi_ras_n got {ras} want {expected.ras_n}"
        )
        assert we == expected.we_n, (
            f"phase {phase}: dfi_we_n got {we} want {expected.we_n}"
        )
        assert csn == expected.cs_n, (
            f"phase {phase}: dfi_cs_n got {csn:#x} want {expected.cs_n:#x}"
        )
        assert odt == expected.odt, (
            f"phase {phase}: dfi_odt got {odt:#x} want {expected.odt:#x}"
        )

    @staticmethod
    def _slice(sig, phase: int, width: int) -> int:
        raw = int(sig.value)
        return (raw >> (phase * width)) & ((1 << width) - 1)
