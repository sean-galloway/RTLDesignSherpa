# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway
#
# Module: addr_mapper_tb
# Purpose: TB for the addr_mapper FUB — purely combinational
#          flat-AXI-address → (rank, bank, row, col) decoder with three
#          runtime-selectable schemes.

"""TB for `addr_mapper`.

The FUB is purely combinational; no clock, no reset. The TB drives
`axi_addr_i` + `scheme_active_i` and reads `(rank_o, bank_o, row_o,
col_o)` after a tiny settle delay. A Python reference function
implements each scheme bit-for-bit so the scoreboard catches any
slicing drift between RTL and the Python `AddressMapping` class that
the DV uses.

The three schemes match the RTL contract documented in
`docs/ddr2_lpddr2_mas/ch02_blocks/03_addr_mapper.md`:

  * ROW_MAJOR        bits = [rank | row | bank | col]
  * BANK_INTERLEAVE  bits = [rank | row | col_hi | bank | col_lo]
  * XOR_HASH         same layout as BANK_INTERLEAVE; bank is XOR'd
                     with row[low] ^ row[mid] ^ seed
"""

from __future__ import annotations

import logging
import os
from dataclasses import dataclass
from typing import Tuple

import cocotb
from cocotb.triggers import Timer

from TBClasses.shared.tbbase import TBBase


_SETTLE_PS = 100

# Enum mirror — must track ddr2_lpddr2_pkg::addr_map_scheme_e.
SCHEME_ROW_MAJOR        = 0
SCHEME_BANK_INTERLEAVE  = 1
SCHEME_XOR_HASH         = 2
SCHEME_RSVD             = 3


@dataclass
class Decoded:
    rank: int
    bank: int
    row:  int
    col:  int


class AddrMapperTB(TBBase):
    def __init__(self, dut) -> None:
        super().__init__(dut)
        self.dut = dut
        self.log = logging.getLogger("addr_mapper_tb")
        self.log.setLevel(logging.INFO)
        self.AXI_ADDR_WIDTH    = self.convert_to_int(
            os.environ.get("AXI_ADDR_WIDTH", "32"))
        self.NUM_RANKS         = self.convert_to_int(
            os.environ.get("NUM_RANKS", "1"))
        self.NUM_BANKS         = self.convert_to_int(
            os.environ.get("NUM_BANKS", "8"))
        self.ROW_WIDTH         = self.convert_to_int(
            os.environ.get("ROW_WIDTH", "14"))
        self.COL_WIDTH         = self.convert_to_int(
            os.environ.get("COL_WIDTH", "10"))
        self.BYTE_OFFSET_WIDTH = self.convert_to_int(
            os.environ.get("BYTE_OFFSET_WIDTH", "3"))
        self.SEED = self.convert_to_int(os.environ.get("SEED", "1"))

        # Derived widths
        self.BW = max(1, (self.NUM_BANKS - 1).bit_length())
        self.KW = max(1, (self.NUM_RANKS - 1).bit_length())
        self.CL = min(4, self.COL_WIDTH)
        self.CH = self.COL_WIDTH - self.CL

        self.MASK_BANK = (1 << self.BW) - 1
        self.MASK_RANK = (1 << self.KW) - 1
        self.MASK_ROW  = (1 << self.ROW_WIDTH) - 1
        self.MASK_COL  = (1 << self.COL_WIDTH) - 1

    # ---- drive + sample ----

    def _drive_idle(self) -> None:
        self.dut.axi_addr_i.value      = 0
        self.dut.scheme_active_i.value = SCHEME_ROW_MAJOR
        self.dut.xor_seed_i.value      = 0
        self.dut.bg_field_pos_i.value  = 0

    async def setup(self):
        self._drive_idle()
        await Timer(_SETTLE_PS, units="ps")

    async def decode_rtl(self, addr: int, scheme: int,
                         xor_seed: int = 0) -> Decoded:
        self.dut.axi_addr_i.value      = addr & ((1 << self.AXI_ADDR_WIDTH) - 1)
        self.dut.scheme_active_i.value = scheme
        self.dut.xor_seed_i.value      = xor_seed & 0xFF
        await Timer(_SETTLE_PS, units="ps")
        return Decoded(
            rank=int(self.dut.rank_o.value),
            bank=int(self.dut.bank_o.value),
            row =int(self.dut.row_o.value),
            col =int(self.dut.col_o.value),
        )

    # ---- Python reference ----

    def _addr_word(self, addr: int) -> int:
        return addr >> self.BYTE_OFFSET_WIDTH

    def decode_row_major(self, addr: int) -> Decoded:
        w = self._addr_word(addr)
        col  = w & self.MASK_COL
        bank = (w >> self.COL_WIDTH) & self.MASK_BANK
        row  = (w >> (self.COL_WIDTH + self.BW)) & self.MASK_ROW
        rank = ((w >> (self.COL_WIDTH + self.BW + self.ROW_WIDTH))
                & self.MASK_RANK) if self.NUM_RANKS > 1 else 0
        return Decoded(rank=rank, bank=bank, row=row, col=col)

    def decode_bank_interleave(self, addr: int) -> Decoded:
        w = self._addr_word(addr)
        col_lo_mask = (1 << self.CL) - 1
        col_hi_mask = (1 << self.CH) - 1 if self.CH > 0 else 0
        col_lo = w & col_lo_mask
        bank   = (w >> self.CL) & self.MASK_BANK
        col_hi = (w >> (self.CL + self.BW)) & col_hi_mask
        row    = (w >> (self.CL + self.BW + self.CH)) & self.MASK_ROW
        rank   = ((w >> (self.CL + self.BW + self.CH + self.ROW_WIDTH))
                  & self.MASK_RANK) if self.NUM_RANKS > 1 else 0
        col = (col_hi << self.CL) | col_lo
        return Decoded(rank=rank, bank=bank, row=row, col=col)

    def decode_xor_hash(self, addr: int, xor_seed: int) -> Decoded:
        base = self.decode_bank_interleave(addr)
        # Hash bits: bank[i] = bank_raw[i] ^ row[LOW] ^ row[MID] ^ seed[i]
        hashed_bank = 0
        for i in range(self.BW):
            low_idx = i
            mid_idx = (i + self.BW) if (i + self.BW < self.ROW_WIDTH) \
                                    else (self.ROW_WIDTH - 1)
            bit = ((base.bank >> i) & 1) \
                ^ ((base.row >> low_idx) & 1) \
                ^ ((base.row >> mid_idx) & 1) \
                ^ ((xor_seed >> i) & 1)
            hashed_bank |= bit << i
        return Decoded(rank=base.rank, bank=hashed_bank,
                       row=base.row, col=base.col)
