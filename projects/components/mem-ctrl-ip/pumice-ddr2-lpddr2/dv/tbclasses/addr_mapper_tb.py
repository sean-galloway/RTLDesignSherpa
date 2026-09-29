# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway
#
# Module: addr_mapper_tb
# Purpose: TB for the addr_mapper FUB — purely combinational
#          flat-AXI-address -> (rank, bank, row, col) decoder driven by the
#          single ADDR_MAP.bank_lsb knob (+ optional bank XOR-hash).

"""TB for `addr_mapper`.

The FUB is purely combinational; no clock, no reset. The TB drives
`axi_addr_i` + `bank_lsb_i` / `hash_en_i` / `hash_seed_i` and reads
`(rank_o, bank_o, row_o, col_o)` after a settle delay. A Python reference
implements the same bank_lsb-driven stack bit-for-bit so the scoreboard
catches any slicing drift.

Layout (word address, low -> high):
  [ col_lo(bank_lsb) | bank(BW) | col_hi(CW-bank_lsb) | row(RW) | rank(KW) ]
  col = { col_hi, col_lo }; row LSB is invariant = CW+BW.

The classic schemes are just settings of bank_lsb:
  bank_lsb == COL_WIDTH        -> ROW_MAJOR
  bank_lsb == log2(cols/burst) -> BANK_INTERLEAVE (max)
  hash_en                      -> XOR_HASH (folded on top of any placement)
"""

from __future__ import annotations

import logging
import os
from dataclasses import dataclass

import cocotb
from cocotb.triggers import Timer

from TBClasses.shared.tbbase import TBBase


_SETTLE_PS = 100


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
        self.AXI_ADDR_WIDTH    = self.convert_to_int(os.environ.get("AXI_ADDR_WIDTH", "32"))
        self.NUM_RANKS         = self.convert_to_int(os.environ.get("NUM_RANKS", "1"))
        self.NUM_BANKS         = self.convert_to_int(os.environ.get("NUM_BANKS", "8"))
        self.ROW_WIDTH         = self.convert_to_int(os.environ.get("ROW_WIDTH", "14"))
        self.COL_WIDTH         = self.convert_to_int(os.environ.get("COL_WIDTH", "10"))
        self.BYTE_OFFSET_WIDTH = self.convert_to_int(os.environ.get("BYTE_OFFSET_WIDTH", "3"))
        self.SEED = self.convert_to_int(os.environ.get("SEED", "1"))

        self.BW = max(1, (self.NUM_BANKS - 1).bit_length())
        self.KW = max(1, (self.NUM_RANKS - 1).bit_length())
        self.MASK_BANK = (1 << self.BW) - 1
        self.MASK_RANK = (1 << self.KW) - 1
        self.MASK_ROW  = (1 << self.ROW_WIDTH) - 1
        self.MASK_COL  = (1 << self.COL_WIDTH) - 1

    # ---- drive + sample ----

    def _drive_idle(self) -> None:
        self.dut.axi_addr_i.value  = 0
        self.dut.bank_lsb_i.value  = self.COL_WIDTH   # ROW_MAJOR
        self.dut.hash_en_i.value   = 0
        self.dut.hash_seed_i.value = 0

    async def setup(self):
        self._drive_idle()
        await Timer(_SETTLE_PS, units="ps")

    async def decode_rtl(self, addr: int, bank_lsb: int, *,
                         hash_en: int = 0, hash_seed: int = 0) -> Decoded:
        self.dut.axi_addr_i.value  = addr & ((1 << self.AXI_ADDR_WIDTH) - 1)
        self.dut.bank_lsb_i.value  = bank_lsb & 0x1F
        self.dut.hash_en_i.value   = hash_en & 1
        self.dut.hash_seed_i.value = hash_seed & 0xFF
        await Timer(_SETTLE_PS, units="ps")
        return Decoded(
            rank=int(self.dut.rank_o.value),
            bank=int(self.dut.bank_o.value),
            row =int(self.dut.row_o.value),
            col =int(self.dut.col_o.value),
        )

    # ---- Python reference (mirrors addr_mapper.sv exactly) ----

    def decode_ref(self, addr: int, bank_lsb: int, *,
                   hash_en: int = 0, hash_seed: int = 0) -> Decoded:
        w = addr >> self.BYTE_OFFSET_WIDTH
        blsb = max(0, min(bank_lsb, self.COL_WIDTH))   # RTL clamp
        col_lo = w & ((1 << blsb) - 1)
        bank   = (w >> blsb) & self.MASK_BANK
        col_hi = (w >> (blsb + self.BW)) & ((1 << (self.COL_WIDTH - blsb)) - 1)
        row    = (w >> (self.COL_WIDTH + self.BW)) & self.MASK_ROW    # row LSB invariant
        rank   = ((w >> (self.COL_WIDTH + self.BW + self.ROW_WIDTH)) & self.MASK_RANK) \
                 if self.NUM_RANKS > 1 else 0
        col = (col_lo | (col_hi << blsb)) & self.MASK_COL
        if hash_en:
            hashed = 0
            for i in range(self.BW):
                mid = (i + self.BW) if (i + self.BW < self.ROW_WIDTH) else (self.ROW_WIDTH - 1)
                bit = ((bank >> i) & 1) ^ ((row >> i) & 1) \
                    ^ ((row >> mid) & 1) ^ ((hash_seed >> i) & 1)
                hashed |= bit << i
            bank = hashed
        return Decoded(rank=rank, bank=bank, row=row, col=col)
