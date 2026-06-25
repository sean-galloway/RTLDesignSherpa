# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway
#
# Module: wr2rd_forward_tb
# Purpose: TB for wr2rd_forward — combinational AR snarf-and-bypass
#          that intercepts AXI reads matching an in-flight write and
#          routes them to the W buffer instead of DRAM.

"""TB for `wr2rd_forward`.

The FUB is purely combinational. The TB drives `ar_*`, the
`cam_*` snapshot vector for each slot, and the downstream
`fwd_ready_i` / `rd_push_ready_i` strobes. The five contracts the
consumer (axi_intake R-emit) and `rd_cmd_cam` push port rely on:

  1. **No-match → passthrough.** ar_valid + no eligible CAM slot
     drives `rd_push_valid_o` with the AR's tuple, gated by
     `rd_push_ready_i`.
  2. **Match → forward.** ar_valid + one eligible slot drives
     `fwd_valid_o` with `cam_w_buf_ptr[slot]`, `ar_id_i`, `ar_len_i`,
     and `fwd_src_slot_o = slot`.
  3. **Multi-match selection.** Two slots match the same address →
     the **higher** slot wins (last-write-wins under the wr_cmd_cam's
     lowest-free-slot allocation pattern).
  4. **Partial-strobe gate.** `cam_full_strb_i[slot] == 0` excludes
     that slot from forwarding even when address + length match.
  5. **Length mismatch gate.** `ar_len_i != cam_len_i[slot]` excludes
     it. Forwarding requires the read to cover *exactly* the write's
     beats — partial overlap would leak uncommitted data.

  Bonus: any of (rank, bank, row, col) differing must NOT match.
"""

from __future__ import annotations

import logging
import os
import random
from dataclasses import dataclass, field
from typing import List, Optional

import cocotb
from cocotb.clock import Clock
from cocotb.triggers import RisingEdge, Timer

from TBClasses.shared.tbbase import TBBase


_SETTLE_PS = 100


@dataclass
class CamSlot:
    valid:      bool = False
    rank:       int  = 0
    bank:       int  = 0
    row:        int  = 0
    col:        int  = 0
    length:     int  = 1
    w_buf_ptr:  int  = 0
    full_strb:  bool = True


@dataclass
class Ar:
    axid:  int = 0
    rank:  int = 0
    bank:  int = 0
    row:   int = 0
    col:   int = 0
    length: int = 1
    qos:   int = 0


class Wr2RdForwardTB(TBBase):
    CLK = 10

    def __init__(self, dut) -> None:
        super().__init__(dut)
        self.dut = dut
        self.log = logging.getLogger("wr2rd_forward_tb")
        self.log.setLevel(logging.INFO)
        self.WR_CAM_DEPTH    = self.convert_to_int(
            os.environ.get("WR_CAM_DEPTH",    "4"))
        self.AXI_ID_WIDTH    = self.convert_to_int(
            os.environ.get("AXI_ID_WIDTH",    "4"))
        self.NUM_RANKS       = self.convert_to_int(
            os.environ.get("NUM_RANKS",       "1"))
        self.NUM_BANKS       = self.convert_to_int(
            os.environ.get("NUM_BANKS",       "8"))
        self.ROW_WIDTH       = self.convert_to_int(
            os.environ.get("ROW_WIDTH",       "14"))
        self.COL_WIDTH       = self.convert_to_int(
            os.environ.get("COL_WIDTH",       "10"))
        self.BURST_LEN_WIDTH = self.convert_to_int(
            os.environ.get("BURST_LEN_WIDTH", "8"))
        self.W_BUF_PTR_WIDTH = self.convert_to_int(
            os.environ.get("W_BUF_PTR_WIDTH", "7"))
        self.SEED = self.convert_to_int(os.environ.get("SEED", "1"))

        self.RKW = max(1, (self.NUM_RANKS - 1).bit_length())
        self.BKW = (self.NUM_BANKS - 1).bit_length()
        self.WSL = max(1, (self.WR_CAM_DEPTH - 1).bit_length())

        # CAM mirror — Python side keeps track of what's been written
        # into the packed bus.
        self.slots: List[CamSlot] = [CamSlot() for _ in range(self.WR_CAM_DEPTH)]

    # ---- setup ----

    async def setup_clocks_and_reset(self):
        cocotb.start_soon(Clock(self.dut.mc_clk, self.CLK, units="ns").start())
        self._drive_idle()
        self.dut.mc_rst_n.value = 0
        await Timer(80, units="ns")
        self.dut.mc_rst_n.value = 1
        await self.wait_clocks("mc_clk", 4)

    def _drive_idle(self) -> None:
        self.dut.ar_valid_i.value = 0
        self.dut.ar_id_i.value    = 0
        self.dut.ar_rank_i.value  = 0
        self.dut.ar_bank_i.value  = 0
        self.dut.ar_row_i.value   = 0
        self.dut.ar_col_i.value   = 0
        self.dut.ar_len_i.value   = 0
        self.dut.ar_qos_i.value   = 0
        self.dut.fwd_ready_i.value     = 1
        self.dut.rd_push_ready_i.value = 1
        # Clear CAM snapshot
        self._push_cam_to_dut()

    # ---- CAM management (Python side mirror → DUT packed buses) ----

    def write_slot(self, slot: int, *, rank: int = 0, bank: int = 0,
                   row: int = 0, col: int = 0, length: int = 1,
                   w_buf_ptr: int = 0, full_strb: bool = True) -> None:
        self.slots[slot] = CamSlot(
            valid=True, rank=rank, bank=bank, row=row, col=col,
            length=length, w_buf_ptr=w_buf_ptr, full_strb=full_strb,
        )

    def clear_slot(self, slot: int) -> None:
        self.slots[slot] = CamSlot()

    def clear_all(self) -> None:
        self.slots = [CamSlot() for _ in range(self.WR_CAM_DEPTH)]

    def _pack(self, getter, width: int) -> int:
        """Pack one field per slot into a single integer, slot i at
        bits [i*width +: width]. Matches the SV packed-array layout."""
        out = 0
        for i, s in enumerate(self.slots):
            val = getter(s) & ((1 << width) - 1)
            out |= val << (i * width)
        return out

    def _push_cam_to_dut(self) -> None:
        # one-bit-per-slot vectors
        self.dut.cam_valid_i.value     = sum(
            (1 << i) for i, s in enumerate(self.slots) if s.valid)
        self.dut.cam_full_strb_i.value = sum(
            (1 << i) for i, s in enumerate(self.slots) if s.full_strb)
        # packed fields
        self.dut.cam_rank_i.value      = self._pack(
            lambda s: s.rank, self.RKW)
        self.dut.cam_bank_i.value      = self._pack(
            lambda s: s.bank, self.BKW)
        self.dut.cam_row_i.value       = self._pack(
            lambda s: s.row,  self.ROW_WIDTH)
        self.dut.cam_col_i.value       = self._pack(
            lambda s: s.col,  self.COL_WIDTH)
        self.dut.cam_len_i.value       = self._pack(
            lambda s: s.length, self.BURST_LEN_WIDTH)
        self.dut.cam_w_buf_ptr_i.value = self._pack(
            lambda s: s.w_buf_ptr, self.W_BUF_PTR_WIDTH)

    # ---- drive an AR + sample outputs ----

    @dataclass
    class Decision:
        fwd_valid:   int  = 0
        fwd_id:      int  = 0
        fwd_w_buf_ptr: int = 0
        fwd_len:     int  = 0
        fwd_src_slot: int = 0
        rd_push_valid: int = 0
        rd_push_id:   int = 0
        rd_push_rank: int = 0
        rd_push_bank: int = 0
        rd_push_row:  int = 0
        rd_push_col:  int = 0
        rd_push_len:  int = 0
        rd_push_qos:  int = 0
        ar_ready:     int = 0

    async def issue_ar(self, ar: Ar) -> "Wr2RdForwardTB.Decision":
        """Drive ar_* + cam_* and read back the combinational decision."""
        self._push_cam_to_dut()
        self.dut.ar_valid_i.value = 1
        self.dut.ar_id_i.value    = ar.axid
        self.dut.ar_rank_i.value  = ar.rank
        self.dut.ar_bank_i.value  = ar.bank
        self.dut.ar_row_i.value   = ar.row
        self.dut.ar_col_i.value   = ar.col
        self.dut.ar_len_i.value   = ar.length
        self.dut.ar_qos_i.value   = ar.qos
        await Timer(_SETTLE_PS, units="ps")
        d = Wr2RdForwardTB.Decision(
            fwd_valid     = int(self.dut.fwd_valid_o.value),
            fwd_id        = int(self.dut.fwd_id_o.value),
            fwd_w_buf_ptr = int(self.dut.fwd_w_buf_ptr_o.value),
            fwd_len       = int(self.dut.fwd_len_o.value),
            fwd_src_slot  = int(self.dut.fwd_src_slot_o.value),
            rd_push_valid = int(self.dut.rd_push_valid_o.value),
            rd_push_id    = int(self.dut.rd_push_id_o.value),
            rd_push_rank  = int(self.dut.rd_push_rank_o.value),
            rd_push_bank  = int(self.dut.rd_push_bank_o.value),
            rd_push_row   = int(self.dut.rd_push_row_o.value),
            rd_push_col   = int(self.dut.rd_push_col_o.value),
            rd_push_len   = int(self.dut.rd_push_len_o.value),
            rd_push_qos   = int(self.dut.rd_push_qos_o.value),
            ar_ready      = int(self.dut.ar_ready_o.value),
        )
        # Deassert
        await RisingEdge(self.dut.mc_clk)
        self.dut.ar_valid_i.value = 0
        await Timer(_SETTLE_PS, units="ps")
        return d
