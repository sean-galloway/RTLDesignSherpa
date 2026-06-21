# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway
#
# Module: WrCmdCamTB
# Purpose: Unit-level testbench for wr_cmd_cam.

"""
Testbench class for `wr_cmd_cam`.

The CAM has no AXI surface — it exposes a custom set of push/query/issued/
beat_pull/b_complete strobes plus a packed snapshot bus. The TB mirrors the
RTL's per-slot state in a Python scoreboard and verifies every combinational
output (match_pending, match_rowhit, beat_pull_ptr, beat_pull_last,
entry_complete, dbg_occupancy, snap_*) on every operation.

Methodology — modelled after stream/dv/tbclasses fub-level TBs:
  * Subclasses TBBase (clock/reset/convert_to_int)
  * Drives idle defaults at construction; per-op helpers raise strobes for
    exactly one cycle and re-idle them
  * One `verify_combo()` per cycle compares ALL DUT outputs against the
    scoreboard
  * Test scenarios live in the test runner; the TB is just plumbing
"""

import os
import sys
import random
import subprocess
from dataclasses import dataclass, field
from typing import Dict, List, Optional, Tuple

import cocotb
from cocotb.triggers import RisingEdge, ReadOnly, Timer

# After awaiting RisingEdge(clk), cocotb resumes the coroutine BEFORE the
# NBA region commits register updates. A tiny Timer step is the canonical
# way to advance past NBA so subsequent reads see post-edge register state,
# while keeping the simulator in a writeable phase (unlike ReadOnly()).
_NBA_SETTLE_PS = 1

_repo_root = subprocess.check_output(['git', 'rev-parse', '--show-toplevel']).decode().strip()
if _repo_root not in sys.path:
    sys.path.insert(0, _repo_root)

from TBClasses.shared.tbbase import TBBase  # noqa: E402


# ---------------------------------------------------------------------------
# Scoreboard
# ---------------------------------------------------------------------------

@dataclass
class WrSlot:
    valid: bool = False
    axi_id: int = 0
    rank: int = 0
    bank: int = 0
    row: int = 0
    col: int = 0
    length: int = 0
    w_buf_ptr: int = 0
    strb_ptr: int = 0
    beats_issued: int = 0
    issued: bool = False
    b_pending: bool = False


class WrCmdCamScoreboard:
    """Cycle-accurate Python mirror of wr_cmd_cam state."""

    def __init__(self, depth: int) -> None:
        self.depth = depth
        self.slots: List[WrSlot] = [WrSlot() for _ in range(depth)]

    # --- mutators (apply at edge) ---------------------------------------------

    def free_slot(self) -> Optional[int]:
        for i, s in enumerate(self.slots):
            if not s.valid:
                return i
        return None

    def push(self, axi_id, rank, bank, row, col, length, wptr, sptr) -> int:
        slot = self.free_slot()
        assert slot is not None, "scoreboard.push with no free slot"
        s = self.slots[slot]
        s.valid = True
        s.axi_id = axi_id
        s.rank = rank
        s.bank = bank
        s.row = row
        s.col = col
        s.length = length
        s.w_buf_ptr = wptr
        s.strb_ptr = sptr
        s.beats_issued = 0
        s.issued = False
        s.b_pending = False
        return slot

    def mark_issued(self, slot: int) -> None:
        self.slots[slot].issued = True

    def beat_pull(self, slot: int) -> Tuple[int, int, bool]:
        """Return the COMBINATIONAL outputs the DUT will drive this cycle —
        ptr / strb_ptr / last — BEFORE the edge advances beats_issued.
        """
        s = self.slots[slot]
        bi = s.beats_issued
        ptr = (s.w_buf_ptr + bi) & ((1 << 7) - 1)        # WPW=7 in the test
        sptr = (s.strb_ptr + bi) & ((1 << 7) - 1)
        last = (bi + 1) == s.length
        return ptr, sptr, last

    def beat_pull_advance(self, slot: int) -> None:
        """Apply the at-edge effect of a beat_pull strobe."""
        s = self.slots[slot]
        last = (s.beats_issued + 1) == s.length
        s.beats_issued += 1
        if last:
            s.b_pending = True

    def b_complete(self, slot: int) -> Tuple[bool, int, int]:
        """Compute the entry_complete combinational outputs for this strobe."""
        s = self.slots[slot]
        return True, slot, s.axi_id

    def b_complete_apply(self, slot: int) -> None:
        s = self.slots[slot]
        s.valid = False
        s.issued = False
        s.b_pending = False

    # --- combinational queries ------------------------------------------------

    def match_pending(self, q_rank: int, q_bank: int) -> int:
        v = 0
        for i, s in enumerate(self.slots):
            if s.valid and (not s.issued) and (s.rank == q_rank) and (s.bank == q_bank):
                v |= (1 << i)
        return v

    def match_rowhit(self, q_rank: int, q_bank: int, q_row: int) -> int:
        v = 0
        for i, s in enumerate(self.slots):
            if (s.valid and (not s.issued)
                    and (s.rank == q_rank) and (s.bank == q_bank)
                    and (s.row == q_row)):
                v |= (1 << i)
        return v

    def occupancy(self) -> int:
        return sum(1 for s in self.slots if s.valid)


# ---------------------------------------------------------------------------
# TB
# ---------------------------------------------------------------------------

class WrCmdCamTB(TBBase):
    CLK_PERIOD_NS = 10

    def __init__(self, dut) -> None:
        super().__init__(dut)
        self.SEED = self.convert_to_int(os.environ.get('SEED', '12345'))
        random.seed(self.SEED)
        self.TEST_LEVEL = os.environ.get('TEST_LEVEL', 'gate').lower()

        # Cached parameters (the test runner passes these via env so the
        # TB doesn't have to introspect the verilator-generated DUT object).
        self.WR_CAM_DEPTH    = self.convert_to_int(os.environ.get('WR_CAM_DEPTH',  '16'))
        self.AXI_ID_WIDTH    = self.convert_to_int(os.environ.get('AXI_ID_WIDTH',   '4'))
        self.NUM_RANKS       = self.convert_to_int(os.environ.get('NUM_RANKS',      '1'))
        self.NUM_BANKS       = self.convert_to_int(os.environ.get('NUM_BANKS',      '8'))
        self.ROW_WIDTH       = self.convert_to_int(os.environ.get('ROW_WIDTH',     '14'))
        self.COL_WIDTH       = self.convert_to_int(os.environ.get('COL_WIDTH',     '10'))
        self.BURST_LEN_WIDTH = self.convert_to_int(os.environ.get('BURST_LEN_WIDTH','8'))
        self.W_BUF_PTR_WIDTH = self.convert_to_int(os.environ.get('W_BUF_PTR_WIDTH','7'))

        self.RKW = 1 if self.NUM_RANKS <= 1 else (self.NUM_RANKS - 1).bit_length()
        self.BKW = (self.NUM_BANKS - 1).bit_length() if self.NUM_BANKS > 1 else 1
        self.SLW = (self.WR_CAM_DEPTH - 1).bit_length() if self.WR_CAM_DEPTH > 1 else 1

        self.MASK_ID  = (1 << self.AXI_ID_WIDTH)   - 1
        self.MASK_RNK = (1 << self.RKW)            - 1
        self.MASK_BNK = (1 << self.BKW)            - 1
        self.MASK_ROW = (1 << self.ROW_WIDTH)      - 1
        self.MASK_COL = (1 << self.COL_WIDTH)      - 1
        self.MASK_LEN = (1 << self.BURST_LEN_WIDTH)- 1
        self.MASK_WPW = (1 << self.W_BUF_PTR_WIDTH)- 1

        self.scb = WrCmdCamScoreboard(self.WR_CAM_DEPTH)

    # ---------- bring-up -----------------------------------------------------

    async def setup_clocks_and_reset(self):
        # Drive ALL inputs to idle BEFORE clock starts so verilator doesn't
        # latch X's on the first edge.
        self._drive_idle()
        await self.start_clock('mc_clk', freq=self.CLK_PERIOD_NS, units='ns')
        self.dut.mc_rst_n.value = 0
        await self.wait_clocks('mc_clk', 5)
        self.dut.mc_rst_n.value = 1
        await self.wait_clocks('mc_clk', 5)

    def _drive_idle(self):
        self.dut.push_valid_i.value      = 0
        self.dut.push_id_i.value         = 0
        self.dut.push_rank_i.value       = 0
        self.dut.push_bank_i.value       = 0
        self.dut.push_row_i.value        = 0
        self.dut.push_col_i.value        = 0
        self.dut.push_len_i.value        = 0
        self.dut.push_w_buf_ptr_i.value  = 0
        self.dut.push_strb_ptr_i.value   = 0

        self.dut.q_rank_i.value = 0
        self.dut.q_bank_i.value = 0
        self.dut.q_row_i.value  = 0

        self.dut.issued_we_i.value    = 0
        self.dut.issued_slot_i.value  = 0

        self.dut.beat_pull_strb_i.value = 0
        self.dut.beat_pull_slot_i.value = 0

        self.dut.b_complete_strb_i.value = 0
        self.dut.b_complete_slot_i.value = 0

    # ---------- one-cycle drivers --------------------------------------------

    async def push(self, axi_id, rank, bank, row, col, length, wptr, sptr,
                   expect_ready: bool = True) -> Optional[int]:
        """Drive a push for one cycle; return the slot consumed (or None when
        push_ready_o was low)."""
        self.dut.push_valid_i.value     = 1
        self.dut.push_id_i.value        = axi_id  & self.MASK_ID
        self.dut.push_rank_i.value      = rank    & self.MASK_RNK
        self.dut.push_bank_i.value      = bank    & self.MASK_BNK
        self.dut.push_row_i.value       = row     & self.MASK_ROW
        self.dut.push_col_i.value       = col     & self.MASK_COL
        self.dut.push_len_i.value       = length  & self.MASK_LEN
        self.dut.push_w_buf_ptr_i.value = wptr    & self.MASK_WPW
        self.dut.push_strb_ptr_i.value  = sptr    & self.MASK_WPW

        # push_ready_o / push_slot_o are combinational on r_valid (sequential)
        # and stable in this cycle; sample them after a delta-settle.
        await Timer(_NBA_SETTLE_PS, units='ps')
        ready = int(self.dut.push_ready_o.value)
        slot  = int(self.dut.push_slot_o.value)
        if expect_ready:
            assert ready == 1, "push_ready_o low when scoreboard had a free slot"
        await RisingEdge(self.dut.mc_clk)
        # Wait for NBA to commit r_valid[slot] := 1 before returning so the
        # next op (verify_snapshot, query, …) sees the new state.
        await Timer(_NBA_SETTLE_PS, units='ps')
        self.dut.push_valid_i.value = 0
        # Mirror in scoreboard if the push was accepted
        if ready:
            mirrored = self.scb.push(axi_id, rank, bank, row, col, length, wptr, sptr)
            assert mirrored == slot, (
                f"push_slot_o={slot} but scoreboard picked {mirrored}"
            )
            return slot
        return None

    async def query(self, q_rank, q_bank, q_row) -> Tuple[int, int]:
        """Drive a query for one cycle and return the (pending, rowhit)
        vectors as integers. Compares to scoreboard before returning."""
        self.dut.q_rank_i.value = q_rank & self.MASK_RNK
        self.dut.q_bank_i.value = q_bank & self.MASK_BNK
        self.dut.q_row_i.value  = q_row  & self.MASK_ROW
        await Timer(_NBA_SETTLE_PS, units='ps')
        pend = int(self.dut.match_pending_o.value)
        rhit = int(self.dut.match_rowhit_o.value)
        exp_p = self.scb.match_pending(q_rank, q_bank)
        exp_r = self.scb.match_rowhit(q_rank, q_bank, q_row)
        assert pend == exp_p, (
            f"match_pending: got 0x{pend:0{self.WR_CAM_DEPTH}b} "
            f"want 0x{exp_p:0{self.WR_CAM_DEPTH}b}"
        )
        assert rhit == exp_r, (
            f"match_rowhit: got 0x{rhit:0{self.WR_CAM_DEPTH}b} "
            f"want 0x{exp_r:0{self.WR_CAM_DEPTH}b}"
        )
        await RisingEdge(self.dut.mc_clk)
        await Timer(_NBA_SETTLE_PS, units='ps')
        return pend, rhit

    async def mark_issued(self, slot: int) -> None:
        self.dut.issued_we_i.value   = 1
        self.dut.issued_slot_i.value = slot & ((1 << self.SLW) - 1)
        await RisingEdge(self.dut.mc_clk)
        await Timer(_NBA_SETTLE_PS, units='ps')
        self.dut.issued_we_i.value   = 0
        self.scb.mark_issued(slot)

    async def beat_pull(self, slot: int) -> Tuple[int, int, bool]:
        """Pulse beat_pull_strb_i for slot. Compare the DUT's beat_pull_ptr_o
        / beat_pull_strb_ptr_o / beat_pull_last_o against the scoreboard."""
        self.dut.beat_pull_strb_i.value = 1
        self.dut.beat_pull_slot_i.value = slot & ((1 << self.SLW) - 1)
        await Timer(_NBA_SETTLE_PS, units='ps')
        ptr  = int(self.dut.beat_pull_ptr_o.value)
        sptr = int(self.dut.beat_pull_strb_ptr_o.value)
        last = bool(int(self.dut.beat_pull_last_o.value))
        e_ptr, e_sptr, e_last = self.scb.beat_pull(slot)
        assert ptr == e_ptr, f"beat_pull ptr slot={slot}: got {ptr} want {e_ptr}"
        assert sptr == e_sptr, f"beat_pull strb_ptr slot={slot}: got {sptr} want {e_sptr}"
        assert last == e_last, f"beat_pull last slot={slot}: got {last} want {e_last}"
        await RisingEdge(self.dut.mc_clk)
        await Timer(_NBA_SETTLE_PS, units='ps')
        self.dut.beat_pull_strb_i.value = 0
        self.scb.beat_pull_advance(slot)
        return ptr, sptr, last

    async def b_complete(self, slot: int) -> Tuple[int, int]:
        """Pulse b_complete_strb_i for slot. Verify entry_complete_o pulses
        with the expected slot/id."""
        self.dut.b_complete_strb_i.value = 1
        self.dut.b_complete_slot_i.value = slot & ((1 << self.SLW) - 1)
        await Timer(_NBA_SETTLE_PS, units='ps')
        ec     = int(self.dut.entry_complete_o.value)
        ec_slt = int(self.dut.entry_complete_slot_o.value)
        ec_id  = int(self.dut.entry_complete_id_o.value)
        assert ec == 1, "entry_complete_o should pulse on b_complete_strb_i"
        assert ec_slt == slot, f"entry_complete_slot: got {ec_slt} want {slot}"
        assert ec_id == self.scb.slots[slot].axi_id, (
            f"entry_complete_id: got {ec_id} want {self.scb.slots[slot].axi_id}"
        )
        await RisingEdge(self.dut.mc_clk)
        await Timer(_NBA_SETTLE_PS, units='ps')
        self.dut.b_complete_strb_i.value = 0
        self.scb.b_complete_apply(slot)
        return ec_slt, ec_id

    # ---------- snapshots / telemetry ---------------------------------------

    async def verify_snapshot(self) -> None:
        """Compare every snap_* slot against the scoreboard. Called at the
        start of a writeable phase (just after a RisingEdge), so the
        combinational snap_* outputs already reflect the latest state and
        we don't need to enter ReadOnly (which would deny the next caller's
        writes)."""
        snap_valid = int(self.dut.snap_valid_o.value)
        snap_iss   = int(self.dut.snap_issued_o.value)
        snap_bp    = int(self.dut.snap_b_pending_o.value)
        for i, s in enumerate(self.scb.slots):
            v = (snap_valid >> i) & 1
            assert v == int(s.valid), (
                f"snap_valid[{i}]: got {v} want {int(s.valid)}"
            )
            iss = (snap_iss >> i) & 1
            assert iss == int(s.issued), (
                f"snap_issued[{i}]: got {iss} want {int(s.issued)}"
            )
            bp = (snap_bp >> i) & 1
            assert bp == int(s.b_pending), (
                f"snap_b_pending[{i}]: got {bp} want {int(s.b_pending)}"
            )
            if s.valid:
                # The packed snap_* arrays in cocotb come back as a single
                # int; index each slot via SystemVerilog-style packed slicing.
                self._check_snap_field('snap_id_o',        i, self.AXI_ID_WIDTH,    s.axi_id)
                self._check_snap_field('snap_rank_o',      i, self.RKW,             s.rank)
                self._check_snap_field('snap_bank_o',      i, self.BKW,             s.bank)
                self._check_snap_field('snap_row_o',       i, self.ROW_WIDTH,       s.row)
                self._check_snap_field('snap_col_o',       i, self.COL_WIDTH,       s.col)
                self._check_snap_field('snap_len_o',       i, self.BURST_LEN_WIDTH, s.length)
                self._check_snap_field('snap_w_buf_ptr_o', i, self.W_BUF_PTR_WIDTH, s.w_buf_ptr)
                self._check_snap_field('snap_strb_ptr_o',  i, self.W_BUF_PTR_WIDTH, s.strb_ptr)

    def _check_snap_field(self, sig_name: str, idx: int, width: int, expected: int) -> None:
        raw = int(getattr(self.dut, sig_name).value)
        masked = (raw >> (idx * width)) & ((1 << width) - 1)
        assert masked == (expected & ((1 << width) - 1)), (
            f"{sig_name}[{idx}]: got {masked:#x} want {expected:#x}"
        )

    async def check_occupancy(self) -> int:
        # Sampled at the current writeable phase — caller is responsible for
        # calling at an edge boundary (just after a wait_clocks / RisingEdge).
        occ = int(self.dut.dbg_occupancy_o.value)
        assert occ == self.scb.occupancy(), (
            f"dbg_occupancy_o: got {occ} want {self.scb.occupancy()}"
        )
        return occ
