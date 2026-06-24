# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway
#
# Module: RdCmdCamTB
# Purpose: Unit-level testbench for rd_cmd_cam.

"""
Testbench for `rd_cmd_cam`.

Same shape as `WrCmdCamTB` but simpler — the read-side CAM has no
w_buf_ptr/strb_ptr fields and tracks `beats_returned` rather than
`beats_issued`. `entry_complete_o` fires on the LAST beat strobe
(combinational), and the slot self-clears the same cycle.
"""

import os
import sys
import random
import subprocess
from dataclasses import dataclass
from typing import List, Optional, Tuple

import cocotb
from cocotb.triggers import RisingEdge, ReadOnly, Timer

# See wr_cmd_cam_tb._NBA_SETTLE_PS for rationale.
_NBA_SETTLE_PS = 1

_repo_root = subprocess.check_output(['git', 'rev-parse', '--show-toplevel']).decode().strip()
if _repo_root not in sys.path:
    sys.path.insert(0, _repo_root)

from TBClasses.shared.tbbase import TBBase  # noqa: E402


# ---------------------------------------------------------------------------
# Scoreboard
# ---------------------------------------------------------------------------

@dataclass
class RdSlot:
    valid: bool = False
    axi_id: int = 0
    rank: int = 0
    bank: int = 0
    row: int = 0
    col: int = 0
    length: int = 0
    beats_returned: int = 0
    issued: bool = False


class RdCmdCamScoreboard:
    def __init__(self, depth: int) -> None:
        self.depth = depth
        self.slots: List[RdSlot] = [RdSlot() for _ in range(depth)]

    def free_slot(self) -> Optional[int]:
        for i, s in enumerate(self.slots):
            if not s.valid:
                return i
        return None

    def push(self, axi_id, rank, bank, row, col, length) -> int:
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
        s.beats_returned = 0
        s.issued = False
        return slot

    def mark_issued(self, slot: int) -> None:
        self.slots[slot].issued = True

    def beat_is_last(self, slot: int) -> bool:
        s = self.slots[slot]
        return (s.beats_returned + 1) == s.length

    def beat_apply(self, slot: int) -> bool:
        """Apply at-edge effect of a beat strobe. Returns True if last."""
        s = self.slots[slot]
        last = (s.beats_returned + 1) == s.length
        s.beats_returned += 1
        if last:
            s.valid = False
            s.issued = False
            s.beats_returned = 0
        return last

    def match_pending(self, q_rank: int, q_bank: int) -> int:
        # match_pending is the broad "needs servicing" signal — it is
        # the bitmask of valid + unissued slots regardless of (rank,
        # bank). The scheduler's slot-picker scans ALL slots and picks
        # the best one; the (rank, bank, row) reachability check lives
        # in `match_rowhit` instead.
        del q_rank, q_bank
        v = 0
        for i, s in enumerate(self.slots):
            if s.valid and (not s.issued):
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

class RdCmdCamTB(TBBase):
    CLK_PERIOD_NS = 10

    def __init__(self, dut) -> None:
        super().__init__(dut)
        self.SEED = self.convert_to_int(os.environ.get('SEED', '12345'))
        random.seed(self.SEED)
        self.TEST_LEVEL = os.environ.get('TEST_LEVEL', 'gate').lower()

        self.RD_CAM_DEPTH    = self.convert_to_int(os.environ.get('RD_CAM_DEPTH',  '16'))
        self.AXI_ID_WIDTH    = self.convert_to_int(os.environ.get('AXI_ID_WIDTH',   '4'))
        self.NUM_RANKS       = self.convert_to_int(os.environ.get('NUM_RANKS',      '1'))
        self.NUM_BANKS       = self.convert_to_int(os.environ.get('NUM_BANKS',      '8'))
        self.ROW_WIDTH       = self.convert_to_int(os.environ.get('ROW_WIDTH',     '14'))
        self.COL_WIDTH       = self.convert_to_int(os.environ.get('COL_WIDTH',     '10'))
        self.BURST_LEN_WIDTH = self.convert_to_int(os.environ.get('BURST_LEN_WIDTH','8'))

        self.RKW = 1 if self.NUM_RANKS <= 1 else (self.NUM_RANKS - 1).bit_length()
        self.BKW = (self.NUM_BANKS - 1).bit_length() if self.NUM_BANKS > 1 else 1
        self.SLW = (self.RD_CAM_DEPTH - 1).bit_length() if self.RD_CAM_DEPTH > 1 else 1

        self.MASK_ID  = (1 << self.AXI_ID_WIDTH)   - 1
        self.MASK_RNK = (1 << self.RKW)            - 1
        self.MASK_BNK = (1 << self.BKW)            - 1
        self.MASK_ROW = (1 << self.ROW_WIDTH)      - 1
        self.MASK_COL = (1 << self.COL_WIDTH)      - 1
        self.MASK_LEN = (1 << self.BURST_LEN_WIDTH)- 1

        self.scb = RdCmdCamScoreboard(self.RD_CAM_DEPTH)

    async def setup_clocks_and_reset(self):
        self._drive_idle()
        await self.start_clock('mc_clk', freq=self.CLK_PERIOD_NS, units='ns')
        self.dut.mc_rst_n.value = 0
        await self.wait_clocks('mc_clk', 5)
        self.dut.mc_rst_n.value = 1
        await self.wait_clocks('mc_clk', 5)

    def _drive_idle(self):
        self.dut.push_valid_i.value = 0
        self.dut.push_id_i.value    = 0
        self.dut.push_rank_i.value  = 0
        self.dut.push_bank_i.value  = 0
        self.dut.push_row_i.value   = 0
        self.dut.push_col_i.value   = 0
        self.dut.push_len_i.value   = 0
        self.dut.q_rank_i.value     = 0
        self.dut.q_bank_i.value     = 0
        self.dut.q_row_i.value      = 0
        self.dut.issued_we_i.value   = 0
        self.dut.issued_slot_i.value = 0
        self.dut.beat_we_i.value     = 0
        self.dut.beat_slot_i.value   = 0

    async def push(self, axi_id, rank, bank, row, col, length,
                   expect_ready: bool = True) -> Optional[int]:
        self.dut.push_valid_i.value = 1
        self.dut.push_id_i.value    = axi_id & self.MASK_ID
        self.dut.push_rank_i.value  = rank   & self.MASK_RNK
        self.dut.push_bank_i.value  = bank   & self.MASK_BNK
        self.dut.push_row_i.value   = row    & self.MASK_ROW
        self.dut.push_col_i.value   = col    & self.MASK_COL
        self.dut.push_len_i.value   = length & self.MASK_LEN
        await Timer(_NBA_SETTLE_PS, units='ps')
        ready = int(self.dut.push_ready_o.value)
        slot  = int(self.dut.push_slot_o.value)
        if expect_ready:
            assert ready == 1, "push_ready_o low when scoreboard had a free slot"
        await RisingEdge(self.dut.mc_clk)
        await Timer(_NBA_SETTLE_PS, units='ps')
        self.dut.push_valid_i.value = 0
        if ready:
            mirrored = self.scb.push(axi_id, rank, bank, row, col, length)
            assert mirrored == slot, (
                f"push_slot_o={slot} but scoreboard picked {mirrored}"
            )
            return slot
        return None

    async def query(self, q_rank, q_bank, q_row) -> Tuple[int, int]:
        self.dut.q_rank_i.value = q_rank & self.MASK_RNK
        self.dut.q_bank_i.value = q_bank & self.MASK_BNK
        self.dut.q_row_i.value  = q_row  & self.MASK_ROW
        await Timer(_NBA_SETTLE_PS, units='ps')
        pend = int(self.dut.match_pending_o.value)
        rhit = int(self.dut.match_rowhit_o.value)
        exp_p = self.scb.match_pending(q_rank, q_bank)
        exp_r = self.scb.match_rowhit(q_rank, q_bank, q_row)
        assert pend == exp_p, (
            f"match_pending: got 0x{pend:0{self.RD_CAM_DEPTH}b} "
            f"want 0x{exp_p:0{self.RD_CAM_DEPTH}b}"
        )
        assert rhit == exp_r, (
            f"match_rowhit: got 0x{rhit:0{self.RD_CAM_DEPTH}b} "
            f"want 0x{exp_r:0{self.RD_CAM_DEPTH}b}"
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

    async def beat(self, slot: int) -> bool:
        """Pulse beat_we_i for slot. Verify entry_complete behaviour."""
        self.dut.beat_we_i.value   = 1
        self.dut.beat_slot_i.value = slot & ((1 << self.SLW) - 1)
        expected_last = self.scb.beat_is_last(slot)
        expected_id   = self.scb.slots[slot].axi_id
        await Timer(_NBA_SETTLE_PS, units='ps')
        ec     = int(self.dut.entry_complete_o.value)
        ec_slt = int(self.dut.entry_complete_slot_o.value)
        ec_id  = int(self.dut.entry_complete_id_o.value)
        if expected_last:
            assert ec == 1, "entry_complete_o should pulse on last beat"
            assert ec_slt == slot, f"entry_complete_slot: got {ec_slt} want {slot}"
            assert ec_id == expected_id, (
                f"entry_complete_id: got {ec_id} want {expected_id}"
            )
        else:
            assert ec == 0, "entry_complete_o should not pulse on a non-last beat"
        await RisingEdge(self.dut.mc_clk)
        await Timer(_NBA_SETTLE_PS, units='ps')
        self.dut.beat_we_i.value = 0
        last = self.scb.beat_apply(slot)
        assert last == expected_last
        return last

    async def verify_snapshot(self) -> None:
        # See WrCmdCamTB.verify_snapshot: called from writeable phase, no
        # ReadOnly() so the next caller can still write inputs this cycle.
        snap_valid = int(self.dut.snap_valid_o.value)
        snap_iss   = int(self.dut.snap_issued_o.value)
        for i, s in enumerate(self.scb.slots):
            v = (snap_valid >> i) & 1
            assert v == int(s.valid), (
                f"snap_valid[{i}]: got {v} want {int(s.valid)}"
            )
            iss = (snap_iss >> i) & 1
            assert iss == int(s.issued), (
                f"snap_issued[{i}]: got {iss} want {int(s.issued)}"
            )
            if s.valid:
                self._check_snap_field('snap_id_o',  i, self.AXI_ID_WIDTH,    s.axi_id)
                self._check_snap_field('snap_col_o', i, self.COL_WIDTH,       s.col)
                self._check_snap_field('snap_len_o', i, self.BURST_LEN_WIDTH, s.length)

    def _check_snap_field(self, sig_name: str, idx: int, width: int, expected: int) -> None:
        raw = int(getattr(self.dut, sig_name).value)
        masked = (raw >> (idx * width)) & ((1 << width) - 1)
        assert masked == (expected & ((1 << width) - 1)), (
            f"{sig_name}[{idx}]: got {masked:#x} want {expected:#x}"
        )

    async def check_occupancy(self) -> int:
        occ = int(self.dut.dbg_occupancy_o.value)
        assert occ == self.scb.occupancy(), (
            f"dbg_occupancy_o: got {occ} want {self.scb.occupancy()}"
        )
        return occ
