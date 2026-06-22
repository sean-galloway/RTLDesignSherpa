# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway

"""
Unit-test runner for `scheduler`. Verifies the closed-page v1
arbiter: priority ordering (init > MR > refresh > pdn > WR/RD CAM)
and the per-op FSM IDLE → NEED_ACT → NEED_RDWR → DONE.
"""

import os
import sys
import random
import pytest

import cocotb
from cocotb.triggers import RisingEdge, Timer
from cocotb_test.simulator import run

from TBClasses.shared.utilities import get_paths
from TBClasses.shared.filelist_utils import get_sources_from_filelist
from TBClasses.shared.tbbase import TBBase

# FlexRandomizer for directed-random scenarios.
from CocoTBFramework.components.shared.flex_randomizer import FlexRandomizer

_DV_DIR = os.path.abspath(os.path.join(os.path.dirname(__file__), "../.."))
if _DV_DIR not in sys.path:
    sys.path.insert(0, _DV_DIR)

from tbclasses.trackers import SchedulerTracker  # noqa: E402


# dram_op_e values
OP_NOP  = 0x0
OP_ACT  = 0x1
OP_RD   = 0x2
OP_RDA  = 0x3
OP_WR   = 0x4
OP_WRA  = 0x5
OP_PRE  = 0x6
OP_PREA = 0x7
OP_REF  = 0x8
OP_MRS  = 0xA


class SchedTB(TBBase):
    CLK = 10

    def __init__(self, dut):
        super().__init__(dut)
        self.WR_CAM_DEPTH = int(os.environ.get('WR_CAM_DEPTH', '16'))
        self.RD_CAM_DEPTH = int(os.environ.get('RD_CAM_DEPTH', '16'))
        self.NUM_RANKS    = int(os.environ.get('NUM_RANKS',    '1'))
        self.NUM_BANKS    = int(os.environ.get('NUM_BANKS',    '8'))
        self.COL_WIDTH    = int(os.environ.get('COL_WIDTH',   '10'))
        self.BLW          = int(os.environ.get('BURST_LEN_WIDTH', '8'))
        self.SEED         = int(os.environ.get('SEED', '12345'))
        # Width constants used by set_*_pending_full helpers
        self.RKW          = max(1, (self.NUM_RANKS - 1).bit_length())
        self.BKW          = max(1, (self.NUM_BANKS - 1).bit_length())
        self.ROW_WIDTH    = int(os.environ.get('ROW_WIDTH', '14'))

    async def setup(self, all_banks_ready: bool = True):
        # Match vectors: empty by default
        self.dut.wr_match_pending_i.value = 0
        self.dut.wr_match_rowhit_i.value  = 0
        self.dut.rd_match_pending_i.value = 0
        self.dut.rd_match_rowhit_i.value  = 0
        # Snap arrays: all zero (rank/bank/row default to 0; tests can
        # override per slot via set_wr_pending / set_rd_pending)
        self.dut.wr_snap_rank_i.value = 0
        self.dut.wr_snap_bank_i.value = 0
        self.dut.wr_snap_row_i.value  = 0
        self.dut.wr_snap_col_i.value  = 0
        self.dut.wr_snap_len_i.value  = 0
        self.dut.rd_snap_rank_i.value = 0
        self.dut.rd_snap_bank_i.value = 0
        self.dut.rd_snap_row_i.value  = 0
        self.dut.rd_snap_col_i.value  = 0
        self.dut.rd_snap_len_i.value  = 0
        # Timer ready vectors: all banks ready by default
        ready_all = (1 << (self.NUM_RANKS * self.NUM_BANKS)) - 1
        self.dut.bank_act_ready_i.value  = ready_all if all_banks_ready else 0
        self.dut.bank_rdwr_ready_i.value = ready_all if all_banks_ready else 0
        self.dut.bank_pre_ready_i.value  = ready_all if all_banks_ready else 0
        self.dut.bank_row_active_i.value = 0
        self.dut.bank_open_row_i.value   = 0
        self.dut.tfaw_window_ok_i.value  = 1
        self.dut.predict_open_i.value    = 0
        # Injection req inputs
        self.dut.refresh_req_i.value = 0
        self.dut.pdn_req_i.value     = 0
        self.dut.init_busy_i.value   = 0
        self.dut.mr_req_i.value      = 0
        self.dut.cmd_ready_i.value   = 1

        await self.start_clock('mc_clk', freq=self.CLK, units='ns')
        self.dut.mc_rst_n.value = 0
        await self.wait_clocks('mc_clk', 5)
        self.dut.mc_rst_n.value = 1
        await self.wait_clocks('mc_clk', 5)

    def set_wr_pending(self, slot: int, col: int = 0x40, length: int = 4):
        """Drive wr_match_pending[slot]=1 with snap_col/len for that slot."""
        self.dut.wr_match_pending_i.value = (1 << slot)
        # Update snap_col[slot] (preserve other slots = 0)
        snap_col = col << (slot * self.COL_WIDTH)
        self.dut.wr_snap_col_i.value = snap_col
        snap_len = length << (slot * self.BLW)
        self.dut.wr_snap_len_i.value = snap_len

    def set_rd_pending(self, slot: int, col: int = 0x40, length: int = 4):
        self.dut.rd_match_pending_i.value = (1 << slot)
        self.dut.rd_snap_col_i.value = col << (slot * self.COL_WIDTH)
        self.dut.rd_snap_len_i.value = length << (slot * self.BLW)

    def set_wr_pending_full(self, slot: int, *, rank: int = 0, bank: int = 0,
                            row: int = 0, col: int = 0x40, length: int = 4):
        """set_wr_pending + full (rank, bank, row) snapshot for the slot."""
        self.dut.wr_match_pending_i.value = (1 << slot)
        self.dut.wr_snap_rank_i.value = rank   << (slot * self.RKW)
        self.dut.wr_snap_bank_i.value = bank   << (slot * self.BKW)
        self.dut.wr_snap_row_i.value  = row    << (slot * self.ROW_WIDTH)
        self.dut.wr_snap_col_i.value  = col    << (slot * self.COL_WIDTH)
        self.dut.wr_snap_len_i.value  = length << (slot * self.BLW)

    def set_rd_pending_full(self, slot: int, *, rank: int = 0, bank: int = 0,
                            row: int = 0, col: int = 0x40, length: int = 4):
        """set_rd_pending + full (rank, bank, row) snapshot for the slot."""
        self.dut.rd_match_pending_i.value = (1 << slot)
        self.dut.rd_snap_rank_i.value = rank   << (slot * self.RKW)
        self.dut.rd_snap_bank_i.value = bank   << (slot * self.BKW)
        self.dut.rd_snap_row_i.value  = row    << (slot * self.ROW_WIDTH)
        self.dut.rd_snap_col_i.value  = col    << (slot * self.COL_WIDTH)
        self.dut.rd_snap_len_i.value  = length << (slot * self.BLW)

    def clear_pending(self):
        self.dut.wr_match_pending_i.value = 0
        self.dut.rd_match_pending_i.value = 0

    def cmd_valid(self) -> int: return int(self.dut.cmd_valid_o.value)
    def cmd_op(self) -> int:    return int(self.dut.cmd_op_o.value)
    def evt_act(self) -> int:   return int(self.dut.evt_act_o.value)
    def evt_rd(self) -> int:    return int(self.dut.evt_rd_o.value)
    def evt_wr(self) -> int:    return int(self.dut.evt_wr_o.value)
    def wr_issued(self) -> int: return int(self.dut.wr_issued_we_o.value)
    def rd_issued(self) -> int: return int(self.dut.rd_issued_we_o.value)
    def refresh_grant(self) -> int: return int(self.dut.refresh_grant_o.value)
    def pdn_grant(self) -> int:     return int(self.dut.pdn_grant_o.value)
    def mr_grant(self) -> int:      return int(self.dut.mr_grant_o.value)


@cocotb.test(timeout_time=10, timeout_unit="ms")
async def cocotb_test_scheduler(dut):
    test_type = os.environ.get("TEST_TYPE", "smoke_wr")
    tb = SchedTB(dut)

    # Attach the scheduler tracker. It auto-writes <sim_build_dir>/sched.out
    # at end of simulation (via atexit) so we can grep the command stream
    # after the test. Other trackers' signals don't exist on this DUT, so
    # only SchedulerTracker is wired here.
    sched_tracker = SchedulerTracker(dut)
    cocotb.start_soon(sched_tracker.run())

    if test_type == "smoke_wr":
        # Outputs are registered (+1 cycle vs the internal FSM state).
        # Sequence:
        #   cycle 0: IDLE → state advances to NEED_ACT
        #   cycle 1: NEED_ACT → handshake at edge; output reg loads ACT
        #   cycle 2: cmd_op_o = ACT visible; state = NEED_RDWR
        #   cycle 3: cmd_op_o = WRA visible; state = DONE
        #   cycle 4: wr_issued_we_o = 1 visible; state = IDLE
        await tb.setup()
        tb.set_wr_pending(slot=3, col=0x80, length=8)
        await tb.wait_clocks('mc_clk', 2)
        assert tb.cmd_valid() == 1, "should be issuing"
        assert tb.cmd_op() == OP_ACT, f"got op {tb.cmd_op()}"
        assert tb.evt_act() == 1
        await tb.wait_clocks('mc_clk', 1)
        assert tb.cmd_op() == OP_WRA, f"expected WRA, got {tb.cmd_op()}"
        assert tb.evt_wr() == 1
        await tb.wait_clocks('mc_clk', 1)
        assert tb.wr_issued() == 1
        tb.clear_pending()

    elif test_type == "smoke_rd":
        await tb.setup()
        tb.set_rd_pending(slot=5, col=0x20, length=4)
        await tb.wait_clocks('mc_clk', 2)
        assert tb.cmd_op() == OP_ACT
        await tb.wait_clocks('mc_clk', 1)
        assert tb.cmd_op() == OP_RDA
        assert tb.evt_rd() == 1
        await tb.wait_clocks('mc_clk', 1)
        assert tb.rd_issued() == 1
        tb.clear_pending()

    elif test_type == "init_busy_nop":
        await tb.setup()
        tb.set_wr_pending(slot=0)
        tb.dut.init_busy_i.value = 1
        # Wait — scheduler should never issue while init_busy
        for _ in range(20):
            await tb.wait_clocks('mc_clk', 1)
            if tb.cmd_valid() == 1:
                assert tb.cmd_op() == OP_NOP, "init_busy must drive NOP"

    elif test_type == "refresh_priority":
        await tb.setup()
        tb.set_wr_pending(slot=0)
        tb.dut.refresh_req_i.value = 1
        await tb.wait_clocks('mc_clk', 2)
        # Refresh should be issued; WR waits.
        assert tb.cmd_op() == OP_REF, f"expected REF, got {tb.cmd_op()}"
        assert tb.refresh_grant() == 1

    elif test_type == "mr_priority":
        await tb.setup()
        tb.set_wr_pending(slot=0)
        tb.dut.mr_req_i.value = 1
        await tb.wait_clocks('mc_clk', 2)
        # MRS should be issued; WR waits.
        assert tb.cmd_op() == OP_MRS, f"expected MRS, got {tb.cmd_op()}"
        assert tb.mr_grant() == 1

    elif test_type == "pdn_grant":
        await tb.setup()
        tb.dut.pdn_req_i.value = 1
        await tb.wait_clocks('mc_clk', 2)
        # pdn_grant pulses; no DRAM cmd needed.
        assert tb.pdn_grant() == 1

    elif test_type == "wait_for_act_ready":
        # Banks NOT ready initially; scheduler holds NEED_ACT until
        # bank_act_ready_i goes high. Output is registered → ACT
        # appears one cycle AFTER bank_act_ready_i transitions.
        await tb.setup(all_banks_ready=False)
        tb.set_wr_pending(slot=0, col=0x40, length=4)
        await tb.wait_clocks('mc_clk', 5)
        assert tb.cmd_valid() == 0, "should not issue while bank not ready"
        # Make banks ready
        ready_all = (1 << (tb.NUM_RANKS * tb.NUM_BANKS)) - 1
        tb.dut.bank_act_ready_i.value  = ready_all
        tb.dut.bank_rdwr_ready_i.value = ready_all
        # 1 cycle for registered output to catch up
        await tb.wait_clocks('mc_clk', 1)
        assert tb.cmd_op() == OP_ACT, f"got op {tb.cmd_op()}"
        assert tb.evt_act() == 1
        await tb.wait_clocks('mc_clk', 1)
        # CLOSE policy → WRA (closed-page default in this test)
        assert tb.cmd_op() == OP_WRA
        tb.clear_pending()

    elif test_type == "open_page_row_hit":
        # OPEN policy + bank already active on the requested row → skip
        # ACT, issue plain WR.
        await tb.setup()
        # Bank 0 active on row 0; slot 0 also targets row 0.
        tb.dut.bank_row_active_i.value = 1
        tb.dut.bank_open_row_i.value   = 0
        tb.set_wr_pending(slot=0, col=0x40, length=4)
        await tb.wait_clocks('mc_clk', 2)
        # No ACT — go straight to RDWR with plain WR
        assert tb.cmd_op() == OP_WR, f"expected WR (no auto-pre), got {tb.cmd_op()}"
        tb.clear_pending()

    elif test_type == "open_page_row_miss":
        # OPEN policy + bank active on DIFFERENT row → PRE first,
        # then ACT, then WR.
        await tb.setup()
        tb.dut.bank_row_active_i.value = 1
        # bank 0 has row 7 open; slot 0 wants row 0 (default snap_row=0)
        tb.dut.bank_open_row_i.value   = (7 << 0)  # bank[0] open row = 7
        tb.set_wr_pending(slot=0, col=0x40, length=4)
        await tb.wait_clocks('mc_clk', 2)
        assert tb.cmd_op() == OP_PRE, f"expected PRE, got {tb.cmd_op()}"
        await tb.wait_clocks('mc_clk', 1)
        assert tb.cmd_op() == OP_ACT, f"expected ACT, got {tb.cmd_op()}"
        await tb.wait_clocks('mc_clk', 1)
        assert tb.cmd_op() == OP_WR, f"expected WR, got {tb.cmd_op()}"
        tb.clear_pending()

    elif test_type == "open_page_bank_idle":
        # OPEN policy + bank IDLE → ACT then plain WR (no auto-pre).
        await tb.setup()
        tb.dut.bank_row_active_i.value = 0
        tb.set_wr_pending(slot=0, col=0x40, length=4)
        await tb.wait_clocks('mc_clk', 2)
        assert tb.cmd_op() == OP_ACT
        await tb.wait_clocks('mc_clk', 1)
        assert tb.cmd_op() == OP_WR, f"OPEN should issue WR, got {tb.cmd_op()}"
        tb.clear_pending()

    elif test_type == "happy_predict_open":
        # HAPPY policy + predictor says "open" → issue WR (no auto-pre)
        await tb.setup()
        # All banks "predicted open"
        nb = tb.NUM_RANKS * tb.NUM_BANKS
        tb.dut.predict_open_i.value = (1 << nb) - 1
        tb.set_wr_pending(slot=0, col=0x40, length=4)
        await tb.wait_clocks('mc_clk', 2)
        assert tb.cmd_op() == OP_ACT
        await tb.wait_clocks('mc_clk', 1)
        assert tb.cmd_op() == OP_WR, f"HAPPY predict-open → WR, got {tb.cmd_op()}"
        tb.clear_pending()

    elif test_type == "happy_predict_close":
        # HAPPY policy + predictor says "close" (counter low) → WRA
        await tb.setup()
        tb.dut.predict_open_i.value = 0
        tb.set_wr_pending(slot=0, col=0x40, length=4)
        await tb.wait_clocks('mc_clk', 2)
        assert tb.cmd_op() == OP_ACT
        await tb.wait_clocks('mc_clk', 1)
        assert tb.cmd_op() == OP_WRA, f"HAPPY predict-close → WRA, got {tb.cmd_op()}"
        tb.clear_pending()

    elif test_type == "dr_close_burst":
        # Directed-random under CLOSE policy. Each iteration: a randomized
        # WR op with FlexRandomizer-weighted (length, col, bank, row),
        # checked against the precise expected CLOSE-policy sequence
        # (ACT → WRA → ISSUED_WR). N=100 iterations.
        await tb.setup()
        rzr = FlexRandomizer({
            # length: small bursts most common, medium next, long rare
            'length': ([(1, 4), (5, 16), (17, 64)], [0.5, 0.3, 0.2]),
            'col':    ([(0, 0xFF), (0x100, 0x3FF)], [0.7, 0.3]),
            'bank':   ([(0, tb.NUM_BANKS - 1)], [1.0]),
            'row':    ([(0, (1 << tb.ROW_WIDTH) - 1)], [1.0]),
        })
        for i in range(100):
            v = rzr.next()
            slot = i % tb.WR_CAM_DEPTH
            tb.set_wr_pending_full(slot=slot, bank=v['bank'], row=v['row'],
                                   col=v['col'], length=v['length'])
            await tb.wait_clocks('mc_clk', 2)
            assert tb.cmd_op() == OP_ACT, (
                f"iter {i}: expected ACT, got {tb.cmd_op()}"
            )
            await tb.wait_clocks('mc_clk', 1)
            assert tb.cmd_op() == OP_WRA, (
                f"iter {i}: CLOSE policy must auto-precharge, got {tb.cmd_op()}"
            )
            await tb.wait_clocks('mc_clk', 1)
            assert tb.wr_issued() == 1
            tb.clear_pending()
            await tb.wait_clocks('mc_clk', 2)

    elif test_type == "dr_open_row_hit":
        # Directed-random under OPEN policy. Each iteration: force a
        # row-hit on a random (bank, row) and expect the scheduler to
        # skip ACT entirely and issue plain WR (no auto-precharge).
        await tb.setup()
        # Function-based generator: prefer column boundaries
        # (col=0, col=max) 30% of the time, else uniform random.
        # Captures a private RNG via closure so FlexRandomizer's
        # generator-invocation convention (may pass dict of current
        # values) doesn't clobber our state.
        _col_rng = random.Random(tb.SEED ^ 0xC01)
        _col_max = (1 << tb.COL_WIDTH) - 1
        def _gen_col(*_args, **_kwargs):
            if _col_rng.random() < 0.3:
                return _col_rng.choice([0, _col_max])
            return _col_rng.randrange(1 << tb.COL_WIDTH)

        rzr = FlexRandomizer({
            'bank': ([(0, tb.NUM_BANKS - 1)], [1.0]),
            'row':  ([(0, (1 << tb.ROW_WIDTH) - 1)], [1.0]),
            'col':  _gen_col,
        })
        for i in range(50):
            v = rzr.next()
            bank = v['bank']
            row  = v['row']
            tb.dut.bank_row_active_i.value = (1 << bank)
            tb.dut.bank_open_row_i.value   = (row << (bank * tb.ROW_WIDTH))
            tb.set_wr_pending_full(slot=0, bank=bank, row=row,
                                   col=v['col'], length=4)
            await tb.wait_clocks('mc_clk', 2)
            assert tb.cmd_op() == OP_WR, (
                f"iter {i}: row-hit must skip ACT and issue WR "
                f"(bank={bank} row={row:#x}), got {tb.cmd_op()}"
            )
            tb.clear_pending()
            tb.dut.bank_row_active_i.value = 0
            await tb.wait_clocks('mc_clk', 2)

    elif test_type == "dr_open_row_miss":
        # Directed-random row-miss: bank is active on row A, request
        # targets row B (≠ A). Expect PRE → ACT → WR.
        await tb.setup()
        rzr = FlexRandomizer({
            'bank':    ([(0, tb.NUM_BANKS - 1)], [1.0]),
            'old_row': ([(0, (1 << tb.ROW_WIDTH) - 1)], [1.0]),
        })
        rng = random.Random(tb.SEED ^ 0xA155)
        for i in range(50):
            v = rzr.next()
            bank    = v['bank']
            old_row = v['old_row']
            # Pick a new row guaranteed different from old_row.
            new_row = (old_row + rng.randint(1, 0x100)) & ((1 << tb.ROW_WIDTH) - 1)
            if new_row == old_row:
                new_row = (old_row + 1) & ((1 << tb.ROW_WIDTH) - 1)

            tb.dut.bank_row_active_i.value = (1 << bank)
            tb.dut.bank_open_row_i.value   = (old_row << (bank * tb.ROW_WIDTH))
            tb.set_wr_pending_full(slot=0, bank=bank, row=new_row,
                                   col=0x40, length=4)
            await tb.wait_clocks('mc_clk', 2)
            assert tb.cmd_op() == OP_PRE, (
                f"iter {i}: row-miss must issue PRE first, got {tb.cmd_op()}"
            )
            await tb.wait_clocks('mc_clk', 1)
            assert tb.cmd_op() == OP_ACT, (
                f"iter {i}: after PRE, expected ACT, got {tb.cmd_op()}"
            )
            await tb.wait_clocks('mc_clk', 1)
            assert tb.cmd_op() == OP_WR, (
                f"iter {i}: OPEN policy must issue plain WR, got {tb.cmd_op()}"
            )
            tb.clear_pending()
            tb.dut.bank_row_active_i.value = 0
            await tb.wait_clocks('mc_clk', 2)

    elif test_type == "random_soak":
        rng = random.Random(tb.SEED)
        test_level = os.environ.get("TEST_LEVEL", "FUNC").upper()
        n = {"GATE": 50, "FUNC": 300, "FULL": 1500}.get(test_level, 300)
        await tb.setup()

        cmd_count = 0
        wr_count = 0
        rd_count = 0
        for _ in range(n):
            is_wr  = rng.random() < 0.5
            slot   = rng.randrange(0, tb.WR_CAM_DEPTH if is_wr else tb.RD_CAM_DEPTH)
            col    = rng.randrange(1, 1 << tb.COL_WIDTH)
            length = min(rng.randint(1, (1 << tb.BLW) - 1), 64)

            if is_wr:
                tb.set_wr_pending(slot=slot, col=col, length=length)
            else:
                tb.set_rd_pending(slot=slot, col=col, length=length)

            for _ in range(20):
                await tb.wait_clocks('mc_clk', 1)
                if tb.cmd_valid() == 1:
                    cmd_count += 1
                if is_wr and tb.wr_issued():
                    wr_count += 1
                    break
                if (not is_wr) and tb.rd_issued():
                    rd_count += 1
                    break
            tb.clear_pending()
            await tb.wait_clocks('mc_clk', 2)

        assert cmd_count >= n, f"only {cmd_count} commands in {n} iterations"
        assert wr_count + rd_count >= n // 2, (
            f"only {wr_count + rd_count} ops issued in {n} iterations"
        )

    else:
        raise ValueError(f"Unknown TEST_TYPE: {test_type}")

    await tb.wait_clocks('mc_clk', 3)


# page_policy_e values match the SV enum.
PAGE_POLICY_OPEN  = 0
PAGE_POLICY_CLOSE = 1
PAGE_POLICY_HAPPY = 2

# (test_type, PAGE_POLICY)
_BASE_CLOSE   = ["smoke_wr", "smoke_rd", "init_busy_nop", "refresh_priority",
                 "mr_priority", "pdn_grant", "wait_for_act_ready"]
_OPEN_ONLY    = ["open_page_row_hit", "open_page_row_miss",
                 "open_page_bank_idle"]
_HAPPY_ONLY   = ["happy_predict_open", "happy_predict_close"]

_GATE = [(t, PAGE_POLICY_CLOSE) for t in ["smoke_wr", "smoke_rd",
                                         "init_busy_nop"]]
_FUNC = ([(t, PAGE_POLICY_CLOSE) for t in _BASE_CLOSE]
       + [(t, PAGE_POLICY_OPEN)  for t in _OPEN_ONLY]
       + [(t, PAGE_POLICY_HAPPY) for t in _HAPPY_ONLY]
       + [("random_soak",     PAGE_POLICY_CLOSE),
          ("random_soak",     PAGE_POLICY_OPEN),
          ("random_soak",     PAGE_POLICY_HAPPY),
          # Directed-random — FlexRandomizer over (length, col, bank, row)
          ("dr_close_burst",  PAGE_POLICY_CLOSE),
          ("dr_open_row_hit", PAGE_POLICY_OPEN),
          ("dr_open_row_miss",PAGE_POLICY_OPEN)])
_FULL = _FUNC
_FULL = list(dict.fromkeys(_FULL))

_TEST_LEVEL = os.environ.get("TEST_LEVEL", "FUNC").upper()
_PARAMS = {"GATE": _GATE, "FUNC": _FUNC, "FULL": _FULL}.get(_TEST_LEVEL, _FUNC)

_POLICY_NAMES = {PAGE_POLICY_OPEN: "open",
                 PAGE_POLICY_CLOSE: "close",
                 PAGE_POLICY_HAPPY: "happy"}


@pytest.mark.parametrize("test_type,page_policy", _PARAMS,
                         ids=[f"{t[0]}-{_POLICY_NAMES[t[1]]}" for t in _PARAMS])
def test_scheduler(request, test_type, page_policy):
    module, repo_root, tests_dir, log_dir, _ = get_paths({})
    dut_name = "scheduler"
    test_name = f"test_scheduler_{test_type}_{_POLICY_NAMES[page_policy]}"

    filelist_path = ("projects/components/memory-controllers/ddr2-lpddr2/"
                     "rtl/filelists/fub/scheduler.f")
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root, filelist_path=filelist_path)

    sim_build = os.path.join(tests_dir, "local_sim_build", test_name)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)

    extra_env = {
        "DUT": dut_name,
        "TEST_TYPE": test_type,
        "WR_CAM_DEPTH": "16",
        "RD_CAM_DEPTH": "16",
        "NUM_RANKS":    "1",
        "NUM_BANKS":    "8",
        "ROW_WIDTH":    "14",
        "COL_WIDTH":    "10",
        "BURST_LEN_WIDTH": "8",
        "AXI_ID_WIDTH": "4",
        "SEED": str(random.randint(0, 100000)),
        "COCOTB_LOG_LEVEL": "INFO",
        "COCOTB_RESULTS_FILE":
            os.path.join(log_dir, f"results_{test_name}.xml"),
    }
    parameters = {
        "WR_CAM_DEPTH": "16",
        "RD_CAM_DEPTH": "16",
        "NUM_RANKS":    "1",
        "NUM_BANKS":    "8",
        "ROW_WIDTH":    "14",
        "COL_WIDTH":    "10",
        "BURST_LEN_WIDTH": "8",
        "AXI_ID_WIDTH": "4",
        "PAGE_POLICY":  str(page_policy),
    }

    enable_waves = bool(int(os.environ.get("WAVES", "0")))
    compile_args = ["+define+USE_ASYNC_RESET"]
    sim_args = []
    plus_args = []
    if enable_waves:
        compile_args += ["--trace-fst", "--trace-structs", "--trace-depth", "99"]
        sim_args     += ["--trace", "--trace-structs", "--trace-depth", "99"]
        plus_args    += ["--trace"]
        extra_env["VERILATOR_TRACE_FST"] = "1"

    run(python_search=[tests_dir],
        verilog_sources=verilog_sources, includes=includes,
        toplevel=dut_name, module=module,
        testcase="cocotb_test_scheduler",
        sim_build=sim_build, simulator="verilator",
        extra_env=extra_env, parameters=parameters,
        compile_args=compile_args, sim_args=sim_args, plus_args=plus_args,
        waves=enable_waves, keep_files=True, timescale="1ns/1ps")
