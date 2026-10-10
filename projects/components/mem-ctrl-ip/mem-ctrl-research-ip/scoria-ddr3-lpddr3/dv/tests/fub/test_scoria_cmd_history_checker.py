# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway

"""Unit test for `scoria_cmd_history_checker` -- auditing the auditor.

Every integration test that reports "no JEDEC violations" is reporting what
THIS block says, so a check that cannot fire makes all of them vacuous. Two
specific ways that has already happened in this family:

  * `--assert` is not a verilator default. An immediate assertion compiled
    without it is silently discarded, and the sim runs green with the checker
    inert. Nothing in a passing run distinguishes "no violations" from "no
    checks". The `fires_*` cases below are the only thing in this file that
    proves otherwise -- they REQUIRE the simulation to die.
  * the window bound was wrong in all six checks (fixed 2026-09-19): a loop
    bounded by T_x scans distances 1..T_x and flags a command at EXACTLY T_x,
    which is legal. That false alarm fires precisely where a well-tuned
    controller lives -- on the minimum -- and it was found by a new instance
    reporting "tRTW violation -- WR only 20 cyc after a RD (need 20)" against
    correct RTL. `legal_at_the_minimum` is that bug.

So the file is two families. `legal_*` drives streams that land exactly on each
JEDEC minimum and must run clean. `fires_*` drives one stream per rule, one
cycle short, and asserts the simulation dies WITH THAT RULE'S OWN MESSAGE --
not merely that it died, which any compile error would also do.

Each `fires_*` case enables ONLY the window it is testing, so a fatal cannot
come from a neighbouring rule and be mistaken for the one under test.
"""

import os
import random

import cocotb
import pytest
from cocotb.triggers import RisingEdge, Timer
from cocotb_test.simulator import run

from TBClasses.shared.filelist_utils import get_sources_from_filelist
from TBClasses.shared.tbbase import TBBase
from TBClasses.shared.utilities import get_paths, sim_build_path

OP_NOP, OP_ACT, OP_RD, OP_RDA, OP_WR, OP_WRA = 0x0, 0x1, 0x2, 0x3, 0x4, 0x5
OP_PRE, OP_PREA, OP_REF, OP_REFPB = 0x6, 0x7, 0x8, 0x9

# The windows, in MC cycles. Deliberately all different so a message naming the
# wrong rule cannot coincidentally carry the right number.
T = {'RCD': 6, 'RP': 5, 'RAS': 10, 'RFC': 20,
     'WTR': 4, 'RTW': 7, 'RRD': 3, 'FAW': 14}
DEPTH = 32


class HistTB(TBBase):
    async def setup(self):
        await self.start_clock('clk', 10, 'ns')
        d = self.dut
        d.cmd_valid_i.value = 0
        d.cmd_op_i.value = OP_NOP
        d.cmd_rank_i.value = 0
        d.cmd_bank_i.value = 0
        await self.assert_reset()
        await self.wait_clocks('clk', 5)
        await self.deassert_reset()
        await self.wait_clocks('clk', 2)
        await Timer(1, 'ns')

    async def assert_reset(self):
        self.dut.rst_n.value = 0

    async def deassert_reset(self):
        self.dut.rst_n.value = 1

    async def setup_clocks_and_reset(self):
        await self.setup()

    async def issue(self, op, bank=0, rank=0):
        """Present one issued command for exactly one cycle."""
        d = self.dut
        d.cmd_valid_i.value = 1
        d.cmd_op_i.value = op
        d.cmd_bank_i.value = bank
        d.cmd_rank_i.value = rank
        await RisingEdge(d.clk)
        d.cmd_valid_i.value = 0
        d.cmd_op_i.value = OP_NOP
        await Timer(1, 'ns')

    async def idle(self, n):
        for _ in range(n):
            await RisingEdge(self.dut.clk)
        await Timer(1, 'ns')

    async def gap(self, op_a, op_b, cycles, *, bank_a=0, bank_b=None):
        """op_a, then op_b exactly `cycles` cycles later (same rank).

        `cycles` is the distance the checker measures: op_a at cycle X and op_b
        at X + cycles. A rule needing >= T is satisfied by cycles == T and
        violated by T-1.
        """
        if bank_b is None:
            bank_b = bank_a
        await self.issue(op_a, bank_a)
        await self.idle(cycles - 1)
        await self.issue(op_b, bank_b)


@cocotb.test(timeout_time=30, timeout_unit="ms")
async def cocotb_test_scoria_cmd_history_checker(dut):
    tt = os.environ.get("TEST_TYPE", "legal_at_the_minimum")
    tb = HistTB(dut)
    await tb.setup()

    # ---------------- legal: must run clean ----------------------------------
    if tt == "legal_at_the_minimum":
        # Exactly ON each minimum. This is the false-alarm case: every one of
        # these is legal, and the old `d < T_x` bound flagged all of them.
        await tb.gap(OP_ACT, OP_RD, T['RCD'], bank_a=1)          # tRCD
        await tb.idle(T['RAS'] + 2)
        await tb.gap(OP_PRE, OP_ACT, T['RP'], bank_a=2)          # tRP
        await tb.idle(T['RCD'] + 2)
        await tb.gap(OP_ACT, OP_PRE, T['RAS'], bank_a=3)         # tRAS
        await tb.idle(T['RP'] + 2)
        await tb.gap(OP_WR, OP_RD, T['WTR'], bank_a=4)           # tWTR
        await tb.idle(T['RTW'] + 2)
        await tb.gap(OP_RD, OP_WR, T['RTW'], bank_a=4)           # tRTW
        await tb.idle(T['RAS'] + 2)
        await tb.gap(OP_ACT, OP_ACT, T['RRD'],                   # tRRD
                     bank_a=5, bank_b=6)
        await tb.idle(T['FAW'] + 4)
        # tRFC: a REF needs every row closed first, so precharge all, then the
        # ACT exactly T_RFC after the REF.
        await tb.issue(OP_PREA, 0)
        await tb.idle(T['RP'] + 2)
        await tb.gap(OP_REF, OP_ACT, T['RFC'], bank_a=0, bank_b=7)
        await tb.idle(4)

    elif tt == "legal_four_acts_in_the_faw_window":
        # Four ACTs inside tFAW is legal; the fifth must wait for the first to
        # leave the window. Spaced by tRRD so that rule stays satisfied too.
        for k in range(4):
            await tb.issue(OP_ACT, bank=k)
            await tb.idle(T['RRD'] - 1)
        # The window is measured from the FIRST of the four: it has already
        # consumed 3*T_RRD cycles, so wait out the remainder plus a margin.
        await tb.idle(T['FAW'] - 3 * T['RRD'] + 2)
        await tb.issue(OP_ACT, bank=4)
        await tb.idle(4)

    elif tt == "legal_refresh_after_every_row_closed":
        # REFab with all banks precharged. The all-bank ops are recorded on
        # every bank's history, which is what makes this scan work at all.
        await tb.issue(OP_ACT, bank=2)
        await tb.idle(T['RAS'] - 1)
        await tb.issue(OP_PRE, bank=2)
        await tb.idle(T['RP'] + 2)
        await tb.issue(OP_REF, 0)
        await tb.idle(T['RFC'] + 2)
        await tb.issue(OP_ACT, bank=2)
        await tb.idle(4)

    elif tt == "legal_auto_precharge_closes_the_row":
        # An RDA/WRA closes the row with no explicit PRE, so a REF behind one
        # must NOT be flagged. If closes_row() missed the AP ops, every
        # auto-precharge build would report a false refresh collision.
        await tb.issue(OP_ACT, bank=1)
        await tb.idle(T['RCD'] - 1)
        await tb.issue(OP_RDA, bank=1)
        await tb.idle(T['RAS'] + 2)
        await tb.issue(OP_REF, 0)
        await tb.idle(4)

    # ---------------- armed: the simulation MUST die -------------------------
    elif tt == "fires_trcd":
        await tb.gap(OP_ACT, OP_RD, T['RCD'] - 1, bank_a=1)
        await tb.idle(4)

    elif tt == "fires_trp":
        await tb.gap(OP_PRE, OP_ACT, T['RP'] - 1, bank_a=2)
        await tb.idle(4)

    elif tt == "fires_tras":
        await tb.gap(OP_ACT, OP_PRE, T['RAS'] - 1, bank_a=3)
        await tb.idle(4)

    elif tt == "fires_trfc":
        await tb.gap(OP_REF, OP_ACT, T['RFC'] - 1, bank_a=0, bank_b=5)
        await tb.idle(4)

    elif tt == "fires_twtr":
        await tb.gap(OP_WR, OP_RD, T['WTR'] - 1, bank_a=4, bank_b=6)
        await tb.idle(4)

    elif tt == "fires_trtw":
        await tb.gap(OP_RD, OP_WR, T['RTW'] - 1, bank_a=4, bank_b=6)
        await tb.idle(4)

    elif tt == "fires_trrd":
        # Different banks on purpose: tRRD is the rule no per-bank history can
        # see, which is why it has its own global ACT stream.
        await tb.gap(OP_ACT, OP_ACT, T['RRD'] - 1, bank_a=5, bank_b=6)
        await tb.idle(4)

    elif tt == "fires_tfaw":
        # Five ACTs inside the window, each one tRRD apart (so tRRD is clean
        # even if it were enabled) -- the fifth is the violation.
        for k in range(5):
            await tb.issue(OP_ACT, bank=k)
            await tb.idle(1)
        await tb.idle(4)

    elif tt == "fires_refresh_with_an_open_row":
        # The bug this block was written for: ACT then REFab with no PRE
        # refreshes an open row, and the coarse registered readiness gate
        # cannot see it.
        await tb.issue(OP_ACT, bank=4)
        await tb.idle(2)
        await tb.issue(OP_REF, 0)
        await tb.idle(4)
    else:
        raise ValueError(f"Unknown TEST_TYPE: {tt}")

    await tb.wait_clocks('clk', 4)


# (case, window overrides, expected fatal substring or None). A fires_* case
# enables ONLY its own rule, so the fatal can only be the one under test.
_ALL = {f"T_{k}": v for k, v in T.items()}
_CASES = [
    ("legal_at_the_minimum", _ALL, None),
    ("legal_four_acts_in_the_faw_window",
     {"T_RRD": T['RRD'], "T_FAW": T['FAW']}, None),
    ("legal_refresh_after_every_row_closed", _ALL, None),
    ("legal_auto_precharge_closes_the_row", _ALL, None),
    ("fires_trcd", {"T_RCD": T['RCD']}, "tRCD violation"),
    ("fires_trp", {"T_RP": T['RP']}, "tRP violation"),
    ("fires_tras", {"T_RAS": T['RAS']}, "tRAS violation"),
    ("fires_trfc", {"T_RFC": T['RFC']}, "tRFC violation"),
    ("fires_twtr", {"T_WTR": T['WTR']}, "GLOBAL tWTR violation"),
    ("fires_trtw", {"T_RTW": T['RTW']}, "GLOBAL tRTW violation"),
    ("fires_trrd", {"T_RRD": T['RRD']}, "GLOBAL tRRD violation"),
    ("fires_tfaw", {"T_FAW": T['FAW']}, "GLOBAL tFAW violation"),
    ("fires_refresh_with_an_open_row", {}, "ROW OPEN"),
]

_GATE_NAMES = {"legal_at_the_minimum", "fires_trcd",
               "fires_refresh_with_an_open_row"}
_TEST_LEVEL = (os.environ.get("REG_LEVEL") or os.environ.get("TEST_LEVEL")
               or "FUNC").upper()
_PARAMS = ([c for c in _CASES if c[0] in _GATE_NAMES]
           if _TEST_LEVEL == "GATE" else _CASES)


@pytest.mark.parametrize("test_type, windows, fatal_text", _PARAMS)
def test_scoria_cmd_history_checker(request, test_type, windows, fatal_text,
                                    capfd, caplog):
    module, repo_root, tests_dir, log_dir, _ = get_paths({})
    dut_name = "scoria_cmd_history_checker"
    test_name = f"test_scoria_cmd_history_checker_{test_type}"
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path=("projects/components/mem-ctrl-ip/mem-ctrl-research-ip/scoria-ddr3-lpddr3/"
                       "rtl/filelists/fub/scoria_cmd_history_checker.f"))
    sim_build = sim_build_path(tests_dir, test_name)
    os.makedirs(sim_build, exist_ok=True); os.makedirs(log_dir, exist_ok=True)
    params = {"NUM_BANKS": "8", "DEPTH": str(DEPTH)}
    params.update({k: str(v) for k, v in windows.items()})
    kwargs = dict(
        python_search=[tests_dir], verilog_sources=verilog_sources,
        includes=includes, toplevel=dut_name, module=module,
        testcase="cocotb_test_scoria_cmd_history_checker",
        sim_build=sim_build, simulator="verilator", parameters=params,
        extra_env={"DUT": dut_name, "TEST_TYPE": test_type,
                   "TEST_LEVEL": _TEST_LEVEL, "COCOTB_LOG_LEVEL": "INFO",
                   "SEED": os.environ.get('SEED', str(random.randint(0, 99999))),
                   "COCOTB_RESULTS_FILE":
                       os.path.join(log_dir, f"results_{test_name}.xml")},
        # --assert is NOT a verilator default. Without it every immediate
        # assertion in the checker is discarded at compile time and the whole
        # block is inert -- a green run then says nothing at all. The fires_*
        # cases are what prove this flag is actually doing something.
        compile_args=["+define+USE_ASYNC_RESET", "--assert"],
        keep_files=True, timescale="1ns/1ps")

    if fatal_text is None:
        run(**kwargs)
        return

    # An armed check kills the simulation. Requiring the RULE'S OWN message
    # matters: a compile error, a missing signal or a cocotb exception would
    # all raise SystemExit too, and would otherwise read as proof the gate
    # fired.
    with pytest.raises(SystemExit):
        run(**kwargs)
    # The simulator's output reaches pytest through cocotb_test's LOGGER, not
    # through the process's stdout -- so caplog is where the $fatal text lands
    # and capfd alone comes back empty. Both are scanned because which one
    # carries it depends on cocotb_test's logging setup, and an empty blob
    # would silently turn this assertion into "the sim died, good enough".
    out = capfd.readouterr()
    blob = (out.out or "") + (out.err or "") + caplog.text
    assert blob.strip(), (
        "no simulator output was captured, so this case cannot tell a checker "
        "fatal from a compile error -- fix the capture before trusting it")
    assert "CMD_HISTORY" in blob and fatal_text in blob, (
        f"the simulation died, but not with the {test_type} message. Expected "
        f"a CMD_HISTORY fatal containing {fatal_text!r}; without it this case "
        f"proves nothing about the check being armed. Tail of the output:\n"
        + "\n".join(blob.strip().splitlines()[-25:]))
