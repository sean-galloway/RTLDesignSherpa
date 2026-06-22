# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway
#
# Author: sean galloway
# Created: 2026-06-20

"""
Unit-test runner for `dfi_cmd_formatter`.

Scenarios (all scoreboarded via DfiCmdFormatterTB.drive_and_check):
  all_ops          drive each DDR2 op, verify phase-0 + phase-1..N-1 NOP
  multi_rank       verify per-rank cs_n decode under NUM_RANKS=2
  a10_auto_pre     verify A10 bit set for RDA/WRA/PREA, cleared for RD/WR/PRE
  cmd_invalid      cmd_valid=0 → bus must be all-deselected NOP every phase
  lpddr2_nop       memtype = LPDDR2 → bus must be all-deselected NOP (TODO)
  random_soak      random ops + addresses; check vs reference each cycle
"""

import os
import sys
import random
import logging
import pytest

import cocotb
from cocotb.triggers import RisingEdge
from cocotb_test.simulator import run

from TBClasses.shared.utilities import get_paths
from TBClasses.shared.filelist_utils import get_sources_from_filelist

_DV_DIR = os.path.abspath(os.path.join(os.path.dirname(__file__), "../.."))
if _DV_DIR not in sys.path:
    sys.path.insert(0, _DV_DIR)

from tbclasses.trackers import DfiCmdFormatterTracker  # noqa: E402
from tbclasses.dfi_cmd_formatter_tb import (  # noqa: E402
    DfiCmdFormatterTB,
    OP_NOP, OP_ACT, OP_RD, OP_RDA, OP_WR, OP_WRA,
    OP_PRE, OP_PREA, OP_REF, OP_MRS,
    MEMTYPE_DDR2, MEMTYPE_LPDDR2,
)


# ---------------------------------------------------------------------------
# CocoTB dispatch
# ---------------------------------------------------------------------------

@cocotb.test(timeout_time=10, timeout_unit="ms")
async def cocotb_test_dfi_cmd_formatter(dut):
    test_type = os.environ.get("TEST_TYPE", "all_ops")
    log = logging.getLogger("dfi_cmd_formatter_test")
    log.info(f"TEST_TYPE={test_type}")

    tb = DfiCmdFormatterTB(dut)
    # Tracker auto-dumps <sim_build>/dficmd.out at end of sim.
    dficmd_tracker = DfiCmdFormatterTracker(dut)
    cocotb.start_soon(dficmd_tracker.run())
    await tb.setup_clocks_and_reset()

    scenarios = {
        "all_ops":      _all_ops,
        "multi_rank":   _multi_rank,
        "a10_auto_pre": _a10_auto_pre,
        "cmd_invalid":  _cmd_invalid,
        "lpddr2_nop":   _lpddr2_nop,
        "random_soak":  _random_soak,
    }
    if test_type not in scenarios:
        raise ValueError(f"Unknown TEST_TYPE: {test_type}")
    await scenarios[test_type](tb)

    await tb.wait_clocks('mc_clk', 4)


# ---------------------------------------------------------------------------
# Scenarios
# ---------------------------------------------------------------------------

ALL_OPS = [OP_NOP, OP_ACT, OP_RD, OP_RDA, OP_WR, OP_WRA,
           OP_PRE, OP_PREA, OP_REF, OP_MRS]


async def _all_ops(tb: DfiCmdFormatterTB):
    """Drive each op at a fixed rank/bank/row/col combination and verify
    phase-0 plus phase-1..N-1 NOP."""
    for op in ALL_OPS:
        await tb.drive_and_check(op=op, rank=0, bank=3, row=0x123, col=0x40)


async def _multi_rank(tb: DfiCmdFormatterTB):
    """Verify cs_n decode for each rank."""
    for rank in range(tb.NUM_RANKS):
        for op in [OP_NOP, OP_ACT, OP_RD, OP_REF]:
            await tb.drive_and_check(op=op, rank=rank, bank=2, row=0x100, col=0x80)


async def _a10_auto_pre(tb: DfiCmdFormatterTB):
    """Auto-precharge / all-bank precharge → A10 = 1; otherwise 0."""
    # Use a col that has A10 = 0 internally so A10 must come from the op,
    # not from the col bits.
    col_no_a10 = 0x33   # bits [9:0] excluding bit 10
    row_no_a10 = 0x1F & ~(1 << 10)  # row with bit 10 forced 0

    # RDA / WRA / PREA → A10 = 1
    for op in [OP_RDA, OP_WRA]:
        await tb.drive_and_check(op=op, rank=0, bank=2, row=0, col=col_no_a10)
    await tb.drive_and_check(op=OP_PREA, rank=0, bank=2, row=0, col=col_no_a10)

    # RD / WR / PRE → A10 = 0 (with col & row not carrying bit 10)
    for op in [OP_RD, OP_WR]:
        await tb.drive_and_check(op=op, rank=0, bank=2, row=0, col=col_no_a10)
    await tb.drive_and_check(op=OP_PRE, rank=0, bank=2, row=row_no_a10,
                              col=col_no_a10)


async def _cmd_invalid(tb: DfiCmdFormatterTB):
    """cmd_valid = 0 — full bus stays all-deselected NOP every phase."""
    for op in ALL_OPS:
        await tb.drive_and_check(op=op, rank=0, bank=5, row=0xABC, col=0x40,
                                  valid=False)


async def _lpddr2_nop(tb: DfiCmdFormatterTB):
    """memtype = LPDDR2 (TODO encoding) → drive NOP for every op."""
    for op in ALL_OPS:
        await tb.drive_and_check(op=op, rank=0, bank=4, row=0x200, col=0x10,
                                  memtype=MEMTYPE_LPDDR2)


async def _random_soak(tb: DfiCmdFormatterTB):
    rng = random.Random(tb.SEED ^ 0xDF1)
    n = {'gate': 32, 'func': 200, 'full': 800}.get(tb.TEST_LEVEL, 200)
    for _ in range(n):
        op = rng.choice(ALL_OPS + [OP_NOP, OP_RD, OP_WR])
        await tb.drive_and_check(
            op=op,
            rank=rng.randint(0, tb.NUM_RANKS - 1),
            bank=rng.randint(0, tb.NUM_BANKS - 1),
            row=rng.randint(0, (1 << tb.ROW_WIDTH) - 1),
            col=rng.randint(0, (1 << tb.COL_WIDTH) - 1),
        )


# ---------------------------------------------------------------------------
# Pytest matrix
# ---------------------------------------------------------------------------

_ALL_TYPES = [
    "all_ops",
    "multi_rank",
    "a10_auto_pre",
    "cmd_invalid",
    "lpddr2_nop",
    "random_soak",
]

# (test_type, DFI_RATE, NUM_RANKS)
_GATE = [(t, 2, 1) for t in ["all_ops", "a10_auto_pre", "cmd_invalid"]]
_FUNC = [(t, 2, 1) for t in _ALL_TYPES] + [
    (t, 4, 1) for t in ["all_ops", "a10_auto_pre", "cmd_invalid"]
] + [
    ("multi_rank", 2, 2),
]
_FULL = _FUNC + [(t, 4, 2) for t in _ALL_TYPES] + [
    ("random_soak", 2, 1),
    ("random_soak", 4, 2),
]
# Dedupe — otherwise pytest disambiguates colliding IDs with _0/_1 suffixes
# and parallel workers race on the same local_sim_build/ directory.
_FULL = list(dict.fromkeys(_FULL))

_TEST_LEVEL = os.environ.get("TEST_LEVEL", "FUNC").upper()
_PARAMS = {"GATE": _GATE, "FUNC": _FUNC, "FULL": _FULL}.get(_TEST_LEVEL, _FUNC)


@pytest.mark.parametrize("test_type,dfi_rate,num_ranks", _PARAMS,
                         ids=[f"{t[0]}-r{t[1]}-nr{t[2]}" for t in _PARAMS])
def test_dfi_cmd_formatter(request, test_type, dfi_rate, num_ranks):
    module, repo_root, tests_dir, log_dir, _ = get_paths({})
    dut_name = "dfi_cmd_formatter"

    test_name = f"test_dfi_cmd_formatter_{test_type}_r{dfi_rate}_nr{num_ranks}"

    filelist_path = (
        "projects/components/memory-controllers/ddr2-lpddr2/"
        "rtl/filelists/fub/dfi_cmd_formatter.f"
    )
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root, filelist_path=filelist_path
    )

    sim_build = os.path.join(tests_dir, "local_sim_build", test_name)
    os.makedirs(sim_build, exist_ok=True)
    log_path     = os.path.join(log_dir, f"{test_name}.log")
    results_path = os.path.join(log_dir, f"results_{test_name}.xml")
    os.makedirs(log_dir, exist_ok=True)

    extra_env = {
        "DUT":               dut_name,
        "LOG_PATH":          log_path,
        "COCOTB_LOG_LEVEL":  "INFO",
        "COCOTB_RESULTS_FILE": results_path,
        "SEED":              str(random.randint(0, 100000)),
        "TEST_TYPE":         test_type,
        "TEST_LEVEL":        _TEST_LEVEL.lower(),
        "NUM_RANKS":         str(num_ranks),
        "NUM_BANKS":         "8",
        "ROW_WIDTH":         "14",
        "COL_WIDTH":         "10",
        "BURST_LEN_WIDTH":   "8",
        "DFI_RATE":          str(dfi_rate),
        "DFI_ADDR_WIDTH":    "14",
        "DFI_BANK_WIDTH":    "3",
        "DFI_CTRL_WIDTH":    "1",
        "DFI_CS_WIDTH":      str(num_ranks),
    }

    enable_waves = bool(int(os.environ.get("WAVES", "0")))
    compile_args = ["+define+USE_ASYNC_RESET"]
    if enable_waves:
        compile_args += ["--trace-fst", "--trace-structs", "--trace-depth", "99"]
        extra_env["VERILATOR_TRACE"] = "1"
        extra_env["VERILATOR_TRACE_FST"] = "1"

    parameters = {
        "NUM_RANKS":       str(num_ranks),
        "NUM_BANKS":       "8",
        "ROW_WIDTH":       "14",
        "COL_WIDTH":       "10",
        "BURST_LEN_WIDTH": "8",
        "DFI_RATE":        str(dfi_rate),
        "DFI_ADDR_WIDTH":  "14",
        "DFI_BANK_WIDTH":  "3",
        "DFI_CTRL_WIDTH":  "1",
        "DFI_CS_WIDTH":    str(num_ranks),
    }

    sim_args  = []
    plus_args = []
    if enable_waves:
        sim_args  += ["--trace", "--trace-structs", "--trace-depth", "99"]
        plus_args += ["--trace"]

    run(
        python_search=[tests_dir],
        verilog_sources=verilog_sources,
        includes=includes,
        toplevel=dut_name,
        module=module,
        testcase="cocotb_test_dfi_cmd_formatter",
        sim_build=sim_build,
        simulator="verilator",
        extra_env=extra_env,
        parameters=parameters,
        compile_args=compile_args,
        sim_args=sim_args,
        plus_args=plus_args,
        waves=enable_waves,
        keep_files=True,
        timescale="1ns/1ps",
    )
