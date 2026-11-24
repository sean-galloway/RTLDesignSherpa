# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: test_peregrine_mdu
# Purpose: FUB test of peregrine_mdu, the iterative M unit: every operation
#          against the spec reference model on the edge-operand cross
#          product plus seeded random operands, the exact stall count of
#          each operation (33 iterative, 1 early-out, 2 MUL_DSP multiply),
#          the done result held until consumed, operands latched at start,
#          and cancel at every step of a running operation.
#
# Documentation: projects/components/riscv-ip/peregrine-rv32im/PRD.md
# Subsystem: riscv-ip/peregrine-rv32im
#
# Author: sean galloway
# Created: 2026-11-23

"""peregrine_mdu unit test (TASK-001 stage 2).

Levels: gate runs the edge cross product once per operation; func adds
2,000 random operations, cancels at every step and done-holds; full adds
20,000 random operations.  Both MUL_DSP builds are cells of the grid.
"""

import os
import random
import sys
from pathlib import Path

import cocotb
import pytest
from cocotb_test.simulator import run

from TBClasses.shared.filelist_utils import get_sources_from_filelist
from TBClasses.shared.test_levels import level_env, reg_level_grid
from TBClasses.shared.utilities import get_paths, sim_build_path

_DV_DIR = str(Path(__file__).resolve().parents[1])
if _DV_DIR not in sys.path:
    sys.path.insert(0, _DV_DIR)

from tbclasses.peregrine.mdu_tb import (M_OPS, MASK32, INT_MIN,  # noqa: E402
                                        ITERATIVE_STALL, MduTB,
                                        expected_stall, m_ref)

EDGES = (0, 1, 2, 3, 7, MASK32, MASK32 - 1, INT_MIN, INT_MIN + 1,
         0x7FFF_FFFF, 0x0001_0000, 0xFFFF_0000, 0x5555_5555, 0xAAAA_AAAA)
RANDOM_OPS = {"gate": 0, "func": 2_000, "full": 20_000}


def _operand(rng: random.Random) -> int:
    """Random 32-bit operand, biased toward the edges and small magnitudes."""
    pick = rng.randrange(4)
    if pick == 0:
        return rng.choice(EDGES)
    if pick == 1:
        return rng.randrange(1 << rng.randrange(1, 33))
    if pick == 2:
        return (-rng.randrange(1, 1 << rng.randrange(1, 32))) & MASK32
    return rng.getrandbits(32)


async def _check(tb, f3, a, b, mul_dsp, hold=0):
    res = await tb.run_op(f3, a, b, hold=hold)
    want = m_ref(f3, a, b)
    assert res.result == want, (f"{M_OPS[f3]} 0x{a:08x}, 0x{b:08x}: got "
                                f"0x{res.result:08x}, want 0x{want:08x}")
    stall = expected_stall(f3, b, a, mul_dsp)
    assert res.stall == stall, (f"{M_OPS[f3]} 0x{a:08x}, 0x{b:08x}: "
                                f"{res.stall} stall cycles, want {stall}")


@cocotb.test(timeout_time=2000, timeout_unit="ms")
async def cocotb_test_peregrine_mdu(dut):
    """All eight M operations: results, stall counts, hold, cancel."""
    level = os.environ.get("TEST_LEVEL", "gate")
    mul_dsp = bool(int(os.environ.get("MUL_DSP", "0")))
    seed = int(os.environ.get("SEED", "1"))
    rng = random.Random(seed)
    tb = MduTB(dut)
    await tb.setup_clocks_and_reset()

    count = 0
    for f3 in range(8):
        for a in EDGES:
            for b in EDGES:
                await _check(tb, f3, a, b, mul_dsp)
                count += 1
    tb.log.info(f"edge cross: {count} operations")

    for _ in range(RANDOM_OPS[level]):
        f3 = rng.randrange(8)
        await _check(tb, f3, _operand(rng), _operand(rng), mul_dsp,
                     hold=rng.choice((0, 0, 0, 1, 3)))
        count += 1

    if level != "gate":
        # Cancel at every step of an iterative operation, and before and
        # after done; the next operation must be unaffected.
        cancels = 0
        for f3 in range(8):
            for k in range(ITERATIVE_STALL + 2):
                a, b = rng.getrandbits(32), rng.getrandbits(32) | 1
                await tb.cancel_after(f3, a, b, k)
                await _check(tb, rng.randrange(8), _operand(rng), _operand(rng),
                             mul_dsp)
                cancels += 1
        tb.log.info(f"cancels: {cancels}, each followed by a checked operation")

    tb.log.info(f"peregrine_mdu (MUL_DSP={int(mul_dsp)}, {level}, seed {seed}): "
                f"{count} operations checked")


@pytest.mark.parametrize("mul_dsp", [0, 1])
@pytest.mark.parametrize("test_level, description",
                         [(lvl, f"peregrine_mdu {lvl}") for lvl in reg_level_grid()])
def test_peregrine_mdu(request, test_level, description, mul_dsp):
    """Pytest wrapper: one Verilator build per (level, MUL_DSP) cell."""
    module, repo_root, tests_dir, log_dir, _ = get_paths({})
    name = f"cocotb_test_peregrine_mdu_dsp{mul_dsp}_{test_level}"
    log_path = os.path.join(log_dir, f"{name}.log")
    sim_build = sim_build_path(tests_dir, name)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path="projects/components/riscv-ip/peregrine-rv32im/rtl/filelists/fub/peregrine_mdu.f",
    )
    run(
        python_search=[tests_dir],
        verilog_sources=verilog_sources,
        includes=includes,
        toplevel="peregrine_mdu",
        module=module,
        testcase="cocotb_test_peregrine_mdu",
        sim_build=sim_build,
        extra_env={
            "DUT": "peregrine_mdu",
            "LOG_PATH": log_path,
            "MUL_DSP": str(mul_dsp),
            "COCOTB_LOG_LEVEL": "INFO",
            "COCOTB_RESULTS_FILE": os.path.join(log_dir, f"results_{name}.xml"),
            **level_env(test_level),
        },
        parameters={"MUL_DSP": str(mul_dsp)},
        waves=bool(int(os.environ.get("WAVES", "0"))),
        keep_files=True,
        compile_args=["--trace", "--timescale", "1ns/1ps",
                      "-Wno-WIDTHTRUNC", "-Wno-WIDTHEXPAND"],
    )
