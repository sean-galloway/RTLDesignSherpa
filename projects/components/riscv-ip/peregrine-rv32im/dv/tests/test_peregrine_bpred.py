# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: test_peregrine_bpred
# Purpose: FUB test of peregrine_bpred: seeded random lookups and updates
#          over a PC pool built to alias (same BTB index with a different
#          tag; same BHT index), checked cycle by cycle against BpredModel,
#          plus the BP_EN=0 build that must never predict taken.  Every build
#          randomizes the initial contents of the unreset BTB payload and
#          BHT, as a 4-state simulator's X or a stale board state would:
#          no prediction may depend on a value no update wrote.
#
# Documentation: projects/components/riscv-ip/peregrine-rv32im/PRD.md
# Subsystem: riscv-ip/peregrine-rv32im
#
# Author: sean galloway
# Created: 2026-11-24

"""peregrine_bpred unit test (TASK-001 stage 3).

Every cycle the TB looks up one PC and, three cycles in four, applies one
update: a conditional branch, a JAL/JALR, or a non-branch that was predicted
taken (the stale-entry kill).  Lookups favour PCs that were updated, so hits
dominate.  Levels: gate 3,000 cycles, func 30,000, full 300,000.
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

from tbclasses.peregrine.bpred_model import BpredModel  # noqa: E402
from tbclasses.peregrine.bpred_tb import BpredTB, Update  # noqa: E402

BASE = 0x8000_0000
CYCLES = {"gate": 3_000, "func": 30_000, "full": 300_000}


def pc_pool(rng: random.Random) -> list:
    """PCs that collide: a few sequential ones, the same BTB index at 128 B
    strides (different tag, different BHT index), and the same BTB and BHT
    index at 1 KiB strides (different tag)."""
    pcs = {BASE + 4 * i for i in range(8)}
    for k in range(1, 4):
        pcs.add(BASE + 128 * k)
        pcs.add(BASE + 1024 * k)
        pcs.add(BASE + 1024 * k + 128)
    pcs |= {(BASE + 4 * rng.randrange(1 << 16)) for _ in range(8)}
    return sorted(pcs)


def random_update(rng, pcs, model) -> Update:
    pc = rng.choice(pcs)
    kind = rng.choices(("cond", "uncond", "other"), weights=(6, 3, 1))[0]
    taken = kind == "uncond" or (kind == "cond" and rng.random() < 0.6)
    target = (BASE + 4 * rng.randrange(1 << 12)) if taken else (pc + 4)
    pred_taken, _ = model.predict_one(pc)
    return Update(pc=pc, cond=kind == "cond", uncond=kind == "uncond", taken=taken,
                  target=target, pred_taken=pred_taken)


@cocotb.test(timeout_time=2000, timeout_unit="ms")
async def cocotb_test_peregrine_bpred(dut):
    """Random lookups and updates against the model, every cycle."""
    level = os.environ.get("TEST_LEVEL", "gate")
    bp_en = os.environ.get("BP_EN", "1") == "1"
    seed = int(os.environ.get("SEED", "1"))
    rng = random.Random(seed)
    tb = BpredTB(dut)
    await tb.setup_clocks_and_reset()

    model = BpredModel()
    pcs = pc_pool(rng)
    counts = {"lookups": 0, "hits_taken": 0, "updates": 0, "kills": 0}
    for _ in range(CYCLES[level]):
        lookup = rng.choice(pcs)
        update = random_update(rng, pcs, model) if rng.random() < 0.75 else None
        want = model.predict_one(lookup) if bp_en else (False, 0)
        got = await tb.cycle(lookup, update)
        assert got[0] == want[0] and (not want[0] or got[1] == want[1]), (
            f"lookup 0x{lookup:08x}: RTL {got[0]}/0x{got[1]:08x}, model "
            f"{want[0]}/0x{want[1]:08x}")
        counts["lookups"] += 1
        counts["hits_taken"] += int(got[0])
        if update is not None:
            counts["updates"] += 1
            counts["kills"] += int(not update.cond and not update.uncond and update.pred_taken)
            model.update(update.pc, update.cond, update.uncond, update.taken,
                         update.target, update.pred_taken)
    tb.log.info(f"peregrine_bpred (BP_EN={int(bp_en)}, {level}, seed {seed}): {counts}")
    if bp_en:
        assert counts["hits_taken"] > counts["lookups"] // 10, "too few taken predictions"
        assert counts["kills"] > 0, "the stale-entry kill never ran"
    else:
        assert counts["hits_taken"] == 0


@pytest.mark.parametrize("bp_en", [1, 0])
@pytest.mark.parametrize("test_level, description",
                         [(lvl, f"peregrine_bpred {lvl}") for lvl in reg_level_grid()])
def test_peregrine_bpred(request, test_level, description, bp_en):
    """Pytest wrapper: one Verilator build per (level, BP_EN) cell."""
    module, repo_root, tests_dir, log_dir, _ = get_paths({})
    name = f"cocotb_test_peregrine_bpred_bp{bp_en}_{test_level}"
    env = level_env(test_level)
    log_path = os.path.join(log_dir, f"{name}.log")
    sim_build = sim_build_path(tests_dir, name)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path="projects/components/riscv-ip/peregrine-rv32im/rtl/filelists/fub/peregrine_bpred.f",
    )
    run(
        python_search=[tests_dir],
        verilog_sources=verilog_sources,
        includes=includes,
        toplevel="peregrine_bpred",
        module=module,
        testcase="cocotb_test_peregrine_bpred",
        sim_build=sim_build,
        extra_env={
            "DUT": "peregrine_bpred",
            "LOG_PATH": log_path,
            "BP_EN": str(bp_en),
            "COCOTB_LOG_LEVEL": "INFO",
            "COCOTB_RESULTS_FILE": os.path.join(log_dir, f"results_{name}.xml"),
            **env,
        },
        parameters={"BP_EN": str(bp_en)},
        # Unreset memories start random, seeded with the test's SEED.
        plus_args=["+verilator+rand+reset+2", f"+verilator+seed+{int(env['SEED']) or 1}"],
        waves=bool(int(os.environ.get("WAVES", "0"))),
        keep_files=True,
        compile_args=["--trace", "--timescale", "1ns/1ps", "--x-initial", "unique",
                      "-Wno-WIDTHTRUNC", "-Wno-WIDTHEXPAND"],
    )
