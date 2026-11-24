# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: test_peregrine_predictor
# Purpose: Core-level branch-predictor test for peregrine_core: the PRD §5
#          predictor stress streams plus generated hazard programs, each run
#          on the BP_EN=1 and BP_EN=0 builds.  Every retired instruction's
#          prediction is held to the predictor model (bpred_model), the
#          programs check themselves and lock against spike, and the A/B
#          comparison is made once both builds have run.
#
# Documentation: projects/components/riscv-ip/peregrine-rv32im/PRD.md
# Subsystem: riscv-ip/peregrine-rv32im
#
# Author: sean galloway
# Created: 2026-11-24

"""peregrine predictor stress streams and the BP_EN A/B (TASK-001 stage 3).

Per program, on each build:

* tohost == 1 (the program's own result check);
* spike lockstep of the (pc, insn) stream: no wrong-path instruction
  retires, and every redirect lands where spike went;
* the RVFI trace rules and the shadow-regfile operand check;
* ``check_trace``: every prediction equals the model's under a state the
  pipeline timing allows, and every mispredict flag matches its prediction
  and outcome.

A/B (in the pytest wrapper, after both builds): on BP_EN=0 every taken
control transfer mispredicts (merlin's fetch); BP_EN=1 never mispredicts
more than BP_EN=0, and is faster on every loop and aliasing stream except
btb_alias, where both entries thrash by construction.  The table of cycles,
mispredicts and taken transfers per stream is written for the book.
"""

import json
import logging
import os
import random
import subprocess
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

from tbclasses.peregrine.battery import (LINK_BASE, elf_image, lockstep,  # noqa: E402
                                         parse_spike_log, read_elf32, run_spike)
from tbclasses.peregrine.bpred_model import check_trace  # noqa: E402
from tbclasses.peregrine.mext_program import generate, shadow_check  # noqa: E402
from tbclasses.peregrine.peregrine_tb import PeregrineTB  # noqa: E402
from tbclasses.peregrine.predictor_streams import (check_alias, program,  # noqa: E402
                                                   streams)

TOOLCHAIN = os.environ.get("RISCV_TOOLCHAIN", "/mnt/data/tools/xpack-riscv-none-elf-gcc/bin")
SPIKE_ISA = "rv32im_zicsr_zifencei"
RANDOM_BLOCKS = {"gate": 60, "func": 300, "full": 1500}
MEM_WAIT_PERCENT = 10
MAX_CYCLES = 400_000
# Streams on which prediction must win outright.  loop_trip1 has no taken
# back edge to predict, and btb_alias's branches thrash by construction.
MUST_SPEED_UP = ("loop_trip2", "loop_trip3", "loop_trip4", "bht_alias", "jalr_targets")
# Streams re-run with random mem_wait (func and full).
MEM_WAIT_STREAMS = ("loop_trip3", "interlock", "trap_shadow")


def build_elf(text: str, work_dir: Path, name: str) -> Path:
    work_dir.mkdir(parents=True, exist_ok=True)
    asm, obj, elf = (work_dir / f"{name}{ext}" for ext in (".s", ".o", ".elf"))
    asm.write_text(text)
    subprocess.run([f"{TOOLCHAIN}/riscv-none-elf-as", "-march=rv32im_zicsr_zifencei",
                    "-mabi=ilp32", str(asm), "-o", str(obj)], check=True)
    # -N: one segment at the link address (spike rejects the header page).
    subprocess.run([f"{TOOLCHAIN}/riscv-none-elf-ld", "--no-relax", "-N",
                    f"-Ttext=0x{LINK_BASE:x}", str(obj), "-o", str(elf)], check=True)
    return elf


async def _run_program(dut, tb, elf, name, bp_en, work_dir, mem_wait=None) -> dict:
    entry, symbols = read_elf32(elf)
    words = dict(elf_image(elf))
    if "irq_enable" in symbols:                 # generated programs: no interrupts
        words[symbols["irq_enable"] >> 2] = 0
    await tb.assert_reset()
    await tb.backdoor_load(words)
    await tb.release_reset()
    value = await tb.run_to_tohost(symbols["tohost"], max_cycles=MAX_CYCLES,
                                   mem_wait_driver=mem_wait)
    assert value == 1, f"{name}: tohost={value} (3 = wrong result, 5 = unexpected trap)"
    tb.check_order_sequence()
    tb.check_x0_rd_zero()
    tb.check_trap_beats()
    tb.check_mem_side_effects()
    shadow = shadow_check(tb.trace)
    verdict = check_trace(tb.trace, bp_en)
    assert not verdict.errors, f"{name}: predictor model: " + "; ".join(verdict.errors)
    log_path = work_dir / f"spike_{name}.log"
    rc = run_spike(SPIKE_ISA, elf, log_path)
    assert rc == 0, f"{name}: spike rc={rc}"
    errors = lockstep(tb.trace, entry, parse_spike_log(log_path))
    assert not errors, f"{name}: lockstep: " + "; ".join(errors)
    cycles = tb.trace[-1]["cycle"] + 1
    return {"name": name, "cycles": cycles, "retired": len(tb.trace),
            "control": verdict.control, "taken": verdict.taken,
            "mispredicts": verdict.mispredicts, "ambiguous": verdict.ambiguous,
            "operands_checked": shadow["operands"]}


def _check_stale_entry(trace: list, site_br: int) -> None:
    """The stale-entry case really happened: the rewritten instruction was
    fetched once with the old taken prediction (and mispredicted), and the
    pass after it predicted nothing."""
    beats = [b for b in trace if b["pc"] == site_br]
    assert len(beats) == 3, f"site_br retired {len(beats)} times, expected 3"
    assert [b["bp_pred_taken"] for b in beats[1:]] == [1, 0] and \
        [b["bp_mispredict"] for b in beats[1:]] == [1, 0], \
        f"stale entry: predictions {[(b['bp_pred_taken'], b['bp_mispredict']) for b in beats]}"


@cocotb.test(timeout_time=3000, timeout_unit="sec")
async def cocotb_test_peregrine_predictor(dut):
    """Predictor streams + generated programs on one BP_EN build."""
    level = os.environ.get("TEST_LEVEL", "gate")
    bp_en = os.environ.get("BP_EN", "1") == "1"
    seed = int(os.environ.get("SEED", "1"))
    work_dir = Path(os.environ["PREDICTOR_WORK"])
    tb = PeregrineTB(dut, reset_addr=LINK_BASE)
    await tb.ensure_clock()
    rng = random.Random(seed)
    results = []

    for s in streams(level):
        elf = build_elf(program(s), work_dir, s.name)
        if s.alias_symbols:
            _, sym = read_elf32(elf)
            check_alias(s.alias_symbols[2], sym[s.alias_symbols[0]], sym[s.alias_symbols[1]])
        results.append(await _run_program(dut, tb, elf, s.name, bp_en, work_dir))
        if s.name == "stale_entry" and bp_en:
            _check_stale_entry(tb.trace, read_elf32(elf)[1]["site_br"])
        # mem_wait on streams that re-execute branches whose counters are
        # still moving: a predictor written more than once per instruction
        # while the pipeline is held shows up only there (a mem_wait run of
        # the generated program alone let that mutant through).
        if level != "gate" and s.name in MEM_WAIT_STREAMS:
            results.append(await _run_program(
                dut, tb, elf, f"{s.name}+mem_wait", bp_en, work_dir,
                mem_wait=lambda d, c: rng.randrange(100) < MEM_WAIT_PERCENT))

    # Generated hazard programs (the M-stress generator, no interrupts),
    # with and without mem_wait: the predictor must be written once per
    # resolved instruction, whatever holds the pipeline.
    gen = generate(seed, RANDOM_BLOCKS[level])
    elf = build_elf(gen.text, work_dir, "generated")
    results.append(await _run_program(dut, tb, elf, "generated", bp_en, work_dir))
    if level != "gate":
        results.append(await _run_program(
            dut, tb, elf, "generated+mem_wait", bp_en, work_dir,
            mem_wait=lambda d, c: rng.randrange(100) < MEM_WAIT_PERCENT))

    for r in results:
        dut._log.info(f"BP_EN={int(bp_en)} {r['name']:<20} cycles {r['cycles']:>7} "
                      f"retired {r['retired']:>6} taken {r['taken']:>5} "
                      f"mispredicts {r['mispredicts']:>5} (ambiguous {r['ambiguous']})")
    (work_dir / f"results_bp{int(bp_en)}.json").write_text(json.dumps(results, indent=1))


def _ab(work: Path, level: str) -> str:
    """Compare the two builds' results; return the table."""
    on = {r["name"]: r for r in json.loads((work / "results_bp1.json").read_text())}
    off = {r["name"]: r for r in json.loads((work / "results_bp0.json").read_text())}
    assert on.keys() == off.keys(), "the two builds ran different programs"
    lines = [f"peregrine predictor A/B ({level}): cycles / mispredicts / taken",
             f"{'stream':<20} {'BP_EN=1':>18} {'BP_EN=0':>18} {'speedup':>8}"]
    for name in on:
        a, b = on[name], off[name]
        assert a["retired"] == b["retired"], f"{name}: retired counts differ"
        assert b["mispredicts"] == b["taken"], \
            f"{name}: BP_EN=0 mispredicted {b['mispredicts']} of {b['taken']} taken transfers"
        assert a["mispredicts"] <= b["mispredicts"], \
            f"{name}: the predictor mispredicted more ({a['mispredicts']}) than none ({b['mispredicts']})"
        if name in MUST_SPEED_UP:
            assert a["cycles"] < b["cycles"], f"{name}: no speedup from prediction"
        lines.append(f"{name:<20} {a['cycles']:>7} {a['mispredicts']:>5} {a['taken']:>4} "
                     f"{b['cycles']:>7} {b['mispredicts']:>5} {b['taken']:>4} "
                     f"{b['cycles'] / a['cycles']:>8.3f}")
    table = "\n".join(lines) + "\n"
    (work / f"predictor_ab_{level}.txt").write_text(table)
    return table


@pytest.mark.parametrize("test_level, description",
                         [(lvl, f"peregrine_predictor {lvl}") for lvl in reg_level_grid()])
def test_peregrine_predictor(request, test_level, description):
    """Pytest wrapper: build and run BP_EN=1 and BP_EN=0, then the A/B."""
    module, repo_root, tests_dir, log_dir, _ = get_paths({})
    work = Path(log_dir) / f"predictor_{test_level}"
    work.mkdir(parents=True, exist_ok=True)
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path="projects/components/riscv-ip/peregrine-rv32im/dv/filelists/peregrine_tb.f",
    )
    for bp_en in (1, 0):
        name = f"cocotb_test_peregrine_predictor_bp{bp_en}_{test_level}"
        sim_build = sim_build_path(tests_dir, name)
        os.makedirs(sim_build, exist_ok=True)
        os.makedirs(log_dir, exist_ok=True)
        run(
            python_search=[tests_dir],
            verilog_sources=verilog_sources,
            includes=includes,
            toplevel="peregrine_tb_top",
            module=module,
            testcase="cocotb_test_peregrine_predictor",
            sim_build=sim_build,
            extra_env={
                "DUT": "peregrine_tb_top",
                "LOG_PATH": os.path.join(log_dir, f"{name}.log"),
                "BP_EN": str(bp_en),
                "PREDICTOR_WORK": str(work),
                "COCOTB_LOG_LEVEL": "INFO",
                "COCOTB_RESULTS_FILE": os.path.join(log_dir, f"results_{name}.xml"),
                **level_env(test_level),
            },
            parameters={"RESET_ADDR": str(LINK_BASE), "BP_EN": str(bp_en)},
            waves=bool(int(os.environ.get("WAVES", "0"))),
            keep_files=True,
            compile_args=["--trace", "--trace-structs", "--timescale", "1ns/1ps",
                          "-Wno-WIDTHTRUNC", "-Wno-WIDTHEXPAND"],
        )
    logging.getLogger(__name__).info("\n%s", _ab(work, test_level))
