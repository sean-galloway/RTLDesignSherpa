# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: test_kestrel_fuzz
# Purpose: CORE-17 constrained-random RV32I program fuzz for kestrel_core:
#          seeded random instruction streams (generated + assembled by
#          fuzz_gen through the house build flow) run through the battery
#          machinery -- per stream: DUT run-to-halt with the gp-at-ecall
#          verdict, golden interpreter full-field trace diff, and spike
#          (pc, insn) lockstep + exit-code check.  gate runs the committed
#          five-seed smoke corpus, func 25 fresh streams, full 200; every
#          level gets both goldens.
#
# Documentation: projects/components/riscv-ip/README.md
# Subsystem: riscv-ip/kestrel-rv32i
#
# Author: sean galloway
# Created: 2026-10-07

"""CORE-17 constrained-random fuzz: kestrel_core vs interpreter + spike.

The pytest cell generates and assembles its streams before the sim: gate
level always runs the fixed corpus in
``tbclasses/kestrel/fuzz_seeds_gate.json``; func/full derive their seeds
from the cell's SEED env (repo-root conftest pins one per test node, and
``level_env(..., SEED=cell_seed)`` re-exports exactly the seed the streams
were built from), so an explicit ``SEED=<n>`` reproduces a failing stream.

Inside the sim, ``FuzzBattery`` (an RV32UIBattery subclass using its
discover/image_words/image_elf seam) loops the streams through the same
assert_reset/backdoor_load/run_to_halt/verdict path as the rv32ui battery,
with the golden diff and the spike lockstep at every level (not func-only:
the whole point of CORE-17 is dual-golden lockstep on random streams).
"""

import logging
import os
import random
import shutil
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

from tbclasses.kestrel import fuzz_gen                                   # noqa: E402
from tbclasses.kestrel.rv32i_interpreter import load_verilog_hex        # noqa: E402
from tbclasses.kestrel.rv32ui_battery import (                          # noqa: E402
    LINK_BASE,
    RV32UIBattery,
)

logging.basicConfig(level=logging.INFO,
                    format="%(asctime)s %(levelname)s %(message)s")
LOG = logging.getLogger("kestrel_fuzz")


class FuzzBattery(RV32UIBattery):
    """RV32UIBattery fed by generated fuzz streams instead of vendor images.

    ``tests`` is the ordered stream-name list; images and ELFs come from
    the cell's stream directory (KESTREL_FUZZ_DIR, populated by the pytest
    wrapper through fuzz_gen.build_streams).
    """

    title = "kestrel fuzz"

    def __init__(self, dut, level, work_dir, stream_dir):
        self.stream_dir = Path(stream_dir)
        names = sorted(p.stem for p in self.stream_dir.glob("fuzz_*.hex"))
        if not names:
            raise FileNotFoundError(f"no fuzz_*.hex streams in {self.stream_dir}")
        repo_root = os.environ.get(
            "REPO_ROOT", str(Path(__file__).resolve().parents[6]))
        super().__init__(dut, repo_root=repo_root, level=level,
                         work_dir=work_dir, tests=names)
        # CORE-17 contract: dual-golden lockstep on every stream, at every
        # level (the rv32ui battery gates lockstep to func; fuzz never does).
        self.lockstep_levels = ("gate", "func", "full")

    def discover(self):
        return list(self.tests)

    def image_words(self, name):
        words = load_verilog_hex(self.stream_dir / f"{name}.hex")
        return {(idx + (LINK_BASE >> 2)): w for idx, w in words.items()}

    def image_elf(self, name):
        elf = self.stream_dir / f"{name}.elf"
        if not elf.exists():
            raise FileNotFoundError(elf)
        return elf


async def _fuzz(dut):
    level = os.environ.get("TEST_LEVEL", "func")
    log_dir = os.path.dirname(os.environ.get("LOG_PATH", "."))
    stream_dir = os.environ["KESTREL_FUZZ_DIR"]
    work_dir = os.path.join(log_dir, "kestrel_fuzz_battery")
    battery = FuzzBattery(dut, level=level, work_dir=work_dir,
                          stream_dir=stream_dir)
    await battery.run()


@cocotb.test(timeout_time=600_000, timeout_unit="ms")
async def cocotb_test_kestrel_fuzz_stream(dut):
    """Every generated stream: DUT vs golden interpreter (full-field) and
    spike (pc, insn) lockstep; gp==1 at the ecall halt verdict per stream."""
    await _fuzz(dut)


# ---------------------------------------------------------------------------
# pytest wrapper
# ---------------------------------------------------------------------------

CASES = {
    "cocotb_test_kestrel_fuzz_stream": LINK_BASE,
}


def _build_streams(test_level, log_dir):
    """Generate + assemble this cell's streams; returns the stream dir."""
    cell_seed = os.environ.get("SEED") or str(random.randint(0, 100000))
    stream_dir = Path(log_dir) / "kestrel_fuzz" / \
        f"cocotb_test_kestrel_fuzz_stream_{test_level}"
    if stream_dir.exists():
        shutil.rmtree(stream_dir)
    stream_dir.mkdir(parents=True)
    seeds = fuzz_gen.seeds_for_level(test_level, cell_seed)
    programs = fuzz_gen.build_streams(seeds, stream_dir)
    LOG.info(f"{test_level}: built {len(programs)} fuzz streams in "
             f"{stream_dir} (cell seed {cell_seed})")
    return stream_dir, cell_seed


@pytest.mark.parametrize("test_level, description",
                         [(lvl, f"kestrel_fuzz {lvl}")
                          for lvl in reg_level_grid()])
@pytest.mark.parametrize("cocotb_testcase", list(CASES))
def test_kestrel_fuzz(request, cocotb_testcase, test_level, description):
    """Pytest wrapper: generate+assemble the level's streams, then one
    Verilator build runs them all through the battery machinery."""
    module, repo_root, tests_dir, log_dir, _ = get_paths({})
    reset_addr = CASES[cocotb_testcase]

    test_name_plus_params = f"{cocotb_testcase}_{test_level}"
    log_path = os.path.join(log_dir, f"{test_name_plus_params}.log")
    sim_build = sim_build_path(tests_dir, test_name_plus_params)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)
    results_path = os.path.join(log_dir, f"results_{test_name_plus_params}.xml")

    stream_dir, cell_seed = _build_streams(test_level, log_dir)

    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path="projects/components/riscv-ip/kestrel-rv32i/dv/filelists/kestrel_tb.f",
    )

    extra_env = {
        "DUT": "kestrel_tb_top",
        "LOG_PATH": log_path,
        "COCOTB_LOG_LEVEL": "INFO",
        "COCOTB_RESULTS_FILE": results_path,
        "KESTREL_FUZZ_DIR": str(stream_dir),
        **level_env(test_level, SEED=cell_seed),
    }

    compile_args = [
        "--trace", "--trace-structs", "--trace-depth", "99",
        "--timescale", "1ns/1ps",
        "-Wno-WIDTHTRUNC", "-Wno-WIDTHEXPAND",
    ]

    run(
        python_search=[tests_dir],
        verilog_sources=verilog_sources,
        includes=includes,
        toplevel="kestrel_tb_top",
        module=module,
        testcase=cocotb_testcase,
        sim_build=sim_build,
        extra_env=extra_env,
        parameters={"RESET_ADDR": str(reset_addr)},
        waves=bool(int(os.environ.get("WAVES", "0"))),
        keep_files=True,
        compile_args=compile_args,
    )
