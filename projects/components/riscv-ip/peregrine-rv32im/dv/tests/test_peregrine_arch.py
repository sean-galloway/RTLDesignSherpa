# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: test_peregrine_arch
# Purpose: riscv-arch-test 3.10.0 rv32i_m/M and rv32i_m/Zifencei on
#          peregrine: each test's signature region, read from the TB memory
#          after the tohost store, against the RISCOF reference signature
#          (spike and Sail agree).  The cacheless core (peregrine_tb_top, both
#          MUL_DSP builds for M) and the cached build (peregrine_sys_tb_top:
#          I$ + amber D$; the TB cleans amber through peregrine_top's hook
#          before reading the signature).
#
# Documentation: vault/handbook/dv/riscv-arch-test.md
# Subsystem: riscv-ip/peregrine-rv32im
#
# Author: sean galloway
# Created: 2026-11-23

"""peregrine riscv-arch-test signature compare (TASK-001 stage 2 and stage
4 gates).

The build, the references and the compare are the shared
``common-rv32i/dv/arch_test/rv32_arch_test.py``.  peregrine traps on
ecall, so it runs the suite's reference image itself, which ends on a
tohost store (``run_tohost``, PRD §5).  M: gate runs mul-01, div-01 and
remu-01; func and full run all eight rv32i_m/M tests.  Zifencei: Fencei
(self-modifying code across fence.i) at every level.

Cells: cacheless M on MUL_DSP 0 and 1, cacheless Zifencei, and the cached
build (CACHE_EN=1) on M and Zifencei.  On the cached build a store sits in
amber until written back, so the TB cleans amber after the tohost store
(ArchSysTB) before it reads the signature from memory.
"""

import os
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
_ARCH_DIR = str(Path(__file__).resolve().parents[3] / "common-rv32i" / "dv" / "arch_test")
if _ARCH_DIR not in sys.path:
    sys.path.insert(0, _ARCH_DIR)

from rv32_arch_test import LINK_BASE, run_tohost                # noqa: E402
from tbclasses.peregrine.peregrine_tb import PeregrineTB      # noqa: E402
from tbclasses.peregrine.peregrine_sys_tb import ArchSysTB    # noqa: E402

MEM_WORDS = 1 << 19          # 2 MiB, as merlin's harness
# Every M test retires a few thousand instructions; at the worst case of
# one 33-cycle stall each, 400k cycles is far above any of them.
MAX_CYCLES = 400_000


@cocotb.test(timeout_time=3000, timeout_unit="sec")
async def cocotb_test_peregrine_arch(dut):
    """All rv32i_m/M arch tests: tohost == 1 + signature == the reference's."""
    repo_root = os.environ.get("REPO_ROOT", str(Path(__file__).resolve().parents[6]))
    level = os.environ.get("TEST_LEVEL", "func")
    dsp = os.environ.get("MUL_DSP", "0")
    ext = os.environ.get("ARCH_EXT", "M")
    cached = os.environ.get("CACHE_EN", "0") == "1"
    tag = f"{ext}_dsp{dsp}" + ("_cached" if cached else "")
    work_dir = Path(os.path.dirname(os.environ.get("LOG_PATH", "."))) / f"arch_test_{tag}_{level}"
    tb = (ArchSysTB if cached else PeregrineTB)(dut, reset_addr=LINK_BASE)
    if cached:
        tb.start_dport_monitor()
    core = f"peregrine_dsp{dsp}" + ("_cached" if cached else "")
    await run_tohost(dut, tb, core, repo_root, level, work_dir,
                     MEM_WORDS, MAX_CYCLES, ext=ext)
    if cached:
        tb.check_dport()


# (CACHE_EN, extension, MUL_DSP).  The cacheless Zifencei cell needs
# fence.i's redirect at CACHE_EN=0 (owner 2026-11-25): as the stage-3 no-op,
# instructions already in the pipeline behind it ran stale and Fencei failed
# 2 of 6 signature words (measured 2026-11-24).
CELLS = [(0, "M", 0), (0, "M", 1), (0, "Zifencei", 0),
         (1, "M", 0), (1, "Zifencei", 0)]


def _cell_name(cache_en, ext, mul_dsp):
    # The cacheless M cells keep their stage-2 names.
    if cache_en == 0 and ext == "M":
        return f"dsp{mul_dsp}"
    return f"{ext.lower()}_dsp{mul_dsp}" + ("_cached" if cache_en else "")


@pytest.mark.parametrize("cache_en, ext, mul_dsp", CELLS,
                         ids=[_cell_name(*c) for c in CELLS])
@pytest.mark.parametrize("test_level, description",
                         [(lvl, f"peregrine_arch {lvl}") for lvl in reg_level_grid()])
def test_peregrine_arch(request, test_level, description, cache_en, ext, mul_dsp):
    """Pytest wrapper: one Verilator build per (level, cell)."""
    module, repo_root, tests_dir, log_dir, _ = get_paths({})
    name = f"cocotb_test_peregrine_arch_{_cell_name(cache_en, ext, mul_dsp)}_{test_level}"
    log_path = os.path.join(log_dir, f"{name}.log")
    sim_build = sim_build_path(tests_dir, name)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)
    tb_top = "peregrine_sys_tb_top" if cache_en else "peregrine_tb_top"
    filelist = "peregrine_sys_tb.f" if cache_en else "peregrine_tb.f"
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path=f"projects/components/riscv-ip/peregrine-rv32im/dv/filelists/{filelist}",
    )
    run(
        python_search=[tests_dir],
        verilog_sources=verilog_sources,
        includes=includes,
        toplevel=tb_top,
        module=module,
        testcase="cocotb_test_peregrine_arch",
        sim_build=sim_build,
        extra_env={
            "DUT": tb_top,
            "LOG_PATH": log_path,
            "MUL_DSP": str(mul_dsp),
            "ARCH_EXT": ext,
            "CACHE_EN": str(cache_en),
            "COCOTB_LOG_LEVEL": "INFO",
            "COCOTB_RESULTS_FILE": os.path.join(log_dir, f"results_{name}.xml"),
            **level_env(test_level),
        },
        parameters={"RESET_ADDR": str(LINK_BASE), "MEM_WORDS": str(MEM_WORDS),
                    "MUL_DSP": str(mul_dsp),
                    # cached build only: amber's held response word is noise
                    # outside its valid (TASK-001 stage 7)
                    **({"RSP_SCRAMBLE": "1"} if cache_en else {})},
        waves=bool(int(os.environ.get("WAVES", "0"))),
        keep_files=True,
        compile_args=["--timescale", "1ns/1ps",
                      "-Wno-WIDTHTRUNC", "-Wno-WIDTHEXPAND"],
    )
