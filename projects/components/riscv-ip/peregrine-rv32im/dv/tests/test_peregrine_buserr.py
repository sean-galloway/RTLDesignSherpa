# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: test_peregrine_buserr
# Purpose: Bus-error handling on the cached peregrine (riscv-ip/
#          peregrine-rv32im TASK-005): load / store access faults from the
#          uncached port and amber's fills, instruction access faults from
#          the I$, and the imprecise write-back error report (platform
#          interrupt 16 and mbuserr), on peregrine_sys_tb_top's error
#          windows.
#
# Documentation: projects/components/riscv-ip/peregrine-rv32im/PRD.md
# Subsystem: riscv-ip/peregrine-rv32im
#
# Author: sean galloway
# Created: 2026-11-27

"""peregrine bus errors (TASK-005).

Two programs, each self-checking (tohost = 1), on the cached build:

* ``buserr_sync.s`` -- every synchronous source: uncached load and store,
  amber load and store fills, I$ fills.  Checked by the program (each
  handler entry's mcause, mepc and mtval; rd untouched; the instructions
  behind a fault run once), by the RVFI trace rules (the memory-request
  count includes the faulting accesses, nothing more), by the shadow
  trap-CSR model (every handler read of mcause / mepc / mtval), per source
  counts, and from func level by spike lockstep (spike maps none of the
  error windows, so it takes the same faults; the lockstep also locks each
  access fault's tval).
* ``buserr_wb.s`` -- the failed write-back of a dirty line: interrupt 16,
  mbuserr's address / overflow / valid, its clear, mie.16 masking, the line
  dropped.  spike has no mbuserr, so no lockstep: the program, the trace
  rules and the shadow model check it.

Levels: gate runs both programs without stalls; func and full add a run
under random memory stalls (seeded, RDS_SEED_BASE).
"""

import os
import random
import subprocess
import sys
from pathlib import Path

import cocotb
import pytest
from cocotb.triggers import FallingEdge, ReadOnly
from cocotb_test.simulator import run

from TBClasses.shared.filelist_utils import get_sources_from_filelist
from TBClasses.shared.test_levels import level_env, reg_level_grid
from TBClasses.shared.utilities import get_paths, sim_build_path

_DV_DIR = str(Path(__file__).resolve().parents[1])
if _DV_DIR not in sys.path:
    sys.path.insert(0, _DV_DIR)

from tbclasses.peregrine.battery import (LINK_BASE, elf_image,             # noqa: E402
                                         expected_tval, lockstep,
                                         parse_spike_log, read_elf32,
                                         run_spike)
from tbclasses.peregrine.csr_shadow import TrapCsrShadow                  # noqa: E402
from tbclasses.peregrine.peregrine_sys_tb import PeregrineSysTB           # noqa: E402
from test_peregrine_sys import PROGRAMS, STALL_PERCENT, TOOLCHAIN       # noqa: E402

SPIKE_ISA = "rv32im_zicsr_zifencei"
IRQ_BUSERR = 0x8000_0010

# buserr_sync.s: the traps each source must produce (cause, window) -> n.
# window: "uc" uncached, "dc" amber, "if" a fetch.
SYNC_TRAPS = {(5, "uc"): 7, (7, "uc"): 1, (5, "dc"): 6, (7, "dc"): 2,
              (1, "if"): 4}


def _build(src: Path, work: Path) -> Path:
    """Assemble and link at LINK_BASE; -N keeps the first PT_LOAD at
    LINK_BASE, where spike's RAM starts (handbook precise-trap-checks)."""
    work.mkdir(parents=True, exist_ok=True)
    obj = work / (src.stem + ".o")
    elf = work / (src.stem + ".elf")
    subprocess.run([f"{TOOLCHAIN}/riscv-none-elf-as", "-march=rv32i_zicsr_zifencei",
                    "-mabi=ilp32", str(src), "-o", str(obj)], check=True)
    subprocess.run([f"{TOOLCHAIN}/riscv-none-elf-ld", "--no-relax", "-N",
                    f"-Ttext=0x{LINK_BASE:x}", str(obj), "-o", str(elf)], check=True)
    return elf


def _seed() -> int:
    return int(os.environ.get("RDS_SEED_BASE", "1"))


def _window(beat: dict) -> str:
    cause = beat["trap_cause"]
    if cause == 1:
        return "if"
    return "uc" if (expected_tval(beat) >> 28) == 0x1 else "dc"


class _FaultPaths:
    """Count the wrapper's error captures by path, sampled every cycle:
    WB's response captured as an error (r_have_err), and MEM's -- an access
    accepted under an I$ hold whose error response was parked
    (r_mem_err)."""

    def __init__(self, dut) -> None:
        self.dut = dut
        self.wb = 0
        self.mem = 0
        self._prev = (0, 0)
        cocotb.start_soon(self._run())

    async def _run(self) -> None:
        top = self.dut.u_top
        while True:
            await FallingEdge(self.dut.clk)
            await ReadOnly()
            now = (int(top.r_have_err.value), int(top.r_mem_err.value))
            self.wb += int(now[0] and not self._prev[0])
            self.mem += int(now[1] and not self._prev[1])
            self._prev = now


async def _run_program(dut, name: str, lock: bool):
    level = os.environ.get("TEST_LEVEL", "gate")
    work = Path(os.path.dirname(os.environ.get("LOG_PATH", "."))) / f"buserr_{name}_{level}"
    elf = _build(PROGRAMS / f"{name}.s", work)
    entry, symbols = read_elf32(elf)
    tb = PeregrineSysTB(dut, reset_addr=LINK_BASE)
    await tb.ensure_clock()
    tb.start_dport_monitor()
    paths = _FaultPaths(dut)
    rng = random.Random(_seed())
    variants = [("no stalls", None)]
    if level != "gate":
        variants.append((f"random memory stalls {STALL_PERCENT}% (seed {_seed()})",
                         lambda d, c: rng.randrange(100) < STALL_PERCENT))
    results = []
    for label, stall in variants:
        await tb.assert_reset()
        await tb.backdoor_load(elf_image(elf))
        await tb.release_reset()
        value = await tb.run_to_tohost(symbols["tohost"], max_cycles=200_000,
                                       mem_wait_driver=stall)
        trace = list(tb.trace)
        dut._log.info(f"{name} {label}: tohost={value:#x} beats={len(trace)} "
                      f"traps={sum(b['trap'] for b in trace)} "
                      f"cycles={trace[-1]['cycle'] if trace else 0}")
        assert value == 1, f"{name} {label}: program failed test {value >> 1}"
        tb.check_order_sequence()
        tb.check_x0_rd_zero()
        tb.check_trap_beats()
        tb.check_mem_side_effects()
        tb.check_dport()
        shadow = TrapCsrShadow().check(trace)
        dut._log.info(f"{name} {label}: shadow trap CSRs {shadow}")
        assert shadow["mcause_reads"] and shadow["mepc_reads"], \
            f"{name} {label}: the shadow model checked no handler read"
        if lock and label == "no stalls" and level != "gate":
            log_path = work / f"spike_{name}.log"
            rc = run_spike(SPIKE_ISA, elf, log_path)
            assert rc == 0, f"spike rc={rc} on {name}"
            errors = lockstep(trace, entry, parse_spike_log(log_path))
            assert not errors, "lockstep: " + "; ".join(errors)
            dut._log.info(f"{name}: spike lockstep ok ({len(trace)} beats)")
        results.append((label, trace))
    dut._log.info(f"{name}: error captures for WB {paths.wb}, parked for MEM "
                  f"{paths.mem}")
    return results, paths


@cocotb.test(timeout_time=600, timeout_unit="ms")
async def cocotb_test_peregrine_buserr_sync(dut):
    """buserr_sync.s: access faults from every synchronous source."""
    results, paths = await _run_program(dut, "buserr_sync", lock=True)
    for label, trace in results:
        got = {}
        for b in trace:
            if b["trap"]:
                assert b["trap_cause"] in (1, 5, 7), \
                    f"{label}: unexpected trap cause {b['trap_cause']:#x}"
                key = (b["trap_cause"], _window(b))
                got[key] = got.get(key, 0) + 1
        assert got == SYNC_TRAPS, f"{label}: traps by source {got}, want {SYNC_TRAPS}"
        ifetch = [b for b in trace if b["trap"] and b["trap_cause"] == 1]
        assert all(b["insn"] == 0 for b in ifetch), \
            f"{label}: a fetch-fault beat reports an instruction word"
    assert paths.mem >= 1, "no error response was parked for MEM (test 8 missed the I$ hold)"


@cocotb.test(timeout_time=600, timeout_unit="ms")
async def cocotb_test_peregrine_buserr_wb(dut):
    """buserr_wb.s: a failed dirty write-back as interrupt 16 + mbuserr."""
    results, _ = await _run_program(dut, "buserr_wb", lock=False)
    for label, trace in results:
        irqs = [b for b in trace if b["trap"]]
        assert all(b["trap_cause"] == IRQ_BUSERR for b in irqs), \
            f"{label}: traps {[hex(b['trap_cause']) for b in irqs]}"
        assert len(irqs) == 3, f"{label}: {len(irqs)} write-back error interrupts, want 3"
        for k, b in enumerate(trace):
            if b["trap"]:
                assert any(nb["pc"] == b["pc"] and not nb["trap"] for nb in trace[k + 1:]), \
                    f"{label}: interrupted pc 0x{b['pc']:x} never re-executed"


CASES = ["cocotb_test_peregrine_buserr_sync", "cocotb_test_peregrine_buserr_wb"]


@pytest.mark.parametrize("test_level, description",
                         [(lvl, f"peregrine_buserr {lvl}") for lvl in reg_level_grid()])
@pytest.mark.parametrize("cocotb_testcase", CASES)
def test_peregrine_buserr(request, cocotb_testcase, test_level, description):
    """Pytest wrapper: one Verilator build per (case, level) cell."""
    module, repo_root, tests_dir, log_dir, _ = get_paths({})
    name = f"{cocotb_testcase}_{test_level}"
    log_path = os.path.join(log_dir, f"{name}.log")
    sim_build = sim_build_path(tests_dir, name)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path="projects/components/riscv-ip/peregrine-rv32im/dv/filelists/peregrine_sys_tb.f",
    )
    run(
        python_search=[tests_dir],
        verilog_sources=verilog_sources,
        includes=includes,
        toplevel="peregrine_sys_tb_top",
        module=module,
        testcase=cocotb_testcase,
        sim_build=sim_build,
        extra_env={
            "DUT": "peregrine_sys_tb_top",
            "LOG_PATH": log_path,
            "COCOTB_LOG_LEVEL": "INFO",
            "COCOTB_RESULTS_FILE": os.path.join(log_dir, f"results_{name}.xml"),
            **level_env(test_level),
        },
        parameters={"RESET_ADDR": str(LINK_BASE), "MEM_WORDS": str(1 << 18),
                    "RSP_SCRAMBLE": "1"},
        waves=bool(int(os.environ.get("WAVES", "0"))),
        keep_files=True,
        compile_args=["--trace", "--trace-structs", "--timescale", "1ns/1ps",
                      "-Wno-WIDTHTRUNC", "-Wno-WIDTHEXPAND"],
    )
