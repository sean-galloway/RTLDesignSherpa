# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: test_peregrine_irq
# Purpose: Machine-interrupt directed test for peregrine_core: masking by
#          mstatus.MIE, MEI > MSI > MTI priority, and precise interrupts
#          landing on loads, stores, load-use pairs and taken branches.
#          The program (programs/irq_basic.s) is self-checking; the TB is
#          the interrupt source.  func adds random mem_wait pulses.
#
# Documentation: projects/components/riscv-ip/peregrine-rv32im/PRD.md
# Subsystem: riscv-ip/peregrine-rv32im
#
# Author: sean galloway
# Created: 2026-11-23

"""peregrine interrupt directed test (TASK-001 stage 1).

The TB drives irq_software / irq_timer / irq_external from the last value
the program stores to ``irq_ctrl`` (bits 0/1/2).  Bit 3 is an auto timer:
while set, the TB re-raises MTIP a random 11-37 cycles (seeded) after each
store that clears bit 1, so timer interrupts land at many different
pipeline states.  spike cannot model the asynchronous pins, so the checks are the
program's own (exact sums, the mcause log) plus the RVFI trap-beat rules.
"""

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

from tbclasses.peregrine.battery import LINK_BASE, elf_image, read_elf32  # noqa: E402
from tbclasses.peregrine.peregrine_tb import PeregrineTB                 # noqa: E402

PROGRAM = Path(__file__).resolve().parent / "programs" / "irq_basic.s"
TOOLCHAIN = os.environ.get("RISCV_TOOLCHAIN", "/mnt/data/tools/xpack-riscv-none-elf-gcc/bin")
AUTO_PERIOD_MIN = 11   # re-raise delay range: varies the loop phase the
AUTO_PERIOD_MAX = 37   # interrupt lands on (a fixed delay always hits one)
MEM_WAIT_PERCENT = 10


def build_elf(work_dir: Path) -> Path:
    """Assemble and link irq_basic.s at LINK_BASE."""
    work_dir.mkdir(parents=True, exist_ok=True)
    obj = work_dir / "irq_basic.o"
    elf = work_dir / "irq_basic.elf"
    subprocess.run([f"{TOOLCHAIN}/riscv-none-elf-as", "-march=rv32i_zicsr",
                    "-mabi=ilp32", str(PROGRAM), "-o", str(obj)], check=True)
    # --no-relax: relaxation turns `la` into gp-relative addressing, and
    # this program uses gp as the test number (riscv-tests convention).
    subprocess.run([f"{TOOLCHAIN}/riscv-none-elf-ld", "--no-relax",
                    f"-Ttext=0x{LINK_BASE:x}",
                    str(obj), "-o", str(elf)], check=True)
    return elf


class IrqSource:
    """The TB's interrupt source, driven by stores to irq_ctrl.

    Called in the ReadOnly phase; the TB applies the returned pins from the
    next falling edge, so they are registered like a real CLINT.  (Raising
    a pin in the same cycle as the store that requested it would interrupt
    that store while it is still in MEM.)
    """

    def __init__(self, ctrl_addr: int, rng: random.Random) -> None:
        self.ctrl_addr = ctrl_addr
        self.rng = rng
        self.ctrl = 0
        self.raise_mti_at = None
        self.interrupts_raised = 0

    def __call__(self, dut, cycle, trace):
        if int(dut.dmem_req.value) and int(dut.dmem_wstrb.value) == 0xF and \
                int(dut.dmem_addr.value) == self.ctrl_addr:
            value = int(dut.dmem_wdata.value)
            if (value & 8) and (self.ctrl & 2) and not (value & 2):
                self.raise_mti_at = cycle + self.rng.randint(AUTO_PERIOD_MIN,
                                                              AUTO_PERIOD_MAX)
            if not (value & 8):
                self.raise_mti_at = None
            self.ctrl = value
        if self.raise_mti_at is not None and cycle >= self.raise_mti_at:
            self.ctrl |= 2
            self.raise_mti_at = None
            self.interrupts_raised += 1
        return (self.ctrl & 1, (self.ctrl >> 1) & 1, (self.ctrl >> 2) & 1)


@cocotb.test(timeout_time=200, timeout_unit="ms")
async def cocotb_test_peregrine_irq(dut):
    """irq_basic.s: masking, priority, precise interrupts under load."""
    level = os.environ.get("TEST_LEVEL", "gate")
    # Per level: parallel cells must not assemble into the same files.
    work_dir = Path(os.path.dirname(os.environ.get("LOG_PATH", "."))) / f"irq_{level}"
    elf = build_elf(work_dir)
    _, symbols = read_elf32(elf)

    tb = PeregrineTB(dut, reset_addr=LINK_BASE)
    await tb.ensure_clock()
    seed = int(os.environ.get("RDS_SEED_BASE", "1"))
    rng = random.Random(seed)
    variants = [(f"no mem_wait (seed {seed})", None)]
    if level != "gate":
        variants.append((f"random mem_wait {MEM_WAIT_PERCENT}% (seed {seed})",
                         lambda d, c: rng.randrange(100) < MEM_WAIT_PERCENT))

    for label, mem_wait in variants:
        source = IrqSource(symbols["irq_ctrl"], rng)
        await tb.assert_reset()
        await tb.backdoor_load(elf_image(elf))
        await tb.release_reset()
        value = await tb.run_to_tohost(symbols["tohost"], max_cycles=50_000,
                                       irq_driver=source,
                                       mem_wait_driver=mem_wait)
        irq_beats = [b for b in tb.trace if b["trap"] and (b["trap_cause"] >> 31)]
        on_mem = sum(1 for b in irq_beats if b["insn"] & 0x5F == 0x03)  # load/store opcodes
        dut._log.info(f"{label}: tohost={value:#x} beats={len(tb.trace)} "
                      f"interrupts taken={len(irq_beats)} (on a load/store: {on_mem}) "
                      f"timer re-raises={source.interrupts_raised}")
        assert value == 1, f"{label}: program failed test {value >> 1}"
        tb.check_order_sequence()
        tb.check_x0_rd_zero()
        tb.check_trap_beats()
        tb.check_mem_side_effects()
        # Every interrupt beat is a real instruction that did not execute:
        # the handler's mret must return to that same pc.
        for k, b in enumerate(tb.trace):
            if b["trap"] and (b["trap_cause"] >> 31):
                assert any(nb["pc"] == b["pc"] and not nb["trap"]
                           for nb in tb.trace[k + 1:]), \
                    f"{label}: interrupted pc 0x{b['pc']:x} never re-executed"
        assert len(irq_beats) >= 8, f"{label}: only {len(irq_beats)} interrupts taken"
        assert on_mem >= 4, f"{label}: only {on_mem} interrupts landed on a load/store"


@pytest.mark.parametrize("test_level, description",
                         [(lvl, f"peregrine_irq {lvl}") for lvl in reg_level_grid()])
def test_peregrine_irq(request, test_level, description):
    """Pytest wrapper: one Verilator build per level."""
    module, repo_root, tests_dir, log_dir, _ = get_paths({})
    name = f"cocotb_test_peregrine_irq_{test_level}"
    log_path = os.path.join(log_dir, f"{name}.log")
    sim_build = sim_build_path(tests_dir, name)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path="projects/components/riscv-ip/peregrine-rv32im/dv/filelists/peregrine_tb.f",
    )
    run(
        python_search=[tests_dir],
        verilog_sources=verilog_sources,
        includes=includes,
        toplevel="peregrine_tb_top",
        module=module,
        testcase="cocotb_test_peregrine_irq",
        sim_build=sim_build,
        extra_env={
            "DUT": "peregrine_tb_top",
            "LOG_PATH": log_path,
            "COCOTB_LOG_LEVEL": "INFO",
            "COCOTB_RESULTS_FILE": os.path.join(log_dir, f"results_{name}.xml"),
            **level_env(test_level),
        },
        parameters={"RESET_ADDR": str(LINK_BASE)},
        waves=bool(int(os.environ.get("WAVES", "0"))),
        keep_files=True,
        compile_args=["--trace", "--trace-structs", "--timescale", "1ns/1ps",
                      "-Wno-WIDTHTRUNC", "-Wno-WIDTHEXPAND"],
    )
