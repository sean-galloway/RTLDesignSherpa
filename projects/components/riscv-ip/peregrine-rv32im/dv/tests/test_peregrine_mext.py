# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: test_peregrine_mext
# Purpose: Core-level M-extension stress test for peregrine_core: seeded
#          generated programs of hazard shapes around M instructions
#          (dependent and independent pairs, ALU / branch / store consumers,
#          a load into an M operand, rd = x0, a taken jump's shadow, an
#          ecall trapping in MEM while an M instruction is in EX), checked
#          three ways: the program's own register compare, an RVFI
#          shadow-regfile check of every operand and every M result, and
#          (without interrupts) spike lockstep.  Interrupt variants raise
#          the machine timer at random, faster than the M unit's latency,
#          so interrupts go pending while M instructions run: none may be
#          taken on an M instruction, and every one must still retire.
#
# Documentation: projects/components/riscv-ip/peregrine-rv32im/PRD.md
# Subsystem: riscv-ip/peregrine-rv32im
#
# Author: sean galloway
# Created: 2026-11-23

"""peregrine M-extension directed stress (TASK-001 stage 2).

Variants per build (MUL_DSP 0 and 1):

* ``lockstep``: no interrupts; the trace is locked against spike's.
* ``irq``: the machine timer re-raises 3-40 cycles (seeded) after each
  acknowledge -- often faster than an M instruction's 33 stall cycles, which
  livelocked the first build (an M instruction interrupted in MEM is
  discarded and restarts; it is now not interruptible).
* ``irq+mem_wait`` (func and full): the same with 10 % random mem_wait.

The cycle count and CPI of the lockstep variant are logged for the PRD P8
comparison (iterative against DSP multiply).
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

from tbclasses.peregrine.battery import (LINK_BASE, elf_image, lockstep,  # noqa: E402
                                         parse_spike_log, read_elf32, run_spike)
from tbclasses.peregrine.mext_program import (generate, is_m_insn,  # noqa: E402
                                              shadow_check)
from tbclasses.peregrine.peregrine_tb import PeregrineTB  # noqa: E402

TOOLCHAIN = os.environ.get("RISCV_TOOLCHAIN", "/mnt/data/tools/xpack-riscv-none-elf-gcc/bin")
SPIKE_ISA = "rv32im_zicsr_zifencei"
BLOCKS = {"gate": 60, "func": 400, "full": 2000}
CYCLES_PER_BLOCK = 160
IRQ_DELAY_MIN = 3
IRQ_DELAY_MAX = 40
MEM_WAIT_PERCENT = 10


def build_elf(source: str, work_dir: Path) -> Path:
    """Assemble and link a generated program at LINK_BASE."""
    work_dir.mkdir(parents=True, exist_ok=True)
    asm = work_dir / "mext.s"
    obj = work_dir / "mext.o"
    elf = work_dir / "mext.elf"
    asm.write_text(source)
    subprocess.run([f"{TOOLCHAIN}/riscv-none-elf-as", "-march=rv32im_zicsr",
                    "-mabi=ilp32", str(asm), "-o", str(obj)], check=True)
    # -N: one segment at the link address.  Without it ld page-aligns the
    # text segment and folds the ELF headers into it, starting the first
    # PT_LOAD at LINK_BASE - 0x1000, which spike refuses to load (its RAM
    # begins at LINK_BASE; the TB's aliasing memory hides it).
    subprocess.run([f"{TOOLCHAIN}/riscv-none-elf-ld", "--no-relax", "-N",
                    f"-Ttext=0x{LINK_BASE:x}", str(obj), "-o", str(elf)], check=True)
    return elf


class TimerSource:
    """Machine timer that re-raises a random delay after each acknowledge.

    Called in the ReadOnly phase; the TB applies the pins from the next
    falling edge (registered, like a CLINT).
    """

    def __init__(self, ack_addr: int, rng: random.Random) -> None:
        self.ack_addr = ack_addr
        self.rng = rng
        self.mtip = 0
        self.raise_at = rng.randint(IRQ_DELAY_MIN, IRQ_DELAY_MAX)
        self.raised = 0

    def __call__(self, dut, cycle, trace):
        if int(dut.dmem_req.value) and int(dut.dmem_wstrb.value) and \
                int(dut.dmem_addr.value) == self.ack_addr:
            self.mtip = 0
            self.raise_at = cycle + self.rng.randint(IRQ_DELAY_MIN, IRQ_DELAY_MAX)
        if not self.mtip and self.raise_at is not None and cycle >= self.raise_at:
            self.mtip = 1
            self.raise_at = None
            self.raised += 1
        return (0, self.mtip, 0)


def _common_checks(tb, label):
    tb.check_order_sequence()
    tb.check_x0_rd_zero()
    tb.check_trap_beats()
    tb.check_mem_side_effects()
    counts = shadow_check(tb.trace)
    # Every interrupted instruction executes later.  "Executes" includes an
    # exception (an interrupted ecall re-executes as an ecall trap); only
    # another interrupt at the same pc does not count.
    for k, b in enumerate(tb.trace):
        if b["trap"] and (b["trap_cause"] >> 31):
            assert any(nb["pc"] == b["pc"] and not (nb["trap"] and nb["trap_cause"] >> 31)
                       for nb in tb.trace[k + 1:]), \
                f"{label}: interrupted pc 0x{b['pc']:x} never re-executed"
    return counts


@cocotb.test(timeout_time=3000, timeout_unit="ms")
async def cocotb_test_peregrine_mext(dut):
    """Generated M hazard programs: register compare, RVFI shadow, lockstep, irqs."""
    level = os.environ.get("TEST_LEVEL", "gate")
    mul_dsp = os.environ.get("MUL_DSP", "0")
    seed = int(os.environ.get("SEED", "1"))
    work_dir = Path(os.path.dirname(os.environ.get("LOG_PATH", "."))) / f"mext_dsp{mul_dsp}_{level}"
    program = generate(seed, BLOCKS[level])
    elf = build_elf(program.text, work_dir)
    entry, symbols = read_elf32(elf)
    image = elf_image(elf)
    max_cycles = CYCLES_PER_BLOCK * BLOCKS[level] + 5000
    dut._log.info(f"mext (MUL_DSP={mul_dsp}, {level}, seed {seed}): "
                  f"{BLOCKS[level]} blocks, {program.m_count} M instructions, "
                  f"shapes {program.shapes}")

    tb = PeregrineTB(dut, reset_addr=LINK_BASE)
    await tb.ensure_clock()
    rng = random.Random(seed)

    variants = [("lockstep", False, None), ("irq", True, None)]
    if level != "gate":
        variants.append(("irq+mem_wait", True,
                         lambda d, c: rng.randrange(100) < MEM_WAIT_PERCENT))

    for label, irqs, mem_wait in variants:
        words = dict(image)
        words[symbols["irq_enable"] >> 2] = 1 if irqs else 0
        source = TimerSource(symbols["irq_ack"], rng) if irqs else None
        await tb.assert_reset()
        await tb.backdoor_load(words)
        await tb.release_reset()
        try:
            value = await tb.run_to_tohost(symbols["tohost"], max_cycles=max_cycles,
                                           irq_driver=source, mem_wait_driver=mem_wait)
        except AssertionError:
            for b in tb.trace[-16:]:
                dut._log.error(f"{label}: cycle {b['cycle']} pc=0x{b['pc']:08x} "
                               f"insn=0x{b['insn']:08x} trap={b['trap']} "
                               f"cause=0x{b['trap_cause']:x} -> 0x{b['pc_wdata']:08x}")
            raise
        assert value == 1, (f"{label}: register x{value >> 1} differs from the "
                            f"generator's model")
        counts = _common_checks(tb, label)
        retired = len(tb.trace)
        cycles = tb.trace[-1]["cycle"] + 1
        irq_beats = [b for b in tb.trace if b["trap"] and (b["trap_cause"] >> 31)]
        on_m = sum(1 for b in irq_beats if is_m_insn(b["insn"]))
        # An interrupt pending while an M instruction runs is taken on the
        # instruction after it (the M instruction is not interruptible).
        after_m = sum(1 for k, b in enumerate(tb.trace)
                      if k and b["trap"] and (b["trap_cause"] >> 31)
                      and is_m_insn(tb.trace[k - 1]["insn"]) and not tb.trace[k - 1]["trap"])
        ecalls = sum(1 for b in tb.trace if b["trap"] and b["trap_cause"] == 11)
        dut._log.info(f"{label}: {retired} retired in {cycles} cycles "
                      f"(CPI {cycles / retired:.3f}); {counts['operands']} operands and "
                      f"{counts['m_results']} M results checked against the RVFI "
                      f"shadow; ecall traps {ecalls}; interrupts {len(irq_beats)} "
                      f"(on an M instruction: {on_m}, on the instruction after one: {after_m})")
        assert counts["m_results"] >= program.m_count // 2, \
            f"{label}: only {counts['m_results']} M results checked"
        if label == "lockstep":
            log_path = work_dir / "spike_mext.log"
            rc = run_spike(SPIKE_ISA, elf, log_path)
            assert rc == 0, f"spike rc={rc} on the generated program"
            errors = lockstep(tb.trace, entry, parse_spike_log(log_path))
            assert not errors, "lockstep: " + "; ".join(errors)
        else:
            assert len(irq_beats) >= 8, f"{label}: only {len(irq_beats)} interrupts"
            assert on_m == 0, f"{label}: {on_m} interrupts taken on an M instruction"
            if level != "gate":
                assert after_m >= 3, (f"{label}: only {after_m} interrupts taken "
                                      f"right after an M instruction")


@pytest.mark.parametrize("mul_dsp", [0, 1])
@pytest.mark.parametrize("test_level, description",
                         [(lvl, f"peregrine_mext {lvl}") for lvl in reg_level_grid()])
def test_peregrine_mext(request, test_level, description, mul_dsp):
    """Pytest wrapper: one Verilator build per (level, MUL_DSP) cell."""
    module, repo_root, tests_dir, log_dir, _ = get_paths({})
    name = f"cocotb_test_peregrine_mext_dsp{mul_dsp}_{test_level}"
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
        testcase="cocotb_test_peregrine_mext",
        sim_build=sim_build,
        extra_env={
            "DUT": "peregrine_tb_top",
            "LOG_PATH": log_path,
            "MUL_DSP": str(mul_dsp),
            "COCOTB_LOG_LEVEL": "INFO",
            "COCOTB_RESULTS_FILE": os.path.join(log_dir, f"results_{name}.xml"),
            **level_env(test_level),
        },
        parameters={"RESET_ADDR": str(LINK_BASE), "MUL_DSP": str(mul_dsp)},
        waves=bool(int(os.environ.get("WAVES", "0"))),
        keep_files=True,
        compile_args=["--trace", "--trace-structs", "--timescale", "1ns/1ps",
                      "-Wno-WIDTHTRUNC", "-Wno-WIDTHEXPAND"],
    )
