# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: test_peregrine_sys
# Purpose: The cached peregrine (peregrine_top: I$, amber D$, CLINT,
#          uncached port, AXI4 arbiter) on a behavioral AXI4 memory
#          (peregrine_sys_tb_top).  TASK-001 stage 4.  Runs the riscv-tests
#          batteries (rv32ui includes fence_i), the pin-driven interrupt
#          suite (irq_basic.s, interrupts landing on loads and stores under
#          the D-side handshake), the CLINT / fence.i directed program
#          (clint_basic.s) and self-modifying code through the write-back
#          D$ (smc_basic.s), each with and without random memory stalls.
#
# Documentation: projects/components/riscv-ip/peregrine-rv32im/PRD.md
# Subsystem: riscv-ip/peregrine-rv32im
#
# Author: sean galloway
# Created: 2026-11-24

"""peregrine cached build (TASK-001 stage 4).

Levels:
  gate -- rv32ui simple/add/lw/sw/fence_i, rv32um mul/div, rv32mi csr/scall,
          irq_basic, clint_basic and smc_basic without stalls
  func -- every rv32ui / rv32um / rv32mi image with spike lockstep; the
          interrupt, CLINT and SMC programs also under random memory stalls
  full -- func, with the stall soak repeated on more images
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

from tbclasses.peregrine.battery import (LINK_BASE, Battery, discover,  # noqa: E402
                                         elf_image, read_elf32)
from tbclasses.peregrine.peregrine_sys_tb import PeregrineSysTB                  # noqa: E402

TOOLCHAIN = os.environ.get("RISCV_TOOLCHAIN", "/mnt/data/tools/xpack-riscv-none-elf-gcc/bin")
PROGRAMS = Path(__file__).resolve().parent / "programs"
SUITES = {"rv32ui": "rv32im_zicsr_zifencei",
          "rv32mi": "rv32im_zicsr_zifencei",
          "rv32um": "rv32im_zicsr_zifencei"}
SYS_GATE = {"rv32ui": ("simple", "add", "lw", "sw", "fence_i"),
            "rv32um": ("mul", "div"),
            "rv32mi": ("csr", "scall")}
STALL_PERCENT = 15
STALL_IMAGES = {"func": ("fence_i", "lw", "sw", "lbu", "sh", "jal"),
                "full": ("fence_i", "lw", "sw", "lbu", "lhu", "sb", "sh", "jal",
                         "jalr", "beq", "bne", "lui", "auipc", "addi")}


def _seed() -> int:
    return int(os.environ.get("RDS_SEED_BASE", "1"))


class SysBattery(Battery):
    """The house battery, with the cached build's gate subset, or an
    explicit image list (``only``)."""

    def __init__(self, *args, only=None, **kwargs) -> None:
        super().__init__(*args, **kwargs)
        self.only = only

    def names(self) -> list:
        keep = self.only if self.only is not None else (
            SYS_GATE.get(self.suite, ()) if self.level == "gate" else None)
        names = discover(self.repo_root, self.suite)
        return names if keep is None else [n for n in names if n in keep]


class _StallRun:
    """Wrap tb.run_to_tohost to stall the memory at random."""

    def __init__(self, tb, rng, percent):
        self._inner = tb.run_to_tohost
        self._rng = rng
        self._percent = percent

    async def __call__(self, tohost, max_cycles=100_000, irq_driver=None,
                       mem_wait_driver=None):
        rng, pct = self._rng, self._percent
        return await self._inner(tohost, max_cycles=max_cycles * 2,
                                 irq_driver=irq_driver,
                                 mem_wait_driver=lambda d, c: rng.randrange(100) < pct)


async def _battery(dut, suite):
    repo_root = os.environ.get("REPO_ROOT", str(Path(__file__).resolve().parents[6]))
    level = os.environ.get("TEST_LEVEL", "func")
    work = Path(os.path.dirname(os.environ.get("LOG_PATH", "."))) / f"sys_{suite}_battery_{level}"
    tb = PeregrineSysTB(dut, reset_addr=LINK_BASE)
    await tb.ensure_clock()
    tb.start_dport_monitor()
    await SysBattery(tb, repo_root, suite, SUITES[suite], level, str(work)).run()
    if level != "gate" and suite == "rv32ui":
        # The stall soak: the same images with random memory stalls.
        rng = random.Random(_seed())
        tb.run_to_tohost = _StallRun(tb, rng, STALL_PERCENT)
        keep = STALL_IMAGES[level]
        # level "gate": tohost and trace checks only; the lockstep ran above.
        stall = SysBattery(tb, repo_root, suite, SUITES[suite], "gate",
                           str(work) + "_stall", only=keep)
        dut._log.info(f"stall soak: {STALL_PERCENT}% memory stalls, seed {_seed()}, "
                      f"images {list(keep)}")
        await stall.run()
    tb.check_dport()
    dut._log.info(f"D-side request contract: {tb.dport_waits} waiting cycles, no violation")


def _build(src: Path, work: Path) -> Path:
    work.mkdir(parents=True, exist_ok=True)
    obj = work / (src.stem + ".o")
    elf = work / (src.stem + ".elf")
    subprocess.run([f"{TOOLCHAIN}/riscv-none-elf-as", "-march=rv32i_zicsr_zifencei",
                    "-mabi=ilp32", str(src), "-o", str(obj)], check=True)
    subprocess.run([f"{TOOLCHAIN}/riscv-none-elf-ld", "--no-relax",
                    f"-Ttext=0x{LINK_BASE:x}", str(obj), "-o", str(elf)], check=True)
    return elf


_LAST_SOURCES: list = []      # the interrupt sources of the last _program run


async def _program(dut, name, irq_source_cls=None):
    level = os.environ.get("TEST_LEVEL", "gate")
    work = Path(os.path.dirname(os.environ.get("LOG_PATH", "."))) / f"sys_{name}_{level}"
    elf = _build(PROGRAMS / f"{name}.s", work)
    _, symbols = read_elf32(elf)
    tb = PeregrineSysTB(dut, reset_addr=LINK_BASE)
    await tb.ensure_clock()
    tb.start_dport_monitor()
    seed = _seed()
    rng = random.Random(seed)
    variants = [("no stalls", None)]
    if level != "gate":
        variants.append((f"random memory stalls {STALL_PERCENT}% (seed {seed})",
                         lambda d, c: rng.randrange(100) < STALL_PERCENT))
    results = []
    _LAST_SOURCES.clear()
    for label, stall in variants:
        source = irq_source_cls(symbols, rng) if irq_source_cls else None
        _LAST_SOURCES.append(source)
        await tb.assert_reset()
        await tb.backdoor_load(elf_image(elf))
        await tb.release_reset()
        value = await tb.run_to_tohost(symbols["tohost"], max_cycles=200_000,
                                       irq_driver=source, mem_wait_driver=stall)
        dut._log.info(f"{name} {label}: tohost={value:#x} beats={len(tb.trace)} "
                      f"cycles={tb.trace[-1]['cycle'] if tb.trace else 0}")
        assert value == 1, f"{name} {label}: program failed test {value >> 1}"
        tb.check_order_sequence()
        tb.check_x0_rd_zero()
        tb.check_trap_beats()
        tb.check_mem_side_effects()
        tb.check_dport()
        results.append((label, tb.trace))
    dut._log.info(f"{name}: D-side request contract held over {tb.dport_waits} waiting cycles")
    return results


@cocotb.test(timeout_time=8000, timeout_unit="ms")
async def cocotb_test_peregrine_sys_rv32ui(dut):
    await _battery(dut, "rv32ui")


@cocotb.test(timeout_time=8000, timeout_unit="ms")
async def cocotb_test_peregrine_sys_rv32um(dut):
    await _battery(dut, "rv32um")


@cocotb.test(timeout_time=8000, timeout_unit="ms")
async def cocotb_test_peregrine_sys_rv32mi(dut):
    await _battery(dut, "rv32mi")


@cocotb.test(timeout_time=400, timeout_unit="ms")
async def cocotb_test_peregrine_sys_clint(dut):
    """clint_basic.s: mtime, timer and software interrupts from the CLINT,
    mip.MTIP, and fence.i over a store to .text."""
    for label, trace in await _program(dut, "clint_basic"):
        irqs = [b for b in trace if b["trap"] and (b["trap_cause"] >> 31)]
        causes = sorted({b["trap_cause"] & 0xFF for b in irqs})
        assert causes == [3, 7], f"{label}: interrupt causes {causes}, want MSI and MTI"
        fencei = [b for b in trace if (b["insn"] & 0x707F) == 0x100F]
        assert fencei, f"{label}: no fence.i retired"


class _IrqPins:
    """irq_basic.s's TB interrupt source (the stage-1 suite's), on the
    cached build: the TB pins are ORed into the CLINT's.

    Aimed at waiting D requests: once the program's auto timer is due, the
    raise is held back until a sample in which a D request is valid and not
    ready (with amber: the load right behind a write hit, which waits out
    the hit's second cycle).  The pin then rises from the next falling
    edge, so the interrupt is pending in the cycle that request's hold
    drops: exactly the cycle the core's interrupt lock covers (measured:
    removing the lock gives 161 dropped requests on irq_lock.s; aiming at
    the store handshake instead caught none).  If no request waits within
    WAIT_AIM_LIMIT cycles the raise goes ahead anyway.
    """

    WAIT_AIM_LIMIT = 400

    def __init__(self, symbols, rng):
        from test_peregrine_irq import IrqSource
        self._ctrl = symbols["irq_ctrl"]
        self._src = IrqSource(self._ctrl, rng)
        self._waited = 0
        self._deadline = None
        self.aimed = 0

    def __call__(self, dut, cycle, trace):
        top = dut.u_top
        waiting = int(top.w_dvalid.value) and not int(top.w_dready.value)
        self._waited = self._waited + 1 if waiting else 0
        due = self._src.raise_mti_at
        if due is not None and cycle >= due:
            if self._deadline is None:
                self._deadline = cycle + self.WAIT_AIM_LIMIT
            aim = self._waited >= 1
            if aim or cycle >= self._deadline:
                self.aimed += int(aim)
                self._deadline = None
            else:
                self._src.raise_mti_at = cycle + 1
        return self._src(dut, cycle, trace)


@cocotb.test(timeout_time=400, timeout_unit="ms")
async def cocotb_test_peregrine_sys_irq(dut):
    """irq_basic.s on the cached build: precise interrupts, including on a
    load or store whose request is waiting for the memory."""
    for label, trace in await _program(dut, "irq_basic", _IrqPins):
        irq_beats = [b for b in trace if b["trap"] and (b["trap_cause"] >> 31)]
        on_mem = sum(1 for b in irq_beats if b["insn"] & 0x5F == 0x03)
        dut._log.info(f"{label}: interrupts {len(irq_beats)}, on a load/store {on_mem}")
        for k, b in enumerate(trace):
            if b["trap"] and (b["trap_cause"] >> 31):
                assert any(nb["pc"] == b["pc"] and not nb["trap"] for nb in trace[k + 1:]), \
                    f"{label}: interrupted pc 0x{b['pc']:x} never re-executed"
        assert len(irq_beats) >= 8, f"{label}: only {len(irq_beats)} interrupts taken"
    dut._log.info("interrupts raised on a waiting D request, per variant: "
                  f"{[src.aimed for src in _LAST_SOURCES]}")


@cocotb.test(timeout_time=400, timeout_unit="ms")
async def cocotb_test_peregrine_sys_irq_lock(dut):
    """irq_lock.s: timer interrupts aimed at loads and stores whose amber
    request is waiting (cold misses): the request must not drop (the
    D-side contract monitor) and the instruction must re-execute."""
    for label, trace in await _program(dut, "irq_lock", _IrqPins):
        irq_beats = [b for b in trace if b["trap"] and (b["trap_cause"] >> 31)]
        on_mem = [b for b in irq_beats if b["insn"] & 0x5F == 0x03]
        dut._log.info(f"{label}: interrupts {len(irq_beats)}, on a load/store {len(on_mem)}")
        for k, b in enumerate(trace):
            if b["trap"] and (b["trap_cause"] >> 31):
                assert any(nb["pc"] == b["pc"] and not nb["trap"] for nb in trace[k + 1:]), \
                    f"{label}: interrupted pc 0x{b['pc']:x} never re-executed"
        # With the lock, an interrupt pending as a waiting load's hold drops
        # is taken on the instruction after it, so on_mem is expected to be
        # small; the checks are the contract monitor and the aimed count.
    aimed = [src.aimed for src in _LAST_SOURCES]
    dut._log.info(f"interrupts raised on a waiting D request, per variant: {aimed}")
    assert all(a >= 4 for a in aimed), \
        f"only {aimed} interrupts landed on a waiting D request; the lock is not exercised"


@cocotb.test(timeout_time=400, timeout_unit="ms")
async def cocotb_test_peregrine_sys_smc(dut):
    """smc_basic.s: code written with stores (dirty in amber) becomes
    fetchable only through fence.i's D$ clean + I$ invalidate; data
    survives a clean; dirty evictions in one set then a clean."""
    for label, trace in await _program(dut, "smc_basic"):
        fencei = [b for b in trace if (b["insn"] & 0x707F) == 0x100F]
        assert len(fencei) == 5, f"{label}: {len(fencei)} fence.i retired, want 5"
        assert not any(b["trap"] for b in trace), f"{label}: a trap was taken"
        # The routine in codebuf ran four times (tests 1, 2 twice, 3).
        rets = [b for b in trace if b["insn"] == 0x00008067]
        assert len(rets) == 4, f"{label}: the patched routine returned {len(rets)} times"


@cocotb.test(timeout_time=400, timeout_unit="ms")
async def cocotb_test_peregrine_sys_io(dut):
    """io_basic.s: the uncached I/O window -- both lanes, every size, the
    D$ bypassed, and a response that arrives while an I$ refill holds the
    core."""
    for label, trace in await _program(dut, "io_basic"):
        assert not any(b["trap"] for b in trace), f"{label}: a trap was taken"
        io = [b for b in trace if (b["mem_rmask"] or b["mem_wmask"])
              and (b["mem_addr"] >> 28) == 0x1]
        # 12 in test 1, 3 in test 2, 3 in test 3
        assert len(io) == 18, f"{label}: {len(io)} I/O-window accesses retired, want 18"


CASES = ["cocotb_test_peregrine_sys_rv32ui", "cocotb_test_peregrine_sys_rv32um",
         "cocotb_test_peregrine_sys_rv32mi", "cocotb_test_peregrine_sys_clint",
         "cocotb_test_peregrine_sys_irq", "cocotb_test_peregrine_sys_smc",
         "cocotb_test_peregrine_sys_io", "cocotb_test_peregrine_sys_irq_lock"]


@pytest.mark.parametrize("test_level, description",
                         [(lvl, f"peregrine_sys {lvl}") for lvl in reg_level_grid()])
@pytest.mark.parametrize("cocotb_testcase", CASES)
def test_peregrine_sys(request, cocotb_testcase, test_level, description):
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
        parameters={"RESET_ADDR": str(LINK_BASE), "MEM_WORDS": str(1 << 18)},
        waves=bool(int(os.environ.get("WAVES", "0"))),
        keep_files=True,
        compile_args=["--trace", "--trace-structs", "--timescale", "1ns/1ps",
                      "-Wno-WIDTHTRUNC", "-Wno-WIDTHEXPAND"],
    )
