# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: test_kestrel_rv32ui
# Purpose: Task 8 system-layer tests (FENCE/FENCE.I NOPs, ECALL/EBREAK halt
#          with hold, illegal-instruction halt with rvfi_trap) plus the full
#          riscv-tests rv32ui-p-* battery with spike lockstep at func level.
#
# Documentation: projects/components/riscv-ip/README.md
# Subsystem: riscv-ip/kestrel-rv32i
#
# Author: sean galloway
# Created: 2026-10-06

"""kestrel-rv32i system layer and rv32ui battery tests.

The directed cases backdoor-load their programs so one Verilator build
covers all four system programs.  The battery discovers every
``vendor/riscv-tests/isa/rv32ui-p-*.hex`` image; the gate level runs the
simple/add/addi smoke subset, the func level runs all 42 with the golden
interpreter full-field diff and the spike (pc, insn) lockstep.
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

PROGRAMS_DIR = Path(__file__).resolve().parent / "programs"
if str(PROGRAMS_DIR) not in sys.path:
    sys.path.insert(0, str(PROGRAMS_DIR))

from tbclasses.kestrel.kestrel_tb import KestrelTB                  # noqa: E402
from tbclasses.kestrel.rv32i_interpreter import (                   # noqa: E402
    RV32IInterpreter,
    load_verilog_hex,
)
from tbclasses.kestrel.rv32ui_battery import RV32UIBattery          # noqa: E402

# Directed system programs, assembled at address 0 (build_progs.sh).
FENCE_INSN = 0x0FF0000F    # fence (any pred/succ/fm field retires as a NOP)
FENCE_I_INSN = 0x0000100F  # fence.i
ILLEGAL_INSN = 0xFFFFFFFF


async def _load_and_run(tb, hex_name):
    """Backdoor-load a program and run it to halt with a fresh golden run."""
    words = load_verilog_hex(PROGRAMS_DIR / hex_name)
    golden = RV32IInterpreter(words, reset_addr=0)
    golden.run()
    await tb.assert_reset()
    await tb.backdoor_load(words)
    await tb.release_reset()
    await tb.run_to_halt()
    return golden


def _check_against_golden(tb, golden):
    tb.check_halt(expected_cause=golden.halt_cause,
                  expected_halt_pc=golden.halt_pc)
    tb.check_first_pc()
    tb.check_order_sequence()
    tb.check_pc_sequential()
    tb.check_x0_rd_zero()
    tb.check_trace(golden.trace)


async def _system_directed(dut):
    """Directed system-layer checks, one program per sub-case."""
    tb = KestrelTB(dut, reset_addr=0x0000_0000)
    await tb.ensure_clock()

    # FENCE / FENCE.I retire as pure NOPs (Review Focus 5): the trace diff
    # pins no register-file, memory, or PC side effects around them.
    golden = await _load_and_run(tb, "system_fence.hex")
    _check_against_golden(tb, golden)
    fence_beats = [b for b in tb.trace
                   if b["insn"] in (FENCE_INSN, FENCE_I_INSN)]
    assert len(fence_beats) == 3, \
        f"expected 3 fence beats, got {len(fence_beats)}"
    for beat in fence_beats:
        assert beat["trap"] == 0, "fence retired as a trap"
        assert beat["rd_addr"] == 0 and beat["rd_wdata"] == 0, \
            "fence must not report a register write"
        assert beat["mem_rmask"] == 0 and beat["mem_wmask"] == 0, \
            "fence must not report a memory access"
        assert beat["pc_wdata"] == (beat["pc"] + 4) & 0xFFFF_FFFF, \
            "fence must not redirect the PC"

    # ECALL halts with cause 1 and holds (Review Focus 4): the post-halt
    # loop in run_to_halt pins imem_addr/rvfi_valid freeze and no retire.
    golden = await _load_and_run(tb, "system_ecall.hex")
    _check_against_golden(tb, golden)
    tb.check_trap_beat()

    # EBREAK halts with cause 2 and holds the same way.
    golden = await _load_and_run(tb, "system_ebreak.hex")
    _check_against_golden(tb, golden)
    tb.check_trap_beat()

    # An illegal instruction halts with cause 0xF and the rvfi_trap beat.
    # No golden here: the M2-tightened interpreter raises on unmodelled
    # encodings instead of mirroring the halt.
    words = load_verilog_hex(PROGRAMS_DIR / "system_illegal.hex")
    await tb.assert_reset()
    await tb.backdoor_load(words)
    await tb.release_reset()
    await tb.run_to_halt()
    tb.check_halt(expected_cause=0xF)
    tb.check_trap_beat()
    assert tb.trace[-1]["insn"] == ILLEGAL_INSN, \
        f"trap beat insn=0x{tb.trace[-1]['insn']:08x} expected 0x{ILLEGAL_INSN:08x}"
    # The two pre-halt vectors retired with their writebacks before the halt.
    assert tb.trace[0]["rd_addr"] == 1 and tb.trace[0]["rd_wdata"] == 0x123
    assert tb.trace[1]["rd_addr"] == 2 and tb.trace[1]["rd_wdata"] == 0x124

    # Misaligned control-flow target halts with cause 3 and the rvfi_trap
    # beat (Task 9, riscv-formal CEX fix): the aligned JAL at the top of
    # the program must still retire normally (link value x1 = pc+4), then
    # the +2-offset JAL traps on its own beat.  The golden interpreter
    # models the halt (it does not raise like the illegal encoding), so the
    # full-field trace diff — including the trap beat's pc_wdata carrying
    # the misaligned target — is checked here.  check_pc_sequential does
    # not apply: the trap beat redirects the PC to the misaligned target.
    golden = await _load_and_run(tb, "system_misalign_jmp.hex")
    tb.check_halt(expected_cause=3, expected_halt_pc=golden.halt_pc)
    tb.check_first_pc()
    tb.check_order_sequence()
    tb.check_x0_rd_zero()
    tb.check_trace(golden.trace)
    tb.check_trap_beat()
    assert tb.trace[0]["rd_addr"] == 1 and tb.trace[0]["rd_wdata"] == 4, \
        "aligned JAL regression: link value missing"
    misaligned_beat = tb.trace[-1]
    assert misaligned_beat["pc_wdata"] == 0x12 and misaligned_beat["trap"] == 1, \
        "misaligned JAL must trap with the +2 target on pc_wdata"

    dut._log.info("system layer directed checks PASSED")


async def _battery(dut):
    repo_root = os.environ.get("REPO_ROOT", str(Path(__file__).resolve().parents[6]))
    level = os.environ.get("TEST_LEVEL", "func")
    log_dir = os.path.dirname(os.environ.get("LOG_PATH", "."))
    work_dir = os.path.join(log_dir, "rv32ui_battery")
    battery = RV32UIBattery(dut, repo_root=repo_root, level=level,
                            work_dir=work_dir)
    await battery.run()


@cocotb.test(timeout_time=2000, timeout_unit="ms")
async def cocotb_test_kestrel_rv32ui_system(dut):
    """FENCE/FENCE.I NOPs, ECALL/EBREAK halt+hold, illegal-instruction
    trap, misaligned-jump-target halt with the rvfi_trap beat (cause 3)."""
    await _system_directed(dut)


@cocotb.test(timeout_time=2000, timeout_unit="ms")
async def cocotb_test_kestrel_rv32ui_battery(dut):
    """All 42 rv32ui-p-* images: tohost pass/fail + spike lockstep."""
    await _battery(dut)


# ---------------------------------------------------------------------------
# pytest wrappers
# ---------------------------------------------------------------------------

CASES = {
    "cocotb_test_kestrel_rv32ui_system": 0x0000_0000,
    "cocotb_test_kestrel_rv32ui_battery": 0x8000_0000,
}


@pytest.mark.parametrize("test_level, description",
                         [(lvl, f"kestrel_rv32ui {lvl}") for lvl in reg_level_grid()])
@pytest.mark.parametrize("cocotb_testcase", list(CASES))
def test_kestrel_rv32ui(request, cocotb_testcase, test_level, description):
    """Pytest wrapper: one Verilator build per (case, level) cell."""
    module, repo_root, tests_dir, log_dir, _ = get_paths({})
    reset_addr = CASES[cocotb_testcase]

    test_name_plus_params = f"{cocotb_testcase}_{test_level}"
    log_path = os.path.join(log_dir, f"{test_name_plus_params}.log")
    sim_build = sim_build_path(tests_dir, test_name_plus_params)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)
    results_path = os.path.join(log_dir, f"results_{test_name_plus_params}.xml")

    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path="projects/components/riscv-ip/kestrel-rv32i/dv/filelists/kestrel_tb.f",
    )

    extra_env = {
        "DUT": "kestrel_tb_top",
        "LOG_PATH": log_path,
        "COCOTB_LOG_LEVEL": "INFO",
        "COCOTB_RESULTS_FILE": results_path,
        **level_env(test_level),
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
