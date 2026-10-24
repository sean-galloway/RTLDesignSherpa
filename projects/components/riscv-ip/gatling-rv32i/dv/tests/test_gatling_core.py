# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: test_gatling_core
# Purpose: Directed barrel tests for gatling_core: four different programs
#          interleaved, per-context halts (context-lock), per-context run
#          control (start late, stop mid-run, restart), the Xcell custom-0
#          opcode locking only its own context, and the rotation timing.
#
# Documentation: projects/components/riscv-ip/gatling-rv32i/docs/gatling_mas
# Subsystem: riscv-ip/gatling-rv32i
#
# Created: 2026-10-21

"""Directed gatling barrel tests.

Programs are kestrel's directed images (assembled at address 0 by kestrel's
build_progs.sh) plus a few built here with a small encoder, so a test can
hold a context running long enough to stop it.  Every context's trace is
diffed against kestrel's golden interpreter, except an illegal encoding,
which that interpreter refuses to model (it raises) -- those are checked by
cause, pc and the trap beat.

Rotation timing is checked on every run: a running context retires exactly
once per four cycles, and beats follow the rotation order.
"""

import os

import cocotb
import pytest

import gatling_sim
from TBClasses.shared.test_levels import reg_level_grid

from gatling.gatling_tb import ALL_HARTS, NUM_HARTS, GatlingTB      # noqa: E402
from tbclasses.kestrel.rv32i_interpreter import (                    # noqa: E402
    RV32IInterpreter,
    load_verilog_hex,
)

PROGRAMS = gatling_sim.KESTREL_PROGRAMS
HALT_ECALL, HALT_EBREAK, HALT_IALIGN = 1, 2, 3
HALT_LALIGN, HALT_SALIGN, HALT_ILL = 4, 5, 0xF


# ---------------------------------------------------------------------------
# A small RV32I encoder for the generated programs
# ---------------------------------------------------------------------------

def _i(op, rd, f3, rs1, imm):
    return ((imm & 0xFFF) << 20) | (rs1 << 15) | (f3 << 12) | (rd << 7) | op


def addi(rd, rs1, imm):
    return _i(0x13, rd, 0, rs1, imm)


def bne(rs1, rs2, off):
    o = off & 0x1FFF
    return ((((o >> 12) & 1) << 31) | (((o >> 5) & 0x3F) << 25) | (rs2 << 20)
            | (rs1 << 15) | (1 << 12) | (((o >> 1) & 0xF) << 8) | (((o >> 11) & 1) << 7)
            | 0x63)


ECALL = 0x0000_0073
XCELL_POP_X5 = (5 << 7) | 0x0B          # custom-0, funct3 000: gatling_pop x5


def csr(rd, f3, rs1, addr):
    """SYSTEM CSR instruction: f3 1/2/3 = CSRRW/S/C, 5/6/7 the immediate forms."""
    return _i(0x73, rd, f3, rs1, addr)


CSR_CYCLE, CSR_TIME, CSR_INSTRET = 0xC00, 0xC01, 0xC02
CSR_CYCLEH, CSR_INSTRETH = 0xC80, 0xC82
CSR_MCYCLE, CSR_MHARTID, CSR_MTVEC = 0xB00, 0xF14, 0x305
STUB_CSRS = (CSR_CYCLE, CSR_TIME, CSR_INSTRET, CSR_CYCLEH, CSR_INSTRETH, CSR_MCYCLE, CSR_MHARTID, CSR_MTVEC)


def csr_stub_prog():
    """Every CSR form against the stub: a write (CSRRW/S/C and the immediate
    forms) then a read of the same CSR into x10..; gp = 1; ecall."""
    words = [addi(5, 0, 0x55)]
    for k, a in enumerate(STUB_CSRS):
        f3 = (1, 2, 3, 5, 6, 7)[k % 6]
        words += [csr(0, f3, 5, a), csr(10 + k, 2, 0, a)]
    words += [addi(3, 0, 1), ECALL]
    return dict(enumerate(words))


def counted_loop(n, step):
    """x6 += step, n times; gp = 1; ecall.  Retires 3n + 4 instructions."""
    words = [addi(5, 0, n), addi(6, 0, 0),
             addi(6, 6, step), addi(5, 5, -1), bne(5, 0, -8),
             addi(3, 0, 1), ECALL]
    return dict(enumerate(words))


def program(name):
    return load_verilog_hex(PROGRAMS / f"{name}.hex")


def golden(words):
    g = RV32IInterpreter(words, reset_addr=0)
    g.run()
    return g


async def _start(dut):
    tb = GatlingTB(dut, reset_addr=0)
    await tb.ensure_clock()
    await tb.assert_reset()
    await tb.release_reset()
    return tb


async def _load(tb, images):
    for c, words in images.items():
        await tb.backdoor_load(c, words)


def _check_against_golden(tb, c, words):
    g = golden(words)
    h = tb.harts[c]
    h.check_halt(expected_cause=g.halt_cause, expected_halt_pc=g.halt_pc)
    h.check_first_pc()
    h.check_order_sequence()
    h.check_x0_rd_zero()
    h.check_trace(g.trace)
    tb.check_window(c)


def _check_locked(tb, c, cause, insn=None):
    h = tb.harts[c]
    h.check_halt(expected_cause=cause)
    h.check_trap_beat()
    h.check_order_sequence()
    tb.check_window(c)
    if insn is not None:
        assert h.trace[-1]["insn"] == insn, \
            f"ctx {c}: trap beat insn 0x{h.trace[-1]['insn']:08x} expected 0x{insn:08x}"


# ---------------------------------------------------------------------------
# Tests
# ---------------------------------------------------------------------------

@cocotb.test(timeout_time=2000, timeout_unit="ms")
async def cocotb_test_gatling_interleave(dut):
    """Four different programs side by side, each matching its golden, with
    every context retiring once per window in rotation order."""
    tb = await _start(dut)
    names = ("loop_sum", "branch_all", "ls_basic", "jal_jalr")
    # Every context gets a program (the four cycle round on a bigger barrel).
    images = {c: program(names[c % len(names)]) for c in range(tb.num_harts)}
    await _load(tb, images)
    tb.set_run(tb.all_harts)
    await tb.run_until_halted(tb.all_harts)
    for c, words in images.items():
        _check_against_golden(tb, c, words)
    tb.check_rotation()
    dut._log.info(f"interleave: {tb.num_harts} programs, golden-identical, rotation held")


@cocotb.test(timeout_time=2000, timeout_unit="ms")
async def cocotb_test_gatling_context_lock(dut):
    """Every halt kind on its own context while the others keep running: an
    ecall, an ebreak, a misaligned jump, misaligned load and store, and an
    illegal encoding -- each locks only its own context (PRD 7 item 4)."""
    tb = await _start(dut)
    rounds = [
        ("system_ecall", "system_illegal", "ls_chain", "system_ebreak"),
        ("ls_misaligned", "rv32ui_ops", "system_misalign_jmp", "ls_misalign_store"),
    ]
    for names in rounds:
        plan = {c: names[c % len(names)] for c in range(tb.num_harts)}
        await tb.assert_reset()
        await tb.release_reset()
        images = {c: program(n) for c, n in plan.items()}
        await _load(tb, images)
        tb.clear_traces()
        tb.set_run(tb.all_harts)
        await tb.run_until_halted(tb.all_harts)
        for c, name in plan.items():
            if name == "system_illegal":
                _check_locked(tb, c, HALT_ILL, insn=0xFFFF_FFFF)
            else:
                _check_against_golden(tb, c, images[c])
            dut._log.info(f"ctx {c} {name}: cause {tb.harts[c].halt_cause}, "
                          f"{len(tb.harts[c].trace)} beats")
        tb.check_rotation()
    # The early halts really were early: the others ran on past them.
    dut._log.info("context-lock: each halt confined to its context")


@cocotb.test(timeout_time=2000, timeout_unit="ms")
async def cocotb_test_gatling_xcell_locks(dut):
    """The Xcell custom-0 opcode is not built yet: it decodes as illegal and
    locks its context after the instructions before it retired; the other
    three run their loops to completion."""
    tb = await _start(dut)
    xcell = {0: addi(1, 0, 0x55), 1: XCELL_POP_X5, 2: addi(2, 0, 7), 3: ECALL}
    loops = {c: counted_loop(40 + 10 * c, c + 1) for c in (0, 2, 3)}
    await _load(tb, {1: xcell, **loops})
    tb.set_run(ALL_HARTS)
    await tb.run_until_halted(ALL_HARTS)
    _check_locked(tb, 1, HALT_ILL, insn=XCELL_POP_X5)
    beats = tb.harts[1].trace
    assert len(beats) == 2 and beats[0]["rd_addr"] == 1 and beats[0]["rd_wdata"] == 0x55, \
        f"ctx 1: expected the addi then the custom-0 trap beat, got {len(beats)} beats"
    for c, words in loops.items():
        _check_against_golden(tb, c, words)
    tb.check_rotation()
    dut._log.info("xcell: custom-0 locks only its context")


@cocotb.test(timeout_time=2000, timeout_unit="ms")
async def cocotb_test_gatling_run_control(dut):
    """Per-context run: a lone context still retires once per window (the
    other slots are bubbles); a context started late begins at RESET_ADDR
    with order 0; a context stopped mid-run retires nothing while held and,
    restarted, runs its program again from the top, golden-identical."""
    tb = await _start(dut)
    images = {c: counted_loop(60, c + 1) for c in range(NUM_HARTS)}
    await _load(tb, images)

    # Context 2 alone.
    tb.set_run(0b0100)
    await tb.run_until_halted(0b0100)
    _check_against_golden(tb, 2, images[2])
    for c in (0, 1, 3):
        assert not tb.harts[c].trace, f"ctx {c} retired while held"

    # Context 0 starts 37 cycles after context 1.  Context 3 is stopped
    # mid-loop and restarted four times, the stops 41 cycles apart so they
    # land on all four rotation phases: a stop must kill context 3's
    # instruction in whichever stage holds it -- including W, where only a
    # stop in that one phase can catch a leaked retirement.
    await tb.assert_reset()
    await tb.release_reset()
    await _load(tb, images)
    tb.clear_traces()
    tb.set_run(0b1010)
    stops = [120 + 41 * k for k in range(4)]
    hold = 20
    held = []          # (stop cycle, beats before the stop, beats while held)
    pending = {}

    async def on_cycle(cycle):
        if cycle == 37:
            tb.set_run(tb.run_mask() | 0b0001)
        elif cycle in stops:
            pending["before"] = len(tb.harts[3].trace)
            tb.set_run(tb.run_mask() & ~0b1000)
        elif cycle - hold in stops:
            held.append((cycle - hold, pending["before"],
                         len(tb.harts[3].trace) - pending["before"]))
            tb.harts[3] = type(tb.harts[3])(3, 0)     # a fresh trace for the rerun
            tb.set_run(tb.run_mask() | 0b1000)

    await tb.run_until_halted(0b1011, on_cycle=on_cycle)
    assert len(held) == len(stops), f"only {len(held)} of {len(stops)} stops happened"
    assert {s % NUM_HARTS for s, _, _ in held} == set(range(NUM_HARTS)), \
        "the stops did not cover every rotation phase"
    for stop, before, during in held:
        # 21 cycles between a restart and the next stop: ~5 windows less the
        # three-cycle fill, so at least 3 beats prove it was running.
        assert before >= 3, f"ctx 3 was not running when stopped at cycle {stop}"
        assert during == 0, f"ctx 3 retired {during} beats while held (stop at cycle {stop})"
    for c in (0, 1, 3):
        _check_against_golden(tb, c, images[c])
    assert not tb.harts[2].trace, "ctx 2 retired while held"
    dut._log.info(f"run control: late start; ctx 3 stopped at {stops} "
                  f"(all four phases), nothing retired while held, rerun golden -- ok")


@cocotb.test(timeout_time=2000, timeout_unit="ms")
async def cocotb_test_gatling_csr_stub(dut):
    """No CSR state (PRD 3.3): every CSR -- the Zicntr counters, mcycle,
    mhartid, mtvec -- reads 0 after a write of every form, and nothing halts
    but the closing ecall, on every context."""
    tb = await _start(dut)
    await _load(tb, {c: csr_stub_prog() for c in range(tb.num_harts)})
    tb.set_run(tb.all_harts)
    await tb.run_until_halted(tb.all_harts)
    for c in range(tb.num_harts):
        h = tb.harts[c]
        h.check_halt(expected_cause=HALT_ECALL)
        h.check_order_sequence()
        tb.check_window(c)
        reads = {beat["rd_addr"]: beat["rd_wdata"] for beat in h.trace
                 if 10 <= beat["rd_addr"] < 10 + len(STUB_CSRS)}
        assert len(reads) == len(STUB_CSRS), f"ctx {c}: {len(reads)} CSR reads retired, expected {len(STUB_CSRS)}"
        for k, a in enumerate(STUB_CSRS):
            assert reads[10 + k] == 0, f"ctx {c}: CSR {a:#05x} read {reads[10 + k]:#x}, expected 0"
    tb.check_rotation()
    dut._log.info(f"csr stub: {len(STUB_CSRS)} CSRs read 0 after a write on all {tb.num_harts} contexts")


# ---------------------------------------------------------------------------
# pytest wrappers
# ---------------------------------------------------------------------------

CASES = ["cocotb_test_gatling_interleave", "cocotb_test_gatling_context_lock",
         "cocotb_test_gatling_xcell_locks", "cocotb_test_gatling_run_control",
         "cocotb_test_gatling_csr_stub"]


@pytest.mark.parametrize("test_level, description",
                         [(lvl, f"gatling_core {lvl}") for lvl in reg_level_grid()])
@pytest.mark.parametrize("cocotb_testcase", CASES)
def test_gatling_core(request, cocotb_testcase, test_level, description):
    gatling_sim.run_cell(
        module="test_gatling_core", testcase=cocotb_testcase,
        toplevel="gatling_tb_top", filelist=gatling_sim.TB_FILELIST,
        cell=f"{cocotb_testcase}_{test_level}", test_level=test_level,
        parameters={"RESET_ADDR": "0"})


# NUM_HARTS is a module parameter (2026-10-22); the default build above is
# the tetrad.  A bigger barrel must still interleave, lock and stub
# correctly, with the window and the rotation stretched to NUM_HARTS: the
# TB reads the count off the DUT, these cases scale their programs to it.
NUM_HARTS_CASES = ["cocotb_test_gatling_interleave", "cocotb_test_gatling_context_lock",
                   "cocotb_test_gatling_csr_stub"]
NUM_HARTS_VALUES = [8]


@pytest.mark.parametrize("test_level, description",
                         [(lvl, f"gatling_core {lvl}") for lvl in reg_level_grid()])
@pytest.mark.parametrize("num_harts", NUM_HARTS_VALUES)
@pytest.mark.parametrize("cocotb_testcase", NUM_HARTS_CASES)
def test_gatling_core_num_harts(request, cocotb_testcase, num_harts, test_level, description):
    gatling_sim.run_cell(
        module="test_gatling_core", testcase=cocotb_testcase,
        toplevel="gatling_tb_top", filelist=gatling_sim.TB_FILELIST,
        cell=f"{cocotb_testcase}_h{num_harts}_{test_level}", test_level=test_level,
        parameters={"RESET_ADDR": "0", "NUM_HARTS": str(num_harts)})
