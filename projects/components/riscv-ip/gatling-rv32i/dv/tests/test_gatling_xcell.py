# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: test_gatling_xcell
# Purpose: Directed Xcell tests on gatling_tetrad (gatling PRD 6, "Xcell
#          unit"): every instruction's effect and its interlock -- POP and
#          PUSH through a register and through the ALU (x0), CFG, ECTX,
#          FLUSH against a slow drain controller, KICK/WAIT as a barrier, the
#          reserved funct3, and a context stalled forever without slowing the
#          other three.
#
# Documentation: projects/components/riscv-ip/gatling-rv32i/docs/gatling_mas
# Subsystem: riscv-ip/gatling-rv32i
#
# Created: 2026-11-26

"""Directed Xcell tests.

The programs are hand-assembled with ``gatling.xcell_asm``.  The cell
blocks are real: cell_mem_in and cell_mem_out, and alu-infer, whose results
are checked against alu-infer's golden model.  The TB stands in for the rx
demux (fill), the packetizer (drain), the drain controller (flush_ready)
and the MonBus (kicks).

A stalled instruction retires nothing, so every context's beats are a
multiple of NUM_HARTS cycles apart -- never less -- whatever the stalls;
``_check_spacing`` holds that on every test.
"""

import os
import random

import cocotb
import pytest

import gatling_sim
from TBClasses.shared.test_levels import reg_level_grid

from gatling.gatling_tetrad_tb import GatlingTetradTB          # noqa: E402
from gatling import xcell_asm as xa                              # noqa: E402
from gatling.tetrad_golden import CellModel, bf16_line, line_ok, spec_str  # noqa: E402
import alu_infer_golden as g                                     # noqa: E402

LEVEL = os.environ.get("TEST_LEVEL", "gate").lower()


def _seed() -> int:
    return int(os.environ.get("SEED", "1"))


async def _start(dut) -> GatlingTetradTB:
    tb = GatlingTetradTB(dut, reset_addr=0, seed=_seed())
    await tb.ensure_clock()
    await tb.assert_reset()
    await tb.release_reset()
    return tb


async def _load_all(tb, words, mask=None):
    for c in range(tb.num_harts):
        if mask is None or (mask >> c) & 1:
            await tb.backdoor_load(c, words)


def _check_spacing(tb, c):
    cyc = tb.harts[c].cycles
    for i in range(1, len(cyc)):
        gap = cyc[i] - cyc[i - 1]
        assert gap >= tb.num_harts and gap % tb.num_harts == 0, \
            f"ctx {c} beat {i}: {gap} cycles after the previous"


def _beats(tb, c, insn):
    return [b for b in tb.harts[c].trace if b["insn"] == insn]


def _check_done(tb, mask):
    for c in range(tb.num_harts):
        if (mask >> c) & 1:
            cause = (int(tb.dut.halt_cause.value) >> (4 * c)) & 0xF
            assert cause == xa.HALT_DONE, f"ctx {c}: halt cause {cause:#x}, expected done"
            assert (tb.done_mask() >> c) & 1, f"ctx {c}: done not raised"
            assert not any(b["trap"] for b in tb.harts[c].trace), f"ctx {c}: a trap beat"


def _check_no_alu_error(tb):
    assert int(tb.dut.alu_err_opcode.value) == 0, "an ALU flagged an illegal func_sel"


def _counted(prog, n, body, reg=7):
    """``body`` n times: li reg, n; loop: body; addi reg, -1; bne."""
    prog.emit(xa.li(reg, n)).label("loop")
    for w in body:
        prog.emit(w)
    prog.emit(xa.addi(reg, reg, -1)).bne(reg, 0, "loop")
    return prog


# ---------------------------------------------------------------------------
# CFG, and the reserved funct3
# ---------------------------------------------------------------------------

@cocotb.test(timeout_time=200, timeout_unit="ms")
async def cocotb_test_xcell_cfg(dut):
    """CFG reads the cell's element mode (func_sel[8:7]) and credit batch;
    index 2 (the context ID, implicit) and an unused index read 0; CFG never
    stalls.  funct3 111 is reserved: it locks the context as illegal."""
    tb = await _start(dut)
    n = tb.num_harts
    for c in range(n):
        tb.configure(c, func_sel=g.func_sel(g.OP_COPY, 0, c % 4), credit_batch=0x100 + c)
    prog = xa.Prog().emit(xa.cfg(10, 0), xa.cfg(11, 1), xa.cfg(12, 2), xa.cfg(13, 7),
                          xa.cfg(14, 0xFFF), xa.xcell_reserved(15))
    await _load_all(tb, prog.words())
    tb.set_run(tb.all_harts)
    await tb.run_until_done(tb.all_harts)
    for c in range(n):
        h = tb.harts[c]
        got = {b["rd_addr"]: b["rd_wdata"] for b in h.trace if b["rd_addr"]}
        exp = {10: c % 4, 11: 0x100 + c, 12: 0, 13: 0, 14: 0}
        assert got == exp, f"ctx {c}: CFG reads {got}, expected {exp}"
        h.check_halt(expected_cause=xa.HALT_ILL)
        h.check_trap_beat()
        assert h.trace[-1]["insn"] == xa.xcell_reserved(15)
        tb.check_window(c)          # nothing stalled: exactly one beat per window
    dut._log.info("cfg: element mode, credit batch, 0 for the rest; funct3 111 illegal")


# ---------------------------------------------------------------------------
# POP rd / PUSH rs1: the register path, both interlocks
# ---------------------------------------------------------------------------

@cocotb.test(timeout_time=2000, timeout_unit="ms")
async def cocotb_test_xcell_pop_push_reg(dut):
    """POP x5 / ADDI / PUSH x5 over more lines than either memory holds.
    Context 0's input arrives late (POP stalls on an empty memory); every
    result memory fills before the drain starts (PUSH stalls on a full one).
    Every result is its input plus one, in order; a stall retires nothing."""
    tb = await _start(dut)
    n = tb.num_harts
    count = {"gate": 40, "func": 96, "full": 320}[LEVEL]
    prog = _counted(xa.Prog(), count, [xa.pop(5), xa.addi(5, 5, 1), xa.push(5)]).emit(xa.ectx())
    await _load_all(tb, prog.words())
    rng = random.Random(_seed())
    inputs = [[rng.getrandbits(32) for _ in range(count)] for _ in range(n)]
    for c in range(1, n):
        tb.feed(c, inputs[c])
    tb.drain_enable = [False] * n

    def hook(cycle):
        if cycle == 300:
            tb.feed(0, inputs[0])
        for c in range(n):
            if xa.XC_PUSH in tb.stall_seen[c]:
                tb.drain_enable[c] = True

    tb.fill_gap = 0.25 if LEVEL != "gate" else 0.0
    tb.set_run(tb.all_harts)
    await tb.run_until_done(tb.all_harts, on_cycle=hook)
    _check_done(tb, tb.all_harts)
    for c in range(n):
        exp = [(x + 1) & 0xFFFF_FFFF for x in inputs[c]]
        assert len(tb.results[c]) == count, f"ctx {c}: {len(tb.results[c])} results, expected {count}"
        bad = [i for i, (r, e) in enumerate(zip(tb.results[c], exp)) if r != e]
        assert not bad, f"ctx {c}: {len(bad)} results differ, first at {bad[0]}"
        pops = _beats(tb, c, xa.pop(5))
        assert [b["rd_wdata"] for b in pops] == inputs[c], f"ctx {c}: POP x5 values differ"
        assert len(_beats(tb, c, xa.push(5))) == count
        assert tb.consumed(c) == count, f"ctx {c}: {tb.consumed(c)} lines consumed, expected {count}"
        assert xa.XC_PUSH in tb.stall_seen[c], f"ctx {c}: PUSH never stalled on a full memory"
        _check_spacing(tb, c)
    assert xa.XC_POP in tb.stall_seen[0], "ctx 0: POP never stalled on an empty memory"
    dut._log.info(f"pop/push reg: {count} lines per context, both interlocks exercised")


# ---------------------------------------------------------------------------
# POP x0 / PUSH x0: the ALU path
# ---------------------------------------------------------------------------

def _alu_cells():
    """One cell per row family: two-line add and multiply, one-line relu,
    and the compare against the threshold (mask on result_flags)."""
    return [CellModel(g.OP_ADD), CellModel(g.OP_MUL), CellModel(g.OP_RELU),
            CellModel(g.OP_CMP, sub_op=1, threshold=0x3F80)]


async def _run_alu(dut, cells, prologue, body, epilogue, invocations, gaps):
    tb = await _start(dut)
    n = tb.num_harts
    for c in range(n):
        m = cells[c % len(cells)]
        tb.configure(c, func_sel=m.func_sel, op_lines=m.op_lines, threshold=m.threshold)
    prog = xa.Prog().emit(*prologue)
    _counted(prog, invocations[1], body).emit(*epilogue)
    await _load_all(tb, prog.words())
    rng = random.Random(_seed())
    expect = []
    for c in range(n):
        m = CellModel(cells[c % len(cells)].opcode, cells[c % len(cells)].sub_op,
                      cells[c % len(cells)].threshold)
        lines, specs = [], []
        for acc in invocations[0]:
            a = bf16_line(rng)
            b = bf16_line(rng) if m.op_lines == 2 else 0
            lines += [a, b] if m.op_lines == 2 else [a]
            specs.append(m.step(a, b, acc))
        if c:
            tb.feed(c, lines)
        expect.append((m, specs, len(lines), lines))
    # Context 0's lines arrive late, so its POP x0 must wait on an empty
    # (then too-short) input memory: the occupancy interlock on the ALU path.
    late_lines = expect[0][3]

    def hook(cycle):
        if cycle == 150:
            tb.feed(0, late_lines)

    tb.fill_gap, tb.drain_gap = gaps
    tb.set_run(tb.all_harts)
    await tb.run_until_done(tb.all_harts, on_cycle=hook)
    assert xa.XC_POP in tb.stall_seen[0], "ctx 0: POP x0 never waited for its input"
    _check_done(tb, tb.all_harts)
    _check_no_alu_error(tb)
    for c in range(n):
        m, specs, nlines, _ = expect[c]
        got = tb.results[c]
        assert len(got) == len(specs), f"ctx {c}: {len(got)} results, expected {len(specs)}"
        for k, (r, s) in enumerate(zip(got, specs)):
            assert line_ok(r, s), f"ctx {c} op {m.opcode} result {k}: 0x{r:08x}, expected {spec_str(s)}"
        assert tb.consumed(c) == nlines, f"ctx {c}: {tb.consumed(c)} lines consumed, expected {nlines}"
        _check_spacing(tb, c)
    return tb


@cocotb.test(timeout_time=2000, timeout_unit="ms")
async def cocotb_test_xcell_alu_ops(dut):
    """POP x0 issues the cell's function on one or two input lines; PUSH x0
    retires the ALU's result into the result memory.  Four row families at
    once, each against alu-infer's golden; every PUSH x0 that comes before
    its result stalls."""
    count = {"gate": 24, "func": 96, "full": 320}[LEVEL]
    gaps = (0.0, 0.0) if LEVEL == "gate" else (0.3, 0.3)
    tb = await _run_alu(dut, _alu_cells(), [], [xa.pop(0), xa.push(0)], [xa.ectx()],
                        ([xa.ACC_HOLD] * count, count), gaps)
    # The add row's three-stage adder (ADDER_LATENCY = 3) is still working
    # when the context's next slot brings PUSH x0, so that PUSH must wait;
    # the zero-latency rows (mul, relu, compare) may be ready in time.
    for c in range(0, tb.num_harts, 4):
        assert xa.XC_PUSH in tb.stall_seen[c], f"ctx {c} (add): PUSH x0 never waited for the ALU"
    dut._log.info(f"alu ops: {count} invocations x 4 row families, golden-identical")


@cocotb.test(timeout_time=2000, timeout_unit="ms")
async def cocotb_test_xcell_mac(dut):
    """acc_ctrl rides in POP x0's insn[21:20]: CLEAR, then a dependent MAC
    chain of ACCUMULATE invocations, each result the accumulator's bf16
    view; every cell runs its own chain."""
    count = {"gate": 16, "func": 64, "full": 256}[LEVEL]
    gaps = (0.0, 0.0) if LEVEL == "gate" else (0.3, 0.3)
    await _run_alu(dut, [CellModel(g.OP_MAC)],
                   [xa.pop(0, xa.ACC_CLEAR), xa.push(0)],
                   [xa.pop(0, xa.ACC_ACCUM), xa.push(0)], [xa.ectx()],
                   ([xa.ACC_CLEAR] + [xa.ACC_ACCUM] * count, count), gaps)
    dut._log.info(f"mac: CLEAR + {count} ACCUMULATE per cell, golden-identical")


# ---------------------------------------------------------------------------
# FLUSH
# ---------------------------------------------------------------------------

@cocotb.test(timeout_time=200, timeout_unit="ms")
async def cocotb_test_xcell_flush(dut):
    """FLUSH latches {tag = rs1[18:15], dest = rs1[14:0]} and offers it to
    the drain controller until accepted; a FLUSH behind an unaccepted one
    stalls.  Three commands per context arrive in order, values intact."""
    tb = await _start(dut)
    n = tb.num_harts
    base = [((0x9 + c) << 15) | (0x1230 + 0x10 * c) for c in range(n)]
    for c in range(n):
        tb.configure(c, func_sel=0, credit_batch=base[c])
    prog = xa.Prog().emit(xa.cfg(5, 1), xa.flush(5), xa.addi(5, 5, 1), xa.flush(5),
                          xa.addi(5, 5, 1), xa.flush(5), xa.ectx())
    await _load_all(tb, prog.words())
    tb.flush_enable = [False] * n

    def hook(cycle):
        if cycle == 120:
            tb.flush_enable = [True] * n
            tb.flush_gap = 0.5

    tb.set_run(tb.all_harts)
    await tb.run_until_done(tb.all_harts, on_cycle=hook, post_cycles=64)
    _check_done(tb, tb.all_harts)
    for c in range(n):
        got = [(d, t) for _, d, t in tb.flushes[c]]
        exp = [((base[c] + k) & 0x7FFF, (base[c] + k) >> 15) for k in range(3)]
        assert got == exp, f"ctx {c}: flushes {got}, expected {exp}"
        assert all(cyc >= 120 for cyc, _, _ in tb.flushes[c])
        assert xa.XC_FLUSH in tb.stall_seen[c], f"ctx {c}: the second FLUSH never stalled"
        _check_spacing(tb, c)
    dut._log.info("flush: three commands per context, the second held behind the first")


# ---------------------------------------------------------------------------
# KICK / WAIT
# ---------------------------------------------------------------------------

@cocotb.test(timeout_time=500, timeout_unit="ms")
async def cocotb_test_xcell_kick_wait(dut):
    """A one-shot barrier.  Round 1: each context spins a different number
    of iterations, KICKs (value = its count), then WAITs on every context;
    no WAIT retires before the last KICK.  Round 2: a context that is done
    (ECTX) satisfies a WAIT without kicking.  Holding a context clears its
    event bit."""
    tb = await _start(dut)
    n = tb.num_harts
    spins = [5 + 17 * c for c in range(n)]
    for c in range(n):
        tb.configure(c, func_sel=0, credit_batch=spins[c])
    prog = (xa.Prog().emit(xa.cfg(8, 1)).label("spin")
            .emit(xa.addi(8, 8, -1)).bne(8, 0, "spin")
            .emit(xa.cfg(9, 1), xa.kick(9), xa.li(6, tb.all_harts), xa.wait(6), xa.ectx()))
    await _load_all(tb, prog.words())
    tb.set_run(tb.all_harts)
    await tb.run_until_done(tb.all_harts)
    _check_done(tb, tb.all_harts)
    last_kick = max(k[0][0] for k in tb.kicks)
    for c in range(n):
        assert [v for _, v in tb.kicks[c]] == [spins[c]], f"ctx {c}: kicks {tb.kicks[c]}"
        waits = _beats(tb, c, xa.wait(6))
        assert len(waits) == 1
        assert tb.harts[c].cycles[tb.harts[c].trace.index(waits[0])] > last_kick, \
            f"ctx {c}: WAIT retired before the last KICK"
        _check_spacing(tb, c)
    for c in range(n - 1):          # the slowest one never waits
        assert xa.XC_WAIT in tb.stall_seen[c], f"ctx {c}: WAIT never stalled"
    assert int(dut.event_flags.value) == tb.all_harts
    tb.set_run(0)
    await tb.idle(4)
    assert int(dut.event_flags.value) == 0, "holding the contexts left event bits set"

    # Round 2: context n-1 only ends; the others wait on it and nothing else.
    await tb.restart()
    last = n - 1
    waiter = xa.Prog().emit(xa.li(6, 1 << last), xa.wait(6), xa.ectx())
    await _load_all(tb, waiter.words(), mask=tb.all_harts & ~(1 << last))
    late = xa.Prog()
    _counted(late, 40, [xa.addi(10, 10, 1)]).emit(xa.ectx())
    await tb.backdoor_load(last, late.words())
    tb.set_run(tb.all_harts)
    await tb.run_until_done(tb.all_harts)
    _check_done(tb, tb.all_harts)
    end_last = tb.harts[last].cycles[-1]
    for c in range(last):
        w = _beats(tb, c, xa.wait(6))
        assert len(w) == 1 and tb.harts[c].cycles[tb.harts[c].trace.index(w[0])] > end_last, \
            f"ctx {c}: WAIT did not hold until ctx {last} was done"
        assert not tb.kicks[c]
    dut._log.info("kick/wait: barrier held to the last kick; done satisfies a wait")


# ---------------------------------------------------------------------------
# Isolation
# ---------------------------------------------------------------------------

@cocotb.test(timeout_time=500, timeout_unit="ms")
async def cocotb_test_xcell_isolation(dut):
    """Context 0 stalls on a POP with no input for a long time; the other
    three run a full POP/PUSH workload to completion, one beat per window,
    and context 0 retires nothing until its line arrives."""
    tb = await _start(dut)
    n = tb.num_harts
    count = {"gate": 24, "func": 64, "full": 160}[LEVEL]
    work = _counted(xa.Prog(), count, [xa.pop(5), xa.push(5)]).emit(xa.ectx())
    await _load_all(tb, work.words())
    rng = random.Random(_seed())
    for c in range(1, n):
        tb.feed(c, [rng.getrandbits(32) for _ in range(count)])
    tb.set_run(tb.all_harts)
    others = tb.all_harts & ~1
    await tb.run_until_done(others)
    _check_done(tb, others)
    pops0 = _beats(tb, 0, xa.pop(5))
    assert not pops0, "ctx 0 retired a POP with nothing to pop"
    assert int(dut.ctx_stalled.value) & 1 and xa.XC_POP in tb.stall_seen[0]
    assert not tb.halted_mask() & 1
    for c in range(1, n):
        # until its first stall a context retires once per window; the
        # whole trace keeps whole-window spacing
        _check_spacing(tb, c)
        assert len(tb.results[c]) == count
    tb.feed(0, [rng.getrandbits(32) for _ in range(count)])
    await tb.run_until_done(1)
    _check_done(tb, 1)
    assert len(tb.results[0]) == count
    _check_spacing(tb, 0)
    dut._log.info("isolation: one context stalled, three ran to completion")


# ---------------------------------------------------------------------------
# pytest wrappers
# ---------------------------------------------------------------------------

CASES = ["cocotb_test_xcell_cfg", "cocotb_test_xcell_pop_push_reg",
         "cocotb_test_xcell_alu_ops", "cocotb_test_xcell_mac",
         "cocotb_test_xcell_flush", "cocotb_test_xcell_kick_wait",
         "cocotb_test_xcell_isolation"]


@pytest.mark.parametrize("test_level, description",
                         [(lvl, f"gatling_xcell {lvl}") for lvl in reg_level_grid()])
@pytest.mark.parametrize("cocotb_testcase", CASES)
def test_gatling_xcell(request, cocotb_testcase, test_level, description):
    seed = os.environ.get("SEED") or str(random.randint(0, 100000))
    gatling_sim.run_cell(
        module="test_gatling_xcell", testcase=cocotb_testcase,
        toplevel="gatling_tetrad_tb_top", filelist=gatling_sim.TETRAD_TB_FILELIST,
        cell=f"{cocotb_testcase}_{test_level}", test_level=test_level,
        parameters={"RESET_ADDR": "0"}, extra_env={"SEED": seed})
