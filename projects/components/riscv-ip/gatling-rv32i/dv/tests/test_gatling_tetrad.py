# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: test_gatling_tetrad
# Purpose: gatling-rv32i TASK-002's "Done when": a hand-assembled tetrad
#          program in DV -- four contexts run one binary that POPs operands
#          into each cell's alu-infer issue handshake, PUSHes the results,
#          meets at a KICK/WAIT barrier and FLUSHes its result memory to a
#          programmed destination, against streaming input, a draining
#          result memory and a slow drain controller.
#
# Documentation: projects/components/riscv-ip/gatling-rv32i/docs/gatling_mas
# Subsystem: riscv-ip/gatling-rv32i
#
# Created: 2026-11-26

"""The tetrad program (dv/tbclasses/gatling/tetrad_program.py, shared with
the Nexys A7 board host): one binary on four contexts over a MAC, ADD, RELU
and COMPARE cell -- CLEAR + N ACCUMULATE, KICK, WAIT on all four, FLUSH, ECTX.

Checks: every result line against alu-infer's golden, in order; the
consumed-line ledger (lines popped = lines fed); one FLUSH per context,
none before the last KICK; every context done; no ALU opcode error; every
context's beats a whole number of windows apart; exactly N+1 ALU
invocations retired per context.
"""

import os
import random

import cocotb
import pytest

import gatling_sim
from TBClasses.shared.test_levels import reg_level_grid

from gatling.gatling_tetrad_tb import GatlingTetradTB          # noqa: E402
from gatling import xcell_asm as xa                              # noqa: E402
from gatling.tetrad_golden import line_ok, spec_str              # noqa: E402
from gatling.tetrad_program import build_runs, tetrad_program    # noqa: E402

LEVEL = os.environ.get("TEST_LEVEL", "gate").lower()


@cocotb.test(timeout_time=5000, timeout_unit="ms")
async def cocotb_test_tetrad_program(dut):
    seed = int(os.environ.get("SEED", "1"))
    tb = GatlingTetradTB(dut, reset_addr=0, seed=seed)
    await tb.ensure_clock()
    await tb.assert_reset()
    await tb.release_reset()
    n_ctx = tb.num_harts
    count = {"gate": 24, "func": 96, "full": 384}[LEVEL]

    prog = tetrad_program(count)
    for c in range(n_ctx):
        await tb.backdoor_load(c, prog.words())

    runs = build_runs(random.Random(seed), n_ctx, count)
    flush_word = [r.word for r in runs]
    expect = []
    for c, r in enumerate(runs):
        m = r.model
        tb.configure(c, func_sel=m.func_sel, op_lines=m.op_lines,
                     threshold=m.threshold, credit_batch=r.word)
        expect.append((m, r.specs, len(r.lines), r.lines))

    # Each cell's stream starts late, staggered, so every context's first
    # POP x0 waits on an empty input memory (the occupancy interlock);
    # after that the gaps decide.
    def hook(cycle):
        for c in range(n_ctx):
            if cycle == 40 * (c + 1):
                tb.feed(c, expect[c][3])

    tb.fill_gap = 0.5
    tb.drain_gap = 0.35
    tb.flush_gap = 0.6

    tb.set_run(tb.all_harts)
    await tb.run_until_done(tb.all_harts, post_cycles=64, on_cycle=hook)

    assert int(dut.alu_err_opcode.value) == 0
    last_kick = max(k[-1][0] for k in tb.kicks if k)
    for c in range(n_ctx):
        m, specs, nlines, _ = expect[c]
        cause = (int(dut.halt_cause.value) >> (4 * c)) & 0xF
        assert cause == xa.HALT_DONE, f"ctx {c}: cause {cause:#x}"
        got = tb.results[c]
        assert len(got) == len(specs), f"ctx {c}: {len(got)} results, expected {len(specs)}"
        for k, (r, s) in enumerate(zip(got, specs)):
            assert line_ok(r, s), \
                f"ctx {c} (op {m.opcode}) result {k}: 0x{r:08x}, expected {spec_str(s)}"
        assert tb.consumed(c) == nlines, f"ctx {c}: {tb.consumed(c)} consumed, {nlines} fed"
        assert [v for _, v in tb.kicks[c]] == [1], f"ctx {c}: kicks {tb.kicks[c]}"
        assert len(tb.flushes[c]) == 1, f"ctx {c}: flushes {tb.flushes[c]}"
        cyc, dest, tag = tb.flushes[c][0]
        assert (dest, tag) == (flush_word[c] & 0x7FFF, flush_word[c] >> 15)
        assert cyc > last_kick, f"ctx {c}: FLUSH before the barrier released"
        h = tb.harts[c]
        assert not any(b["trap"] for b in h.trace)
        issued = [b for b in h.trace if b["insn"] in (xa.pop(0, xa.ACC_CLEAR), xa.pop(0, xa.ACC_ACCUM))]
        assert len(issued) == count + 1, f"ctx {c}: {len(issued)} ALU invocations retired"
        assert len(h.trace) == len(prog.words()) + (count - 1) * 4, \
            f"ctx {c}: {len(h.trace)} instructions retired"
        for i in range(1, len(h.cycles)):
            gap = h.cycles[i] - h.cycles[i - 1]
            assert gap >= n_ctx and gap % n_ctx == 0, f"ctx {c} beat {i}: gap {gap}"
    for c in range(n_ctx):
        assert xa.XC_POP in tb.stall_seen[c], f"ctx {c}: POP x0 never waited for its input"
    stalls = {c: sorted(xa.XC_NAMES[s] for s in tb.stall_seen[c]) for c in range(n_ctx)}
    dut._log.info(f"tetrad program: {count + 1} invocations per cell, golden-identical; "
                  f"{tb.cycle} cycles; stalls seen {stalls}")


@pytest.mark.parametrize("test_level, description",
                         [(lvl, f"gatling_tetrad {lvl}") for lvl in reg_level_grid()])
def test_gatling_tetrad(request, test_level, description):
    seed = os.environ.get("SEED") or str(random.randint(0, 100000))
    gatling_sim.run_cell(
        module="test_gatling_tetrad", testcase="cocotb_test_tetrad_program",
        toplevel="gatling_tetrad_tb_top", filelist=gatling_sim.TETRAD_TB_FILELIST,
        cell=f"tetrad_program_{test_level}", test_level=test_level,
        parameters={"RESET_ADDR": "0"}, extra_env={"SEED": seed})
