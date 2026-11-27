#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""Host programs for gatling build-tetrad on the Nexys A7, authored ONCE.

The board host (build-tetrad/host/host_gatling_tetrad.py) and the cocotb UART
sim (dv/tests/test_gatling_tetrad_board_uart.py) run these same functions;
only the bridge's transport differs.

  smoke    harness ID, the memory system's BUILD_ID, every cell's config
           registers written and read back distinct, both memories empty
  tetrad   the hand-assembled tetrad program (gatling-rv32i
           dv/tbclasses/gatling/tetrad_program.py, the one the DV test runs):
           four contexts over a MAC, ADD, RELU and COMPARE cell, CLEAR + N
           ACCUMULATE, KICK, WAIT on all four, FLUSH, ECTX.  The contexts are
           started BEFORE any line is fed, so every context's first POP x0
           waits on its empty input memory; the host then feeds and drains
           over the UART, which keeps both memories near empty and full in
           turn.  Verdicts: every result line against alu-infer's golden, in
           order; lines consumed == lines fed; one KICK of value 1 per
           context; one FLUSH per context with its {tag, dest}, captured
           after all four KICKs; every context halted DONE (cause 8); no ALU
           opcode error; each context's retired count exact; POP x0 seen
           stalled on every context.
"""

from __future__ import annotations

import os
import random
import sys
import time
from typing import Optional

from gatling_board import BUILD_ID, NUM_HARTS
from gatling_programs import Report
from gatling_tetrad_board import HARNESS_ID, IN_DEPTH, TetradBoard, cell_reg

_REPO = os.environ["REPO_ROOT"]
for _p in (os.path.join(_REPO, "projects/components/riscv-ip/gatling-rv32i/dv/tbclasses"),
           os.path.join(_REPO, "projects/components/compute-eng-ip/alu-infer/dv/tbclasses")):
    if _p not in sys.path:
        sys.path.insert(0, _p)
from gatling import xcell_asm as xa                                 # noqa: E402
from gatling.tetrad_golden import line_ok, spec_str                  # noqa: E402
from gatling.tetrad_program import build_runs, tetrad_program        # noqa: E402

ALL = (1 << NUM_HARTS) - 1


def smoke(k: TetradBoard) -> Report:
    r = Report("smoke")
    hid, bid = k.harness_id(), k.build_id()
    if hid != HARNESS_ID:
        r.failures.append(f"harness ID 0x{hid:08X}, expected 0x{HARNESS_ID:08X}")
    if bid != BUILD_ID:
        r.failures.append(f"BUILD_ID 0x{bid:08X}, expected 0x{BUILD_ID:08X}")
    for c in range(NUM_HARTS):
        k.configure(c, func_sel=0x100 | c, op_lines=c & 3, threshold=0xA500 | c,
                    credit_batch=0x1234_5600 | c)
    for c in range(NUM_HARTS):
        got = tuple(k.read(cell_reg(c, n)) for n in ("FUNC", "LINES", "THR", "BATCH"))
        want = (0x100 | c, c & 3, 0xA500 | c, 0x1234_5600 | c)
        if got != want:
            r.failures.append(f"cell {c} config read back {got}, wrote {want}")
        occ_in, occ_out = k.occupancy(c)
        if occ_in or occ_out:
            r.failures.append(f"cell {c}: memories not empty ({occ_in} in, {occ_out} out)"
                              " -- reset the board")
    return r


def tetrad(k: TetradBoard, count: int = 96, seed: int = 1,
           timeout_s: float = 120.0, log=None) -> Report:
    r = Report("tetrad")
    prog = tetrad_program(count)
    words = prog.words()
    runs = build_runs(random.Random(seed), NUM_HARTS, count)

    k.set_run(0)                       # hold every context: clears its event bit
    for c in range(NUM_HARTS):
        occ_in, occ_out = k.occupancy(c)
        if occ_in or occ_out:
            r.failures.append(f"cell {c}: memories not empty at start ({occ_in} in, "
                              f"{occ_out} out) -- reset the board")
    if r.failures:
        return r
    k.clear_observers()
    for c, run in enumerate(runs):
        k.load(c, words)
        m = run.model
        k.configure(c, func_sel=m.func_sel, op_lines=m.op_lines, threshold=m.threshold,
                    credit_batch=run.word)

    # Start first, feed after: every first POP x0 waits on an empty memory
    k.set_run(ALL)
    pending = [list(run.lines) for run in runs]
    got = [[] for _ in range(NUM_HARTS)]
    t0 = time.time()
    polls = 0
    while True:
        polls += 1
        for c in range(NUM_HARTS):
            occ_in, occ_out = k.occupancy(c)
            for _ in range(min(IN_DEPTH - occ_in, len(pending[c]))):
                k.fill(c, pending[c].pop(0))
            for _ in range(occ_out):
                got[c].append(k.drain(c))
        _, done, _ = k.flags()
        if done == ALL and not any(pending) and all(
                k.occupancy(c)[1] == 0 for c in range(NUM_HARTS)):
            break
        if time.time() - t0 > timeout_s:
            r.failures.append(f"timeout after {polls} polls: done 0b{done:04b}, "
                              f"{[len(p) for p in pending]} lines unfed, "
                              f"{[len(g_) for g_ in got]} results")
            return r

    expect_instret = len(words) + (count - 1) * 4
    for c, run in enumerate(runs):
        m = run.model
        st = k.status(c)
        if not (st.halted and st.cause == xa.HALT_DONE):
            r.failures.append(f"ctx {c}: halted={st.halted} cause={st.cause}")
        if st.instret != expect_instret:
            r.failures.append(f"ctx {c}: {st.instret} retired, expected {expect_instret}")
        if len(got[c]) != len(run.specs):
            r.failures.append(f"ctx {c}: {len(got[c])} results, expected {len(run.specs)}")
        bad = [(i, v, s) for i, (v, s) in enumerate(zip(got[c], run.specs)) if not line_ok(v, s)]
        for i, v, s in bad[:3]:
            r.failures.append(f"ctx {c} (op {m.opcode}) result {i}: 0x{v:08x}, "
                              f"expected {spec_str(s)}")
        cons = k.consumed(c)
        if cons != len(run.lines):
            r.failures.append(f"ctx {c}: {cons} lines consumed, {len(run.lines)} fed")
        kval, kcnt = k.kick(c)
        if (kval, kcnt) != (1, 1):
            r.failures.append(f"ctx {c}: kick value {kval}, {kcnt} kicks")
        f = k.flush(c)
        if not f.valid or f.count != 1 or (f.dest, f.tag) != (run.dest, run.tag):
            r.failures.append(f"ctx {c}: flush {f}, expected one to "
                              f"dest 0x{run.dest:x} tag {run.tag}")
        if f.kicks_at_capture != NUM_HARTS:
            r.failures.append(f"ctx {c}: FLUSH captured after {f.kicks_at_capture} kicks "
                              f"(before the barrier released)")
        s = k.stat(c)
        if s.alu_err or s.underflow:
            r.failures.append(f"ctx {c}: {s}")
        if not s.stall_seen & (1 << xa.XC_POP):
            r.failures.append(f"ctx {c}: POP x0 never seen waiting for its input")
        r.rows.append(f"ctx {c} op {m.opcode:2}: {len(got[c])} results, {cons} lines, "
                      f"stalls 0b{s.stall_seen:08b}, instret {st.instret}, "
                      f"cycles {st.cycles}")
    r.numbers = {"invocations": count + 1, "polls": polls,
                 "seconds": round(time.time() - t0, 2)}
    if log:
        log(r.line())
    return r


def all_programs(k: TetradBoard, count: Optional[int] = None, seed: int = 1):
    return [smoke(k), tetrad(k, count=count or 96, seed=seed)]
