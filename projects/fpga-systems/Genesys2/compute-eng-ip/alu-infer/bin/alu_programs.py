#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""Host programs for the ALU harness, authored ONCE.

The board host (build-infer/host/host_alu.py) and the cocotb UART sim
(dv/tests/test_alu_harness_uart.py) run these same functions against an
AluHarness; only the bridge's transport differs.

Every program returns a Report: a name, a list of failure strings (empty =
pass) and a few measured numbers. Expected values are exact by construction:
small integers in the float formats, and the PWL row against its bit-level
model (projects/components/compute-eng-ip/alu-infer/bin/alu_infer_pwl.py).
The full numeric verification of every row lives in the alu-infer DV; this
proves the silicon matches it on a set of known answers, at speed.
"""

from __future__ import annotations

import os
import random
import sys
from dataclasses import dataclass, field
from typing import Callable, Dict, List

from alu_harness import (AluHarness, Cmd, RunResult, func_sel, SLOT_ALU_INFER,
                         BUILD_ID, STALL_NONE, STALL_RANDOM, STALL_FILL)

_PWL = os.path.join(os.environ["REPO_ROOT"], "projects/components/compute-eng-ip/alu-infer/bin")
if _PWL not in sys.path:
    sys.path.insert(0, _PWL)
import alu_infer_pwl as pwl  # noqa: E402

# Opcodes and formats (alu-infer rtl/includes/alu_infer_pkg.sv)
COPY, ADD, SUB, MUL, MAC, MINMAX, CMP, RELU = range(8)
REDUCE, PWL, PWL_LUT, CONST, CVT = 8, 9, 10, 11, 21
BF16, INT8, FP32, FP8 = 0, 1, 2, 3
HOLD, ACCUM, CLEAR, DRAIN = 0, 1, 2, 3


@dataclass
class Report:
    name: str
    failures: List[str] = field(default_factory=list)
    numbers: Dict[str, float] = field(default_factory=dict)

    @property
    def ok(self) -> bool:
        return not self.failures

    def line(self) -> str:
        nums = " ".join(f"{k}={v}" for k, v in self.numbers.items())
        verdict = "PASS" if self.ok else f"FAIL ({len(self.failures)})"
        return f"{self.name:14} {verdict:10} {nums}"


def bf(x: float) -> int:
    return pwl.bf16_rne(x)


def bf2(lo: float, hi: float) -> int:
    return (bf(hi) << 16) | bf(lo)


def fp32(x: float) -> int:
    return pwl.fp32_bits(x)


# ---------------------------------------------------------------------------
# smoke
# ---------------------------------------------------------------------------

def smoke(h: AluHarness) -> Report:
    r = Report("smoke")
    bid = h.build_id()
    if bid != BUILD_ID:
        r.failures.append(f"BUILD_ID 0x{bid:08X}, expected 0x{BUILD_ID:08X}")
    for w, rd, ok in h.scratch_check():
        if not ok:
            r.failures.append(f"SCRATCH wrote 0x{w:08X} read 0x{rd:08X}")
    s = h.slot_info()
    if s["kind"] != SLOT_ALU_INFER:
        r.failures.append(f"SLOT_INFO.kind {s['kind']}, expected {SLOT_ALU_INFER} (alu-infer)")
    r.numbers.update(depth=s["depth"], clk_mhz=s["clk_mhz"], pipe_depth=s["pipe_depth"],
                     full=int(all(s["en"].values())))
    return r


# ---------------------------------------------------------------------------
# known answers
# ---------------------------------------------------------------------------

def _known_answer_cases(slot: dict):
    """(Cmd, expected line, expected flags, expected err) per case."""
    en = slot["en"]
    c = []
    # bf16 v1 rows: exact small integers
    c.append((Cmd(a=bf2(1, 2), func_sel=func_sel(COPY)), bf2(1, 2), 0, False))
    c.append((Cmd(a=bf2(1, 3), b=bf2(2, 4), func_sel=func_sel(ADD)), bf2(3, 7), 0, False))
    c.append((Cmd(a=bf2(5, 2), b=bf2(1, 3), func_sel=func_sel(SUB)), bf2(4, -1), 0, False))
    c.append((Cmd(a=bf2(3, -2), b=bf2(2, 4), func_sel=func_sel(MUL)), bf2(6, -8), 0, False))
    c.append((Cmd(a=bf2(1, 5), b=bf2(2, 4), func_sel=func_sel(MINMAX, 0)), bf2(1, 4), 0, False))
    c.append((Cmd(a=bf2(1, 5), b=bf2(2, 4), func_sel=func_sel(MINMAX, 1)), bf2(2, 5), 0, False))
    c.append((Cmd(a=bf2(1, 5), b=bf2(2, 4), func_sel=func_sel(CMP, 0)), 0, 0b01, False))
    c.append((Cmd(a=bf2(1, 5), imm=bf(3), func_sel=func_sel(CMP, 1)), 0, 0b01, False))
    c.append((Cmd(a=bf2(-1, 2), func_sel=func_sel(RELU)), bf2(0, 2), 0, False))
    # MAC chain: clear, 2*3, 1*1 (lane 1: 4*0.5, 1*1), drain
    c.append((Cmd(func_sel=func_sel(MAC), acc_ctrl=CLEAR), 0, 0, False))
    c.append((Cmd(a=bf2(2, 4), b=bf2(3, 0.5), func_sel=func_sel(MAC), acc_ctrl=ACCUM), bf2(6, 2), 0, False))
    c.append((Cmd(a=bf2(1, 1), b=bf2(1, 1), func_sel=func_sel(MAC), acc_ctrl=ACCUM), bf2(7, 3), 0, False))
    c.append((Cmd(func_sel=func_sel(MAC), acc_ctrl=DRAIN), bf2(7, 3), 0, False))
    # unassigned opcode: zero line, err_opcode
    c.append((Cmd(a=bf2(1, 1), func_sel=func_sel(31)), 0, 0, True))
    if en["int8"]:
        c.append((Cmd(a=0x7F64_0102, b=0x0164_0304, func_sel=func_sel(ADD, 0, INT8)),
                  0x7F7F_0406, 0, False))           # 127+1 and 100+100 saturate
    else:
        c.append((Cmd(a=1, b=1, func_sel=func_sel(ADD, 0, INT8)), 0, 0, True))
    if en["fp32"]:
        c.append((Cmd(a=fp32(1.5), b=fp32(2.25), func_sel=func_sel(ADD, 0, FP32)), fp32(3.75), 0, False))
        c.append((Cmd(a=fp32(1.5), b=fp32(-4.0), func_sel=func_sel(MUL, 0, FP32)), fp32(-6.0), 0, False))
    if en["fp8"]:
        c.append((Cmd(a=0x3838_3838, b=0x3838_4040, func_sel=func_sel(ADD, 0, FP8)),
                  0x4040_4444, 0, False))           # e4m3 lanes 0..3: 1+2=3 (0x44) x2, 1+1=2 (0x40) x2
    if en["cvt"]:
        c.append((Cmd(a=bf2(1.5, -2), b=0, func_sel=func_sel(CVT, FP32, BF16)), fp32(1.5), 0, False))
    if en["reduce"]:
        c.append((Cmd(func_sel=func_sel(REDUCE, 0), acc_ctrl=CLEAR), 0, 0, False))
        c.append((Cmd(a=bf2(1, 2), func_sel=func_sel(REDUCE, 0), acc_ctrl=ACCUM), bf2(1, 2), 0, False))
        c.append((Cmd(a=bf2(3, 4), func_sel=func_sel(REDUCE, 0), acc_ctrl=ACCUM), bf2(4, 6), 0, False))
        c.append((Cmd(func_sel=func_sel(REDUCE, 2), acc_ctrl=DRAIN), bf2(10, 10), 0, False))
    return c


def known_answer(h: AluHarness) -> Report:
    r = Report("known_answer")
    cases = _known_answer_cases(h.slot_info())
    h.load([c[0] for c in cases])
    rr = h.run(len(cases))
    _check_run(r, rr, len(cases))
    for i, ((cmd, line, flags, err), got) in enumerate(zip(cases, rr.results)):
        if (got.line, got.flags, got.err) != (line, flags, err):
            r.failures.append(f"case {i} func_sel=0x{cmd.func_sel:03X}: got line 0x{got.line:08X} "
                              f"flags 0x{got.flags:X} err {got.err}, expected 0x{line:08X} "
                              f"0x{flags:X} {err}")
    r.numbers.update(cases=len(cases), errs=rr.err_count)
    return r


# ---------------------------------------------------------------------------
# stream / backpressure / latency
# ---------------------------------------------------------------------------

def _check_run(r: Report, rr: RunResult, n: int) -> None:
    if not rr.done or rr.retired != n or rr.issued != n:
        r.failures.append(f"run did not complete: issued {rr.issued}, retired {rr.retired} of {n}")


def stream(h: AluHarness, n: int = 0) -> Report:
    """n back-to-back copies: in order, and II=1 from the hardware timestamps."""
    r = Report("stream")
    n = n or h.slot_info()["depth"]
    cmds = [Cmd(a=(0x1000_0000 + 0x0101_0101 * i) & 0xFFFF_FFFF, func_sel=func_sel(COPY))
            for i in range(n)]
    h.load(cmds)
    rr = h.run(n)
    _check_run(r, rr, n)
    for i, (c, got) in enumerate(zip(cmds, rr.results)):
        if got.line != c.a:
            r.failures.append(f"entry {i}: 0x{got.line:08X}, expected 0x{c.a:08X}")
            break
    issue_gaps = {b.issue - a.issue for a, b in zip(rr.results, rr.results[1:])}
    retire_gaps = {b.retire - a.retire for a, b in zip(rr.results, rr.results[1:])}
    if issue_gaps != {1} or retire_gaps != {1}:
        r.failures.append(f"not II=1: issue gaps {sorted(issue_gaps)}, retire gaps {sorted(retire_gaps)}")
    r.numbers.update(n=n, cycles=rr.cycles, stall_cycles=rr.stall_cycles,
                     latency=rr.results[0].latency if rr.results else -1)
    return r


def backpressure(h: AluHarness, n: int = 64, seed: int = 1) -> Report:
    """Mixed ops under a full stall (fill the FIFO, then drain) and random
    consumer ready: every result in order, issue backpressured."""
    r = Report("backpressure")
    rnd = random.Random(seed)
    vals = [bf2(rnd.randint(-8, 8), rnd.randint(-8, 8)) for _ in range(2 * n)]
    cmds, exp = [], []
    for i in range(n):
        a, b = vals[2 * i], vals[2 * i + 1]
        k = i % 3
        if k == 0:
            cmds.append(Cmd(a=a, func_sel=func_sel(COPY)))
            exp.append(a)
        elif k == 1:
            cmds.append(Cmd(a=a, func_sel=func_sel(RELU)))
            lo, hi = pwl.bf16_float(a & 0xFFFF), pwl.bf16_float(a >> 16)
            exp.append(bf2(max(lo, 0.0), max(hi, 0.0)))
        else:
            cmds.append(Cmd(a=a, b=b, func_sel=func_sel(ADD)))
            exp.append(bf2(pwl.bf16_float(a & 0xFFFF) + pwl.bf16_float(b & 0xFFFF),
                           pwl.bf16_float(a >> 16) + pwl.bf16_float(b >> 16)))
    h.load(cmds)
    for mode, name in ((STALL_FILL, "fill"), (STALL_RANDOM, "random")):
        rr = h.run(n, stall_mode=mode)
        _check_run(r, rr, n)
        for i, (got, e) in enumerate(zip(rr.results, exp)):
            if got.line != e:
                r.failures.append(f"{name} entry {i}: 0x{got.line:08X}, expected 0x{e:08X}")
                break
        if rr.stall_cycles == 0:
            r.failures.append(f"{name}: issue was never backpressured (STALL_CYCLES = 0)")
        if [x.retire for x in rr.results] != sorted(x.retire for x in rr.results):
            r.failures.append(f"{name}: results retired out of order")
        r.numbers[f"{name}_stall"] = rr.stall_cycles
        r.numbers[f"{name}_cycles"] = rr.cycles
    return r


def latency(h: AluHarness) -> Report:
    """Each result port at its built latency, one isolated invocation each."""
    r = Report("latency")
    s = h.slot_info()
    probes = [("comb", Cmd(a=bf2(1, 1), func_sel=func_sel(COPY)), 0),
              ("adder", Cmd(a=bf2(1, 1), b=bf2(1, 1), func_sel=func_sel(ADD)), s["add_lat"]),
              ("mul", Cmd(a=bf2(1, 1), b=bf2(1, 1), func_sel=func_sel(MUL)), s["mul_lat"]),
              ("acc", Cmd(a=bf2(1, 1), b=bf2(1, 1), func_sel=func_sel(MAC), acc_ctrl=ACCUM),
               s["mac_lat"])]
    for name, cmd, want in probes:
        h.load([cmd])
        rr = h.run(1)
        _check_run(r, rr, 1)
        got = rr.results[0].latency if rr.results else -1
        r.numbers[name] = got
        if got != want:
            r.failures.append(f"{name}: latency {got}, expected {want}")
    return r


# ---------------------------------------------------------------------------
# PWL: load a table in-band, evaluate against the bit-level row model
# ---------------------------------------------------------------------------

def pwl_eval(h: AluHarness, func: str = "sigmoid", n: int = 64, seed: int = 2) -> Report:
    r = Report(f"pwl_{func}")
    if not h.slot_info()["en"]["pwl"]:
        r.numbers["skipped"] = 1
        return r
    table = pwl.build_table(func)
    h.load([Cmd(a=pwl.entry_word(s, c), b=i, func_sel=func_sel(PWL_LUT, 0))
            for i, (s, c) in enumerate(table)])
    rr = h.run(len(table))
    _check_run(r, rr, len(table))
    lo, hi = pwl.DOMAIN[func]
    rnd = random.Random(seed)
    xs = [pwl.bf16_rne(lo + (hi - lo) * rnd.random()) for _ in range(2 * n)]
    cmds = [Cmd(a=(xs[2 * i + 1] << 16) | xs[2 * i], func_sel=func_sel(PWL)) for i in range(n)]
    h.load(cmds)
    rr = h.run(n)
    _check_run(r, rr, n)
    for i, got in enumerate(rr.results):
        want = (pwl.pwl_eval(table, xs[2 * i + 1]) << 16) | pwl.pwl_eval(table, xs[2 * i])
        if got.line != want:
            r.failures.append(f"x=(0x{xs[2*i]:04X}, 0x{xs[2*i+1]:04X}): 0x{got.line:08X}, "
                              f"expected 0x{want:08X}")
            break
    r.numbers["points"] = 2 * n
    return r


PROGRAMS: Dict[str, Callable[[AluHarness], Report]] = {
    "smoke": smoke,
    "known_answer": known_answer,
    "stream": stream,
    "backpressure": backpressure,
    "latency": latency,
    "pwl": pwl_eval,
}


def run_all(h: AluHarness, names=None) -> List[Report]:
    return [PROGRAMS[n](h) for n in (names or PROGRAMS)]
