# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: test_gatling_arch
# Purpose: riscv-arch-test 3.10.0 rv32i_m/I on the gatling barrel: four
#          different tests at once, one per context, rotated so every
#          context runs every test; each (context, test) signature against
#          the RISCOF reference signature (spike and Sail agree).
#
# Documentation: vault/handbook/dv/riscv-arch-test.md
# Subsystem: riscv-ip/gatling-rv32i
#
# Author: sean galloway
# Created: 2026-11-22

"""gatling-rv32i riscv-arch-test signature compare.

Round r runs test ``names[(r + c) % n]`` on context c (the rv32ui battery's
rotation), so each context runs every test and the four running side by side
are always different programs.  A context passes on an ecall halt at
rvmodel_halt and a signature, read from its own memory bank, equal to
the reference's (spike's, which Sail must reproduce); every round also
checks the barrel (one retirement per context per four-cycle window).  The
build, both references and the compare are the shared
``common-rv32i/dv/arch_test/rv32_arch_test.py``.
"""

import os
import sys
from pathlib import Path

import cocotb
import pytest

import gatling_sim
from TBClasses.shared.test_levels import reg_level_grid

_ARCH_DIR = str(Path(__file__).resolve().parents[3] / "common-rv32i" / "dv" / "arch_test")
if _ARCH_DIR not in sys.path:
    sys.path.insert(0, _ARCH_DIR)

import rv32_arch_test as arch                                # noqa: E402
from gatling.gatling_tb import GatlingTB                     # noqa: E402

MEM_WORDS = 1 << 19          # 2 MiB per context (jal-01 is a 1.7 MiB image)
# The longest test retires under 7,000 instructions; a context retires once
# per four cycles.
ROUND_CYCLES = 50_000 * 4


async def _round(dut, tb, r, plan, dirty, results):
    await tb.assert_reset()
    for c, test in enumerate(plan):
        arch.poke(dut.mem, MEM_WORDS, {a: 0 for a in dirty[c]}, bank=c)
        arch.poke(dut.mem, MEM_WORDS, test.load_words(), bank=c)
        dirty[c] = test.dirty_words()
    await tb.release_reset()
    tb.clear_traces()
    tb.set_run(tb.all_harts)
    try:
        await tb.run_until_halted(tb.all_harts, max_cycles=ROUND_CYCLES)
        timeout = None
    except AssertionError as exc:
        timeout = str(exc)

    for c, test in enumerate(plan):
        hart = tb.harts[c]
        res = {"name": f"{test.name}@ctx{c}", "passed": False}
        if hart.halt_cause is None:
            res["detail"] = f"no halt: {timeout}"
        elif hart.halt_cause != 1 or hart.halt_pc != test.halt_pc:
            res["detail"] = (f"halted cause {hart.halt_cause} at 0x{hart.halt_pc:08x}, "
                             f"expected ecall (1) at rvmodel_halt 0x{test.halt_pc:08x}")
        else:
            try:
                tb.check_window(c)
                ok, detail = arch.compare(
                    test, arch.peek_signature(dut.mem, MEM_WORDS, test, bank=c),
                    f"gatling-ctx{c}")
                res["passed"] = ok
                res["detail"] = f"{detail}; {len(hart.trace)} retired"
            except AssertionError as exc:
                res["detail"] = f"barrel: {exc}"
        results.append(res)
        dut._log.info(f"round {r} ctx {c} {test.name}: "
                      f"{'PASS' if res['passed'] else 'FAIL'} {res['detail']}")

@cocotb.test(timeout_time=6000, timeout_unit="sec")
async def cocotb_test_gatling_arch(dut):
    """Every rv32i_m/I arch test on every context, four different at a time."""
    repo_root = os.environ["REPO_ROOT"]
    level = os.environ.get("TEST_LEVEL", "func")
    work_dir = Path(os.path.dirname(os.environ.get("LOG_PATH", "."))) / f"arch_test_{level}"
    work_dir.mkdir(parents=True, exist_ok=True)

    tb = GatlingTB(dut, reset_addr=arch.LINK_BASE)
    await tb.ensure_clock()
    names = arch.discover(repo_root, level)
    tests = {name: arch.build(repo_root, name, work_dir) for name in names}
    n = len(names)
    dut._log.info(f"riscv-arch-test {arch.PINNED_TAG} rv32i_m/I on gatling "
                  f"({level} level): {n} tests x {tb.num_harts} contexts, {n} rounds")

    results = []
    dirty = [set() for _ in range(tb.num_harts)]
    for r in range(n):
        plan = [tests[names[(r + c) % n]] for c in range(tb.num_harts)]
        await _round(dut, tb, r, plan, dirty, results)

    failures = [x["name"] for x in results if not x["passed"]]
    summary = arch.write_summary(work_dir, "gatling", level, results)
    dut._log.info(f"riscv-arch-test summary: {len(results) - len(failures)}/"
                  f"{len(results)} (context, test) runs passed ({summary})"
                  + (f", failures: {failures}" if failures else ""))
    assert not failures, f"riscv-arch-test failures on gatling: {failures}"


@pytest.mark.parametrize("test_level, description",
                         [(lvl, f"gatling_arch {lvl}") for lvl in reg_level_grid()])
def test_gatling_arch(request, test_level, description):
    gatling_sim.run_cell(
        module="test_gatling_arch", testcase="cocotb_test_gatling_arch",
        toplevel="gatling_tb_top", filelist=gatling_sim.TB_FILELIST,
        cell=f"test_gatling_arch_{test_level}", test_level=test_level,
        parameters={"RESET_ADDR": str(arch.LINK_BASE), "MEM_WORDS": str(MEM_WORDS)})
