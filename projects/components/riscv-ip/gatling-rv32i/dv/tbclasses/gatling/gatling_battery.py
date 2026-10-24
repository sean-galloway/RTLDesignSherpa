# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: gatling_battery
# Purpose: rv32ui-p-* battery for the gatling barrel: four DIFFERENT images
#          run at once, one per context, rotated so every context runs every
#          image; each (context, image) is scored by the riscv-tests verdict
#          and, at the lockstep levels, diffed against kestrel's golden
#          interpreter and spike.
#
# Documentation: projects/components/riscv-ip/gatling-rv32i/docs/gatling_mas
# Subsystem: riscv-ip/gatling-rv32i
#
# Author: sean galloway
# Created: 2026-10-21

"""Concurrent rv32ui battery for gatling.

Round r runs image ``names[(r + c) % n]`` on context c, so after n rounds
every context has run every image and in every round the four contexts run
four different programs side by side -- the isolation case, not just four
copies of one.  (With fewer than four images some contexts share one.)

The verdict, the expected-halt table, the image normalizer, the ELF reader,
spike and the lockstep diff are kestrel's (``tbclasses.kestrel.
rv32ui_battery``): gatling's ISA contract is kestrel's, so its golden is too.
The golden interpreter and spike run once per image; each context's trace is
checked against them separately.

``discover``/``image_words``/``image_elf`` are the subclass seam, as in
kestrel's RV32UIBattery (the fuzz battery overrides them).
"""

from pathlib import Path

from gatling.gatling_tb import NUM_HARTS, GatlingTB
from tbclasses.kestrel.rv32i_interpreter import RV32IInterpreter
from tbclasses.kestrel.rv32ui_battery import (
    EXPECTED_HALTS,
    GATE_TESTS,
    LINK_BASE,
    discover_tests,
    lockstep_diff,
    normalize_image,
    parse_spike_log,
    read_elf32,
    run_spike,
)

ALL_HARTS = (1 << NUM_HARTS) - 1
# kestrel's per-image budget is 100,000 cycles at CPI 1-2; a context here
# retires once per four cycles.
_ROUND_CYCLES = 100_000 * NUM_HARTS


class GatlingBattery:
    """Run images four at a time on the barrel and score every context."""

    title = "gatling rv32ui battery"
    # The golden full-field diff runs at EVERY level: a verdict alone cannot
    # see cross-context leakage (a context reading another's registers can
    # still compute 0 == 0 and retire gp == 1).  Spike, the costly half,
    # runs at these levels.
    lockstep_levels = ("func",)
    # True: n rounds, every context runs every image.  False: each image runs
    # once, four different per round (ceil(n/4) rounds, the last wrapping) --
    # the fuzz battery's setting, where more distinct pairings per sim cycle
    # beat repeating a stream on every context.
    rotate = True

    def __init__(self, dut, repo_root, level, work_dir, tests=None,
                 tb_class=None):
        self.dut = dut
        self.repo_root = str(repo_root)
        self.level = level
        self.work_dir = Path(work_dir)
        self.work_dir.mkdir(parents=True, exist_ok=True)
        self.tests = tests
        self.tb_class = tb_class or GatlingTB
        self.results = []
        self._golden = {}
        self._spike = {}

    # ---- subclass seam ----------------------------------------------------
    def discover(self):
        names = discover_tests(self.repo_root)
        if self.tests is not None:
            wanted = set(self.tests)
            names = [n for n in names if n in wanted]
        elif self.level == "gate":
            names = [n for n in names if n in GATE_TESTS]
        return names

    def image_words(self, name):
        return normalize_image(self.repo_root, name)

    def image_elf(self, name):
        return Path(self.repo_root) / "vendor" / "riscv-tests" / "isa" / f"rv32ui-p-{name}"

    def expected_halt(self, name):
        return EXPECTED_HALTS.get(name)

    # ---- run --------------------------------------------------------------
    async def run(self):
        tb = self.tb_class(self.dut, reset_addr=LINK_BASE)
        await tb.ensure_clock()
        names = self.discover()
        n = len(names)
        rounds = n if self.rotate else -(-n // NUM_HARTS)
        self.dut._log.info(f"{self.title} ({self.level} level): {n} images, "
                           f"{rounds} rounds of {NUM_HARTS} contexts")
        for r in range(rounds):
            if self.rotate:
                plan = [names[(r + c) % n] for c in range(NUM_HARTS)]
            else:
                plan = [names[(NUM_HARTS * r + c) % n] for c in range(NUM_HARTS)]
            await self._round(tb, r, plan)

        failures = [f"{x['name']}@ctx{x['ctx']}" for x in self.results if not x["passed"]]
        passed = len(self.results) - len(failures)
        self.dut._log.info(f"{self.title} summary: {passed}/{len(self.results)} "
                           f"(context, image) runs passed"
                           + (f", failures: {failures}" if failures else ""))
        self._write_summary()
        assert not failures, f"{self.title} failures: {failures}"
        return self.results

    async def _round(self, tb, r, plan):
        images = [self.image_words(name) for name in plan]
        tohost = {}
        for c, name in enumerate(plan):
            _, symbols = read_elf32(self.image_elf(name))
            if symbols.get("tohost") is None:
                raise ValueError(f"{name}: no tohost symbol")
            tohost[c] = symbols["tohost"]

        await tb.assert_reset()
        await tb.release_reset()
        for c, words in enumerate(images):
            await tb.backdoor_load(c, words)
        tb.clear_traces()
        tb.set_run(ALL_HARTS)
        try:
            await tb.run_until_halted(ALL_HARTS, max_cycles=_ROUND_CYCLES,
                                      watch_tohost=tohost)
            timeout = None
        except AssertionError as exc:
            timeout = str(exc)

        for c, name in enumerate(plan):
            self.results.append(self._score(tb, c, name, images[c], timeout))
            x = self.results[-1]
            self.dut._log.info(
                f"round {r} ctx {c} {name}: {'PASS' if x['passed'] else 'FAIL'} "
                f"cause={x['halt_cause']} gp={x['gp']:#x} beats={x['beats']} {x['detail']}")

    def _score(self, tb, c, name, words, timeout):
        hart = tb.harts[c]
        res = {"name": name, "ctx": c, "passed": False, "halt_cause": hart.halt_cause,
               "gp": hart.gp_at_halt() if hart.trace else 0, "beats": len(hart.trace),
               "detail": ""}
        if hart.halt_cause is None:
            res["detail"] = f"timeout: {timeout}"
            return res
        expected = self.expected_halt(name)
        if expected is not None:
            passed = hart.halt_cause == expected[0]
        else:
            passed = (hart.halt_cause == 1 and res["gp"] == 1) or (1 in hart.tohost_writes)
        try:
            tb.check_window(c)
        except AssertionError as exc:
            res["detail"] = f"barrel: {exc}"
            return res
        ok, detail = self._golden_diff(hart, name, words)
        if ok and self.level in self.lockstep_levels:
            ok, detail = self._spike_lockstep(hart, name, expected)
        res["detail"] = detail
        if not ok:
            return res
        res["passed"] = passed
        return res

    def _golden_diff(self, hart, name, words):
        if name not in self._golden:
            golden = RV32IInterpreter(words, reset_addr=LINK_BASE)
            golden.run()
            self._golden[name] = golden
        golden = self._golden[name]
        try:
            hart.check_halt(expected_cause=golden.halt_cause,
                            expected_halt_pc=golden.halt_pc)
            hart.check_order_sequence()
            hart.check_x0_rd_zero()
            hart.check_trace(golden.trace)
        except AssertionError as exc:
            return False, f"golden diff: {exc}"
        return True, f"golden ok ({len(golden.trace)} beats)"

    def _spike_lockstep(self, hart, name, expected):
        if name not in self._spike:
            log_path = self.work_dir / f"spike_{name}.log"
            rc = run_spike(self.image_elf(name), log_path)
            self._spike[name] = (rc, parse_spike_log(log_path))
        rc, records = self._spike[name]
        entry, _ = read_elf32(self.image_elf(name))
        ok, errors, stub_traps, term_trap = lockstep_diff(
            hart.trace, hart.halt_pc, entry, records)
        detail = (f"spike rc={rc} stream ok, {len(records)} records, "
                  f"{len(stub_traps)} stub trap(s), term trap {term_trap}")
        if expected is not None:
            if term_trap != expected[1]:
                ok = False
                errors.append(f"expected spike {expected[1]} at the halt pc, got {term_trap}")
        elif rc != 0:
            ok = False
            errors.append("spike timed out or failed to start" if rc is None
                          else f"spike exit code {rc} (tohost != 1)")
        return (True, detail) if ok else (False, "; ".join(errors))

    def _write_summary(self):
        lines = [f"{self.title} ({self.level} level) "
                 f"{sum(x['passed'] for x in self.results)}/{len(self.results)}",
                 f"{'image':<12} {'ctx':<3} {'status':<6} {'cause':<5} {'gp':<10} "
                 f"{'beats':<6} detail"]
        for x in self.results:
            cause = x["halt_cause"] if x["halt_cause"] is not None else "N/A"
            lines.append(f"{x['name']:<12} {x['ctx']:<3} {'PASS' if x['passed'] else 'FAIL':<6} "
                         f"{cause!s:<5} {x['gp']:#010x} {x['beats']:<6} {x['detail']}")
        (self.work_dir / f"gatling_battery_summary_{self.level}.txt").write_text(
            "\n".join(lines) + "\n")
