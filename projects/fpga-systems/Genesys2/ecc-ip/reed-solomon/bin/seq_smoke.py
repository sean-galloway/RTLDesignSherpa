# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""rs loop smoke: bypass, a clean run, a run at e = t, a run at e = t + 1.

Four runs that between them touch every path: the generator/checker plumbing
(bypass), the codec with nothing to correct, both decoders correcting the
maximum, and both decoders refusing one more. Each is judged by
rs_loop_programs.verdict against the profile's t.
"""
from __future__ import annotations

import rs_env  # noqa: F401
from sequence import Sequence
import rs_loop_programs as progs
from rs_loop import RsLoopDriver


class Smoke(Sequence):
    name = "smoke"
    requires = ("init",)
    description = "bypass, clean, e = t, e = t + 1"

    def run(self, ctx):
        drv = ctx.bus
        t = ctx.result("init").profile["t"]
        n = ctx.result("init").profile["n"]
        blocks = ctx.param("blocks", 16)
        results = {}
        step = n // blocks if n > blocks else 1
        plan = [("bypass", lambda: progs.bypass(drv, blocks)),
                ("clean", lambda: progs.run(drv, RsLoopDriver.INJ_NONE, blocks=blocks)),
                (f"e={t}", lambda: progs.run(drv, RsLoopDriver.INJ_COUNT, count=t, blocks=blocks)),
                (f"e={t + 1}", lambda: progs.run(drv, RsLoopDriver.INJ_COUNT, count=t + 1, blocks=blocks)),
                ("debug", lambda: progs.run(drv, RsLoopDriver.INJ_DEBUG, count=1, rate=step, blocks=blocks))]
        failures = []
        for label, fn in plan:
            r = fn()
            bad = progs.verdict(r, t)
            if label == "debug":
                for d in r.present:
                    if d.blk_corr != blocks or d.sym_corr != blocks:
                        bad.append(f"{d.name} debug walk: expected {blocks} corrected blocks with "
                                   f"1 symbol each, got corr={d.blk_corr} sym={d.sym_corr}")
            results[label] = r
            ctx.say(f"[smoke] {label:>7}: {r.cycles_per_block:6.1f} cycles/block, "
                    f"riBM ok/corr/unc={r.a.blk_ok}/{r.a.blk_corr}/{r.a.blk_unc}, "
                    f"Euclid ok/corr/unc={r.b.blk_ok}/{r.b.blk_corr}/{r.b.blk_unc}, "
                    f"A=B={'yes' if not r.cmp_err else 'NO'} -> {'PASS' if not bad else 'FAIL'}")
            for b in bad:
                ctx.say(f"          {b}")
            failures += [f"{label}: {b}" for b in bad]
        if failures:
            raise RuntimeError("; ".join(failures))
        return results
