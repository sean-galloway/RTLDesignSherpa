# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""bch loop smoke: bypass, a clean run, a run at e = t, a run at e = t + 1.

Four runs that between them touch every path: the generator/checker plumbing
(bypass), the codec with nothing to correct, the decoder correcting the
maximum, and the decoder refusing one more. Each is judged by
bch_loop_programs.verdict against the profile's t.
"""
from __future__ import annotations

import bch_env  # noqa: F401
from sequence import Sequence
import bch_loop_programs as progs
from bch_loop import BchLoopDriver


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
                ("clean", lambda: progs.run(drv, BchLoopDriver.INJ_NONE, blocks=blocks)),
                (f"e={t}", lambda: progs.run(drv, BchLoopDriver.INJ_COUNT, count=t, blocks=blocks)),
                (f"e={t + 1}", lambda: progs.run(drv, BchLoopDriver.INJ_COUNT, count=t + 1, blocks=blocks)),
                ("debug", lambda: progs.run(drv, BchLoopDriver.INJ_DEBUG, count=1, rate=step, blocks=blocks))]
        failures = []
        for label, fn in plan:
            r = fn()
            bad = progs.verdict(r, t)
            if label == "debug":
                ctx.say(f"[smoke] debug details: inj_symbols={r.inj_symbols} inj_blocks={r.inj_blocks} "
                        f"inj_over_t={r.inj_over_t} last={getattr(r, 'inj_last', 'n/a')}")
                if r.a.blk_corr != blocks or r.a.sym_corr != blocks:
                    bad.append(f"debug walk: expected {blocks} corrected blocks with 1 symbol each, "
                               f"got corr={r.a.blk_corr} sym={r.a.sym_corr}")
            results[label] = r
            ctx.say(f"[smoke] {label:>7}: {r.cycles_per_block:6.1f} cycles/block, "
                    f"ok/corr/unc={r.a.blk_ok}/{r.a.blk_corr}/{r.a.blk_unc} sym={r.a.sym_corr} "
                    f"data={'x' if r.a.data_err else 'ok'} -> {'PASS' if not bad else 'FAIL'}")
            for b in bad:
                ctx.say(f"          {b}")
            failures += [f"{label}: {b}" for b in bad]
        if failures:
            raise RuntimeError("; ".join(failures))
        return results
