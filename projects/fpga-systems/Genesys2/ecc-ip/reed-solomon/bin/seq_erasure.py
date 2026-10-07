# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""rs loop erasure: marked runs across the doubled bound (TASK-002).

INJ_CFG.mark makes the injector's hit mask ride the decoders' in_erasure
sideband, so the decoder is TOLD which symbols were corrupted. The correction
bound doubles: f = 1 .. 2t corrects, every block, with exactly f symbols; and
f = 2t+1 is refused by inspection -- every block uncorrectable,
deterministically, no miscorrection case (the decoder never has to find the
errors, so the beyond-threshold acceptance the errors-only sweep tolerates
cannot happen).

Skipped, not failed, when TOPOLOGY.erasure reads 0: a bitstream built with
ERASURE_SUPPORT = 0 has nowhere for the flags to go, and a "skip" here is the
host reading the config register rather than assuming the build.
"""
from __future__ import annotations

import rs_env  # noqa: F401
from sequence import Sequence
import rs_loop_programs as progs
from rs_loop import RsLoopDriver


class Erasure(Sequence):
    name = "erasure"
    requires = ("init",)
    description = "marked runs: f = t, 2t correct; f = 2t+1 refused (skipped without the erasure build)"

    def run(self, ctx):
        drv = ctx.bus
        t = ctx.result("init").profile["t"]
        if not drv.topology()["erasure"]:
            ctx.say("[erasure] TOPOLOGY.erasure = 0: this bitstream has no "
                    "erasure path; skipping (build with ERASURE_SUPPORT = 1)")
            return []
        blocks = ctx.param("blocks", 8)
        rows = []
        for f in (t, 2 * t, 2 * t + 1):
            r = progs.run(drv, RsLoopDriver.INJ_COUNT, count=f, blocks=blocks, mark=True)
            complaints = progs.verdict(r)
            rows.append((f, r, complaints))
            ctx.say(f"[erasure] f={f:>2}  cyc/blk={r.cycles_per_block:7.1f}  "
                    f"riBM ok/corr/unc={r.a.blk_ok}/{r.a.blk_corr}/{r.a.blk_unc} sym={r.a.sym_corr}  "
                    f"Euclid ok/corr/unc={r.b.blk_ok}/{r.b.blk_corr}/{r.b.blk_unc} sym={r.b.sym_corr}  "
                    f"A=B:{'yes' if not r.cmp_err else 'NO'}  "
                    f"{'PASS' if not complaints else 'FAIL ' + '; '.join(complaints)}")
        bad = [(f, c) for f, _, c in rows if c]
        if bad:
            raise RuntimeError(f"{len(bad)} of {len(rows)} erasure runs failed: "
                               + ", ".join(str(f) for f, _ in bad))
        return rows
