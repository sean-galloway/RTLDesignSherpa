# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""bch loop random campaign: many DIFFERENT patterns, not one pattern many times.

The sweep sequence proves the verdict boundary at each error count, but it runs
every point with the same data and the same error positions. This draws a fresh
(data seed, error seed) pair per run, plus a random mode and error count, and
judges each run with the same bch_loop_programs.verdict the sweep uses.

Params: `runs` (default 64), `seed` (the host-side RNG seed, default 1), and
`blocks` per run (default 4).
"""
from __future__ import annotations

import random

import bch_env  # noqa: F401
from sequence import Sequence
import bch_loop_programs as progs
from bch_loop import BchLoopDriver


class RandomCampaign(Sequence):
    name = "random"
    requires = ("init",)
    description = "N runs, each a fresh data seed / error seed / mode / count"

    def run(self, ctx):
        drv = ctx.bus
        t = ctx.result("init").profile["t"]
        n = ctx.result("init").profile["n"]
        runs = ctx.param("runs", 64)
        blocks = ctx.param("blocks", 4)
        rnd = random.Random(ctx.param("seed", 1))

        modes = [BchLoopDriver.INJ_COUNT, BchLoopDriver.INJ_COUNT,
                 BchLoopDriver.INJ_BURST, BchLoopDriver.INJ_RATE]

        tallies = {"count": 0, "burst": 0, "rate": 0}
        corrected = uncorrectable = clean = 0
        failures = []

        for i in range(runs):
            mode = rnd.choice(modes)
            gen_seed = rnd.randrange(1, 1 << 32)
            inj_seed = rnd.randrange(1, 1 << 32)
            count = rate = 0
            if mode == BchLoopDriver.INJ_COUNT:
                count = rnd.randint(0, 2 * t + 2)
                tallies["count"] += 1
            elif mode == BchLoopDriver.INJ_BURST:
                count = rnd.randint(1, 2 * t + 2)
                tallies["burst"] += 1
            else:
                rate = rnd.randint(1, int(0.03 * 65536))
                tallies["rate"] += 1

            r = drv.run(mode=mode, count=count, rate=rate, blocks=blocks,
                        gen_seed=gen_seed, inj_seed=inj_seed,
                        throttle_a=bool(rnd.getrandbits(1)),
                        throttle_b=bool(rnd.getrandbits(1)))
            bad = progs.verdict(r, t)
            clean += r.a.blk_ok
            corrected += r.a.blk_corr
            uncorrectable += r.a.blk_unc
            if bad:
                failures.append((i, mode, count, rate, gen_seed, inj_seed, bad))
                ctx.say(f"[random] run {i} FAILED  mode={mode} count={count} rate={rate} "
                        f"gen_seed=0x{gen_seed:08X} inj_seed=0x{inj_seed:08X}")
                for b in bad:
                    ctx.say(f"           {b}")

        k = ctx.result("init").profile["k"]
        ctx.say(f"[random] {runs} runs x {blocks} blocks on BCH({n},{k}): "
                f"{tallies['count']} exact-count, {tallies['burst']} burst, {tallies['rate']} rate; "
                f"blocks {clean} clean / {corrected} corrected / {uncorrectable} uncorrectable; "
                f"{len(failures)} failing run(s)")
        if failures:
            raise RuntimeError(f"{len(failures)} of {runs} random runs failed; first: {failures[0][:6]}")
        return {"runs": runs, "blocks": blocks, "modes": tallies,
                "clean": clean, "corrected": corrected, "uncorrectable": uncorrectable}
