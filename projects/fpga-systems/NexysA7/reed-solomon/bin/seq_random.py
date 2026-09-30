# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""rs loop random campaign: many DIFFERENT patterns, not one pattern many times.

The sweep sequence proves the verdict boundary at each error count, but it runs
every point with the same data and the same error positions: GEN_SEED and
INJ_SEED default to fixed values and the injector is reseeded from INJ_SEED on
every kick, so the positions repeat run to run. That is one pattern exercised
N times, which is not what a random campaign is for.

This draws a fresh (data seed, error seed) pair per run, plus a random mode and
error count, and judges each run with the same rs_loop_programs.verdict the
sweep uses. Every run is reproducible on its own: the report carries the two
seeds, so a failure is replayable with
`host_rs_loop.py run --mode ... --count ... --gen-seed ... --inj-seed ...`.

Params: `runs` (default 64), `seed` (the host-side RNG seed, default 1), and
`blocks` per run (default 4 -- many patterns beat many blocks of one pattern).
"""
from __future__ import annotations

import random

import rs_env  # noqa: F401
from sequence import Sequence
import rs_loop_programs as progs
from rs_loop import RsLoopDriver


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

        # modes worth mixing: exact count (the sharp verdict check), burst
        # (adjacent symbols, the case a naive Chien/Forney lane split breaks),
        # and rate (no per-block guarantee, so only agreement and delivery are
        # checked -- see rs_loop_programs.verdict)
        modes = [RsLoopDriver.INJ_COUNT, RsLoopDriver.INJ_COUNT,
                 RsLoopDriver.INJ_BURST, RsLoopDriver.INJ_RATE]

        tallies = {"count": 0, "burst": 0, "rate": 0}
        corrected = uncorrectable = clean = 0
        failures = []

        for i in range(runs):
            mode = rnd.choice(modes)
            gen_seed = rnd.randrange(1, 1 << 32)
            inj_seed = rnd.randrange(1, 1 << 32)
            count = rate = 0
            if mode == RsLoopDriver.INJ_COUNT:
                count = rnd.randint(0, 2 * t + 2)
                tallies["count"] += 1
            elif mode == RsLoopDriver.INJ_BURST:
                count = rnd.randint(1, 2 * t + 2)
                tallies["burst"] += 1
            else:
                rate = rnd.randint(1, int(0.03 * 65536))   # up to ~3% per symbol
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

        ctx.say(f"[random] {runs} runs x {blocks} blocks on RS({n},{n - 2 * t}): "
                f"{tallies['count']} exact-count, {tallies['burst']} burst, {tallies['rate']} rate; "
                f"blocks {clean} clean / {corrected} corrected / {uncorrectable} uncorrectable; "
                f"{len(failures)} failing run(s)")
        if failures:
            raise RuntimeError(f"{len(failures)} of {runs} random runs failed; first: {failures[0][:6]}")
        return {"runs": runs, "blocks": blocks, "modes": tallies,
                "clean": clean, "corrected": corrected, "uncorrectable": uncorrectable}
