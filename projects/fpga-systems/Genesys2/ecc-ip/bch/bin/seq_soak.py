# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""bch loop soak: push a million blocks through the codec, in random patterns.

The random campaign (`seq_random.py`) answers "does a fresh pattern break it?"
with 64 runs of 4 blocks. This answers the other question: does the datapath
still hold up after a million blocks? Counters wrap, FIFOs reach occupancies a
short run never visits, and a one-in-a-hundred-thousand pattern gets a chance
to appear.

Structure: `target` blocks in total, split into runs of `blocks` each, every
run with its own data seed, error seed, mode and error count. Every run is
judged by the same `bch_loop_programs.verdict` the sweep and random campaign
use.

Params: `target` (default 1,000,000 blocks), `blocks` per run (default 4096),
`seed` (host RNG seed, default 1), and `progress` (report every N runs,
default 16).
"""
from __future__ import annotations

import random
import time

import bch_env  # noqa: F401
from sequence import Sequence
import bch_loop_programs as progs
from bch_loop import BchLoopDriver


class Soak(Sequence):
    name = "soak"
    requires = ("init",)
    description = "a million blocks of random patterns, judged run by run"

    def run(self, ctx):
        drv = ctx.bus
        prof = ctx.result("init").profile
        t, n, k = prof["t"], prof["n"], prof["k"]

        target = ctx.param("target", 1_000_000)
        blocks = ctx.param("blocks", 4096)
        every = ctx.param("progress", 16)
        rnd = random.Random(ctx.param("seed", 1))

        runs = max(1, (target + blocks - 1) // blocks)
        modes = [BchLoopDriver.INJ_COUNT, BchLoopDriver.INJ_COUNT,
                 BchLoopDriver.INJ_BURST, BchLoopDriver.INJ_RATE]

        ctx.say(f"[soak] {runs} runs x {blocks} blocks = {runs * blocks} blocks on "
                f"BCH({n},{k}), t={t}; {blocks * n} bits per run; "
                f"{ctx.param('over_t_fraction', 0.15):.0%} of runs aimed past the "
                f"correction limit, the rest inside it")

        done = clean = corrected = uncorrectable = 0
        bits = 0
        over_t_blocks = miscorrected = 0
        failures = []
        t0 = time.time()

        for i in range(runs):
            mode = rnd.choice(modes)
            gen_seed = rnd.randrange(1, 1 << 32)
            inj_seed = rnd.randrange(1, 1 << 32)
            count = rate = 0
            over = rnd.random() < ctx.param("over_t_fraction", 0.15)
            if mode == BchLoopDriver.INJ_COUNT:
                count = rnd.randint(t + 1, 2 * t + 2) if over else rnd.randint(0, t)
            elif mode == BchLoopDriver.INJ_BURST:
                count = rnd.randint(t + 1, 2 * t + 2) if over else rnd.randint(1, t)
            else:
                hi = max(1, int(0.4 * t / n * 65536))
                rate = rnd.randint(1, hi * 3 if over else hi)

            r = drv.run(mode=mode, count=count, rate=rate, blocks=blocks, meters=False,
                        gen_seed=gen_seed, inj_seed=inj_seed,
                        throttle_a=bool(rnd.getrandbits(1)),
                        throttle_b=bool(rnd.getrandbits(1)),
                        timeout_s=max(30.0, blocks * n * 4e-8 + 15.0))

            bad = progs.verdict(r, t)
            done += blocks
            if mode == BchLoopDriver.INJ_COUNT and count > t:
                over_t_blocks += blocks
                miscorrected += r.a.blk_corr
            clean += r.a.blk_ok
            corrected += r.a.blk_corr
            uncorrectable += r.a.blk_unc
            bits += r.a.sym_corr
            if bad:
                failures.append((i, mode, count, rate, gen_seed, inj_seed, bad))
                ctx.say(f"[soak] run {i} FAILED at block {done}  mode={mode} count={count} "
                        f"rate={rate} gen_seed=0x{gen_seed:08X} inj_seed=0x{inj_seed:08X}")
                for b in bad:
                    ctx.say(f"         {b}")
                if len(failures) >= ctx.param("max_failures", 5):
                    ctx.say(f"[soak] stopping after {len(failures)} failing runs")
                    break

            if every and (i + 1) % every == 0:
                el = time.time() - t0
                ctx.say(f"[soak] {done}/{runs * blocks} blocks  {el:.0f}s  "
                        f"{done / el:.0f} blk/s  clean/corr/unc="
                        f"{clean}/{corrected}/{uncorrectable}  {len(failures)} failing run(s)")

        el = time.time() - t0
        rate_mis = miscorrected / over_t_blocks if over_t_blocks else 0.0
        ctx.say(f"[soak] {done} blocks in {el:.0f}s ({done / max(el, 1e-9):.0f} blk/s); "
                f"{clean} clean / {corrected} corrected / {uncorrectable} uncorrectable; "
                f"{bits} bits corrected; {len(failures)} failing run(s)")
        if over_t_blocks:
            ctx.say(f"[soak] beyond the threshold: {miscorrected} of {over_t_blocks} blocks "
                    f"were accepted and silently mis-decoded "
                    f"({rate_mis:.2e}, 1 in {over_t_blocks / max(miscorrected, 1):.0f})")

        CEILING = ctx.param("miscorrect_ceiling", 1e-2)
        if over_t_blocks and rate_mis > CEILING:
            raise RuntimeError(
                f"beyond the threshold {miscorrected} of {over_t_blocks} blocks were "
                f"accepted ({rate_mis:.2e}), over the {CEILING:.0e} ceiling -- the "
                f"decoder is accepting blocks it should be flagging")
        if failures:
            raise RuntimeError(f"{len(failures)} soak run(s) failed out of "
                               f"{done // blocks}; first: {failures[0][:6]}")
        return {"blocks": done, "runs": done // blocks, "clean": clean,
                "corrected": corrected, "uncorrectable": uncorrectable,
                "bits_corrected": bits,
                "over_t_blocks": over_t_blocks, "miscorrected": miscorrected,
                "miscorrect_rate": rate_mis,
                "seconds": el, "blocks_per_s": done / max(el, 1e-9)}
