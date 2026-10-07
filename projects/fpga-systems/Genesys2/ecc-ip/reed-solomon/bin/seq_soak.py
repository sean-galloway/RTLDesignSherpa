# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""rs loop soak: push a million blocks through the codec, in random patterns.

The random campaign (`seq_random.py`) answers "does a fresh pattern break it?"
with 64 runs of 4 blocks -- broad, shallow, and sized to fit the sim harness's
100 ms budget. This answers the other question: does the datapath still hold up
after a million blocks? Counters wrap, FIFOs reach occupancies a short run
never visits, and a one-in-a-hundred-thousand pattern gets a chance to appear.

Structure: `target` blocks in total, split into runs of `blocks` each, every
run with its own data seed, error seed, mode and error count. Splitting rather
than one enormous run is deliberate -- a single 1M-block run would report one
aggregate verdict, and a failure in block 700,000 would carry no replayable
pattern. Per-run seeds mean any failure replays as a single short run:

  host_rs_loop.py run --mode M --count C --gen-seed G --inj-seed I --blocks B

Every run is judged by the same `rs_loop_programs.verdict` the sweep and the
random campaign use, so the pass criteria are identical -- exact correction
below the threshold, uncorrectable above it, riBM == Euclid always.

Sizing. A block is CFG_N_BEATS beats and the decoder retires roughly one beat
per cycle, so 1e6 blocks is about 6.4e7 cycles, a bit under a second of board
time at 100 MHz. The UART dominates the wall clock: a few dozen register
transactions per run at 115200 baud. Hence runs of 4096 blocks rather than
tiny ones -- 244 runs instead of 250,000.

Params: `target` (default 1,000,000 blocks), `blocks` per run (default 4096),
`seed` (host RNG seed, default 1), and `progress` (report every N runs,
default 16). This sequence is BOARD-scale; it does not fit the sim harness's
sim-time budget, and `seq_random.py` is the campaign that runs in both.
"""
from __future__ import annotations

from math import comb
import random
import time

import rs_env  # noqa: F401
from sequence import Sequence
import rs_loop_programs as progs
from rs_loop import RsLoopDriver


class Soak(Sequence):
    name = "soak"
    requires = ("init",)
    description = "a million blocks of random patterns, judged run by run"

    def run(self, ctx):
        drv = ctx.bus
        prof = ctx.result("init").profile
        # the PROFILE register reports n, t, m and spb; k is derived, as
        # seq_init.py's own report line derives it
        t, n = prof["t"], prof["n"]
        k = n - 2 * t
        m = prof["m"]

        target = ctx.param("target", 1_000_000)
        blocks = ctx.param("blocks", 4096)
        every = ctx.param("progress", 16)
        rnd = random.Random(ctx.param("seed", 1))

        runs = max(1, (target + blocks - 1) // blocks)
        modes = [RsLoopDriver.INJ_COUNT, RsLoopDriver.INJ_COUNT,
                 RsLoopDriver.INJ_BURST, RsLoopDriver.INJ_RATE]

        ctx.say(f"[soak] {runs} runs x {blocks} blocks = {runs * blocks} blocks on "
                f"RS({n},{k}), t={t}; {blocks * n} symbols per run; "
                f"{ctx.param('over_t_fraction', 0.15):.0%} of runs aimed past the "
                f"correction limit, the rest inside it")

        done = clean = corrected = uncorrectable = 0
        beats = symbols = 0
        # Beyond the threshold a bounded-distance decoder occasionally lands on
        # a DIFFERENT valid codeword and reports success, having produced the
        # wrong message. That is the code's behaviour, not a defect, and
        # rs_loop_programs.verdict no longer treats it as one -- but the RATE
        # has to stay where the mathematics puts it, and a million blocks is
        # the only place there are enough samples to say so. These two tally it.
        over_t_blocks = miscorrected = 0
        failures = []
        t0 = time.time()

        for i in range(runs):
            mode = rnd.choice(modes)
            gen_seed = rnd.randrange(1, 1 << 32)
            inj_seed = rnd.randrange(1, 1 << 32)
            count = rate = 0
            # Where to spend the blocks. Drawing e uniformly over 0 .. 2t+2
            # puts HALF of them beyond the correction limit, where the only
            # possible outcome is "uncorrectable" and the Chien/Forney
            # correction path never produces an answer to check. That is a
            # stress test of the reject path, not of the decoder. So most of
            # the campaign runs in the operational regime, e <= t, where the
            # correction must be EXACTLY right, and a deliberate slice runs
            # past the limit to keep the reject path and the miscorrection
            # rate under measurement.
            over = rnd.random() < ctx.param("over_t_fraction", 0.15)
            if mode == RsLoopDriver.INJ_COUNT:
                count = rnd.randint(t + 1, 2 * t + 2) if over else rnd.randint(0, t)
            elif mode == RsLoopDriver.INJ_BURST:
                count = rnd.randint(t + 1, 2 * t + 2) if over else rnd.randint(1, t)
            else:
                # A rate of r per symbol averages r * n errors per block, so
                # the ceiling is set from t, not picked as a round percentage:
                # 0.4 * t / n keeps a typical block comfortably correctable
                # while the tail still crosses the limit sometimes.
                hi = max(1, int(0.4 * t / n * 65536))
                rate = rnd.randint(1, hi * 3 if over else hi)

            # a long run needs a longer patience than the 10 s default: the
            # block count, not the UART, sets the floor here
            # meters=False: the four bandwidth windows are 16 register reads
            # over the UART and the soak does not look at them. Reading them
            # here cost 31% of the soak rate (7,315 -> 5,020 blk/s).
            r = drv.run(mode=mode, count=count, rate=rate, blocks=blocks, meters=False,
                        gen_seed=gen_seed, inj_seed=inj_seed,
                        throttle_a=bool(rnd.getrandbits(1)),
                        throttle_b=bool(rnd.getrandbits(1)),
                        timeout_s=max(30.0, blocks * n * 4e-8 + 15.0))

            bad = progs.verdict(r)
            done += blocks
            if mode == RsLoopDriver.INJ_COUNT and count > t:
                over_t_blocks += blocks
                miscorrected += r.a.blk_corr
            clean += r.a.blk_ok
            corrected += r.a.blk_corr
            uncorrectable += r.a.blk_unc
            beats += r.cmp_beats
            symbols += r.a.sym_corr
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

        # A ceiling, not an expectation -- and calibrated to the code's
        # geometry, not universal. Any bounded-distance decoder intrinsically
        # accepts ~C(n,t)/2^(mt) of beyond-t words; on the full-size profile
        # that floor is ~1e-7 against the legacy 1e-2, and the measured rate
        # ~5e-5 is two hundred times below it, so this cannot fail on sampling
        # noise. Where a smaller geometry pushes the floor above the base
        # (the BCH small profile's is ~15%, issue #86) the ceiling rises to
        # sit ~11 binomial sigma over the model rate; a decoder with a real
        # accept bug -- the dangerous, silent-corruption direction -- sails
        # past it.
        base = ctx.param("miscorrect_ceiling", 1e-2)
        floor = comb(n, t) / 2 ** (m * t)
        ceiling = max(base, 1.25 * floor)

        el = time.time() - t0
        rate_mis = miscorrected / over_t_blocks if over_t_blocks else 0.0
        ctx.say(f"[soak] {done} blocks in {el:.0f}s ({done / max(el, 1e-9):.0f} blk/s); "
                f"{clean} clean / {corrected} corrected / {uncorrectable} uncorrectable; "
                f"{symbols} symbols corrected; {beats} beats compared riBM vs Euclid; "
                f"{len(failures)} failing run(s)")
        if over_t_blocks:
            ctx.say(f"[soak] beyond the threshold: {miscorrected} of {over_t_blocks} blocks "
                    f"were accepted and silently mis-decoded "
                    f"({rate_mis:.2e}, 1 in {over_t_blocks / max(miscorrected, 1):.0f}); "
                    f"the code's intrinsic floor on this geometry is ~{floor:.2e}, "
                    f"ceiling {ceiling:.2e}")

        if over_t_blocks and rate_mis > ceiling:
            raise RuntimeError(
                f"beyond the threshold {miscorrected} of {over_t_blocks} blocks were "
                f"accepted ({rate_mis:.2e}), over the {ceiling:.2e} ceiling "
                f"(base {base:.0e}, code floor {floor:.2e} x 1.25) -- the "
                f"decoder is accepting blocks it should be flagging")
        if failures:
            raise RuntimeError(f"{len(failures)} soak run(s) failed out of "
                               f"{done // blocks}; first: {failures[0][:6]}")
        return {"blocks": done, "runs": done // blocks, "clean": clean,
                "corrected": corrected, "uncorrectable": uncorrectable,
                "symbols_corrected": symbols, "beats_compared": beats,
                "over_t_blocks": over_t_blocks, "miscorrected": miscorrected,
                "miscorrect_rate": rate_mis,
                "seconds": el, "blocks_per_s": done / max(el, 1e-9)}
