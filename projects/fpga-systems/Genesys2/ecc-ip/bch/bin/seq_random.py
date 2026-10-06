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

import math
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


class ClusterCampaign(Sequence):
    name = "clusters"
    requires = ("init",)
    description = "a few random-cluster configurations, checked against coarse envelopes"

    def run(self, ctx):
        drv = ctx.bus
        t = ctx.result("init").profile["t"]
        n = ctx.result("init").profile["n"]
        blocks = ctx.param("blocks", 16)
        rnd = random.Random(ctx.param("seed", 1))

        combos = [
            (1, 1, 1, 1),   # exactly one single-error cluster per block
            (1, 2, 1, 2),   # 1-2 clusters, 1-2 errors each
            (1, 4, 2, 4),   # 1-4 clusters, 2-4 errors each
            (2, 4, 1, 8),   # 2-4 clusters, 1-8 errors each
        ]

        failures = []
        for cnt_min, cnt_max, len_min, len_max in combos:
            gen_seed = rnd.randrange(1, 1 << 32)
            inj_seed = rnd.randrange(1, 1 << 32)
            drv.soft_reset()
            drv.clear()
            drv.set_inj_ranges(cnt_min, cnt_max, len_min, len_max)
            r = drv.run(mode=BchLoopDriver.INJ_RANDOM, blocks=blocks,
                        gen_seed=gen_seed, inj_seed=inj_seed)
            bad = self._cluster_checks(r, t, cnt_min, cnt_max, len_min, len_max)
            if bad:
                failures.append((cnt_min, cnt_max, len_min, len_max, gen_seed, inj_seed, bad))
                ctx.say(f"[clusters] FAILED cnt=({cnt_min},{cnt_max}) len=({len_min},{len_max}) "
                        f"gen_seed=0x{gen_seed:08X} inj_seed=0x{inj_seed:08X}")
                for b in bad:
                    ctx.say(f"           {b}")

        k = ctx.result("init").profile["k"]
        ctx.say(f"[clusters] {len(combos)} combos x {blocks} blocks on BCH({n},{k}); "
                f"{len(failures)} failing combo(s)")
        if failures:
            raise RuntimeError(f"{len(failures)} of {len(combos)} cluster combos failed; "
                               f"first: {failures[0][:6]}")
        return {"combos": len(combos), "blocks": blocks, "failures": len(failures)}

    def _cluster_checks(self, r, t, cnt_min, cnt_max, len_min, len_max):
        bad = []
        if r.timed_out:
            bad.append("run did not finish")
        if r.a.pkts != r.blocks:
            bad.append(f"RIBM: {r.a.pkts} of {r.blocks} blocks reached its checker")
        if r.a.blk_frame:
            bad.append(f"RIBM: {r.a.blk_frame} framing errors")
        # Every block should have received at least one cluster.
        if r.inj_blocks == 0:
            bad.append("injector placed no errors")
        # Total injected symbols must sit inside the configured envelope.
        min_symbols = r.blocks * cnt_min * len_min
        max_symbols = r.blocks * cnt_max * len_max
        if not (min_symbols <= r.inj_symbols <= max_symbols):
            bad.append(f"injector placed {r.inj_symbols} symbols, expected "
                       f"{min_symbols}..{max_symbols}")
        # The checker must have seen the corruption.
        # the decoder must have SEEN the corruption. Corrected symbols prove
        # it for sub-t runs; heavy runs leave every block uncorrectable
        # (sym_corr legitimately 0), so accept any non-clean signature.
        if r.a.blk_corr == 0 and r.a.blk_unc == 0 and not r.a.data_err:
            bad.append("decoder saw no corruption")
        return bad


class LocalizedCampaign(Sequence):
    name = "localized"
    requires = ("init",)
    description = "a few localized-window configurations, checked against coarse envelopes"

    def run(self, ctx):
        drv = ctx.bus
        t = ctx.result("init").profile["t"]
        n = ctx.result("init").profile["n"]
        blocks = ctx.param("blocks", 16)
        rnd = random.Random(ctx.param("seed", 1))

        combos = [
            (1, 8, 2000),
            (4, 16, 5000),
            (1, max(1, n // 8), 10000),
        ]

        failures = []
        for len_min, len_max, rate in combos:
            if len_max > n:
                len_max = n
            if len_min > len_max:
                len_min = len_max
            gen_seed = rnd.randrange(1, 1 << 32)
            inj_seed = rnd.randrange(1, 1 << 32)
            drv.soft_reset()
            drv.clear()
            drv.set_inj_ranges(cnt_min=0, cnt_max=0, len_min=len_min, len_max=len_max)
            r = drv.run(mode=BchLoopDriver.INJ_LOCALIZED, count=0, rate=rate, blocks=blocks,
                        gen_seed=gen_seed, inj_seed=inj_seed)
            bad = self._localized_checks(r, t, len_min, len_max, rate)
            if bad:
                failures.append((len_min, len_max, rate, gen_seed, inj_seed, bad))
                ctx.say(f"[localized] FAILED len=({len_min},{len_max}) rate={rate} "
                        f"gen_seed=0x{gen_seed:08X} inj_seed=0x{inj_seed:08X}")
                for b in bad:
                    ctx.say(f"           {b}")

        k = ctx.result("init").profile["k"]
        ctx.say(f"[localized] {len(combos)} combos x {blocks} blocks on BCH({n},{k}); "
                f"{len(failures)} failing combo(s)")
        if failures:
            raise RuntimeError(f"{len(failures)} of {len(combos)} localized combos failed; "
                               f"first: {failures[0][:6]}")
        return {"combos": len(combos), "blocks": blocks, "failures": len(failures)}

    def _localized_checks(self, r, t, len_min, len_max, rate):
        bad = []
        if r.timed_out:
            bad.append("run did not finish")
        if r.a.pkts != r.blocks:
            bad.append(f"RIBM: {r.a.pkts} of {r.blocks} blocks reached its checker")
        if r.a.blk_frame:
            bad.append(f"RIBM: {r.a.blk_frame} framing errors")
        # Honest envelope: at most one error per lane in the window.
        max_symbols = r.blocks * len_max
        if r.inj_symbols > max_symbols:
            bad.append(f"injector placed {r.inj_symbols} symbols, expected <= {max_symbols}")
        if rate > 0 and r.inj_blocks == 0:
            bad.append("injector placed no errors")
        # the decoder must have SEEN the corruption. Corrected symbols prove
        # it for sub-t runs; heavy runs leave every block uncorrectable
        # (sym_corr legitimately 0), so accept any non-clean signature.
        if r.a.blk_corr == 0 and r.a.blk_unc == 0 and not r.a.data_err:
            bad.append("decoder saw no corruption")
        return bad


class BadBlockCampaign(Sequence):
    name = "badblock"
    requires = ("init",)
    description = "bad-block probability sweep with binomial band and symbol envelope"

    def run(self, ctx):
        drv = ctx.bus
        t = ctx.result("init").profile["t"]
        n = ctx.result("init").profile["n"]
        blocks = ctx.param("blocks", 64)
        rnd = random.Random(ctx.param("seed", 1))

        # (bad probability threshold p, elevated rate, clean rate)
        combos = [
            (0, 65535, 0),
            (16384, 65535, 0),
            (32768, 65535, 0),
            (65535, 65535, 0),
        ]

        failures = []
        for p, rate_hi, rate_lo in combos:
            gen_seed = rnd.randrange(1, 1 << 32)
            inj_seed = rnd.randrange(1, 1 << 32)
            drv.soft_reset()
            drv.clear()
            drv.set_inj_ranges(cnt_min=0, cnt_max=0, len_min=p, len_max=rate_hi)
            r = drv.run(mode=BchLoopDriver.INJ_BADBLOCK, count=0, rate=rate_lo, blocks=blocks,
                        gen_seed=gen_seed, inj_seed=inj_seed)
            bad = self._badblock_checks(r, t, n, p, rate_hi, rate_lo)
            if bad:
                failures.append((p, rate_hi, rate_lo, gen_seed, inj_seed, bad))
                ctx.say(f"[badblock] FAILED p={p} hi={rate_hi} lo={rate_lo} "
                        f"gen_seed=0x{gen_seed:08X} inj_seed=0x{inj_seed:08X}")
                for b in bad:
                    ctx.say(f"          {b}")

        k = ctx.result("init").profile["k"]
        ctx.say(f"[badblock] {len(combos)} combos x {blocks} blocks on BCH({n},{k}); "
                f"{len(failures)} failing combo(s)")
        if failures:
            raise RuntimeError(f"{len(failures)} of {len(combos)} bad-block combos failed; "
                               f"first: {failures[0][:6]}")
        return {"combos": len(combos), "blocks": blocks, "failures": len(failures)}

    def _badblock_checks(self, r, t, n, p, rate_hi, rate_lo):
        bad = []
        if r.timed_out:
            bad.append("run did not finish")
        if r.a.pkts != r.blocks:
            bad.append(f"RIBM: {r.a.pkts} of {r.blocks} blocks reached its checker")
        if r.a.blk_frame:
            bad.append(f"RIBM: {r.a.blk_frame} framing errors")
        # With rate_lo == 0, every block that received a hit was a bad block.
        if rate_lo == 0:
            observed = r.inj_blocks / r.blocks if r.blocks else 0.0
            expected = p / 65536.0
            if p == 0:
                if r.inj_blocks != 0:
                    bad.append(f"p=0 but {r.inj_blocks} blocks were hit")
            elif p == 65535:
                if r.inj_blocks == 0:
                    bad.append("p=65535 but no blocks were hit")
            else:
                sigma = math.sqrt(expected * (1.0 - expected) / r.blocks) if r.blocks else 0.0
                if abs(observed - expected) > 5 * sigma:
                    bad.append(f"bad fraction {observed:.4f}, expected {expected:.4f} +/- {5 * sigma:.4f}")
        # Symbol envelope over the campaign.
        lo = r.blocks * rate_lo * n / 65536 * 0.5
        hi = r.blocks * max(rate_hi, rate_lo) * n / 65536 * 1.5
        if not (lo <= r.inj_symbols <= hi):
            bad.append(f"injector placed {r.inj_symbols} symbols, expected {lo:.1f}..{hi:.1f}")
        # the decoder must have SEEN the corruption. Corrected symbols prove
        # it for sub-t runs; heavy runs leave every block uncorrectable
        # (sym_corr legitimately 0), so accept any non-clean signature.
        if (p > 0 or rate_lo > 0) and r.a.blk_corr == 0 \
                and r.a.blk_unc == 0 and not r.a.data_err:
            bad.append("decoder saw no corruption")
        return bad
