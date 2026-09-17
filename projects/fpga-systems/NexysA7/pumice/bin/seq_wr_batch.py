# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""Write-batching validation (PUMICE-039 / 042 / 043), as ONE board run.

Everything this checks was previously a pile of standalone scripts that each
opened their own port and re-ran leveling. That is why board work had to be
serialised by hand, why every run needed watching, and why launching two at
once corrupted a measurement by re-levelling underneath it. As a Sequence it
touches the device only through `ctx.bus`, so the whole batch shares one
transport and one init -- and the same steps run against a cocotb bus.

Steps, in order, because each answers the question the previous one raises:

  1. watermark A/B at the gaps where the turnaround cost bites. Batching
     (SCHED_WR_WM) amortises tWTR/tRTW over a drain instead of paying it per
     direction switch -- pumice's equivalent of LiteDRAM staying in READ until
     reads are exhausted. Shipped disabled, no host accessor until 6ba9dba62,
     and it corrupted when first enabled because the DFI-side pacer ignored
     direction (PUMICE-042, fixed 91db52b47).
  2. REPEATS at the chosen setting. A single pass cannot distinguish 0% from a
     low-rate intermittent; that is exactly how PUMICE-037's first closure
     failed (a point clean ~20% of the time passed a one-rep sweep).
  3. the aggressive setting, repeated, to characterise PUMICE-043's residue
     (1 beat in 1/8 runs at hi=8/lo=4).
"""

from __future__ import annotations

import pumice_env  # noqa: F401  (import side effect: sys.path setup)

from sequence import Sequence

import dataclasses

import pumice_char as pc


class WrBatch(Sequence):
    name = "wr_batch"
    description = "SCHED_WR_WM write-batching A/B + repeats (PUMICE-039/042/043)"
    requires = ("init",)

    def _point(self, drv, geom, gap, txn, cfg, n_gen=1):
        """One concurrent 1w+1r point via the LIBRARY api.

        pumice_char.measure_concurrent is what the sim characterization test
        drives too, so this step stays sim/silicon-portable -- which is the
        property the sequence framework exists to preserve. (An earlier draft
        reached into bank_gap_sweep's private helpers: that is a standalone
        sweep SCRIPT, not a library, and it is not on the sequence path.)
        It pre-fills the reader regions itself, so there is no separate
        prefill step to forget."""
        sc = pc.Scenario(name=f"wrbatch_gap{gap}", family=pc.FAM_INCREMENTAL,
                         burst_len=8, txn_count=txn, gap=gap)
        return pc.measure_concurrent(drv, sc, cfg=cfg,
                                     geom=geom, n_wr=n_gen, n_rd=n_gen,
                                     clk_mhz=75.0, timeout_s=120.0)

    def run(self, ctx):
        drv  = ctx.bus
        geom = pc.DEFAULT_GEOM
        gaps = [int(g) for g in str(ctx.param("gaps", "12,15")).split(",")]
        reps = int(ctx.param("reps", 8))
        txn  = int(ctx.param("txn", 2000))
        # Generator counts. BOTH bank_gap_sweep attempts with batching on by
        # default got cleanly through 4+4 and 3+3 and then died/stalled in
        # 2+2 (alive, ~0 CPU, no output -- engines timing out, not
        # corruption). 1+1 is clean here, so the question is whether a
        # particular generator count starves under the drain.
        gens = [int(g) for g in str(ctx.param("gens", "1")).split(",")]
        wms  = [(0, 0), (2, 1), (8, 4)]
        cfg  = pc.CONFIGS["open_page"]
        out  = {}

        for hi, lo in wms:
            # Carry the watermarks IN THE CONFIG, not as a separate CSR write.
            # measure_concurrent calls cfg.apply(drv) internally, and apply()
            # now programs SCHED_WR_WM from the config -- so a standalone
            # set_sched_wr_wm() before it is overwritten, and every point
            # silently ran at the config default. Measured: hi=0/2/8 all
            # returned ~313 MB/s (the hi=2 number) instead of 240/313/295.
            point_cfg = dataclasses.replace(cfg, wr_high_wm=hi, wr_low_wm=lo)
            for n_gen, gap in [(g, k) for g in gens for k in gaps]:
                point_cfg.apply(drv)
                drv.sync_gen_config()

                mism, bus, timeouts = [], [], 0
                for _ in range(reps):
                    r = self._point(drv, geom, gap, txn, point_cfg, n_gen)
                    # A point whose engines did not complete is a TIMEOUT, not a
                    # clean result -- that distinction is the whole question here.
                    if not r.ok:
                        timeouts += 1
                    # Anti-vacuity: a record that moved no bytes compares
                    # nothing, and would report "clean".
                    if not r.bytes_moved:
                        ctx.say("[wr_batch] no bytes moved -- vacuous"); continue
                    mism.append(r.mismatched)
                    bus.append(r.wr_bw_mb_s + r.rd_bw_mb_s)
                fails = sum(1 for m in mism if m)
                avg   = sum(bus) / len(bus) if bus else 0.0
                out[(hi, n_gen, gap)] = (fails, len(mism), avg, mism)
                ctx.say(f"[wr_batch] hi={hi}/lo={lo} {n_gen}+{n_gen} gap={gap}: "
                        f"{fails}/{len(mism)} failing  bus={avg:.1f} MB/s  "
                        f"timeouts={timeouts}  {mism}")

        ctx.say("[wr_batch] --- vs batching disabled ---")
        for n_gen, gap in [(g, k) for g in gens for k in gaps]:
            base = out.get((0, n_gen, gap))
            for hi, _lo in wms[1:]:
                v = out.get((hi, n_gen, gap))
                if base and v and base[2]:
                    ctx.say(f"[wr_batch]   {n_gen}+{n_gen} gap{gap} hi={hi}: bus "
                            f"{(v[2]-base[2])/base[2]*100:+.1f}%   "
                            f"{v[0]}/{v[1]} failing")
        return out
