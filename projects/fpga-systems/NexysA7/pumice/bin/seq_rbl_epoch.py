# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""RBL epoch sweep -- isolates the rbl_static streaming collapse (TASK-002).

The axis-2 board sweep measured `rbl_static` at 34.9 MB/s on incremental
traffic against plain open page's 554.1 -- a 15.9x regression, with a 0.0% row
hit rate and 8.17 ACT/txn, i.e. byte-for-byte close-page behaviour. Its only
difference from `rbl_dyn` (549.7 MB/s, healthy) is PAGE_RBL_CFG.reset_interval:
0 vs 256.

This sweeps ONLY that field and holds everything else, which is what turns
"rbl_static is bad" into a mechanism statement. Measured:

    epoch 0            34.9 MB/s   0.0% hit   8.17 ACT/txn   <- collapsed
    epoch 1/16/64/256  553.7-553.8 99.4% hit  0.05 ACT/txn   <- healthy
    epoch 1024         207.1 MB/s  88.3% hit  0.94 ACT/txn   <- too slow to relearn

col_major is 163.8 MB/s at EVERY epoch: it genuinely misses, so the predictor
is right to close, and a col_major-only sweep can never see this. That is why
the profile runs both families.

`reset_interval = 0` means "never reset" (pumice_csr.rdl) and is the RTL RESET
DEFAULT, so this is the shipped behaviour, not an unusual setting.
"""

from __future__ import annotations

import dataclasses

import pumice_env  # noqa: F401  (import side effect: sys.path setup)

from sequence import Sequence

import pumice_char as pc


class RblEpoch(Sequence):
    name = "rbl_epoch"
    description = "PAGE_RBL_CFG.reset_interval sweep (TASK-002 axis 2)"
    requires = ("init",)

    def run(self, ctx):
        drv = ctx.bus
        base = pc.CONFIGS["rbl_static"]
        clk = pc.resolve_clk_mhz(drv, ctx.param("clk_mhz"))
        txn = int(ctx.param("txn", 4000))
        epochs = [int(e) for e in str(ctx.param("epochs", "0,1,16,64,256,1024")).split(",")]
        out = {}
        for epoch in epochs:
            cfg = dataclasses.replace(
                base, name=f"rbl_e{epoch}",
                page_rbl={**base.page_rbl, "reset_interval": epoch})
            for fam in (pc.FAM_INCREMENTAL, pc.FAM_COL_MAJOR):
                sc = pc.Scenario(name=f"{fam}_bl8", family=fam,
                                 burst_len=8, txn_count=txn)
                r = pc.measure(drv, sc, cfg=cfg, clk_mhz=clk, timeout_s=120.0)
                st = r.rd_stats
                # Anti-vacuity: a point that moved nothing compares nothing.
                if not r.bytes_moved:
                    ctx.say(f"[rbl] epoch={epoch} {fam}: no bytes moved -- vacuous")
                    continue
                hit = "-" if st is None or st.row_hit_rate is None else f"{st.row_hit_rate:.1%}"
                apt = "-" if r.rd_acts_per_txn is None else f"{r.rd_acts_per_txn:.2f}"
                ctx.say(f"[rbl] epoch={epoch:<5} {fam:<12} rd={r.rd_bw_mb_s:7.1f} MB/s  "
                        f"hit={hit:>6}  ACT/txn={apt:>5}  ok={r.ok}")
                out[(epoch, fam)] = (r.rd_bw_mb_s,
                                     st.row_hit_rate if st else None, r.ok)

        ref = out.get((0, pc.FAM_INCREMENTAL))
        best = max((v[0] for k, v in out.items() if k[1] == pc.FAM_INCREMENTAL),
                   default=0.0)
        if ref and ref[0] and best:
            ctx.say(f"[rbl] streaming: epoch=0 {ref[0]:.1f} MB/s vs best "
                    f"{best:.1f} MB/s -- {best / ref[0]:.1f}x")
        return out
