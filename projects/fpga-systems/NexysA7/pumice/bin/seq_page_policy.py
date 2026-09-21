# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""OPEN vs CLOSE page-policy A/B on the board (runtime-policy bitstream).

The commit that made page policy a runtime CSR claimed an 8.8x streaming-read
win from OPEN over CLOSE on silicon; this sequence measures it directly. For
each scenario family it runs the identical traffic twice -- once CLOSE, once
OPEN -- through `pumice_char.measure` and reports the read-BW ratio.

Replaces the standalone host_compare_page_policy.py: same measurement, but as a
runner sequence so it composes transport once (via `ctx.bus`) and shares the
init/leveling step instead of re-opening the port and re-configuring by hand.
"""

from __future__ import annotations

import pumice_env  # noqa: F401  (import side effect: sys.path setup)

from sequence import Sequence

import ddr2_char as dc
import pumice_char as pc

# NO DFI PHY OVERRIDE HERE. This used to pin t_phy_wrlat=0 / t_rddata_en=6 as
# "mandatory on this board" (2026-09-08, f34c121ef). That is stale: `init` now
# levels the read path and programs the PHY itself, and the leveled point has
# since moved (bitslip 0 / tap 4 / eye width 10, against the tap 8 / eye 17 the
# note was written against).
#
# Measured 2026-09-21 on 210292BFA3EE: with the override, ALL FOUR cells failed
# their integrity check (mismatches) while still reporting healthy bandwidth --
# OPEN read 552.3 MB/s and "FAIL" on the same line. Without it, the same four
# cells pass and the bandwidth is unchanged (553.4 MB/s). So the override
# corrupted DATA and left the PERFORMANCE number intact, which is the worst
# shape a measurement bug can take: the number a reader would quote survives,
# and only the correctness flag says it came from a run whose data was wrong.
#
# `char` never overrode these, which is why it passed on the same board in the
# same session while this sequence failed 4/4.

_FAM = {"incremental": pc.FAM_INCREMENTAL, "row_major": pc.FAM_ROW_MAJOR}


class PagePolicy(Sequence):
    name = "page_policy"
    description = "OPEN vs CLOSE streaming-read BW A/B across scenario families"
    requires = ("init",)

    def run(self, ctx):
        drv = ctx.bus
        fams = [_FAM[f] for f in ctx.param("families", ["incremental", "row_major"])]
        bl = ctx.param("burst_len", 16)
        txn = ctx.param("pp_txn", 2000)
        base = ctx.param("base_addr", 0x0)
        # Measured off the board, not a constant -- see seq_char.py.
        clk = pc.resolve_clk_mhz(drv, ctx.param("clk_mhz"))
        policies = [("CLOSE", dc.PAGE_POLICY_CLOSE), ("OPEN", dc.PAGE_POLICY_OPEN)]

        results = {}
        for fam in fams:
            sc = pc.Scenario(name=f"{fam}_bl{bl}", family=fam,
                             burst_len=bl, txn_count=txn)
            for pname, pol in policies:
                cfg = pc.ControllerConfig(
                    f"ab_{pname.lower()}", scheme=dc.SCHEME_ROW_MAJOR,
                    # lookahead / force_inorder were PRE-REARCHITECTURE knobs,
                    # removed from ControllerConfig in the cleanup noted at
                    # pumice_char.py:404. This sequence still passed them, so it
                    # died with TypeError before touching the board -- a 0.00s
                    # "FAIL" that looked like a board failure and was not.
                    page_policy=pol,
                    rd_in_order=True)
                rec = pc.measure(drv, sc, cfg=cfg, base_addr=base, clk_mhz=clk)
                results[(fam, pname)] = rec
                ctx.say(f"[page_policy] {fam:<12} {pname:<6} "
                        f"wr={rec.wr_bw_mb_s:6.1f} rd={rec.rd_bw_mb_s:6.1f} MB/s "
                        f"{'OK' if rec.ok else 'FAIL'}")

        speedups = {}
        for fam in fams:
            c = results[(fam, "CLOSE")].rd_bw_mb_s
            o = results[(fam, "OPEN")].rd_bw_mb_s
            ratio = (o / c) if c else 0.0
            speedups[fam] = round(ratio, 2)
            ctx.say(f"[page_policy] {fam}: CLOSE={c:.1f} OPEN={o:.1f} -> {ratio:.2f}x read")

        failed = [k for k, r in results.items() if not r.ok]
        if failed:
            raise RuntimeError(
                f"page_policy: {len(failed)}/{len(results)} cells failed: {failed}")

        return {"ok": True, "speedups": speedups}
