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

# Board-specific DFI knobs (see project_pumice_board_perf_char): t_phy_wrlat=0 is
# mandatory on this board (the default misaligns the write and leveling finds no
# passing tap); t_rddata_en=6.
_WRLAT = 0
_T_RDDATA_EN = 6

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
        clk = ctx.param("clk_mhz", 100.0)
        policies = [("CLOSE", dc.PAGE_POLICY_CLOSE), ("OPEN", dc.PAGE_POLICY_OPEN)]

        results = {}
        for fam in fams:
            sc = pc.Scenario(name=f"{fam}_bl{bl}", family=fam,
                             burst_len=bl, txn_count=txn)
            for pname, pol in policies:
                cfg = pc.ControllerConfig(
                    f"ab_{pname.lower()}", scheme=dc.SCHEME_ROW_MAJOR,
                    page_policy=pol, lookahead=0, force_inorder=False,
                    rd_in_order=True, t_phy_wrlat=_WRLAT, t_rddata_en=_T_RDDATA_EN)
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
