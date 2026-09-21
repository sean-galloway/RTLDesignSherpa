# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""pumice characterization sweep -- the perf matrix, run on the board.

Runs the SAME engine the sim characterization test drives (`pumice_char`): a
named RUN_PROFILE crosses controller configs against generator scenarios and
reports bandwidth / utilisation / latency per cell. `run_profile(drv, "smoke")`
is byte-for-byte the same program in sim and on silicon -- only `txn_scale`
differs (1 in sim, ~1000 on the FPGA so the meters have something to integrate).

Like every sequence it touches the device only through `ctx.bus`, never a port,
so it stays sim/silicon-portable. Each scenario re-applies the board-validated
DFI tuple through `ControllerConfig.apply`, so it does not depend on whatever
the previous step left in the timing CSRs.
"""

from __future__ import annotations

import pumice_env  # noqa: F401  (import side effect: sys.path setup)

from sequence import Sequence

import pumice_char as pc


class Char(Sequence):
    name = "char"
    description = "controller-config x scenario perf matrix (pumice_char run_profile)"
    requires = ("init",)

    def run(self, ctx):
        drv = ctx.bus
        profile = ctx.param("profile", "smoke")
        # Board default: many transactions so the perf window is meaningful.
        # A sim caller (ctx.bus = cocotb model) would pass txn_scale=1.
        txn_scale = ctx.param("txn_scale", 1000)

        # READ the clock off the board rather than carrying a constant.
        # Bandwidth is bytes / (cycles / clk_mhz), so a wrong clk_mhz scales
        # every number and nothing else complains: the old 100.0 default (the
        # raw board INPUT, not the 75 MHz sys domain the meters count in) put
        # open_page reads at 739 MB/s -- 123% of what a 64-bit port at 75 MHz
        # can carry -- and the run still said PASS. An explicit --clk-mhz is
        # still honoured (the cocotb caller has no board to time against) and
        # is cross-checked when a board is present.
        clk = pc.resolve_clk_mhz(drv, ctx.param("clk_mhz"))
        ctx.say(f"[char] profile={profile} txn_scale={txn_scale} clk={clk} MHz")
        recs = pc.run_profile(
            drv, profile,
            txn_scale=txn_scale,
            base_addr=ctx.param("base_addr", 0x0),
            clk_mhz=clk,
            progress=lambda msg, i, n: ctx.say(f"[char] {msg} ({i}/{n})"),
        )

        ctx.say("\n" + pc.format_table(recs))
        for line in pc.summarize(recs):
            ctx.say(line)

        csv = ctx.param("char_csv")
        if csv:
            pc.write_csv(recs, csv)
            ctx.say(f"[char] wrote {len(recs)} records -> {csv}")

        failed = [r for r in recs if not r.ok]
        if failed:
            raise RuntimeError(
                f"char: {len(failed)}/{len(recs)} scenarios failed "
                f"(first: {failed[0].config}/{failed[0].scenario.name})")

        return {
            "ok": True,
            "profile": profile,
            "records": len(recs),
            "wr_mb_s": [round(r.wr_bw_mb_s, 1) for r in recs],
            "rd_mb_s": [round(r.rd_bw_mb_s, 1) for r in recs],
        }
