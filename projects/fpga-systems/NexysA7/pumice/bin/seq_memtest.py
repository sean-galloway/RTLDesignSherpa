# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""pumice full-device memtest sequence -- write-all then read-all.

The coverage the smoke test cannot give: proves the whole row/bank/column
addressing path and read-after-full-write retention across the entire device,
chunked to the engine's 16-bit transaction limit. Minutes-scale -- schedule it
in a soak run, not in a bring-up smoke.
"""

from __future__ import annotations

import pumice_env  # noqa: F401  (import side effect: sys.path setup)

from sequence import Sequence

from pumice_master import memtest


class Memtest(Sequence):
    name = "memtest"
    description = "full-device write-all / read-all across every chunk"
    requires = ("init",)

    def run(self, ctx):
        test = ctx.result("init")["test"]
        mem_bytes = ctx.param("mem_bytes", 128 << 20)
        blen = ctx.param("memtest_burst_len", 16)

        ctx.say(f"[memtest] {mem_bytes >> 20} MB at bl{blen}")
        ok = memtest(ctx.bus, test, mem_bytes=mem_bytes, blen=blen)

        if not ok:
            raise RuntimeError(
                f"memtest failed over {mem_bytes >> 20} MB -- see the per-chunk "
                f"lines above for the failing addresses")
        return {"ok": True, "mem_bytes": mem_bytes, "burst_len": blen}
