# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""rs loop sweep: exactly e errors per block for e = 0 .. 2t + 2, both decoders.

The table this prints is the board-level validation of the two solvers: up to
t every block is corrected with exactly e symbols and the CRC matches the
generator's; above t every block is flagged uncorrectable; at every e the
riBM and Euclid decoders agree beat for beat and verdict for verdict.
"""
from __future__ import annotations

import rs_env  # noqa: F401
from sequence import Sequence
import rs_loop_programs as progs


class Sweep(Sequence):
    name = "sweep"
    requires = ("init",)
    description = "e = 0 .. 2t+2, exact count per block, riBM vs Euclid"

    def run(self, ctx):
        drv = ctx.bus
        t = ctx.result("init").profile["t"]
        blocks = ctx.param("blocks", 16)
        counts = ctx.param("counts") or list(range(0, 2 * t + 3))
        rows = progs.sweep(drv, counts, blocks=blocks, throttle=ctx.param("throttle", False))
        for row in rows:
            ctx.say("[sweep] " + progs.format_row(row))
        bad = [row for row in rows if not row.ok]
        if bad:
            raise RuntimeError(f"{len(bad)} of {len(rows)} error counts failed: "
                               + ", ".join(str(r.count) for r in bad))
        return rows
