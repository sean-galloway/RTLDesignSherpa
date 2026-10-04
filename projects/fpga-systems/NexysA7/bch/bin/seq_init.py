# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""bch loop init: prove the link and the bitstream before any run.

BUILD_ID must be BCHP, SCRATCH must round-trip, and the PROFILE register tells
the later sequences what code the board carries (t drives the expectations).
TOPOLOGY tells them what the bitstream BUILT -- one RIBM decoder, AXIS or AXI4.
Touches registers only through ctx.bus (a BchLoopDriver).
"""
from __future__ import annotations

import bch_env  # noqa: F401
from sequence import Sequence
import bch_loop_programs as progs


class Init(Sequence):
    name = "init"
    description = "BUILD_ID, SCRATCH round-trip, PROFILE"

    def run(self, ctx):
        r = progs.smoke(ctx.bus)
        if not r.build_id_ok:
            raise RuntimeError(f"wrong bitstream: BUILD_ID 0x{r.build_id:08X}")
        if not r.ok:
            raise RuntimeError(f"SCRATCH round-trip failed: {r.scratch}")
        p = r.profile
        ctx.say(f"[init] BCH({p['n']},{p['k']}) t={p['t']} m={p['m']} {p['spb']} symbols/beat")
        topo = ctx.bus.topology()
        ctx.say(f"[init] 1 decoder: {topo['name_a']}; datapath {topo['iface']}; "
                f"no comparator, so the B-side counters read 0 by design")
        return r
