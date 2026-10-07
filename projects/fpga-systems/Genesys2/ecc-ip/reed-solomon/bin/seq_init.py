# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""rs loop init: prove the link and the bitstream before any run.

BUILD_ID must be a known profile ID, SCRATCH must round-trip, and the PROFILE
register tells the later sequences what code the board carries (t drives the
expectations). TOPOLOGY tells them what the bitstream BUILT -- one decoder or
two, and which solver is in each slot -- so nothing downstream has to be told
which image is loaded. Touches registers only through ctx.bus (an RsLoopDriver).
"""
from __future__ import annotations

import rs_env  # noqa: F401
from sequence import Sequence
import rs_loop_programs as progs


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
        ctx.say(f"[init] RS({p['n']},{p['n'] - 2 * p['t']}) t={p['t']} m={p['m']} {p['spb']} symbols/beat")
        topo = ctx.bus.topology()
        if topo["decoders"] == 2:
            ctx.say(f"[init] 2 decoders: A={topo['name_a']} B={topo['name_b']}, "
                    f"comparator {'on' if topo['compare'] else 'OFF'}")
        else:
            ctx.say(f"[init] 1 decoder: {topo['name_a']}; no comparator, so the "
                    f"B-side counters and CMP_* read 0 by design")
        return r
