# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""pumice write-then-read sequence -- the smoke test.

Programs both engines over the same window with one seed, runs write then read,
and reports the honest verdict: `beats_mismatched` is authoritative in every
mode, and a hang is a failure rather than a clean zero.
"""

from __future__ import annotations

import pumice_env  # noqa: F401  (import side effect: sys.path setup)

from sequence import Sequence


class WriteRead(Sequence):
    name = "write_read"
    description = "linear write-then-read pass with per-beat integrity check"
    requires = ("init",)

    def run(self, ctx):
        test = ctx.result("init")["test"]

        blen = ctx.param("burst_len", 8)
        txn = ctx.param("txn_count", 64)
        ctx.say(f"[write_read] bl{blen} x {txn} txn @ 0x{test.base:08X}")

        res = test.run(burst_len=blen, txn_count=txn)

        ctx.say(f"[write_read] mismatched={res.mismatched} "
                f"crc exp=0x{res.expected:08X} act=0x{res.actual:08X}")

        if not res.ok:
            # Returning the detail AND failing: the runner records the value,
            # so a failing run still leaves the numbers behind for triage.
            raise RuntimeError(
                f"write/read failed: mismatched={res.mismatched}, "
                f"crc exp=0x{res.expected:08X} act=0x{res.actual:08X}")

        return {
            "ok": True,
            "mismatched": res.mismatched,
            "expected": res.expected,
            "actual": res.actual,
            "burst_len": blen,
            "txn_count": txn,
        }
