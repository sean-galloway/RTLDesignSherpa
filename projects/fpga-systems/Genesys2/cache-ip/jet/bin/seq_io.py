# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""io sequence -- the IO doorbell against the warm caches (onyx TASK-001 step 7).

Runs after smoke on the reference rig's onyx selections (REF_CACHE_SEL 4 / 5):
WriteNoSnoop / ReadNoSnoop / ReadOnce of a line of its own, then ReadOnce,
WriteUnique and the reads back of a line the caches hold.  Skips itself where
IO_STATUS.absent reads 1 (no IO port in the selection).
"""

from __future__ import annotations

import jet_env  # noqa: F401  (path setup)

from sequence import Sequence

from jet_board import io_check


class Io(Sequence):
    name = "io"
    description = "the IO doorbell: no-snoop and coherent accesses against the warm caches"
    requires = ("smoke",)

    def run(self, ctx):
        drv = ctx.bus
        sleep_fn = ctx.param("sleep_fn", None)
        result = io_check(drv, sleep_fn=sleep_fn, say=ctx.say)
        if not result.get("ok"):
            raise RuntimeError(f"io check failed: {result}")
        return result
