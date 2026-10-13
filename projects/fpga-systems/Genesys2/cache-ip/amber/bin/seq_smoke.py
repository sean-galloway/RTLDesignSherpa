# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""amber smoke sequence -- kick both cycle injectors and dump results.

Depends on init having configured the injectors. The transport is already
injected into ctx.bus, so this same sequence runs on the board and in the
cocotb cosim.
"""

from __future__ import annotations

import amber_env  # noqa: F401  (path setup)

from sequence import Sequence

from amber_board import smoke


class Smoke(Sequence):
    name = "smoke"
    description = "kick cycle injectors, poll done, read CRCs and tallies"
    requires = ("init",)

    def run(self, ctx):
        drv = ctx.bus
        count = ctx.param("count", 20000)
        blind = ctx.param("blind", False)
        sleep_fn = ctx.param("sleep_fn", None)

        result = smoke(drv, count=count, blind=blind, sleep_fn=sleep_fn,
                       say=ctx.say)

        if not (result.get("ok") or result.get("blind")):
            raise RuntimeError(f"smoke failed: {result}")

        return result
