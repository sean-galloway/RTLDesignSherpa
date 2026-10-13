# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""amber init sequence -- load tally profile and configure both cycle injectors.

This sequence is imported by the runner; it never opens its own port. It
receives a `ctx.bus` that is already an AmberDriver over the chosen transport.
"""

from __future__ import annotations

import amber_env  # noqa: F401  (path setup)

from sequence import Sequence

from amber_board import AmberDriver, build_default_profile


class Init(Sequence):
    name = "init"
    description = "load tally legal-set profile and configure cycle injectors"

    def run(self, ctx):
        drv = ctx.bus
        if not isinstance(drv, AmberDriver):
            raise TypeError(f"ctx.bus must be AmberDriver, got {type(drv).__name__}")

        count = ctx.param("count", 20000)
        we_mix = ctx.param("we_mix", 64)

        ctx.say(f"[init] loading tally profile, count={count} we_mix={we_mix}")
        drv.clear_and_load_profile(build_default_profile())

        mask = 0x0000_0FFF
        base = 0x0000_0000
        drv.configure_ci("ci0", seed=0x1234_5678, addr_base=base,
                         addr_mask=mask, count=count, we_mix=we_mix)
        drv.configure_ci("ci1", seed=0xDEAD_BEEF, addr_base=base,
                         addr_mask=mask, count=count, we_mix=we_mix)

        ctx.say("[init] cycle injectors configured")
        return {"configured": True, "count": count, "we_mix": we_mix}
