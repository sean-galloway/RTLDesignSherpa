# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""Report the generator array shape as BUILT (TASK-010 scoping)."""
from __future__ import annotations
import pumice_env  # noqa: F401
from sequence import Sequence


class GenShape(Sequence):
    name = "genshape"
    description = "generator array shape as synthesized"
    requires = ("init",)

    def run(self, ctx):
        cfg = ctx.bus.gen_config()
        ctx.say(f"[genshape] {cfg}")
        return cfg
