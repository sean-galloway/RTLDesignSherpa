# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""pumice endurance soak sequence -- `pumice_master.long_soak` under a named
controller configuration.

Rotating 4 MB write/read rounds across the device for `--soak-minutes`
wall-clock, every tenth round with the two engines concurrent, the leveled eye
re-verified every five minutes. Minutes-to-hours scale: the confidence tier
above the memtest, not a bring-up smoke.

The soak runs the controller AS THE CHAR MEASURES IT: `--soak-config` names a
`pumice_char.ControllerConfig` (default `defaults`, the SKU's power-on paging
with the host's lane, phases and JEDEC set), re-applied after every per-round
reset. Without that the soak would exercise the RTL reset state -- row lane
off, row_phase 0 -- and report it as the SKU. Filed from memory-controllers
MC-020: the phase-exact JEDEC derivation counts every hop from the DFI phases,
so the soak that qualifies it has to run on the phases the SKU runs on.
"""

from __future__ import annotations

import pumice_env  # noqa: F401  (import side effect: sys.path setup)

from sequence import Sequence

import pumice_char as pc
from pumice_master import A7Leveling, long_soak


class Soak(Sequence):
    name = "soak"
    description = "endurance soak (long_soak) for --soak-minutes under --soak-config"
    requires = ("init",)

    def run(self, ctx):
        drv = ctx.bus
        test = ctx.result("init")["test"]
        minutes = float(ctx.param("soak_minutes", 30.0))
        cfg_name = ctx.param("soak_config", "defaults")
        csv = ctx.param("soak_csv")
        mem_bytes = ctx.param("mem_bytes", 128 << 20)

        if cfg_name not in pc.CONFIGS:
            raise RuntimeError(f"soak: unknown config {cfg_name!r}; have {sorted(pc.CONFIGS)}")
        if test.level is None or not test.level.ok:
            raise RuntimeError("soak needs a leveled read window -- run init with leveling")
        cfg = pc.CONFIGS[cfg_name].resolved(drv)

        def reapply() -> None:
            cfg.apply(drv)

        lv = A7Leveling(drv, rd_phase=test.rd_phase, rddata_delay=test.rddata_delay,
                        verbose=False)
        ctx.say(f"[soak] {minutes:g} min, config {cfg_name}, {mem_bytes >> 20} MB"
                + (f", heartbeat -> {csv}" if csv else ""))
        ok = long_soak(drv, test, lv, test.level, minutes, mem_bytes=mem_bytes,
                       csv_path=csv, reapply=reapply)
        if not ok:
            raise RuntimeError(f"soak FAILED under {cfg_name} -- see the round lines above")
        return {"ok": True, "minutes": minutes, "config": cfg_name, "csv": csv}
