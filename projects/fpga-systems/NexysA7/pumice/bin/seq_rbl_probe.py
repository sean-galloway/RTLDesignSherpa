# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""Read back PAGE_RBL_CFG after applying each rbl config (PUMICE-013/006/047).

The rbl_static collapse was attributed to reset_interval=0 on the strength of a
sweep. But the RTL says mode 6's epoch only CLEARS counters, and the counter is
already reset to 1 on every tag miss (pumice_rbl_table.sv:172), so on streaming
the epoch should be nearly inert. Either the RTL reading is wrong or the CSR is
not landing what the host thinks -- which is exactly PUMICE-047's suspicion.
Read the register back and find out before changing any default.
"""
from __future__ import annotations

import dataclasses

import pumice_env  # noqa: F401

from sequence import Sequence

import pumice_char as pc


class RblProbe(Sequence):
    name = "rbl_probe"
    description = "PAGE_RBL_CFG write/readback fidelity"
    requires = ("init",)

    def run(self, ctx):
        drv = ctx.bus
        f = drv.pumice.regs.field
        out = {}
        base = pc.CONFIGS["rbl_static"]
        for epoch in (0, 64, 256):
            cfg = dataclasses.replace(
                base, name=f"probe_e{epoch}",
                page_rbl={**base.page_rbl, "reset_interval": epoch})
            cfg.apply(drv)
            # regmap field names are ways/sets; the host kwargs are *_log2
            got = {n: int(f("PAGE_RBL_CFG", n))
                   for n in ("miss_thresh", "ways", "sets", "reset_interval")}
            want = {"miss_thresh": cfg.page_rbl["miss_thresh"],
                    "ways": cfg.page_rbl["ways_log2"],
                    "sets": cfg.page_rbl["sets_log2"],
                    "reset_interval": epoch}
            mode = int(f("PAGE_POLICY_CFG", "policy_mode"))
            pol  = int(f("PAGE_POLICY_CFG", "policy_scope"))
            bad = {k: (want[k], got[k]) for k in want if want[k] != got[k]}
            ctx.say(f"[probe] epoch={epoch:<5} policy_mode={mode} scope={pol} "
                    f"RBL={got}  {'MISMATCH ' + str(bad) if bad else 'match'}")
            out[epoch] = (got, bad, mode, pol)
        return out
