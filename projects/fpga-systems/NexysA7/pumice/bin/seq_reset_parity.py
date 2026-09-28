# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""Reset-parity check ON SILICON (pumice TASK-015 layer 0).

`bin/check_csr_reset_parity.py` gates the manifest against the generated regmap
-- that is a check on two FILES. This sequence checks the third thing neither
file can speak for: what the flops in the part actually come up holding.

They can differ. The regmap is generated from the .rdl, the bitstream is built
from the same .rdl, but a stale bitstream, a partial regeneration, or a
regblock the synthesiser optimised differently all break the chain silently --
and every one of those failures looks exactly like a passing file-level gate.
So this reads every `sw=rw` field back over UART BEFORE anything programs the
controller, and compares against the manifest.

It must run FIRST, before `init`: `init` programs the PHY, the geometry and the
policy, so a reset read taken after it measures the host, not the reset.

    make run SEQ="reset_parity"
    make run SEQ="reset_parity init write_read"
"""

from __future__ import annotations

import importlib.util
import os

import pumice_env  # noqa: F401  (import side effect: sys.path setup)

from sequence import Sequence

_REPO = os.environ.get("REPO_ROOT") or os.path.abspath(
    os.path.join(os.path.dirname(__file__), "..", "..", "..", ".."))
_PUMICE = os.path.join(_REPO, "projects/components/memory-controllers/pumice-ddr2-lpddr2")
_MANIFEST = os.path.join(_PUMICE, "dv/csr_reset_parity.py")
_REGMAP = os.path.join(_PUMICE, "regs/generated/pumice_csr_regmap.py")


def _load(path, name):
    spec = importlib.util.spec_from_file_location(name, path)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


class ResetParity(Sequence):
    name = "reset_parity"
    description = "read every sw=rw CSR back at reset and compare to the manifest"
    requires = ()          # deliberately none: this must precede `init`

    def run(self, ctx):
        drv = ctx.bus

        # Put the CSRs BACK to their resets before reading, so this sequence is
        # repeatable rather than only valid on a freshly programmed board. A
        # second run in the same session would otherwise read whatever the first
        # run (or an `init`) left behind and call it the reset state.
        #
        # restore_geometry=False is the whole point: the driver's default is to
        # re-program the build geometry immediately after the reset (because
        # soft_reset reverts the CSRs to RTL defaults that are a DIFFERENT
        # geometry -- pumice ISSUE-016), and that would overwrite three of the
        # very fields being checked. The driver's docstring says this flag exists
        # "only to observe the raw reset state", which is exactly this.
        if ctx.param("soft_reset_first", True):
            drv.soft_reset(restore_geometry=False)

        man = _load(_MANIFEST, "_rp_manifest")
        regmap = _load(_REGMAP, "_rp_regmap").top_block

        # Fields the manifest says ship at their reset value. `swept` fields are
        # varied by DV on purpose and `waived` ones are strobes or counters, so
        # neither has a reset worth asserting here -- but they are COUNTED, so a
        # shrinking manifest cannot quietly reduce what this proves.
        want, skipped = {}, {"swept": 0, "waived": 0}
        for key, entry in man.FIELDS.items():
            if "ships" in entry:
                want[key] = entry["ships"]
            elif "swept" in entry:
                skipped["swept"] += 1
            else:
                skipped["waived"] += 1

        # BY NAME through the generated regmap -- no offsets, no hand bit-slicing
        # (handbook: registers by name). The regmap is loaded anyway, to notice a
        # manifest entry naming a field the current map does not have.
        field = drv.pumice.regs.field
        mismatches, checked = [], 0
        for key in sorted(want):
            reg, fname = key.split(".", 1)
            if reg not in regmap or fname not in regmap[reg]:
                raise AssertionError(
                    f"{key} is in the manifest but not in the generated regmap -- "
                    f"run bin/check_csr_reset_parity.py, which gates exactly this.")
            got = int(field(reg, fname))
            exp = want[key]
            checked += 1
            if got != exp:
                mismatches.append((key, exp, got))

        for name, exp, got in mismatches:
            ctx.say(f"[reset_parity] MISMATCH {name}: manifest says it ships "
                    f"0x{exp:X}, the part came up 0x{got:X}")

        ctx.say(f"[reset_parity] {checked} field(s) checked against the manifest, "
                f"{len(mismatches)} mismatch(es); skipped {skipped['swept']} swept "
                f"+ {skipped['waived']} waived")

        # A pass has to be non-vacuous: if the manifest stopped declaring
        # shipping values, this would read zero fields and "succeed".
        if checked < 40:
            raise AssertionError(
                f"only {checked} fields carried a shipping value -- expected 40+. "
                f"Either the manifest shrank or the regmap did; a near-empty "
                f"comparison must not report a clean board.")
        if mismatches:
            raise AssertionError(
                f"{len(mismatches)} CSR(s) did not come up at the value the "
                f"manifest says ships: "
                f"{', '.join(n for n, _, _ in mismatches)}. The bitstream and "
                f"the .rdl have diverged -- rebuild before trusting any "
                f"measurement from this board.")

        return {"checked": checked, "mismatches": 0,
                "skipped_swept": skipped["swept"],
                "skipped_waived": skipped["waived"]}
