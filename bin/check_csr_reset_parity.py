#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""CSR reset-parity gate (pumice TASK-015 layer 0).

Every software-writable field must be accounted for in exactly one of three
ways, declared in a manifest that a human edits:

  ships=<v>   the field's reset value IS the configuration we ship, so a suite
              that runs resets is testing the shipping design. Checked: the
              reset in the generated regmap must equal <v>.
  swept=(..)  the field is deliberately varied by DV, >= 2 distinct values,
              `by=` names the artifact that varies it, and `oracle=` says what
              would FAIL if a value were wrong. Checked: the count, the
              distinctness, that the artifact exists and mentions the field
              (a typo-catcher, NOT proof that it sweeps), and that an oracle is
              named. The oracle requirement is the load-bearing one: a CSR
              read/write walk touches every field with two values and proves
              nothing about behaviour, so a sweep that cannot name what breaks
              is not a sweep.
  waived="..."  neither -- with a written reason. Checked: the reason is not empty.

WHY THIS GATE EXISTS. pumice BUG-003 shipped because the reset values and the
configuration anyone actually ran had diverged, silently: the top suite runs
resets, the board host programs everything, and nobody had ever written down
that those two should agree. Five of the six defects in that class on record are
the same shape -- a field resets to a value that disables the feature and
nothing ever writes it (pumice TASK-011 RBL reset_interval=0, TASK-013
check_interval=0, TASK-007 watermarks reset to disabled, the board tCCD left
unprogrammed). A field cannot be in that state and pass this gate: it is neither
swept nor declared to ship, so it fails until someone decides which it is.

The gate is deliberately NOT satisfiable by declaring `ships=<the current
reset>` for everything without reading it. That would pass, and it would also be
a written, reviewable claim that each of those resets is the shipping intent --
which is the artifact this gate is really after. A silent default is the bug; a
signed-for default is a decision.

Usage:
    python3 bin/check_csr_reset_parity.py                    # every manifest found
    python3 bin/check_csr_reset_parity.py --manifest <path>
    python3 bin/check_csr_reset_parity.py --list-unaccounted  # skeleton for new fields
"""
from __future__ import annotations

import argparse
import importlib.util
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
MANIFEST_GLOB = "projects/components/**/dv/csr_reset_parity.py"


def _rel(path: Path) -> str:
    """Repo-relative when it can be, absolute otherwise -- a manifest under a
    tmp dir (the checker's own tests) must not crash the error formatter."""
    try:
        return str(path.relative_to(ROOT))
    except ValueError:
        return str(path)


def _load(path: Path, name: str):
    spec = importlib.util.spec_from_file_location(name, path)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


def _rw_fields(regmap_path: Path) -> dict[str, int]:
    """{'REG.field': reset_int} for every sw=rw field in the generated regmap."""
    top = _load(regmap_path, "_rp_regmap").top_block
    out = {}
    for rname, reg in top.items():
        if not isinstance(reg, dict) or reg.get("type") != "reg":
            continue
        for fname, f in reg.items():
            if isinstance(f, dict) and f.get("type") == "field" and f.get("sw") == "rw":
                out[f"{rname}.{fname}"] = int(str(f["default"]), 16)
    return out


def check(manifest_path: Path, list_unaccounted: bool = False) -> list[str]:
    errs: list[str] = []
    man = _load(manifest_path, "_rp_manifest")
    base = manifest_path.parent

    regmap = (base / man.REGMAP).resolve()
    rdl = (base / man.RDL).resolve()
    for p, what in ((regmap, "REGMAP"), (rdl, "RDL")):
        if not p.exists():
            errs.append(f"{what} does not exist: {p}")
    if errs:
        return errs

    fields = _rw_fields(regmap)

    # (A) the regmap must actually be generated from the .rdl this manifest names.
    #     Staleness itself is NOT checked here: bin/check_rdl_regen.py already owns
    #     it in the same pre-commit gate, and a second implementation would drift.
    #     (A textual `sw = rw` count does not work anyway -- OBS_ROW_HIT is one reg
    #     definition instantiated 8 times, so 66 declarations elaborate to 73
    #     fields. That miscount failed this gate against a perfectly current
    #     regmap on its first run.)
    head = regmap.read_text(errors="replace")[:2000]
    if rdl.name not in head:
        errs.append(
            f"{regmap.name} does not name {rdl.name} as its source -- the manifest "
            f"is pointing at a regmap generated from something else"
        )

    declared = dict(man.FIELDS)

    if list_unaccounted:
        missing = sorted(set(fields) - set(declared))
        print(f"# {len(missing)} unaccounted sw=rw field(s) -- skeleton:")
        for k in missing:
            print(f'    "{k}": dict(ships=0x{fields[k]:X}),   # TODO: ships / swept / waived')
        return []

    # (F) manifest entries for fields that no longer exist
    for key in sorted(set(declared) - set(fields)):
        errs.append(f"{key}: in the manifest but not a sw=rw field in {regmap.name} "
                    f"(renamed, made reserved, or deleted -- drop the entry)")

    # (B..E) every field accounted for, exactly once, and the claim holds
    for key in sorted(fields):
        reset = fields[key]
        entry = declared.get(key)
        if entry is None:
            errs.append(
                f"{key}: UNACCOUNTED (resets to 0x{reset:X}). Declare ships=/swept=/waived= "
                f"in {_rel(manifest_path)}. This is the pumice BUG-003 class: "
                f"a field nobody decided about."
            )
            continue
        kinds = [k for k in ("ships", "swept", "waived") if k in entry]
        if len(kinds) != 1:
            errs.append(f"{key}: needs exactly one of ships/swept/waived, found {kinds or 'none'}")
            continue
        kind = kinds[0]
        if kind == "ships":
            want = entry["ships"]
            if reset != want:
                errs.append(
                    f"{key}: RESET PARITY BROKEN -- manifest says it ships 0x{want:X}, "
                    f"the reset is 0x{reset:X}. Either change the reset in "
                    f"{rdl.name} to the value you ship, or say why it differs "
                    f"(waived=) -- do not leave the suite testing one value and "
                    f"the board running another."
                )
        elif kind == "swept":
            vals = list(entry["swept"])
            if len(set(vals)) < 2:
                errs.append(f"{key}: swept= needs >= 2 distinct values, got {vals}")
            if not str(entry.get("oracle", "")).strip():
                errs.append(
                    f"{key}: swept= must name an oracle= -- what FAILS if a value is "
                    f"wrong. A sweep with no oracle only proves the field is writable."
                )
            by = entry.get("by")
            if not by:
                errs.append(f"{key}: swept= must name the artifact that varies it (by=)")
            else:
                art = (ROOT / by)
                if not art.exists():
                    errs.append(f"{key}: swept by={by}, which does not exist")
                else:
                    # A layer below the CSR drives the RTL port, not the field
                    # name; `drives=` names that port so the check still bites.
                    token = entry.get("drives") or fname_of(key)
                    if token not in art.read_text():
                        errs.append(
                            f"{key}: swept by={by}, but that file never mentions "
                            f"'{token}' -- the claim is unverifiable. If the sweep "
                            f"drives an RTL port rather than the CSR field, name "
                            f"the port in drives=."
                        )
        else:
            if not str(entry["waived"]).strip():
                errs.append(f"{key}: waived= needs a written reason")

    # (G) clock parity -- a sim that runs a different clock than the board is not
    #     testing the board (pumice TASK-015: the 54%-vs-3% comparison in
    #     TASK-013 was a 100 MHz DUT against a 75 MHz one).
    clk = getattr(man, "CLOCK", None)
    if clk:
        site = ROOT / clk["declared_by"]
        if not site.exists():
            errs.append(f"CLOCK.declared_by does not exist: {clk['declared_by']}")
        else:
            txt = site.read_text()
            hz = clk["hz"]
            if not re.search(rf'{clk["env"]}"?,\s*"{hz}"', txt) and str(hz) not in txt:
                errs.append(
                    f"CLOCK: manifest declares {hz} Hz but {clk['declared_by']} "
                    f"does not carry that number -- sim and board clocks have drifted"
                )
    return errs


def fname_of(key: str) -> str:
    return key.split(".", 1)[1]


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--manifest", help="one manifest to check (default: all found)")
    ap.add_argument("--list-unaccounted", action="store_true",
                    help="print a manifest skeleton for fields not yet declared")
    a = ap.parse_args()

    mans = [Path(a.manifest).resolve()] if a.manifest else sorted(ROOT.glob(MANIFEST_GLOB))
    if not mans:
        print("check_csr_reset_parity: no manifests found -- nothing to gate")
        return 0

    bad = 0
    for m in mans:
        errs = check(m, a.list_unaccounted)
        if a.list_unaccounted:
            continue
        rel = _rel(m)
        if errs:
            bad += 1
            print(f"FAIL {rel}", file=sys.stderr)
            for e in errs:
                print(f"  - {e}", file=sys.stderr)
        else:
            man = _load(m, "_rp_count")
            print(f"PASS {rel} ({len(man.FIELDS)} sw=rw fields accounted for)")
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
