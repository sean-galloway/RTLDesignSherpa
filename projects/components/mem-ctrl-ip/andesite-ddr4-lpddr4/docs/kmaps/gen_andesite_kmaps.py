#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""Generate andesite_cmd_kmaps.xlsx + generated/*.md for the andesite MAS v0.1.

Modeled on projects/components/ecc-ip/bch/docs/gen_bch_signal_contracts_kmaps.py.

At MAS v0.1 there is no RTL, so the citations point at the MAS pages where
the intended expressions are written verbatim. When RTL lands, the citations
are re-pointed at the corresponding .sv file:line and the generator's
citation gate will catch drift.

Builds, from scratch (rerunnable / idempotent):
  * "DDR4 command decode" sheet -- the ACT_n x RAS_n x CAS_n x WE_n truth
    table as a multi-valued K-map, plus the per-command minimal qualifier
    SOPs derived by Quine-McCluskey
  * generated/01_ddr4_command_table.md -- the markdown rendering of the
    same table (cited from the HAS ch06 verification list and the MAS ch04
    anchor map)

Rerun after MAS or RTL changes (from the repo root or this directory):
    python3 projects/components/mem-ctrl-ip/andesite-ddr4-lpddr4/docs/kmaps/gen_andesite_kmaps.py
"""
import os
import sys
from datetime import datetime

HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.abspath(os.path.join(HERE, *(".." for _ in range(6))))
sys.path.insert(0, os.path.join(REPO, "bin"))

import openpyxl
from kmaps import (verify_citations, qm_minimize, sop_str,
                   new_kmap_sheet)

XLSX = os.path.join(HERE, "andesite_cmd_kmaps.xlsx")
GEN = os.path.join(HERE, "generated")

# ---------------------------------------------------------------------------
# MAS paths (citations point here until RTL exists)
# ---------------------------------------------------------------------------
CMD = ("projects/components/mem-ctrl-ip/andesite-ddr4-lpddr4/docs/"
       "andesite_mas/ch02_blocks/01_cmd_formatter.md")
CTR = ("projects/components/mem-ctrl-ip/andesite-ddr4-lpddr4/docs/"
       "andesite_mas/ch04_contracts/01_core_contracts.md")

CITES = [
    # the DDR4 command truth table anchor (don't renumber the fence)
    (CMD, 91, "ACT_n  RAS_n  CAS_n  WE_n"),
    (CMD, 93, "ACT"),
    (CMD, 101, "auto-precharge variants"),
    # the MAS ch04 anchor map names this fence as the decode contract's source
    (CTR, 47, "truth table fence"),
]

# ---------------------------------------------------------------------------
# The decode itself -- single source of truth for xlsx and markdown.
# Anchor: 01_cmd_formatter.md Table 2.3 (citation anchor, don't renumber).
# (ACT_n, RAS_n, CAS_n, WE_n) MSB-first, CS_n=0.
# ---------------------------------------------------------------------------
VARS = ["ACT_n", "RAS_n", "CAS_n", "WE_n"]
COMMANDS = [
    ("NOP", (1, 1, 1, 1)),
    ("ACT", (0, 1, 1, 1)),
    ("RD",  (1, 1, 0, 1)),
    ("WR",  (1, 1, 0, 0)),
    ("MRS", (0, 0, 0, 0)),
    ("REF", (0, 0, 0, 1)),
    ("PRE", (1, 0, 1, 0)),
    ("ZQ",  (1, 1, 1, 0)),
]
BY_CODE = {bits: name for name, bits in COMMANDS}
UNUSED = [tuple((i >> (4 - 1 - k)) & 1 for k in range(4))
          for i in range(16) if tuple((i >> (4 - 1 - k)) & 1 for k in range(4))
          not in BY_CODE]


def decode(*bits):
    """Multi-valued map cell: command name, or None (don't-care) for the
    codes outside the anchored table -- an X, never a forced 0."""
    return BY_CODE.get(tuple(bits))


def sop_rows():
    """Per-command minimal qualifier SOPs: each command is one anchored
    minterm; the 8 unused codes are free to join the cover."""
    rows = []
    for name, bits in COMMANDS:
        idx = 0
        for b in bits:
            idx = (idx << 1) | b
        unused_idx = []
        for u in UNUSED:
            ui = 0
            for b in u:
                ui = (ui << 1) | b
            unused_idx.append(ui)
        cubes = qm_minimize(4, [idx], unused_idx)
        rows.append((name, "".join(str(b) for b in bits),
                     sop_str(cubes, VARS)))
    return rows


def build_ddr4_command_decode(wb):
    km = new_kmap_sheet(wb, "DDR4 command decode")
    km.sheet_intro(
        "andesite DDR4 command decode (pre-RTL, cites MAS pages)",
        ["One K-map over the four DFI command pins, CS_n=0 slice. Each cell is",
         "the decoded command; the 8 codes outside the anchored truth table are",
         "X (illegal/unused), free to widen the per-command minimal covers.",
         "Verdicts on the SOP table are DERIVED, not RTL-diffed -- no RTL exists",
         "yet (HAS ch06 posture; citations re-point at .sv when RTL lands)."])
    km.kmap(
        "op = decode(ACT_n, RAS_n, CAS_n, WE_n)", f"{CMD}:91",
        "op = decode(ACT_n, RAS_n, CAS_n, WE_n)   -- CS_n = 0 slice",
        [("ACT_n", "DFI activate select pin", f"{CMD}:91"),
         ("RAS_n", "DFI row-address strobe command pin", f"{CMD}:91"),
         ("CAS_n", "DFI column-address strobe command pin", f"{CMD}:91"),
         ("WE_n",  "DFI write-enable command pin", f"{CMD}:91")],
        decode,
        "One command per anchored cell; every non-anchored code is X. "
        "RDA/WRA/PREA/ZQCL are NOT separate cells -- AP (A10) is an address "
        "input qualifying the same rows, per the anchor's own note.",
        values={name: name for name, _ in COMMANDS},
        depends_only_on=(
            "these four pins. The slice holds CS_n=0 (CS_n=1 is DES, outside "
            "the decode), CKE registered high (SRE/SRX are CKE-qualified "
            "entries, outside the slice), and memtype=DDR4 (LPDDR4's CA path "
            "is a different submodule). AP (A10) is an address input, not a "
            "pin: the auto-precharge and ZQ-long variants are the RD/WR/PRE/ZQ "
            "rows with AP=1."))
    km.table(
        "Per-command minimal qualifier SOPs", f"{CMD}:91",
        ["Command", "Code (ACT_n RAS_n CAS_n WE_n)", "Minimal qualifier SOP"],
        [(n, c, s) for n, c, s in sop_rows()],
        note=("Each SOP is derived by Quine-McCluskey with the 8 unused codes "
              "as don't-cares; when RTL lands, rtl_sop= diffs the "
              "implementation against these covers."))


def write_markdown():
    os.makedirs(GEN, exist_ok=True)
    path = os.path.join(GEN, "01_ddr4_command_table.md")
    lines = []
    lines.append("# DDR4 Command Truth Table (generated)")
    lines.append("")
    lines.append("Generated by `docs/kmaps/gen_andesite_kmaps.py` from the "
                 "citation anchor in")
    lines.append("`andesite_mas/ch02_blocks/01_cmd_formatter.md` "
                 "(Table 2.3). Do not edit; rerun the generator.")
    lines.append("")
    lines.append("Slice: `CS_n = 0`, CKE registered high, memtype = DDR4. "
                 "Every code outside the anchored table is ILLEGAL/unused "
                 "(X), never forced to 0. RDA/WRA/PREA/ZQCL are the "
                 "RD/WR/PRE/ZQ rows with the AP address bit (A10) set -- AP "
                 "is an input, not a pin variant.")
    lines.append("")
    lines.append("| ACT_n | RAS_n | CAS_n | WE_n | Command |")
    lines.append("|---|---|---|---|---|")
    for name, bits in COMMANDS:
        lines.append("| {} | {} | {} | {} | {} |".format(*bits, name))
    lines.append("| — | — | — | — | DES (CS_n=1) |")
    lines.append("")
    lines.append("## Minimal qualifier SOPs")
    lines.append("")
    lines.append("Derived by Quine-McCluskey with the 8 unused codes as "
                 "don't-cares (they are free to join the cover):")
    lines.append("")
    lines.append("| Command | Code | Minimal qualifier SOP |")
    lines.append("|---|---|---|")
    for name, code, sop in sop_rows():
        lines.append("| {} | {} | `{}` |".format(name, code, sop))
    lines.append("")
    lines.append("Verdict posture: DERIVED, not RTL-diffed -- no RTL exists "
                 "at MAS v0.1 (HAS ch06). When RTL lands, the generator "
                 "re-points citations at `.sv` lines and the workbook diffs "
                 "the implementation against these covers.")
    lines.append("")
    with open(path, "w") as f:
        f.write("\n".join(lines))
    return path


def main():
    verify_citations(CITES, REPO)
    wb = openpyxl.Workbook()
    del wb[wb.sheetnames[0]]           # drop the default sheet
    # fixed document properties so reruns are byte-identical
    wb.properties.creator = "RTL Design Sherpa"
    wb.properties.lastModifiedBy = "RTL Design Sherpa"
    stamp = datetime(2026, 10, 3)
    wb.properties.created = stamp
    wb.properties.modified = stamp

    build_ddr4_command_decode(wb)

    md = write_markdown()
    wb.save(XLSX)
    print(f"wrote {XLSX}")
    for name in wb.sheetnames:
        print("  ", name)
    print(f"wrote {md}")


if __name__ == "__main__":
    main()
