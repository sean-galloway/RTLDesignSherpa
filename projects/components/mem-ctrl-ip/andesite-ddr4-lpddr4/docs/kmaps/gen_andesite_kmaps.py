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
  * "LPDDR4 CA commands" sheet -- contract table of command classes to
    12-bit CA encoding source and carried fields
  * "Address decode maps" sheet -- field-order table and 2-var BG map for
    the DDR4 design-point geometry
  * "MR0-MR6 programming maps" sheet -- per-memtype mode-register semantics
  * "ODT truth table" sheet -- multi-valued K-map of termination policy
  * "FGR refresh select" sheet -- FGR factor to tREFI/tRFC selection
  * generated/01_ddr4_command_table.md through generated/06_fgr_refresh_map.md

Rerun after MAS or RTL changes (from the repo root or this directory):
    python3 projects/components/mem-ctrl-ip/andesite-ddr4-lpddr4/docs/kmaps/gen_andesite_kmaps.py
"""
import os
import re
import sys
import zipfile
from datetime import datetime

HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.abspath(os.path.join(HERE, *(".." for _ in range(6))))
sys.path.insert(0, os.path.join(REPO, "bin"))

import openpyxl
from kmaps import (verify_citations, qm_minimize, sop_str,
                   new_kmap_sheet)

XLSX = os.path.join(HERE, "andesite_cmd_kmaps.xlsx")
GEN = os.path.join(HERE, "generated")

# Fixed zip timestamp + core properties so reruns are byte-identical.
# openpyxl sets zip entry date_time from the wall clock and also writes
# dcterms:modified in docProps/core.xml from the current time; we rewrite both
# to constants after save.
_FIXED_ZIP_DATE = (2026, 10, 3, 0, 0, 0)
_FIXED_CORE_MODIFIED = "2026-10-03T00:00:00Z"


def _normalize_xlsx_timestamps(path):
    """Rewrite zip entry date_times and fix dcterms:modified in core.xml."""
    core_re = re.compile(
        r"(<dcterms:modified[^>]*>)[^<]*(</dcterms:modified>)")
    tmp = path + ".tmp"
    with zipfile.ZipFile(path, "r") as zin:
        with zipfile.ZipFile(tmp, "w", compression=zipfile.ZIP_DEFLATED) as zout:
            for info in zin.infolist():
                data = zin.read(info.filename)
                if info.filename == "docProps/core.xml":
                    text = data.decode("utf-8")
                    text = core_re.sub(
                        r"\g<1>" + _FIXED_CORE_MODIFIED + r"\g<2>", text)
                    data = text.encode("utf-8")
                info.date_time = _FIXED_ZIP_DATE
                zout.writestr(info, data)
    os.replace(tmp, path)


# ---------------------------------------------------------------------------
# MAS paths (citations point here until RTL exists)
# ---------------------------------------------------------------------------
CMD = ("projects/components/mem-ctrl-ip/andesite-ddr4-lpddr4/docs/"
       "andesite_mas/ch02_blocks/01_cmd_formatter.md")
FMT = ("projects/components/mem-ctrl-ip/andesite-ddr4-lpddr4/rtl/fub/"
       "andesite_dfi_cmd_formatter.sv")
AM = ("projects/components/mem-ctrl-ip/andesite-ddr4-lpddr4/docs/"
      "andesite_mas/ch02_blocks/04_addr_mapper.md")
MR = ("projects/components/mem-ctrl-ip/andesite-ddr4-lpddr4/docs/"
      "andesite_mas/ch02_blocks/03_mode_register.md")
ODT = ("projects/components/mem-ctrl-ip/andesite-ddr4-lpddr4/docs/"
       "andesite_mas/ch02_blocks/08_odt_ctrl.md")
REF = ("projects/components/mem-ctrl-ip/andesite-ddr4-lpddr4/docs/"
       "andesite_mas/ch02_blocks/06_refresh_ctrl.md")
CTR = ("projects/components/mem-ctrl-ip/andesite-ddr4-lpddr4/docs/"
       "andesite_mas/ch04_contracts/01_core_contracts.md")
HAS_DP = ("projects/components/mem-ctrl-ip/andesite-ddr4-lpddr4/docs/"
          "andesite_has/ch02_overview/04_design_point.md")

CITES = [
    # the DDR4 command decode -- RTL lines now that the formatter exists
    # (the MAS fence stays the design citation; the RTL is what the
    # workbook diffs rtl_sop against)
    (FMT, 77, "unique case (op_i)"),
    (FMT, 78, "OP_ACT"),
    (FMT, 17, "AP (A10) is an address input, not a pin"),
    # LPDDR4 CA placeholder fence
    (CMD, 139, "Command class -> CA encoding source"),
    (CMD, 148, "REFpb    -> kmap table (bank carried in command)"),
    # address decode structure
    (AM, 77, "sys_addr -> { cs[CS-1:0],"),
    (AM, 78, "bg[BG-1:0]       (DDR4: BG0/BG1; LPDDR4: constant 0),"),
    (AM, 79, "bank[BANK-1:0]   (DDR4: 2 bits; LPDDR4: 3 bits),"),
    (AM, 83, "Field boundaries are runtime CSRs (ADDR_MAP-style),"),
    # design-point geometry
    (HAS_DP, 37, "4 bank groups × 4 banks = 16 banks"),
    # DDR4 MR semantics table
    (MR, 83, "| Register | Fields (semantics-binding) |"),
    (MR, 85, "| MR0 | Burst length (fixed 8 or on-the-fly 4/8), read burst type (sequential/interleaved), CAS latency select, DLL reset bit, write recovery"),
    (MR, 86, "| MR1 | DLL enable, additive latency (AL), RTT_NOM, write-leveling enable, TDQS enable, output driver impedance"),
    (MR, 87, "| MR2 | CAS write latency (CWL), RTT_WR, write CRC mode bits (inert this edition per HAS Ch 3.1), LP ASR |"),
    (MR, 88, "| MR3 | MPR operation and page select, FGR refresh factor (1x/2x/4x), gear-down mode, MPR read format"),
    (MR, 89, "| MR4 | Temperature status, preamble, CAL"),
    (MR, 90, "| MR5 | Read DBI enable, write DBI enable, RTT_PARK, data-mask enable, CA parity latency/mode (A[2:0]), parity persistent-error (A9), parity error status (A4)"),
    (MR, 91, "| MR6 | VrefDQ training range and value, tCCD_L select"),
    (MR, 99, "LPDDR4 doesn't use the same MRS command as DDR4."),
    # ODT policy state fence
    (ODT, 88, "state        | RTT applied   | entered when"),
    (ODT, 89, "IDLE         | RTT_PARK      | no rank selected (park policy)"),
    (ODT, 90, "RD (other)   | RTT_NOM       | a read granted to any rank"),
    (ODT, 91, "WR (self)    | RTT_WR        | a write granted to this rank"),
    # FGR interval arithmetic fence
    (REF, 99, "fgr_factor = {1x:1, 2x:2, 4x:4}   (MR3 image, runtime CSR)"),
    (REF, 100, "tREFI_effective = tREFI / fgr_factor   (counter reload value)"),
    (REF, 101, "tRFC_active = tRFC(fgr)                 (CSR per density)"),
    # the MAS ch04 anchor map names these fences as the contracts' sources
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


# ---------------------------------------------------------------------------
# LPDDR4 CA command contract (sheet 02)
# ---------------------------------------------------------------------------
LPDDR4_CA_COMMANDS = [
    ("NOP", "TBC(JESD209-4)", "None"),
    ("ACT", "TBC(JESD209-4)", "Row + bank + bank-group (DDR4-style fields carried to CA mapper)"),
    ("RD", "TBC(JESD209-4)", "Bank + column"),
    ("WR", "TBC(JESD209-4)", "Bank + column"),
    ("MPC", "TBC(JESD209-4)", "MPC opcode"),
    ("MRW", "TBC(JESD209-4)", "MR address + write data"),
    ("MRR", "TBC(JESD209-4)", "MR address"),
    ("REFab", "TBC(JESD209-4)", "None"),
    ("REFpb", "TBC(JESD209-4)", "Bank (controller-directed per-bank refresh)"),
]


def build_lpddr4_ca_commands(wb):
    km = new_kmap_sheet(wb, "LPDDR4 CA commands")
    km.sheet_intro(
        "andesite LPDDR4 CA command contract (pre-RTL, cites MAS pages)",
        ["Contract-style table: command class, 12-bit CA encoding source, and",
         "carried fields. Exact CA bit encodings are deliberately not fabricated;",
         "they are TBC at the JESD209-4 cold-storage read (HAS Q1).",
         "Verdict posture: NOT CHECKED -- no RTL exists at MAS v0.1."])
    km.table(
        "LPDDR4 CA command placeholder", f"{CMD}:143",
        ["Command", "CA encoding (12-bit, two-cycle)", "Carries"],
        LPDDR4_CA_COMMANDS,
        note=("NOP/ACT/RD/WR/MPC/MRW/MRR/REFab/REFpb are the command classes "
              "listed in the MAS placeholder fence. REFpb carries the bank; "
              "MPC carries its opcode; MRW carries MR address and data."))


def write_lpddr4_ca_command_table():
    os.makedirs(GEN, exist_ok=True)
    path = os.path.join(GEN, "02_lpddr4_ca_command_table.md")
    lines = []
    lines.append("# LPDDR4 CA Command Table (generated)")
    lines.append("")
    lines.append("Generated by `docs/kmaps/gen_andesite_kmaps.py` from the "
                 "placeholder fence in")
    lines.append("`andesite_mas/ch02_blocks/01_cmd_formatter.md` (Table 2.4). "
                 "Do not edit; rerun the generator.")
    lines.append("")
    lines.append("LPDDR4 uses a 6-bit double-data-rate CA bus, two cycles per "
                 "command, so each entry is a 12-bit symbol split across two "
                 "half-rate beats. The exact CA encodings are deliberately not "
                 "fabricated; they are pinned as `TBC(JESD209-4)` pending the "
                 "HAS Q1 cold-storage read.")
    lines.append("")
    lines.append("| Command | CA encoding (12-bit, two-cycle) | Carries |")
    lines.append("|---|---|---|")
    for cmd, enc, carries in LPDDR4_CA_COMMANDS:
        lines.append("| {} | {} | {} |".format(cmd, enc, carries))
    lines.append("")
    lines.append("Verdict posture: NOT CHECKED -- no RTL exists at MAS v0.1. "
                 "When RTL lands, the generator re-points citations at the "
                 "`.sv` lines that drive the CA mapper and this table is "
                 "replaced by the actual JESD209-4 encodings.")
    lines.append("")
    with open(path, "w") as f:
        f.write("\n".join(lines))
    return path


# ---------------------------------------------------------------------------
# Address decode maps (sheet 03)
# ---------------------------------------------------------------------------
ADDR_FIELD_ORDER = [
    ("DDR4", "CS -> BG[1:0] -> BA[1:0] -> row -> col",
     "Chip select, bank group, bank, row, column"),
    ("LPDDR4", "CS -> BA[2:0] -> row -> col",
     "Chip select, bank, row, column (no bank group -- degenerate, not special-cased)"),
]


def bg_map(*bits):
    """2-var map: (BG1, BG0) -> bank-group number 0..3."""
    bg1, bg0 = bits
    return (bg1 << 1) | bg0


def build_address_decode_maps(wb):
    km = new_kmap_sheet(wb, "Address decode maps")
    km.sheet_intro(
        "andesite address decode maps (pre-RTL, cites MAS pages)",
        ["Field-order table from the address-mapper decode fence and a 2-var",
         "K-map of the DDR4 design-point bank-group geometry.",
         "Verdict posture: NOT CHECKED -- no RTL exists at MAS v0.1."])
    km.table(
        "Field order by memtype", f"{AM}:77",
        ["Memtype", "Field order", "Note"],
        ADDR_FIELD_ORDER,
        note=("Field boundaries are runtime ADDR_MAP-style CSRs, reset to the "
              "design-point geometry. LPDDR4 has no bank group; the BG stage "
              "is degenerate, not special-cased."))
    km.kmap(
        "bg = {BG1, BG0}", f"{HAS_DP}:37",
        "bg = {BG1, BG0}   -- DDR4 design-point bank-group decode",
        [("BG1", "bank group bit 1", f"{AM}:78"),
         ("BG0", "bank group bit 0", f"{AM}:78")],
        bg_map,
        "Each cell is the bank-group number selected by (BG1, BG0); the design "
        "point is 4 bank groups x 4 banks = 16 banks.",
        values={0: "BG0", 1: "BG1", 2: "BG2", 3: "BG3"},
        depends_only_on=(
            "BG1 and BG0. The map is a slice of the DDR4 address path with "
            "memtype=DDR4; LPDDR4 has no bank group (BG width = 0)."))


def write_address_decode_maps():
    os.makedirs(GEN, exist_ok=True)
    path = os.path.join(GEN, "03_addr_decode_maps.md")
    lines = []
    lines.append("# Address Decode Maps (generated)")
    lines.append("")
    lines.append("Generated by `docs/kmaps/gen_andesite_kmaps.py` from the "
                 "decode-structure fence in")
    lines.append("`andesite_mas/ch02_blocks/04_addr_mapper.md` (Figure 2.2) "
                 "and the design-point geometry in")
    lines.append("`andesite_has/ch02_overview/04_design_point.md` (Table 2.4). "
                 "Do not edit; rerun the generator.")
    lines.append("")
    lines.append("## Field order by memtype")
    lines.append("")
    lines.append("Field boundaries are runtime `ADDR_MAP`-style CSRs, reset to "
                 "the design-point geometry.")
    lines.append("")
    lines.append("| Memtype | Field order | Note |")
    lines.append("|---|---|---|")
    for memtype, order, note in ADDR_FIELD_ORDER:
        lines.append("| {} | {} | {} |".format(memtype, order, note))
    lines.append("")
    lines.append("## DDR4 design-point bank-group decode")
    lines.append("")
    lines.append("2-var map over `(BG1, BG0)`. The design point is "
                 "`4 bank groups x 4 banks = 16 banks`.")
    lines.append("")
    lines.append("| BG1 | BG0 | Bank group |")
    lines.append("|---|---|---|")
    for bg1 in (0, 1):
        for bg0 in (0, 1):
            bg = bg_map(bg1, bg0)
            lines.append("| {} | {} | BG{} |".format(bg1, bg0, bg))
    lines.append("")
    lines.append("Verdict posture: NOT CHECKED -- no RTL exists at MAS v0.1. "
                 "When RTL lands, the generator re-points citations at the "
                 "`.sv` lines that implement the field extraction and diffs "
                 "the implementation against these maps.")
    lines.append("")
    with open(path, "w") as f:
        f.write("\n".join(lines))
    return path


# ---------------------------------------------------------------------------
# MR0-MR6 programming maps (sheet 04)
# ---------------------------------------------------------------------------
MRProgrammingRows = [
    # DDR4
    ("DDR4", "MR0", "Burst length", "Fixed 8 or on-the-fly 4/8",
     "bit map per JESD79-4 (HAS Q1)"),
    ("DDR4", "MR0", "Read burst type", "Sequential or interleaved",
     "bit map per JESD79-4 (HAS Q1)"),
    ("DDR4", "MR0", "CAS latency", "CL select",
     "bit map per JESD79-4 (HAS Q1)"),
    ("DDR4", "MR0", "DLL reset", "DLL reset bit",
     "bit map per JESD79-4 (HAS Q1)"),
    ("DDR4", "MR0", "Write recovery", "WR select",
     "bit map per JESD79-4 (HAS Q1)"),
    ("DDR4", "MR1", "DLL enable", "DLL on/off",
     "bit map per JESD79-4 (HAS Q1)"),
    ("DDR4", "MR1", "Additive latency", "AL select",
     "bit map per JESD79-4 (HAS Q1)"),
    ("DDR4", "MR1", "RTT_NOM", "Nominal termination value",
     "bit map per JESD79-4 (HAS Q1)"),
    ("DDR4", "MR1", "Write leveling", "Write-leveling enable",
     "bit map per JESD79-4 (HAS Q1)"),
    ("DDR4", "MR2", "CAS write latency", "CWL select",
     "bit map per JESD79-4 (HAS Q1)"),
    ("DDR4", "MR2", "RTT_WR", "Write termination value",
     "bit map per JESD79-4 (HAS Q1)"),
    ("DDR4", "MR2", "Write CRC mode", "Inert this edition per HAS Ch 3.1",
     "bit map per JESD79-4 (HAS Q1)"),
    ("DDR4", "MR2", "LP ASR", "Low-power auto self-refresh select",
     "bit map per JESD79-4 (HAS Q1)"),
    ("DDR4", "MR3", "MPR access/select", "MPR operation and page select",
     "bit map per JESD79-4 (HAS Q1)"),
    ("DDR4", "MR3", "FGR select", "1x / 2x / 4x refresh granularity",
     "bit map per JESD79-4 (HAS Q1)"),
    ("DDR4", "MR3", "Gear-down", "Gear-down mode",
     "bit map per JESD79-4 (HAS Q1)"),
    ("DDR4", "MR4", "Temperature status", "Temperature status",
     "bit map per JESD79-4 (HAS Q1)"),
    ("DDR4", "MR4", "Preamble", "Preamble mode",
     "bit map per JESD79-4 (HAS Q1)"),
    ("DDR4", "MR4", "CAL", "Command address latency",
     "bit map per JESD79-4 (HAS Q1)"),
    ("DDR4", "MR5", "RD DBI", "Read DBI enable",
     "bit map per JESD79-4 (HAS Q1)"),
    ("DDR4", "MR5", "WR DBI", "Write DBI enable",
     "bit map per JESD79-4 (HAS Q1)"),
    ("DDR4", "MR5", "RTT_PARK", "Idle termination value",
     "bit map per JESD79-4 (HAS Q1)"),
    ("DDR4", "MR5", "CA parity", "CA parity latency/mode",
     "bit map per JESD79-4 (HAS Q1)"),
    ("DDR4", "MR6", "VrefDQ", "VrefDQ training range and value",
     "bit map per JESD79-4 (HAS Q1)"),
    # LPDDR4
    ("LPDDR4", "MRW set", "ODT/DQ-ODT", "Termination programming",
     "bit map per JESD209-4 (HAS Q1)"),
    ("LPDDR4", "MRW set", "Drive strength", "Output driver impedance",
     "bit map per JESD209-4 (HAS Q1)"),
    ("LPDDR4", "MRW set", "CA training patterns", "CA training patterns",
     "bit map per JESD209-4 (HAS Q1)"),
    ("LPDDR4", "MRW set", "Refresh-related", "Refresh mode bits",
     "bit map per JESD209-4 (HAS Q1)"),
    ("LPDDR4", "MRW set", "Vendor area", "Vendor-specific MR space",
     "bit map per JESD209-4 (HAS Q1)"),
]


def build_mr_programming_maps(wb):
    km = new_kmap_sheet(wb, "MR0-MR6 programming maps")
    km.sheet_intro(
        "andesite MR0-MR6 / LPDDR4 MRW programming maps (pre-RTL)",
        ["Per-memtype mode-register semantics. Bit positions are named, not",
         "numbered; the exact bit maps are confirmed at the JESD79-4 /",
         "JESD209-4 cold-storage read (HAS Q1).",
         "Verdict posture: NOT CHECKED -- no RTL exists at MAS v0.1."])
    km.table(
        "MR programming map", f"{MR}:83",
        ["Memtype", "MR", "Field", "Function", "Values/notes"],
        MRProgrammingRows,
        note=("DDR4 MR0-MR6 are MRS-programmed; LPDDR4 MRs are MRW-programmed "
              "over the 6-bit CA bus and read back by MRR."))


def write_mr_programming_maps():
    os.makedirs(GEN, exist_ok=True)
    path = os.path.join(GEN, "04_mr_programming_maps.md")
    lines = []
    lines.append("# MR0-MR6 / LPDDR4 MRW Programming Maps (generated)")
    lines.append("")
    lines.append("Generated by `docs/kmaps/gen_andesite_kmaps.py` from the "
                 "mode-register semantics table in")
    lines.append("`andesite_mas/ch02_blocks/03_mode_register.md` (Table 2.7). "
                 "Do not edit; rerun the generator.")
    lines.append("")
    lines.append("Bit positions are intentionally named, not numbered; the "
                 "exact bit maps are confirmed at the JESD79-4 / JESD209-4 "
                 "cold-storage read (HAS Q1).")
    lines.append("")
    lines.append("| Memtype | MR | Field | Function | Values/notes |")
    lines.append("|---|---|---|---|---|")
    for memtype, mr, field, func, vals in MRProgrammingRows:
        lines.append("| {} | {} | {} | {} | {} |".format(
            memtype, mr, field, func, vals))
    lines.append("")
    lines.append("Verdict posture: NOT CHECKED -- no RTL exists at MAS v0.1. "
                 "When RTL lands, the generator re-points citations at the "
                 "`.sv` lines that hold the MR images and diffs the field "
                 "fanout against this map.")
    lines.append("")
    with open(path, "w") as f:
        f.write("\n".join(lines))
    return path


# ---------------------------------------------------------------------------
# ODT truth table (sheet 05)
# ---------------------------------------------------------------------------
ODT_VALUES = {
    "PARK": "RTT_PARK",
    "NOM": "RTT_NOM",
    "OFF": "ODT off",
    "WR": "RTT_WR",
}


def odt_policy(*bits):
    """Multi-valued ODT policy: bits = (access[1], access[0], self).

    access encoding: 00=idle, 01=read, 10=write.
    self: 1 = command targets this rank, 0 = other rank.
    """
    access = (bits[0] << 1) | bits[1]
    self = bits[2]
    if access == 0:
        return "PARK"
    if access == 1:       # read
        return "OFF" if self else "NOM"
    if access == 2:       # write
        return "WR" if self else "NOM"
    return "PARK"         # 11: illegal access encoding, clamp to PARK


def build_odt_truth_table(wb):
    km = new_kmap_sheet(wb, "ODT truth table")
    km.sheet_intro(
        "andesite ODT termination policy (pre-RTL, cites MAS pages)",
        ["Multi-valued K-map over access type and self/other rank. Mirrors the",
         "policy-state fence in the MAS ODT controller page.",
         "Verdict posture: NOT CHECKED -- no RTL exists at MAS v0.1."])
    km.kmap(
        "rtt = odt_policy(access[1:0], self)", f"{ODT}:88",
        "rtt = odt_policy(access[1:0], self)",
        [("access[1]", "MSB of access encoding", f"{ODT}:88"),
         ("access[0]", "LSB of access encoding", f"{ODT}:88"),
         ("self", "command targets this rank", f"{ODT}:88")],
        odt_policy,
        "IDLE/illegal -> RTT_PARK; read to other rank -> RTT_NOM; read to self "
        "-> ODT off; write to self -> RTT_WR; write to other -> RTT_NOM.",
        values=ODT_VALUES,
        depends_only_on=(
            "access[1:0] (idle/read/write) and self. The policy is per-rank; "
            "NUM_RANKS > 1 is held in the surrounding structure. Illegal access "
            "encoding 11 clamps to PARK."))


def write_odt_truth_table():
    os.makedirs(GEN, exist_ok=True)
    path = os.path.join(GEN, "05_odt_truth_table.md")
    lines = []
    lines.append("# ODT Truth Table (generated)")
    lines.append("")
    lines.append("Generated by `docs/kmaps/gen_andesite_kmaps.py` from the "
                 "policy-state fence in")
    lines.append("`andesite_mas/ch02_blocks/08_odt_ctrl.md`. Do not edit; rerun "
                 "the generator.")
    lines.append("")
    lines.append("Termination is per-rank. `access` encodes the granted command "
                 "type: `00` = idle, `01` = read, `10` = write. `self` is 1 "
                 "when the command targets the rank whose ODT is being decided.")
    lines.append("")
    lines.append("| access[1] | access[0] | self | RTT selection |")
    lines.append("|---|---|---|---|")
    for a1 in (0, 1):
        for a0 in (0, 1):
            for self_ in (0, 1):
                sel = ODT_VALUES[odt_policy(a1, a0, self_)]
                access = ((a1 << 1) | a0)
                desc = {0: "idle", 1: "read", 2: "write", 3: "illegal"}[access]
                if access == 3:
                    desc = "illegal (clamp to PARK)"
                lines.append("| {} | {} | {} | {} |".format(
                    a1, a0, self_, sel))
    lines.append("")
    lines.append("The MAS policy states are: IDLE -> RTT_PARK; RD (other) -> "
                 "RTT_NOM; WR (self) -> RTT_WR. The read-to-self and "
                 "write-to-other cases follow from per-rank dynamic ODT: the "
                 "accessed rank turns ODT off during reads, and non-accessed "
                 "ranks present RTT_NOM during writes.")
    lines.append("")
    lines.append("Verdict posture: NOT CHECKED -- no RTL exists at MAS v0.1. "
                 "When RTL lands, the generator re-points citations at the "
                 "`.sv` lines that implement the policy state machine and diffs "
                 "the RTT selection against this table.")
    lines.append("")
    with open(path, "w") as f:
        f.write("\n".join(lines))
    return path


# ---------------------------------------------------------------------------
# FGR refresh select (sheet 06)
# ---------------------------------------------------------------------------
FGR_ROWS = [
    ("1x", "1", "tREFI / 1", "tRFC(1x)"),
    ("2x", "2", "tREFI / 2", "tRFC(2x)"),
    ("4x", "4", "tREFI / 4", "tRFC(4x)"),
    ("illegal encoding", "clamp", "clamped to 1x (tREFI / 1)", "tRFC(1x)"),
]


def build_fgr_refresh_map(wb):
    km = new_kmap_sheet(wb, "FGR refresh select")
    km.sheet_intro(
        "andesite FGR refresh select (pre-RTL, cites MAS pages)",
        ["FGR factor from the MR3 image to effective tREFI reload and tRFC",
         "selection. Mirrors the interval-arithmetic fence in the MAS refresh",
         "controller page.",
         "Verdict posture: NOT CHECKED -- no RTL exists at MAS v0.1."])
    km.table(
        "FGR refresh select", f"{REF}:99",
        ["FGR select (MR3 image)", "Factor", "tREFI reload", "tRFC select"],
        FGR_ROWS,
        note=("The credit-window ceiling (+-8) is unchanged; bookkeeping tracks "
              "effective refreshes, not raw commands. Illegal encodings clamp "
              "to the 1x row per the MAS/HAS note."))


def write_fgr_refresh_map():
    os.makedirs(GEN, exist_ok=True)
    path = os.path.join(GEN, "06_fgr_refresh_map.md")
    lines = []
    lines.append("# FGR Refresh Select (generated)")
    lines.append("")
    lines.append("Generated by `docs/kmaps/gen_andesite_kmaps.py` from the "
                 "interval-arithmetic fence in")
    lines.append("`andesite_mas/ch02_blocks/06_refresh_ctrl.md`. Do not edit; "
                 "rerun the generator.")
    lines.append("")
    lines.append("DDR4 MR3 selects 1x, 2x, or 4x refresh granularity. The "
                 "controller scales its interval arithmetic by the FGR factor "
                 "and selects the matching tRFC CSR.")
    lines.append("")
    lines.append("| FGR select (MR3 image) | Factor | tREFI reload | tRFC select |")
    lines.append("|---|---|---|---|")
    for sel, factor, trefi, trfc in FGR_ROWS:
        lines.append("| {} | {} | {} | {} |".format(sel, factor, trefi, trfc))
    lines.append("")
    lines.append("Timing values are named, not numbered; the exact values are "
                 "runtime CSRs derived from the JESD79-4 speed bin at "
                 "CSR-derivation time (HAS Ch 5; numeric constants are HAS open "
                 "question Q1).")
    lines.append("")
    lines.append("Verdict posture: NOT CHECKED -- no RTL exists at MAS v0.1. "
                 "When RTL lands, the generator re-points citations at the "
                 "`.sv` lines that implement the interval counter and diffs "
                 "the reload/select logic against this map.")
    lines.append("")
    with open(path, "w") as f:
        f.write("\n".join(lines))
    return path


# ---------------------------------------------------------------------------
# DDR4 command decode (sheet 01)
# ---------------------------------------------------------------------------
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


def write_ddr4_command_table():
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


# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------
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
    build_lpddr4_ca_commands(wb)
    build_address_decode_maps(wb)
    build_mr_programming_maps(wb)
    build_odt_truth_table(wb)
    build_fgr_refresh_map(wb)

    paths = []
    paths.append(write_ddr4_command_table())
    paths.append(write_lpddr4_ca_command_table())
    paths.append(write_address_decode_maps())
    paths.append(write_mr_programming_maps())
    paths.append(write_odt_truth_table())
    paths.append(write_fgr_refresh_map())

    wb.save(XLSX)
    _normalize_xlsx_timestamps(XLSX)
    print(f"wrote {XLSX}")
    for name in wb.sheetnames:
        print("  ", name)
    for p in paths:
        print(f"wrote {p}")


if __name__ == "__main__":
    main()
