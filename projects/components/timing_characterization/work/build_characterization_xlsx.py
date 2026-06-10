#!/usr/bin/env python3
"""Build asap7_characterization.xlsx — the design-time prediction table.

Reads /tmp/charwork/asap7/timing_char_data.csv (two-point synth probes per
primitive per corner) and derives:

  - Tflop[corner]            = Tcq + Tsu, the flop-to-flop overhead
                               (derived from NAND chain, the cleanest probe)
  - per_level[gate, corner]  = average std-cell delay per logic level
                               for that primitive in that corner

Then for each (corner, freq) combination:

      max_levels[gate, corner, freq] = floor((period - Tflop) / per_level)

Writes a single sheet `characterization` with columns of corner_freq
permutations and rows that match the methodology table (Tcq+Tsu, max levels
per gate type, per-level gate delay).
"""
from __future__ import annotations
import csv
import math
from pathlib import Path
from openpyxl import Workbook
from openpyxl.styles import Font, PatternFill, Alignment, Border, Side
from openpyxl.utils import get_column_letter

CSV_IN  = Path("/tmp/charwork/asap7/timing_char_data.csv")
OUT     = Path("/mnt/data/github/RTLDesignSherpa/projects/components/timing_characterization/work/asap7_characterization.xlsx")

CORNERS = ["TT", "FF", "SS"]
FREQS   = [500, 750, 1000]  # MHz

# Primitives used for the per-level lookup. INV is excluded — ABC collapses
# inverter pairs, so the chain depth is not preserved across the optimization
# pass and the two-point probe doesn't yield a meaningful slope.
GATE_PRIMS  = ["NAND", "XOR", "MUX"]
TFLOP_PROBE = "NAND"  # canonical probe for Tcq+Tsu (smallest, most uniform map)

# ---------------------------------------------------------------------------- #
HDR_FONT = Font(bold=True, color="FFFFFF")
HDR_FILL = PatternFill("solid", fgColor="1F4E78")
SECTION_FONT = Font(bold=True)
SECTION_FILL = PatternFill("solid", fgColor="D9E1F2")
NUM_FONT = Font()
CENTER = Alignment(horizontal="center")
THIN = Side(border_style="thin", color="A0A0A0")
BOX = Border(top=THIN, bottom=THIN, left=THIN, right=THIN)


def read_probes() -> dict:
    """Return {(prim, corner): [(value, delay_ps, lev), ...]}."""
    probes: dict = {}
    with CSV_IN.open() as f:
        for r in csv.DictReader(f):
            if r["status"] != "OK":
                continue
            k = (r["primitive"], r["corner"])
            probes.setdefault(k, []).append(
                (int(r["value"]), float(r["delay_ps"]), int(r["lev"])))
    return probes


def derive(probes: dict) -> tuple[dict, dict]:
    """Return (per_level, tflop) keyed by (gate, corner) and corner."""
    per_level: dict = {}
    tflop: dict = {}
    for prim in GATE_PRIMS:
        for corner in CORNERS:
            ps = probes.get((prim, corner))
            if not ps or len(ps) < 2:
                continue
            ps_sorted = sorted(ps, key=lambda x: x[0])
            (v1, d1, lev1), (v2, d2, lev2) = ps_sorted[0], ps_sorted[-1]
            if lev2 == lev1:
                continue
            per_lv = (d2 - d1) / (lev2 - lev1)
            per_level[(prim, corner)] = per_lv
            if prim == TFLOP_PROBE:
                tflop[corner] = d1 - lev1 * per_lv
    return per_level, tflop


def build_sheet(wb: Workbook, per_level: dict, tflop: dict):
    ws = wb.active
    ws.title = "characterization"

    # Column layout: row label | TT_500 | TT_750 | TT_1000 | FF_500 | ... | SS_1000
    col_headers = ["metric"] + [f"{c}_{f}MHz" for c in CORNERS for f in FREQS]
    ws.append(col_headers)
    for c in range(1, len(col_headers) + 1):
        cell = ws.cell(row=1, column=c)
        cell.font = HDR_FONT
        cell.fill = HDR_FILL
        cell.alignment = CENTER
        cell.border = BOX

    # Reference: period per freq column
    row = ["Period (ps)"]
    for corner in CORNERS:
        for f in FREQS:
            row.append(round(1_000_000 / f, 1))
    ws.append(row)

    # Tflop per corner — same value across freq columns within a corner
    row = ["Clock-to-Out (Tcq + Tsu, ps)"]
    for corner in CORNERS:
        v = tflop.get(corner, 0)
        for _ in FREQS:
            row.append(round(v, 2))
    ws.append(row)

    # Blank visual separator
    ws.append([""] * len(col_headers))

    # Per-gate-type max-level rows
    section_header_row(ws, "Max combinational levels per cycle", len(col_headers))
    for gate in GATE_PRIMS:
        row = [f"Max {gate} levels"]
        for corner in CORNERS:
            per_lv = per_level.get((gate, corner), 0)
            tf = tflop.get(corner, 0)
            for f in FREQS:
                period = 1_000_000 / f
                budget = period - tf
                if per_lv > 0 and budget > 0:
                    row.append(math.floor(budget / per_lv))
                else:
                    row.append("")
        ws.append(row)

    ws.append([""] * len(col_headers))

    # Per-level delay table (constants per corner)
    section_header_row(ws, "Per-level gate delay (ps)  - freq-independent", len(col_headers))
    for gate in GATE_PRIMS:
        row = [f"per {gate} delay (ps)"]
        for corner in CORNERS:
            v = per_level.get((gate, corner), 0)
            for _ in FREQS:
                row.append(round(v, 2))
        ws.append(row)

    # Notes
    ws.append([""] * len(col_headers))
    ws.append(["Notes"])
    ws.cell(row=ws.max_row, column=1).font = SECTION_FONT
    notes = [
        "Probe corner_freq columns are independent measurements (see Per-level "
        "table above).",
        f"Tflop = Tcq + Tsu derived from {TFLOP_PROBE} chain two-point probe "
        "(LEVELS={3,6}).",
        "max_levels = floor((period_ps - Tflop) / per_level_delay).",
        "INV chain omitted: ABC's strash collapses inverter pairs, so the chain "
        "depth is not preserved through optimization and the two-point probe is "
        "degenerate (delta_D = 0). Use NAND or MUX as the buffer-cost proxy.",
        "Raw probe data is in work/timing_char_data.csv. Reproducer is "
        "work/timing_char_sweep.py.",
    ]
    for n in notes:
        ws.append([n])

    # Column widths
    ws.column_dimensions["A"].width = 38
    for c in range(2, len(col_headers) + 1):
        ws.column_dimensions[get_column_letter(c)].width = 12

    # Style data cells
    for row_cells in ws.iter_rows(min_row=2):
        for cell in row_cells:
            if cell.column > 1 and isinstance(cell.value, (int, float)):
                cell.alignment = CENTER


def section_header_row(ws, text, n_cols):
    ws.append([text] + [""] * (n_cols - 1))
    r = ws.max_row
    ws.cell(row=r, column=1).font = SECTION_FONT
    ws.cell(row=r, column=1).fill = SECTION_FILL


def main():
    probes = read_probes()
    per_level, tflop = derive(probes)
    wb = Workbook()
    build_sheet(wb, per_level, tflop)
    OUT.parent.mkdir(parents=True, exist_ok=True)
    wb.save(OUT)
    print(f"wrote {OUT}")
    print(f"  Tflop: {tflop}")
    print(f"  per-level (TT only): "
          f"{ {g: round(per_level.get((g, 'TT'), 0), 2) for g in GATE_PRIMS} }")


if __name__ == "__main__":
    main()
