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

# Primitives used for the per-level lookup, in display order.
# - NAND/XOR/MUX: the most useful gates (clean two-point slope, simple to reason about)
# - CARRY/MULT/GRAY_CTR/QUEUE: scale cleanly with their probe param
# - MULT is the RECOMMENDED PROXY for "mixed-bag" combinational logic - a real
#   multiplier tree contains AND, XOR, full adder, and carry cells, so its per-
#   level delay is a sensible blended estimate for generic combinational stuff.
# - INV and CLK_DIV are listed in 'Reference single-point measurements' but
#   excluded from the per-level / max-levels tables because their lev count does
#   not change between the two probe sizes (INV: ABC collapses pairs;
#   CLK_DIV: critical path is intra-stage, not depth-scaled by NUM_STAGES).
GATE_PRIMS         = ["NAND", "XOR", "MUX", "CARRY", "MULT", "GRAY_CTR", "QUEUE"]
DEGENERATE_PRIMS   = ["INV", "CLK_DIV"]
TFLOP_PROBE        = "NAND"
MIXED_PROXY        = "MULT"  # highlight this row as the generic-mixed-logic proxy

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


def derive(probes: dict) -> tuple[dict, dict, dict]:
    """Return (per_level, tflop, single_point_d) keyed by (gate, corner)/corner."""
    per_level: dict = {}
    tflop: dict = {}
    single_pt: dict = {}  # smallest-size delay for degenerate-slope prims
    all_prims = GATE_PRIMS + DEGENERATE_PRIMS
    for prim in all_prims:
        for corner in CORNERS:
            ps = probes.get((prim, corner))
            if not ps:
                continue
            ps_sorted = sorted(ps, key=lambda x: x[0])
            (_v1, d1, lev1) = ps_sorted[0]
            single_pt[(prim, corner)] = (d1, lev1)
            if len(ps) < 2:
                continue
            (_v2, d2, lev2) = ps_sorted[-1]
            if lev2 == lev1:
                continue  # degenerate slope (INV pairs, CLK_DIV intra-stage)
            per_lv = (d2 - d1) / (lev2 - lev1)
            per_level[(prim, corner)] = per_lv
            if prim == TFLOP_PROBE:
                tflop[corner] = d1 - lev1 * per_lv
    return per_level, tflop, single_pt


def build_sheet(wb: Workbook, per_level: dict, tflop: dict, single_pt: dict):
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
        label = f"Max {gate} levels"
        if gate == MIXED_PROXY:
            label += "  (PROXY for mixed-bag logic)"
        row = [label]
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
        # Highlight the MULT row to visually call it out as the mixed-bag proxy
        if gate == MIXED_PROXY:
            for c in range(1, len(col_headers) + 1):
                ws.cell(row=ws.max_row, column=c).fill = PatternFill(
                    "solid", fgColor="FFF2CC")

    ws.append([""] * len(col_headers))

    # Per-level delay table (constants per corner)
    section_header_row(ws, "Per-level gate delay (ps)  - freq-independent", len(col_headers))
    for gate in GATE_PRIMS:
        label = f"per {gate} delay (ps)"
        if gate == MIXED_PROXY:
            label += "  (PROXY)"
        row = [label]
        for corner in CORNERS:
            v = per_level.get((gate, corner), 0)
            for _ in FREQS:
                row.append(round(v, 2))
        ws.append(row)
        if gate == MIXED_PROXY:
            for c in range(1, len(col_headers) + 1):
                ws.cell(row=ws.max_row, column=c).fill = PatternFill(
                    "solid", fgColor="FFF2CC")

    # Reference single-point measurements for degenerate-slope primitives
    ws.append([""] * len(col_headers))
    section_header_row(
        ws,
        "Reference single-point delays (ps) - degenerate slope, no per-level number",
        len(col_headers))
    for gate in DEGENERATE_PRIMS:
        row = [f"{gate} flop-to-flop delay (ps)"]
        for corner in CORNERS:
            d, _lev = single_pt.get((gate, corner), (0, 0))
            for _ in FREQS:
                row.append(round(d, 2))
        ws.append(row)

    # ---------------------------------------------------------------------- #
    # Wire delay per mm by metal layer.  ASAP7 NLDM has no wire_load table, so
    # ABC reports WireLoad = "none" on every gate-delay run above.  These are
    # 7nm industry rules-of-thumb for *buffered* routes:
    #   M2/M3   intermediate, used for short FUB-internal nets
    #   M4/M5   semi-global, used for FUB-to-FUB inside a partition
    #   M6/M7   global, used for partition-to-partition
    #   M8/M9   thick, clock/power/bus
    # Corner scaling: FF ~ 0.80 x TT, SS ~ 1.30 x TT (R rises with temp).
    # Numbers are freq-independent (distance-based), repeated across freq cols
    # to keep the sheet shape uniform.
    # ---------------------------------------------------------------------- #
    WIRE_PS_PER_MM_TT = {
        "M2/M3 (local / intermediate)": 120.0,
        "M4/M5 (semi-global)":          65.0,
        "M6/M7 (global)":               40.0,
        "M8/M9 (thick)":                22.0,
    }
    CORNER_WIRE_SCALE = {"TT": 1.0, "FF": 0.8, "SS": 1.3}

    ws.append([""] * len(col_headers))
    section_header_row(
        ws,
        "Wire delay per mm by metal layer (buffered route, ps/mm) - "
        "cross-partition route estimate",
        len(col_headers))
    for layer, tt_val in WIRE_PS_PER_MM_TT.items():
        row = [layer]
        for corner in CORNERS:
            v = tt_val * CORNER_WIRE_SCALE[corner]
            for _ in FREQS:
                row.append(round(v, 1))
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
        f"** When the critical path is a mixed bag of cells (typical for "
        f"datapath / FSM next-state / arbitration logic), use the {MIXED_PROXY} "
        f"per-level number. It bakes in AND / XOR / full-adder / carry mix.",
        "INV: ABC's strash collapses inverter pairs across the chain, so lev "
        "doesn't change between probe sizes - per-level slope is degenerate. "
        "Single-point delay is reported in the reference table.",
        "CLK_DIV: critical path is intra-stage (counter + pickoff), so NUM_STAGES "
        "doesn't move lev. Single-point delay is reported in the reference table.",
        "Wire delays are 7nm industry rule-of-thumb for buffered routes; the "
        "ASAP7 NLDM ships no wire_load table so ABC measured gate delay only. "
        "For partition-to-partition output budgeting, look up the destination "
        "metal layer and multiply by route length (mm).",
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


def build_blocks_sheet(wb: Workbook):
    """Per-block structural estimator that scales from the characterization sheet.

    Each block is one row. Cells B..G are editable params (highlighted yellow).
    Flop count / NAND-equivalent gate count / data-to-D combinational delay
    are formulas that scale automatically when the user edits the params.

    Cell refs into 'characterization':
      Tflop per corner:  $D$3 (TT)  $G$3 (FF)  $J$3 (SS)
      per NAND delay:    $D$11 (TT) $G$11 (FF) $J$11 (SS)
      per MUX  delay:    $D$13 (TT) $G$13 (FF) $J$13 (SS)
    """
    ws = wb.create_sheet("building blocks")
    PARAM_FILL = PatternFill("solid", fgColor="FFF2CC")  # yellow = editable
    FORMULA_FILL = PatternFill("solid", fgColor="E7E6E6")  # grey = computed

    header = [
        "block",
        "P1", "P2", "P3", "P4", "P5", "P6",       # editable params (B..G)
        "params",                                  # H = labels for the row
        "flop_count",                              # I
        "NAND_eq_gates",                           # J
        "MUX_levels",                              # K  (critical data->D path)
        "NAND_levels",                             # L
        "data->D TT (ps)", "data->D FF (ps)", "data->D SS (ps)",   # M, N, O
        "fmax TT (MHz)",   "fmax FF (MHz)",   "fmax SS (MHz)",     # P, Q, R
        "notes",                                   # S
    ]
    ws.append(header)
    for c in range(1, len(header) + 1):
        cell = ws.cell(row=1, column=c)
        cell.font = HDR_FONT
        cell.fill = HDR_FILL
        cell.alignment = CENTER
        cell.border = BOX

    # ----------------------------------------------------------------------- #
    # Block definitions
    #   params: tuple of (label, base_value) — written to B..G in order
    #   flops:  Excel formula using {R} as the current row index for self-refs
    #   nand:   Excel formula for NAND-equivalent combinational gates
    #   mux_lv: Excel formula or literal int — MUX levels on data->D path
    #   nand_lv: Excel formula or literal int — NAND levels on data->D path
    #   notes:  string
    # ----------------------------------------------------------------------- #
    BLOCKS = [
        dict(
            name="gaxi_skid_buffer",
            params=[("W", 1), ("D", 2)],
            flops="=B{R}*C{R} + C{R} + 2",
            nand="=B{R}*C{R}*4 + 10",
            mux_lv=1,
            nand_lv=1,
            notes="data->D path is the bypass MUX2 (1 level). "
                  "Flops = W*D storage + D valid + 2 control.",
        ),
        dict(
            name="gaxi_fifo_sync (REG=0)",
            params=[("W", 1), ("D", 2)],
            flops="=B{R}*C{R} + 3*CEILING(LOG(C{R},2),1) + 1",
            nand="=B{R}*C{R}*6 + CEILING(LOG(C{R},2),1)*8 + 20",
            mux_lv="=CEILING(LOG(C{R},2),1)",      # read mux depth (output side)
            nand_lv=2,                              # full/empty cmp
            notes="Critical path is the READ mux tree, depth=log2(D). "
                  "Flops = W*D storage + 3*log2(D) ptrs/count + 1 state.",
        ),
        dict(
            name="gaxi_fifo_sync (REG=1)",
            params=[("W", 1), ("D", 2)],
            flops="=B{R}*C{R} + 3*CEILING(LOG(C{R},2),1) + B{R} + 1",
            nand="=B{R}*C{R}*6 + CEILING(LOG(C{R},2),1)*8 + 20",
            mux_lv=0,                               # output reg hides the mux
            nand_lv=1,                              # just downstream handshake AND
            notes="REGISTERED=1 adds an output flop bank (W flops); "
                  "the read mux is hidden behind it so data->D shrinks to ~1 NAND.",
        ),
        dict(
            name="arbiter_round_robin",
            params=[("N", 2)],
            flops="=B{R} + 2",
            nand="=B{R}*8",
            mux_lv="=CEILING(LOG(B{R},2),1)",
            nand_lv=1,
            notes="Priority encoder is log2(N) MUX levels. "
                  "Flops = N (last-grant tracker) + 2 (state).",
        ),
        dict(
            name="axi4_master_rd",
            params=[("AW", 32), ("DW", 32), ("IW", 4), ("UW", 1),
                    ("SKID_AR", 2), ("SKID_R", 2)],
            # AR slot width = AW+IW+UW+29 (per axi4_master_rd ARSize formula);
            # R slot width  = IW+DW+UW+3 (per RSize).
            flops="=F{R}*(B{R}+D{R}+E{R}+29) + G{R}*(D{R}+C{R}+E{R}+3)",
            nand="=4*(F{R}*(B{R}+D{R}+E{R}+29) + G{R}*(D{R}+C{R}+E{R}+3))",
            mux_lv=1,
            nand_lv=1,
            notes="Two skid buffers in series (AR + R). data->D path is the "
                  "skid bypass MUX. Flops scale with SKID_AR*ARw + SKID_R*Rw.",
        ),
        dict(
            name="axi4_master_wr",
            params=[("AW", 32), ("DW", 32), ("IW", 4), ("UW", 1),
                    ("SKID_AW", 2), ("SKID_W", 2)],
            # AW slot width = AW+IW+UW+29; W slot width = DW + DW/8 + UW + 1;
            # B slot width = IW + UW + 2.  Assume SKID_B=2 for the constant.
            flops="=F{R}*(B{R}+D{R}+E{R}+29) + G{R}*(C{R}+C{R}/8+E{R}+1) + 2*(D{R}+E{R}+2)",
            nand="=4*(F{R}*(B{R}+D{R}+E{R}+29) + G{R}*(C{R}+C{R}/8+E{R}+1) + 2*(D{R}+E{R}+2))",
            mux_lv=1,
            nand_lv=1,
            notes="Three skid buffers (AW + W + B); SKID_B fixed at 2 in this row. "
                  "data->D path is the skid bypass MUX.",
        ),
    ]

    # Characterization cell refs (per_NAND / per_MUX / Tflop, by corner)
    REFS = {
        "TT": {"nand": "$D$11", "mux": "$D$13", "tflop": "$D$3"},
        "FF": {"nand": "$G$11", "mux": "$G$13", "tflop": "$G$3"},
        "SS": {"nand": "$J$11", "mux": "$J$13", "tflop": "$J$3"},
    }

    for b in BLOCKS:
        r = ws.max_row + 1  # current target row
        params = b["params"]
        # Block name (col A)
        ws.cell(row=r, column=1, value=b["name"]).font = SECTION_FONT
        # Params P1..P6 (cols B..G)
        for i, (_lbl, v) in enumerate(params):
            cell = ws.cell(row=r, column=2 + i, value=v)
            cell.fill = PARAM_FILL
            cell.alignment = CENTER
        # Param-label string (col H)
        ws.cell(row=r, column=8,
                value=", ".join(f"P{i+1}={lbl}" for i, (lbl, _) in enumerate(params)))
        # Formulas — use .format(R=r) to splice the row index
        ws.cell(row=r, column=9,  value=b["flops"].format(R=r))      # I flops
        ws.cell(row=r, column=10, value=b["nand"].format(R=r))       # J NAND eq
        # MUX / NAND level counts can be literal int or formula string
        for col, key in ((11, "mux_lv"), (12, "nand_lv")):
            v = b[key]
            if isinstance(v, str):
                v = v.format(R=r)
            ws.cell(row=r, column=col, value=v)
        # data->D combo delay per corner (cols M, N, O)
        for off, corner in enumerate(("TT", "FF", "SS")):
            ref = REFS[corner]
            f = (f"=K{r}*characterization!{ref['mux']} "
                 f"+ L{r}*characterization!{ref['nand']}")
            cell = ws.cell(row=r, column=13 + off, value=f)
            cell.alignment = CENTER
            cell.fill = FORMULA_FILL
        # fmax per corner (cols P, Q, R)  = 1e6 / (combo + Tflop)
        for off, corner in enumerate(("TT", "FF", "SS")):
            ref = REFS[corner]
            combo_col = chr(ord("M") + off)  # M, N, O
            f = f"=ROUND(1000000/({combo_col}{r} + characterization!{ref['tflop']}), 0)"
            cell = ws.cell(row=r, column=16 + off, value=f)
            cell.alignment = CENTER
            cell.fill = FORMULA_FILL
        # Notes (col S)
        ws.cell(row=r, column=19, value=b["notes"])

    # Column widths
    widths = {1: 26, 8: 38, 9: 11, 10: 13, 11: 7, 12: 8,
              13: 16, 14: 16, 15: 16, 16: 13, 17: 13, 18: 13, 19: 60}
    for c in range(2, 8):
        widths.setdefault(c, 8)
    for c, w in widths.items():
        ws.column_dimensions[get_column_letter(c)].width = w

    # Legend
    legend_row = ws.max_row + 2
    ws.cell(row=legend_row, column=1, value="Cell coding").font = SECTION_FONT
    ws.cell(row=legend_row + 1, column=1, value="Yellow = editable param").fill = PARAM_FILL
    ws.cell(row=legend_row + 2, column=1, value="Grey = derived formula").fill = FORMULA_FILL
    ws.cell(row=legend_row + 4, column=1, value=(
        "data->D = critical combinational delay on the path that loads the "
        "downstream flop. Compare against (period - Tflop) to size for a freq."
    ))
    ws.cell(row=legend_row + 5, column=1, value=(
        "Estimates are first-order: structural flop/gate counts + characterization "
        "per-level delays. Treat them as design-time SWAGs, not post-synth truth."
    ))


def build_stream_sheet(wb: Workbook):
    """Per-input signal-path trace for a small STREAM FUB.

    Walked stream_latency_bridge.sv by hand. Each non-clock/reset input is
    traced through the local combinational network until it either:
      - terminates at a flop's D pin (r_drain_ip), OR
      - terminates at an output port, OR
      - enters a building block (gaxi_fifo_sync u_skid_buffer); the BB row in
        the 'building blocks' sheet covers the cost from that boundary inward.

    Local NAND depth/count = combinational gate-equivalents traversed in this
    FUB only. Local delay = depth * per_NAND[corner] (from characterization).
    """
    ws = wb.create_sheet("stream")

    header = [
        "FUB", "input signal", "building block crossed",
        "local NAND depth", "local NAND count",
        "terminator (flop / output / BB port)",
        "local delay TT (ps)", "local delay FF (ps)", "local delay SS (ps)",
        "notes",
    ]
    ws.append(header)
    for c in range(1, len(header) + 1):
        cell = ws.cell(row=1, column=c)
        cell.font = HDR_FONT
        cell.fill = HDR_FILL
        cell.alignment = CENTER
        cell.border = BOX

    # Path trace of stream_latency_bridge (rtl/fub/stream_latency_bridge.sv)
    # Logic from lines 100-194 of the SV. Each row = one (input, end-point) pair.
    FUB = "stream_latency_bridge"
    rows = [
        # input        bb_crossed                  depth count terminator                                          notes
        ("s_valid",    "",                          1,    1,   "r_drain_ip (flop D)",
         "s_valid AND s_ready -> w_drain_fifo -> flop D"),
        ("s_data[DW-1:0]", "gaxi_fifo_sync",        0,    0,   "u_skid_buffer.wr_data",
         "direct wire to FIFO write port; cost inside BB row"),
        ("m_ready (path 1)", "",                    2,    2,   "s_ready (output port)",
         "m_ready AND m_valid -> w_draining_now -> OR w_room_available -> s_ready"),
        ("m_ready (path 2)", "gaxi_fifo_sync",      0,    0,   "u_skid_buffer.rd_ready",
         "direct wire to FIFO read port"),
        # Internal flop outputs that fan to outputs/BB
        ("r_drain_ip (Q)", "",                      0,    0,   "u_skid_buffer.wr_valid",
         "skid_wr_valid = r_drain_ip; pure wire"),
        ("r_drain_ip (Q)", "",                      0,    0,   "dbg_r_pending (output)",
         "dbg_r_pending = r_drain_ip; pure wire"),
        # FIFO outputs back through this FUB to the boundary
        ("u_skid_buffer.rd_valid", "gaxi_fifo_sync", 0,   0,   "m_valid (output)",
         "wire from FIFO rd_valid; m_valid = u_skid_buffer.rd_valid"),
        ("u_skid_buffer.rd_data",  "gaxi_fifo_sync", 0,   0,   "m_data[DW-1:0] (output)",
         "wire from FIFO rd_data"),
        ("u_skid_buffer.count",    "gaxi_fifo_sync", 3,   6,   "s_ready (output port)",
         "skid_count + write_stalled (3b adder) -> magnitude cmp < SKID_DEPTH -> OR -> s_ready"),
        ("u_skid_buffer.count",    "gaxi_fifo_sync", 0,   0,   "occupancy[2:0] (output)",
         "occupancy = skid_count; direct wire"),
    ]

    PARAM_FILL = PatternFill("solid", fgColor="FFF2CC")
    FORMULA_FILL = PatternFill("solid", fgColor="E7E6E6")

    # Characterization refs for per_NAND in each corner
    REFS = {"TT": "$D$11", "FF": "$G$11", "SS": "$J$11"}

    for (sig, bb, depth, count, term, note) in rows:
        r = ws.max_row + 1
        ws.cell(row=r, column=1, value=FUB)
        ws.cell(row=r, column=2, value=sig)
        ws.cell(row=r, column=3, value=bb)
        # Editable depth / count cells (yellow)
        c = ws.cell(row=r, column=4, value=depth); c.fill = PARAM_FILL; c.alignment = CENTER
        c = ws.cell(row=r, column=5, value=count); c.fill = PARAM_FILL; c.alignment = CENTER
        ws.cell(row=r, column=6, value=term)
        # Delay formulas referencing the characterization per-NAND cells
        for off, corner in enumerate(("TT", "FF", "SS")):
            f = f"=D{r}*characterization!{REFS[corner]}"
            cell = ws.cell(row=r, column=7 + off, value=f)
            cell.fill = FORMULA_FILL; cell.alignment = CENTER
        ws.cell(row=r, column=10, value=note)

    # Column widths
    widths = [1, 28, 24, 26, 16, 16, 30, 18, 18, 18, 80]
    for c, w in enumerate(widths[1:], start=1):
        ws.column_dimensions[get_column_letter(c)].width = w

    # Notes block under the table
    r = ws.max_row + 2
    ws.cell(row=r, column=1, value="Methodology").font = SECTION_FONT
    notes = [
        "One row per (input signal, end-point) pair. End-point is one of: a flop's D pin, "
        "an output port, or a building-block port (whose internal cost is captured on the "
        "'building blocks' sheet).",
        "'local NAND depth' = combinational gate-equivalents on the path *within this FUB*. "
        "Walked by hand from the RTL.",
        "'local delay' = depth * per_NAND[corner] (from characterization sheet). "
        "Underestimates wide-bus buffering - same caveat as 'building blocks' SWAG.",
        "When a signal enters a BB, the row's depth/count is for the wires only; the BB row "
        "in the 'building blocks' sheet adds the internal cost.",
    ]
    for n in notes:
        r += 1
        ws.cell(row=r, column=1, value=n)
        ws.merge_cells(start_row=r, end_row=r, start_column=1, end_column=10)


def main():
    probes = read_probes()
    per_level, tflop, single_pt = derive(probes)
    wb = Workbook()
    build_sheet(wb, per_level, tflop, single_pt)
    build_blocks_sheet(wb)
    build_stream_sheet(wb)
    OUT.parent.mkdir(parents=True, exist_ok=True)
    wb.save(OUT)
    print(f"wrote {OUT}")
    print(f"  Tflop: {tflop}")
    print("  per-level (TT only):")
    for g in GATE_PRIMS:
        print(f"     {g:9s}: {per_level.get((g, 'TT'), 0):6.2f} ps")
    print("  degenerate single-point (TT, smallest size):")
    for g in DEGENERATE_PRIMS:
        d, lev = single_pt.get((g, "TT"), (0, 0))
        print(f"     {g:9s}: {d:6.2f} ps (lev={lev})")


if __name__ == "__main__":
    main()
