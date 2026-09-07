#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""Detailed WRITE-PATH drain/commit/serializer spec -- the handshake granularity
where the same-bank-concurrency wedge lives (gen_kmaps.py's WR_DRAIN/WR_COMMIT_B
are coarse cycle diagrams; this is the FUB-handshake truth).

Spec-first: define the ideal drain/commit/serializer signalling so the RTL fix is
written to a spec. Grounded in the RTL:
  * pumice_wr_data_cam.sv : u_drain_q (DEPTH=NUM_ENTRIES=8), commit_ready_o =
    drain-FIFO room; commit_done (B) = w_cm_fire && w_hd_blast && (!w_hd_agg ||
    w_hd_slast); cm_rd_ready_i backpressures the drain read-engine.
  * pumice_dfi_wr_serializer.sv : r_owed counts matured (wr_fire_i) bursts;
    w_drive = (owed!=0) && wd_valid_i; POSITIONAL (Nth wr_fire drives Nth
    wrdata burst) -- correct only while issue order == drain order.
  * pumice_cmd_arbiter.sv : WR column gated on wr_commit_ready_i (drain-FIFO room).

    python3 gen_write_path.py  # -> kmaps/pumice_write_path_kmap.xlsx, waves/10,11
"""
from __future__ import annotations
import json, os
from openpyxl import Workbook
from openpyxl.styles import Font, PatternFill, Alignment, Border, Side

HERE = os.path.dirname(os.path.abspath(__file__))
KM, WV = os.path.join(HERE, "kmaps"), os.path.join(HERE, "waves")
HDR = Font(bold=True, color="FFFFFF"); HDR_FILL = PatternFill("solid", fgColor="374151")
TITLE = Font(bold=True, size=13); NOTE = Font(italic=True, color="6B7280")
CEN = Alignment(horizontal="center", vertical="center")
WRAP = Alignment(horizontal="left", vertical="top", wrap_text=True)
THIN = Border(*[Side(style="thin", color="D1D5DB")] * 4)
OK, BAD = PatternFill("solid", fgColor="BBF7D0"), PatternFill("solid", fgColor="FCA5A5")


def _hdr(ws, r, cols, w):
    for c, n in enumerate(cols, 1):
        x = ws.cell(row=r, column=c, value=n); x.font = HDR; x.fill = HDR_FILL
        x.alignment = CEN; x.border = THIN
    for c, wi in enumerate(w, 1):
        ws.column_dimensions[ws.cell(row=1, column=c).column_letter].width = wi


def _row(ws, r, vals, flag=None):
    for c, v in enumerate(vals, 1):
        x = ws.cell(row=r, column=c, value=v)
        x.alignment = CEN if len(str(v)) < 16 else WRAP; x.border = THIN
        if flag and c == flag[0]:
            x.fill = OK if flag[1] else BAD
            x.font = Font(bold=True)


def _t(ws, t, s):
    ws.cell(row=1, column=1, value=t).font = TITLE
    ws.cell(row=2, column=1, value=s).font = NOTE
    return 4


def kmap():
    wb = Workbook()

    # 1) drain handshake -----------------------------------------------------
    ws = wb.active; ws.title = "DRAIN_HANDSHAKE"
    r = _t(ws, "write drain: arbiter commit -> drain FIFO -> DFI wr_fire -- IDEAL",
           "The arbiter marks a WR slot scheduled and enqueues it in u_drain_q "
           "(DEPTH=8); the drain read-engine streams cm_rd to the DFI at its own "
           "pace. commit_ready (=drain-FIFO room) gates the arbiter's WR issue. "
           "For same-bank WR streaming the drain MUST keep pace with commit.")
    _hdr(ws, r, ["commit_valid\n(arb WR)", "drain FIFO\nroom (=commit_ready)",
                 "cm_rd_valid\n(drain->DFI)", "cm_rd_ready\n(DFI accepts)",
                 "=> action", "drain FIFO next", "note"],
         [12, 16, 14, 14, 16, 14, 34]); r += 1
    for x, ok in [
        (["1", "1", "-", "-", "ENQUEUE slot", "+1", "arbiter commits a WR"], True),
        (["-", "-", "1", "1", "DRAIN 1 slot -> wr_fire", "-1", "DFI takes it @tCCD"], True),
        (["1", "1", "1", "1", "enqueue + drain (net 0)", "steady", "STREAMING: paced by tCCD"], True),
        (["1", "0", "-", "0", "STALL: FIFO full, drain blocked", "8 (full)", "commit_ready low -> arbiter WR stalls => the wedge if drain never resumes"], False),
    ]:
        _row(ws, r, x, flag=(5, ok)); r += 1
    r += 1
    ws.cell(row=r, column=1,
            value="WEDGE CONDITION: drain FIFO fills (8) AND cm_rd_ready stays 0 "
                  "-> commit_ready=0 -> arbiter stops issuing WR -> gen_wr_done "
                  "never asserts. So the fix question is: WHY does cm_rd_ready "
                  "(DFI accepting writes) stall under same-bank WR concurrency? "
                  "Candidates below.").font = NOTE

    # 2) why cm_rd_ready stalls (the diagnostic) ----------------------------
    ws = wb.create_sheet("CM_RD_STALL_CANDIDATES")
    r = _t(ws, "why the DFI stops accepting writes (cm_rd_ready=0) -- to MEASURE",
           "The drain streams cm_rd only while the DFI cmd path fires WR "
           "commands (wr_fire). Enumerate what can hold wr_fire off under "
           "same-bank WR concurrency; the waveform measurement confirms which.")
    _hdr(ws, r, ["candidate", "mechanism (file)", "same-bank trigger", "confirm by"],
         [30, 34, 30, 26]); r += 1
    for x in [
        ["DFI cmd FIFO full", "shared u_cmd_fifo, in-order (mem_cmd_scheduler)",
         "WR cmds queue faster than DFI drains", "cmd-FIFO count in waves"],
        ["tCCD/bank gate at DFI", "dfi_cmd_path w_col_ok / col pacing",
         "same-bank WR spaced by tCCD -> drain paced", "dfi wr_fire spacing"],
        ["serializer owed vs wrdata desync", "dfi_wr_serializer positional r_owed",
         "wr_fire without matching wrdata (or vice versa)", "r_owed vs wd_valid"],
        ["wrdata CDC FIFO empty/full", "pumice_dfi_cdc wrdata FIFO",
         "wrdata not keeping pace with wr_fire", "cdc wrdata occupancy"],
        ["B-consolidation backpressure", "commit_done agg/slast gating",
         "a split burst's B never completes -> slot not evicted", "commit_done/agg/slast"],
    ]:
        _row(ws, r, x); r += 1

    # 3) serializer owed/drive ----------------------------------------------
    ws = wb.create_sheet("SERIALIZER_OWED")
    r = _t(ws, "dfi_wr_serializer: matured-burst owed accounting -- IDEAL",
           "r_owed += wr_fire (a WR cmd matured); w_drive=(owed!=0)&&wd_valid; "
           "drives 1 wrdata word/cycle; -1 on the burst's last word. POSITIONAL: "
           "the Nth wr_fire binds the Nth wrdata burst -- correct only while "
           "issue order == drain order (true today; NO tag to recover if not).")
    _hdr(ws, r, ["r_owed", "wr_fire (mature)", "wd_valid", "=> w_drive",
                 "dfi_wrdata_en", "r_owed next", "note"],
         [10, 15, 10, 10, 14, 12, 34]); r += 1
    for x, ok in [
        (["0", "0", "-", "0", "0", "0", "idle -- no matured WR"], True),
        (["0", "1", "1", "1", "1", "0 or +", "matures + drives same cycle"], True),
        (["1", "0", "1", "1", "1", "-1 on last", "draining an owed burst"], True),
        (["1", "-", "0", "0", "0", "hold", "owed but wrdata not ready -> BUBBLE (wrdata CDC underrun)"], False),
        (["N", "1/cyc", "1", "1", "1", "steady", "STREAM: 1 wr_fire/tCCD, 1 word/cyc, no bubble"], True),
    ]:
        _row(ws, r, x, flag=(4, ok)); r += 1

    # 4) B consolidation -----------------------------------------------------
    ws = wb.create_sheet("B_CONSOLIDATION")
    r = _t(ws, "one B per host burst -- commit_done (agg/slast/blast)",
           "commit_done_valid = w_cm_fire && w_hd_blast && (!w_hd_agg || "
           "w_hd_slast): B strobes on the LAST beat of the LAST sub-burst. A "
           "split burst holds B until its final sub drains. Slot evicts on drain "
           "last -- so a never-draining sub never evicts, never frees the FIFO.")
    _hdr(ws, r, ["w_cm_fire", "w_hd_blast\n(beat last)", "w_hd_agg\n(split)",
                 "w_hd_slast\n(sub last)", "=> B (commit_done)", "note"],
         [11, 12, 10, 12, 18, 36]); r += 1
    for x, ok in [
        (["1", "1", "0", "-", "1", "non-split burst -> B now"], True),
        (["1", "1", "1", "0", "0", "mid sub of a split -> hold B, evict slot"], True),
        (["1", "1", "1", "1", "1", "final sub -> single B for the host burst"], True),
        (["0", "-", "-", "-", "0", "no drain fire -> slot stuck -> FIFO fills => wedge"], False),
    ]:
        _row(ws, r, x, flag=(5, ok)); r += 1
    wb.save(os.path.join(KM, "pumice_write_path_kmap.xlsx"))
    print("  kmaps/pumice_write_path_kmap.xlsx")


def waves():
    # 10) ideal write drain pipeline (2 same-bank WR pipelined) --------------
    ideal = {
        "signal": [
            {"name": "aclk", "wave": "p..........."},
            ["arbiter -> drain FIFO",
             {"name": "cmd_op_o (WR)", "wave": "x4.4.x......",
              "data": ["WR b0 c0", "WR b0 c1"]},
             {"name": "commit_valid",  "wave": "01.1.0......"},
             {"name": "commit_ready\n(drain room)", "wave": "1..........."},
             {"name": "drain FIFO cnt", "wave": "=.=.=.=.=...",
              "data": ["0", "1", "1", "1", "0"]},
            ],
            ["drain -> DFI serializer",
             {"name": "cm_rd_valid",  "wave": "0.1...1...0."},
             {"name": "cm_rd_ready\n(DFI wr_fire)", "wave": "1..........."},
             {"name": "wr_fire_i",    "wave": "0..1...1..0."},
             {"name": "r_owed",       "wave": "=..=...=..=.",
              "data": ["0", "1", "1", "0"]},
            ],
            ["DFI wrdata + B",
             {"name": "wd_valid",       "wave": "0..1.....0.."},
             {"name": "dfi_wrdata_en",  "wave": "0..1.1.1.0.."},
             {"name": "dfi_wrdata",     "wave": "x..5.5.5.x..",
              "data": ["w0", "w1", "w2"]},
             {"name": "commit_done (B)","wave": "0.......1.0."},
            ],
        ],
        "head": {"text": "IDEAL write drain: 2 same-bank WR columns pipeline at "
                         "tCCD; drain FIFO stays shallow, cm_rd_ready/wr_fire "
                         "keep pace, wrdata streams, one B per host burst. No "
                         "stall on commit_ready."},
        "config": {"hscale": 1},
    }
    # 11) the wedge reference (current, to be confirmed by measurement) ------
    wedge = {
        "signal": [
            {"name": "aclk", "wave": "p..............."},
            ["arbiter (same-bank WR pipelined)",
             {"name": "commit_valid",  "wave": "01............0."},
             {"name": "commit_ready\n(drain room)", "wave": "1........0.....",
              "data": []},
             {"name": "drain FIFO cnt", "wave": "=.======......=",
              "data": ["0","1","2","3","4","8","8","8"]},
            ],
            ["DFI stops accepting (ROOT to MEASURE)",
             {"name": "cm_rd_ready\n(DFI wr_fire)", "wave": "1......0......."},
             {"name": "wr_fire_i",    "wave": "01.....0......."},
             {"name": "dfi_wrdata_en","wave": "01.....0......."},
            ],
            ["result",
             {"name": "arbiter WR issue", "wave": "1........0....."},
             {"name": "gen_wr_done",      "wave": "0.............."},
            ],
        ],
        "head": {"text": "CURRENT WEDGE (hypothesis, to confirm by waveform): "
                         "same-bank WR pipelining fills the drain FIFO (8); "
                         "cm_rd_ready (DFI accepting writes) stalls -> "
                         "commit_ready=0 -> arbiter WR stops -> gen_wr_done never "
                         "asserts. MEASURE which CM_RD_STALL candidate holds "
                         "wr_fire off (see kmap sheet 2)."},
        "config": {"hscale": 1},
    }
    for name, obj in [("10_write_drain_pipeline_ideal.json", ideal),
                      ("11_write_same_bank_wedge_ref.json", wedge)]:
        with open(os.path.join(WV, name), "w") as f:
            json.dump(obj, f, indent=2)
        print("  waves/" + name)


def main():
    os.makedirs(KM, exist_ok=True); os.makedirs(WV, exist_ok=True)
    print("wrote:")
    kmap(); waves()


if __name__ == "__main__":
    main()
