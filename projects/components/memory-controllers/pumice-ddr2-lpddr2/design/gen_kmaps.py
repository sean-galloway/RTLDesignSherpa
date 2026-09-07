#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""Generate the pumice IDEAL command/data-path K-map (truth-table) workbooks.

Spec-first flow: these truth tables + the WaveJSON timing diagrams (design/waves/)
DEFINE the ideal signalling. RTL is then written to match the spec, not the other
way round. Every gate name here is a real arbiter/timer signal
(rtl/fub/pumice_cmd_arbiter.sv, bank_timer.sv, global_timers.sv); every command is
a dram_op_e (rtl/includes/pumice_pkg.sv).

    python3 gen_kmaps.py       # writes kmaps/pumice_cmd_path_kmap.xlsx
                               #        kmaps/pumice_data_path_kmap.xlsx

Regenerate whenever the ideal decision changes. DDR2-300 timing (controller/aclk
cycles) is the sim/board tuple: tRCD=3 tRP=3 tRAS=4 tRC=6 tCCD=2(BL4) tWTR=2
tRTW=2 tRRD=2 tFAW=6 CL=3 CWL=2 tWR=3 tRTP=2, t_phy_wrlat/write_latency=0,
t_rddata_en=6.
"""
from __future__ import annotations
import os
from openpyxl import Workbook
from openpyxl.styles import Font, PatternFill, Alignment, Border, Side

HERE = os.path.dirname(os.path.abspath(__file__))
OUT = os.path.join(HERE, "kmaps")

HDR = Font(bold=True, color="FFFFFF")
HDR_FILL = PatternFill("solid", fgColor="374151")
TITLE = Font(bold=True, size=13)
NOTE = Font(italic=True, color="6B7280")
CENTER = Alignment(horizontal="center", vertical="center")
WRAP = Alignment(horizontal="left", vertical="top", wrap_text=True)
THIN = Border(*[Side(style="thin", color="D1D5DB")] * 4)
# command -> fill (semantic colour so the decision reads at a glance)
CMDFILL = {
    "NOP":  "E5E7EB", "ACT":  "BFDBFE", "PRE":  "FDE68A", "PREA": "FCD34D",
    "RD":   "BBF7D0", "RDA":  "86EFAC", "WR":   "FBCFE8", "WRA":  "F9A8D4",
    "REF":  "FCA5A5", "REFPB":"FECACA",
}


def _hdr_row(ws, row, cols, widths=None):
    for c, name in enumerate(cols, 1):
        cell = ws.cell(row=row, column=c, value=name)
        cell.font = HDR; cell.fill = HDR_FILL; cell.alignment = CENTER
        cell.border = THIN
    if widths:
        for c, w in enumerate(widths, 1):
            ws.column_dimensions[ws.cell(row=1, column=c).column_letter].width = w


def _row(ws, row, vals, cmd_col=None):
    for c, v in enumerate(vals, 1):
        cell = ws.cell(row=row, column=c, value=v)
        cell.alignment = CENTER if len(str(v)) < 14 else WRAP
        cell.border = THIN
        if cmd_col and c == cmd_col and v in CMDFILL:
            cell.fill = PatternFill("solid", fgColor=CMDFILL[v])
            cell.font = Font(bold=True)


def _title(ws, text, sub=None):
    ws.cell(row=1, column=1, value=text).font = TITLE
    if sub:
        ws.cell(row=2, column=1, value=sub).font = NOTE
    return 4  # first data row


# ---------------------------------------------------------------------------
# CMD-PATH workbook
# ---------------------------------------------------------------------------
def cmd_path():
    wb = Workbook()

    # --- Sheet 1: the per-bank FR-FCFS command decision -------------------
    ws = wb.active; ws.title = "CMD_DECISION"
    r = _title(ws,
        "pumice per-bank command decision (FR-FCFS) -- IDEAL",
        "One row = one decision case, in PRIORITY order (top wins). Evaluated "
        "per candidate bank every aclk; the picker emits the highest-priority "
        "ready command across banks, ONE per cycle. '-' = don't-care. Issue "
        "rate is gated ONLY by DRAM timers -- never by pick-pipeline occupancy.")
    cols = ["prio", "refresh_due", "row_active", "row_hit", "col_pending",
            "act_ready\n(tRC/tRP)", "rdwr_ready\n(tRCD)", "pre_ready\n(tRAS)",
            "tCCD_ok", "tRRD/tFAW_ok", "turn_ok\n(tWTR/tRTW)", "=> CMD",
            "why / effect"]
    _hdr_row(ws, r, cols,
             widths=[5,11,10,8,11,11,10,10,8,12,11,8,46]); r += 1
    CMD = len(cols)  # cmd column index for fill
    rows = [
        [1,"Y","-","-","-","-","-","Y","-","-","-","REF",
         "refresh due AND all banks precharge-safe -> REFab (see PRE_ALL row)"],
        [2,"Y","Y","-","-","-","-","Y","-","-","-","PRE",
         "refresh due but a row is still open -> precharge it first (all banks), THEN REF"],
        [3,"N","Y","Y","Y","-","Y","-","Y","-","Y","RD/WR",
         "PAGE HIT: row open, column ready, tCCD+turnaround met -> issue column. "
         "The throughput path: back-to-back at tCCD, NO occupancy stall."],
        [4,"N","N","-","Y","Y","-","-","-","Y","-","ACT",
         "PAGE EMPTY: activate the requested row. tRRD/tFAW gate cross-bank ACT rate, "
         "not the column stream."],
        [5,"N","Y","N","Y","-","-","Y","-","-","-","PRE",
         "PAGE CONFLICT: row open but wrong row -> precharge (tRAS met) to reopen"],
        [6,"N","Y","Y","Y","-","N","-","-","-","-","NOP",
         "hit but tRCD not yet met (just ACTed) -> wait; do NOT block other banks"],
        [7,"N","-","-","N","-","-","-","-","-","-","NOP",
         "no pending column for this bank -> idle (page stays OPEN in open-page policy)"],
        [8,"N","Y","Y","Y","-","Y","-","N","-","-","NOP",
         "column ready but tCCD not met -> the ONLY legal reason to space same-bank "
         "columns; == tCCD, not pipeline depth"],
    ]
    for x in rows:
        _row(ws, r, x, cmd_col=CMD); r += 1
    r += 1
    ws.cell(row=r, column=1,
            value="Broken today: the arbiter ANDs an extra !w_col_inflight_bank "
                  "term (pick-pipeline occupancy) into rows 3/6/8, forcing one "
                  "same-bank column per ~pipeline-depth instead of per tCCD. "
                  "IDEAL removes it: only the DRAM timers above gate issue.").font = NOTE

    # --- Sheet 2: auto-precharge (AP) bit / page policy ------------------
    ws = wb.create_sheet("AP_DECISION")
    r = _title(ws, "column auto-precharge (RD->RDA / WR->WRA) -- page policy",
               "Decides the A10 auto-precharge bit on a column command. Sets "
               "whether the row stays open (streaming) or self-closes.")
    cols = ["page_policy", "last_col_to_page", "page_timeout_fired", "=> AP bit",
            "=> emitted op", "effect"]
    _hdr_row(ws, r, cols, widths=[13,16,17,9,13,40]); r += 1
    for x in [
        ["OPEN","N","N","0","RD / WR","row stays open -> next hit streams at tCCD"],
        ["OPEN","-","Y","1","RDA / WRA","idle/timeout close (fixed_open/adapt_time)"],
        ["CLOSE","-","-","1","RDA / WRA","every access self-precharges; next access re-ACTs"],
        ["OPEN","Y","N","0","RD / WR","open policy never AP on last col; explicit PRE closes"],
    ]:
        _row(ws, r, x, cmd_col=5); r += 1

    # --- Sheet 3: timing-gate legend ------------------------------------
    ws = wb.create_sheet("TIMING_GATES")
    r = _title(ws, "timing gates -> DDR2-300 values (controller/aclk cycles)",
               "Each gate is a registered timer output the decision consumes. "
               "These are the ONLY things allowed to throttle issue rate.")
    cols = ["gate signal", "DDR2 param", "cyc @75MHz", "gates which command", "meaning"]
    _hdr_row(ws, r, cols, widths=[22,14,11,20,44]); r += 1
    for x in [
        ["bank_act_ready_i","tRC / tRP","6 / 3","ACT","row-cycle / precharge done -> may ACT"],
        ["bank_rdwr_ready_i","tRCD","3","RD / WR","ACT-to-column met -> may issue column"],
        ["bank_pre_ready_i","tRAS / tRTP","4 / 2","PRE","min row-open / read-to-precharge met"],
        ["tccd_ok_i","tCCD","2 (BL4)","RD / WR","column-to-column; THE same-bank spacing"],
        ["twtr_ok_i","tWTR","2","RD after WR","write-to-read turnaround"],
        ["trtw_ok_i","tRTW","2","WR after RD","read-to-write turnaround"],
        ["trrd_ok_i","tRRD","2","ACT","activate-to-activate (cross-bank)"],
        ["tfaw_ok_i","tFAW","6","ACT","<=4 ACTs per rolling window (cross-bank)"],
        ["(rd data)","CL + t_rddata_en","3 + 6","-","RD-to-rddata_valid latency (return path)"],
        ["(wr data)","CWL / t_phy_wrlat","2 / 0","-","WR-to-wrdata_en latency (drain path)"],
    ]:
        _row(ws, r, x); r += 1

    # --- Sheet 4: forward-state overlay (the real deadlock fix) ----------
    ws = wb.create_sheet("FORWARD_STATE")
    r = _title(ws,
        "forward-state classification -- delete !w_col_inflight_bank safely",
        "The arbiter picks against a 1-3 cyc STALE registered bank image "
        "(r_bank_row_active etc.). Instead of blocking a same-bank column while "
        "one is in the pipe, OVERLAY the in-flight op's pending effect so the "
        "next same-bank column is classified against POST-op state. Then same-"
        "bank columns pipeline at tCCD with no stale-image race.")
    cols = ["in-flight op to bank b", "registered image says", "forwarded (ideal) says",
            "2nd same-bank column decision", "note"]
    _hdr_row(ws, r, cols, widths=[22,20,22,24,34]); r += 1
    for x in [
        ["RD/WR (column, open row)","row_active=1 (stale ok)","row stays open",
         "issue next column @tCCD","the streaming case -- was blocked, now flows"],
        ["ACT (just opened)","row_active still 0","row_active=1, tRCD pending",
         "NOP until tRCD, then column","no false column on a not-yet-open row"],
        ["PRE / AP-close","row_active still 1","row closing -> 0",
         "do NOT issue column; re-ACT","kills the wrong/closed-row bad read"],
        ["refresh-drain PRE","row_active still 1","row closing -> 0",
         "hold column until re-ACT","same race source as PRE"],
    ]:
        _row(ws, r, x); r += 1
    r += 1
    ws.cell(row=r, column=1,
            value="Signals already present to build the overlay: r_bank (in-flight "
                  "bank), w_inflight_col, w_inflight_preact, w_col_inflight_guard, "
                  "r_ap_closing. Keep the per-ENTRY double-issue mask "
                  "(w_rd/wr_col_inflight_ent); REMOVE the per-BANK occupancy mask "
                  "(w_col_inflight_bank). See design/README.md + waves/07,08,09.").font = NOTE
    return wb


# ---------------------------------------------------------------------------
# DATA-PATH workbook
# ---------------------------------------------------------------------------
def data_path():
    wb = Workbook()

    # --- Sheet 1: write-data drain (dfi_wrdata presentation) -------------
    ws = wb.active; ws.title = "WR_DRAIN"
    r = _title(ws,
        "write-data drain: WR command -> dfi_wrdata -- IDEAL",
        "Cycle-relative to the WR/WRA column ISSUE. write_latency=0 "
        "(pre-pull, board tuple). One WR moves BL4 = 2 DFI words (DFI_RATE=2). "
        "Must sustain one WR every tCCD with NO drain bubble.")
    cols = ["cyc since WR", "dfi_wrdata_en", "dfi_wrdata (source)", "dfi_wrdata_mask",
            "wr_cam action", "note"]
    _hdr_row(ws, r, cols, widths=[13,15,26,18,20,34]); r += 1
    for x in [
        ["0 (WR issued)","1","wr_cam[slot] word0","strobe0","pop word0","concurrent w/ cmd (wrlat=0)"],
        ["1","1","wr_cam[slot] word1","strobe1","pop word1 -> free slot","BL4/RATE2 = 2 words"],
        ["2","1 (next WR)","wr_cam[slot2] word0","strobe0","next burst","tCCD=2 -> back-to-back, no gap"],
        ["...","1","...","...","stream","drain FIFO never empties while cmds flow"],
    ]:
        _row(ws, r, x); r += 1
    r += 1
    ws.cell(row=r, column=1,
            value="INVARIANT: dfi_wrdata_en high every cycle a WR is in flight; "
                  "wr_commit_ready_i (drain-FIFO room) must cover >= (tCCD * max "
                  "same-bank outstanding) so the arbiter never stalls the column "
                  "stream on drain-FIFO backpressure.").font = NOTE

    # --- Sheet 2: B-response gating -------------------------------------
    ws = wb.create_sheet("WR_COMMIT_B")
    r = _title(ws, "write B-response gating (split/aggregate)",
               "One AXI AW may split into >1 DRAM WR (chopper). B returns ONCE, "
               "on the LAST sub-burst's commit. Must not assume in-order same-bank "
               "commit.")
    cols = ["sub-burst", "agg (more to come)", "last", "commit_done", "=> B_valid", "note"]
    _hdr_row(ws, r, cols, widths=[11,18,8,13,11,40]); r += 1
    for x in [
        ["0 of N","1","0","1","0","gate B: !(agg && !last)"],
        ["k of N","1","0","1","0","hold B until last"],
        ["N of N","0","1","1","1","emit single B for the whole AXI burst"],
        ["single","0","1","1","1","N=1 fast path"],
    ]:
        _row(ws, r, x, cmd_col=5); r += 1
    r += 1
    ws.cell(row=r, column=1,
            value="IDEAL: B-gate keyed on the CAM entry's own agg/last, NOT on a "
                  "per-bank single-outstanding flag -- so two same-bank writes in "
                  "flight each retire independently (today's deadlock is here).").font = NOTE

    # --- Sheet 3: read-data return -------------------------------------
    ws = wb.create_sheet("RD_RETURN")
    r = _title(ws,
        "read-data return: RD command -> dfi_rddata -> AXI R -- IDEAL",
        "Cycle-relative to RD/RDA issue. t_rddata_en=6, CL adds to first "
        "rddata_valid. Aligner captures dfi_rddata on dfi_rddata_valid and "
        "returns in AR order. Must hold MANY same-bank reads outstanding.")
    cols = ["cyc since RD", "dfi_rddata_en", "dfi_rddata_valid (PHY)", "aligner",
            "s_axi_rvalid", "note"]
    _hdr_row(ws, r, cols, widths=[13,15,22,22,14,34]); r += 1
    for x in [
        ["0 (RD issued)","assert @ t_rddata_en","0","arm capture","0","enable window opens later"],
        ["t_rddata_en (6)","1","0->1","capture word0","0->1","first beat; fill latency (not a bubble)"],
        ["+1","1","1","capture word1, push R","1","BL4/RATE2 = 2 words -> 2 R beats"],
        ["+tCCD (next RD)","1","1","capture next burst","1","STREAM: rvalid stays high, back-to-back"],
        ["gap (no cmd)","0","0","idle","0","only when no RD was issued tCCD ago"],
    ]:
        _row(ws, r, x); r += 1

    # --- Sheet 4: same-bank outstanding tracker (the deadlock fix) ------
    ws = wb.create_sheet("SAME_BANK_OUTSTANDING")
    r = _title(ws,
        "per-bank outstanding-column tracker -- the DEADLOCK FIX",
        "Today the arbiter allows exactly ONE column per bank in flight "
        "(occupancy mask) because the return/drain path deadlocks otherwise. "
        "IDEAL: a small per-bank counter permits up to RETURN_DEPTH columns; "
        "issue is gated by tCCD + counter<DEPTH, never by pipeline occupancy.")
    cols = ["outstanding", "new_col_issued", "completion", "tCCD_ok", "can_issue",
            "outstanding_next", "note"]
    _hdr_row(ws, r, cols, widths=[12,15,12,9,10,16,40]); r += 1
    for x in [
        ["0","-","-","Y","YES","1 (on issue)","first column to an open row"],
        ["1..D-1","N","N","Y","YES","+1 (on issue)","pipeline more same-bank cols -> streaming"],
        ["1..D","N","Y","-","-","-1 (on completion)","completion (B / R-last) frees a slot"],
        ["D (full)","-","-","Y","NO","hold","only stall: return path at capacity, NOT pipeline"],
        ["any","N","N","N","NO","hold","tCCD not met -> legal DRAM spacing"],
    ]:
        _row(ws, r, x, cmd_col=5); r += 1
    r += 1
    ws.cell(row=r, column=1,
            value="RETURN_DEPTH (D) must be >= ceil((t_rddata_en + CL) / tCCD) so "
                  "the pipe stays full across the read round-trip: with "
                  "t_rddata_en=6, CL=3, tCCD=2 -> D >= 5. Reads: rd issue-order "
                  "FIFO + aligner MAX_OUTSTANDING must both be >= D. Writes: "
                  "wr drain FIFO + independent per-entry B-gating.").font = NOTE

    # --- Sheet 5: tag-based recoverable returns (defense in depth) -------
    ws = wb.create_sheet("RETURN_TAGGING")
    r = _title(ws,
        "tag-based, recoverable read return -- fail-safe not fail-wedge",
        "Today the return is POSITIONAL: fill matches the issue-FIFO head "
        "(rd_cmd_cam), aligner slices fixed BL_WORDS with no per-read id. One "
        "short/lost burst desyncs every later read and wedges the AR-order "
        "drain forever. IDEAL: carry a read TAG end to end and length-check.")
    cols = ["mechanism today", "failure it causes", "ideal (tagged)", "recovers?"]
    _hdr_row(ws, r, cols, widths=[30,30,30,10]); r += 1
    for x in [
        ["return fill = issue-FIFO head (positional)","wrong data -> slot mismatch",
         "match return to slot by TAG/id","YES"],
        ["AR-drain gated on oldest r_ready","one stuck read wedges all younger",
         "drain any ready slot; watchdog the stuck one","YES"],
        ["aligner fixed BL_WORDS, no id","short burst desyncs all later reads",
         "per-read length watchdog + tag","YES"],
        ["dfi_rddata_valid no backpressure","beat into full FIFO is LOST",
         "size RD_FIFO >= D*BL_WORDS; assert never-full","N/A"],
    ]:
        _row(ws, r, x, cmd_col=4); r += 1
    r += 1
    ws.cell(row=r, column=1,
            value="Priority: the forward-state overlay (cmd kmap) removes the "
                  "CAUSE (no bad read is issued); tagging removes the "
                  "CONSEQUENCE (a bad/short return cannot permanently wedge). "
                  "Ship the overlay first; tagging is defense in depth.").font = NOTE
    return wb


def main():
    os.makedirs(OUT, exist_ok=True)
    cmd_path().save(os.path.join(OUT, "pumice_cmd_path_kmap.xlsx"))
    data_path().save(os.path.join(OUT, "pumice_data_path_kmap.xlsx"))
    print("wrote:")
    for f in ("pumice_cmd_path_kmap.xlsx", "pumice_data_path_kmap.xlsx"):
        print("  kmaps/" + f)


if __name__ == "__main__":
    main()
