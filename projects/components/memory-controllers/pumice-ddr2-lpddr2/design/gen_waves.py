#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""Generate the pumice IDEAL-signalling WaveJSON timing diagrams (design/waves/).

Spec-first: these diagrams DEFINE the ideal cadence the RTL must hit; the K-maps
(design/kmaps/) define the control logic that produces them. Render with WaveDrom
(https://wavedrom.com/editor.html) or `npx wavedrom-cli -i <f>.json -s <f>.svg`.

DDR2-300 @ aclk=75MHz, DFI_RATE=2, BL4 (2 DFI words/burst). Timing in aclk cycles:
tRCD=3 tRP=3 tRAS=4 tRC=6 tCCD=2 tWTR=2 tRTW=2 tRRD=2 tFAW=6 CL=3 CWL=2
t_rddata_en=6 write_latency(t_phy_wrlat)=0.

    python3 gen_waves.py     # writes design/waves/*.json
"""
from __future__ import annotations
import json, os

HERE = os.path.dirname(os.path.abspath(__file__))
OUT = os.path.join(HERE, "waves")

# shared timing (aclk cycles)
tCCD, tRCD, tRP, tRAS, tRRD, tRDEN = 2, 3, 3, 4, 2, 6


def save(name, obj):
    with open(os.path.join(OUT, name), "w") as f:
        json.dump(obj, f, indent=2)
    print("  waves/" + name)


# 1) IDEAL open-page READ stream -- the throughput target ------------------
def open_read_stream():
    # RD issued every tCCD(=2); data returns t_rddata_en(=6)+CL later, then
    # streams 2 words/burst back-to-back. rvalid stays HIGH once filled.
    return {
        "signal": [
            {"name": "aclk",             "wave": "p................."},
            ["command",
             {"name": "cmd_valid_o",     "wave": "01.......0......."},
             {"name": "cmd_op_o",        "wave": "x2.2.2.2.x.......",
              "data": ["RD b0", "RD b0", "RD b0", "RD b0"]},
             {"name": "cmd_col_o",       "wave": "x2.2.2.2.x.......",
              "data": ["c0", "c1", "c2", "c3"]},
            ],
            ["dfi (read window)",
             {"name": "dfi_rddata_en",   "wave": "0......1......0.."},
             {"name": "dfi_rddata_valid","wave": "0......1......0.."},
             {"name": "dfi_rddata",      "wave": "x......3333333x..",
              "data": ["d0", "d0", "d1", "d1", "d2", "d2", "d3"]},
            ],
            ["axi return",
             {"name": "s_axi_rvalid",    "wave": "0......1......0.."},
             {"name": "s_axi_rready",    "wave": "1................"},
             {"name": "s_axi_rlast",     "wave": "0.......10.10.10."},
            ],
        ],
        "head": {"text": "IDEAL open-page READ stream: RD every tCCD=2, rvalid "
                         "continuous after the fill (t_rddata_en+CL). ~100% bus "
                         "util. NO occupancy stall between same-bank columns."},
        "config": {"hscale": 1},
    }


# 2) IDEAL open-page WRITE stream ------------------------------------------
def open_write_stream():
    return {
        "signal": [
            {"name": "aclk",             "wave": "p..........."},
            ["command",
             {"name": "cmd_valid_o",     "wave": "01.......0.."},
             {"name": "cmd_op_o",        "wave": "x4.4.4.4.x..",
              "data": ["WR b0", "WR b0", "WR b0", "WR b0"]},
            ],
            ["dfi (write, wrlat=0)",
             {"name": "dfi_wrdata_en",   "wave": "01.......0.."},
             {"name": "dfi_wrdata",      "wave": "x5555555x...",
              "data": ["w0", "w0", "w1", "w1", "w2", "w2", "w3"]},
             {"name": "dfi_wrdata_mask", "wave": "x0.......x.."},
            ],
            ["axi B",
             {"name": "s_axi_bvalid",    "wave": "0....1......."},
             {"name": "s_axi_bready",    "wave": "1..........."},
            ],
        ],
        "head": {"text": "IDEAL open-page WRITE stream: WR every tCCD=2, "
                         "wrdata concurrent (write_latency=0), drain FIFO never "
                         "empties. B per AXI burst on last sub-commit."},
        "config": {"hscale": 1},
    }


# 3) page-MISS: ACT -> tRCD -> RD -----------------------------------------
def act_rd():
    return {
        "signal": [
            {"name": "aclk",         "wave": "p........"},
            {"name": "cmd_op_o",     "wave": "x1..2.2.x",
             "data": ["ACT b0", "RD b0", "RD b0"]},
            {"name": "cmd_valid_o",  "wave": "01..1...0"},
            {"name": "bank_row_active","wave": "0.1......"},
            {"name": "bank_rdwr_ready\n(tRCD=3)", "wave": "0...1...."},
            {"name": "note",         "wave": "x1..2...x",
             "data": ["ACT opens row", "column only after tRCD"]},
        ],
        "head": {"text": "PAGE MISS: ACT then wait tRCD=3 before the first "
                         "column. First-access latency only -- subsequent hits "
                         "stream at tCCD (see open_read_stream)."},
        "config": {"hscale": 1},
    }


# 4) cross-bank ACT pipelining (tRRD / tFAW) ------------------------------
def bank_parallel_act():
    return {
        "signal": [
            {"name": "aclk",        "wave": "p........."},
            {"name": "cmd_op_o",    "wave": "x1.1.1.1.x",
             "data": ["ACT b0", "ACT b1", "ACT b2", "ACT b3"]},
            {"name": "cmd_valid_o", "wave": "01......0."},
            {"name": "trrd_ok\n(=2)","wave": "1.0101010."},
            {"name": "tfaw_ok\n(<=4/win)","wave": "1.......0."},
            {"name": "b0 rows",     "wave": "0.1......."},
            {"name": "b1 rows",     "wave": "0...1....."},
            {"name": "note",        "wave": "x1......2x",
             "data": ["ACTs pipeline across banks @tRRD", "5th ACT waits tFAW"]},
        ],
        "head": {"text": "CROSS-BANK ACT pipelining: one ACT per tRRD=2, capped "
                         "at 4 per tFAW window. Their tRCDs overlap so columns "
                         "from multiple banks are ready together -> the 4x."},
        "config": {"hscale": 1},
    }


# 5) page CONFLICT: PRE -> tRP -> ACT -> tRCD -> RD -----------------------
def pre_act_rd():
    return {
        "signal": [
            {"name": "aclk",        "wave": "p.........."},
            {"name": "cmd_op_o",    "wave": "x6..1..2.x.",
             "data": ["PRE b0", "ACT b0", "RD b0"]},
            {"name": "cmd_valid_o", "wave": "01..1..1.0."},
            {"name": "bank_pre_ready\n(tRAS=4)", "wave": "1.0......."},
            {"name": "bank_act_ready\n(tRP=3)",  "wave": "0...1....."},
            {"name": "bank_rdwr_ready\n(tRCD=3)","wave": "0......1.."},
        ],
        "head": {"text": "PAGE CONFLICT: PRE (after tRAS) -> tRP -> ACT -> tRCD "
                         "-> RD. Worst case; open-page avoids it on hits."},
        "config": {"hscale": 1},
    }


# 6) REFRESH insertion -----------------------------------------------------
def refresh():
    return {
        "signal": [
            {"name": "aclk",        "wave": "p..........."},
            {"name": "refresh_due", "wave": "01.....0...."},
            {"name": "cmd_op_o",    "wave": "x2.7.8...1.x",
             "data": ["RD", "PREA", "REF", "ACT"]},
            {"name": "cmd_valid_o", "wave": "01........0."},
            {"name": "any_row_active","wave": "1..0....1..."},
            {"name": "trfc_ok\n(tRFC)","wave": "1...0...1..."},
        ],
        "head": {"text": "REFRESH: precharge-all -> REFab -> wait tRFC -> resume "
                         "(re-ACT). The only maintenance bubble; postpone/pullin "
                         "credits (PUMICE-006) move it out of demand windows."},
        "config": {"hscale": 1},
    }


# 7) the pick pipeline as a TRUE pipeline -- the CORRECTION ----------------
def pick_pipeline():
    return {
        "signal": [
            {"name": "aclk",          "wave": "p........."},
            ["3-flop pick pipeline (latency, NOT rate)",
             {"name": "stage1 snapshot", "wave": "x2222x....",
              "data": ["A", "B", "C", "D"]},
             {"name": "stage2 pre-pick", "wave": "x.2222x...",
              "data": ["A", "B", "C", "D"]},
             {"name": "stage3 output",   "wave": "x..2222x..",
              "data": ["A", "B", "C", "D"]},
            ],
            {"name": "cmd_valid_o",   "wave": "0..1111 0.".replace(" ", "")},
            {"name": "cmd_op_o",      "wave": "x..2222x..",
             "data": ["A", "B", "C", "D"]},
            {"name": "issue rate",    "wave": "x..3...x..",
             "data": ["ONE command PER CYCLE"]},
        ],
        "head": {"text": "IDEAL pick pipeline: A,B,C,D advance one stage/cycle, "
                         "one FIRES every cycle after a 3-cycle fill. Pipeline = "
                         "LATENCY, not throughput. Today's bug: an occupancy mask "
                         "blocks B until A drains -> 1 per 4 cycles. DELETE it; "
                         "gate only on DRAM timers."},
        "config": {"hscale": 1},
    }


# 8) same-bank outstanding -- the deadlock fix spec -----------------------
def same_bank_outstanding():
    return {
        "signal": [
            {"name": "aclk",           "wave": "p..............."},
            ["issue (same bank, open row)",
             {"name": "cmd_op_o",      "wave": "x2.2.2.2.x......",
              "data": ["RD b0 c0", "RD b0 c1", "RD b0 c2", "RD b0 c3"]},
             {"name": "tccd_ok",       "wave": "1.0101010.1....."},
             {"name": "outstanding[b0]","wave": "=.=.=.=.=.=.=.=.=",
              "data": ["0","1","2","3","4","3","2","1","0"]},
             {"name": "can_issue (cnt<D=5 & tccd)", "wave": "1.......1......."},
            ],
            ["return (in AR order, after round-trip)",
             {"name": "dfi_rddata_valid","wave": "0........1....0.."},
             {"name": "s_axi_rvalid",   "wave": "0........1....0.."},
             {"name": "s_axi_rlast",    "wave": "0.........10.10.1"},
            ],
        ],
        "head": {"text": "DEADLOCK FIX: up to D=ceil((t_rddata_en+CL)/tCCD)=5 "
                         "same-bank columns in flight; per-bank counter gates "
                         "issue (cnt<D & tCCD), completion (R-last/B) decrements. "
                         "Today one-per-bank is forced -> 15%% util. Return path "
                         "(rd issue-FIFO, aligner MAX_OUTSTANDING) must hold D."},
        "config": {"hscale": 1},
    }


# 9) the CURRENT failure chain -- reference for what NOT to do --------------
def failure_stale_image_wedge():
    return {
        "signal": [
            {"name": "aclk",              "wave": "p..............."},
            ["arbiter (mask relaxed -> stale-image race)",
             {"name": "r_bank_row_active\n(STALE 1-3cyc)", "wave": "1......0........"},
             {"name": "actual row (closing)","wave": "1....0........."},
             {"name": "cmd_op_o",         "wave": "x2.2.x.........",
              "data": ["RD b0 c0", "RD b0 c1 (on stale img!)"]},
            ],
            ["read return (in-order, untagged)",
             {"name": "dfi_rddata_valid", "wave": "0.......10......"},
             {"name": "RD c1 data",       "wave": "x........4......",
              "data": ["never returns (wrong row)"]},
             {"name": "rd_cam AR-drain\n(oldest r_ready)", "wave": "1........0.....",
              "data": []},
            ],
            ["shared cmd FIFO -> write wedge",
             {"name": "u_cmd_fifo head",  "wave": "x2.......5.....",
              "data": ["RD(stuck)", "WR blocked behind"]},
             {"name": "wr drain / commit", "wave": "1.........0...."},
             {"name": "s_axi_bvalid (gen_wr_done)", "wave": "0.............."},
            ],
        ],
        "head": {"text": "CURRENT FAILURE (mask relaxed, no forward-state): 2nd "
                         "same-bank RD classified on STALE row image -> lands on "
                         "closing row -> never returns -> in-order AR-drain wedges "
                         "-> stuck RD head-of-line-blocks WRs in the shared cmd "
                         "FIFO -> write 'wedges first'. Reference only."},
        "config": {"hscale": 1},
    }


WAVES = {
    "01_open_read_stream.json": open_read_stream,
    "02_open_write_stream.json": open_write_stream,
    "03_page_miss_act_rd.json": act_rd,
    "04_bank_parallel_act.json": bank_parallel_act,
    "05_page_conflict_pre_act_rd.json": pre_act_rd,
    "06_refresh_insertion.json": refresh,
    "07_pick_pipeline_ideal.json": pick_pipeline,
    "08_same_bank_outstanding_fix.json": same_bank_outstanding,
    "09_failure_stale_image_wedge.json": failure_stale_image_wedge,
}


def main():
    os.makedirs(OUT, exist_ok=True)
    print("wrote:")
    for name, fn in WAVES.items():
        save(name, fn())


if __name__ == "__main__":
    main()
