#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""Generate the pumice IDEAL-signalling WaveJSON timing diagrams (design/waves/).

Spec-first: these diagrams DEFINE the ideal cadence the RTL must hit; the K-maps
(the decision-table sheets in ../docs/pumice_signal_contracts.xlsx) define the
control logic that produces them. Render with WaveDrom
(https://wavedrom.com/editor.html) or `npx wavedrom-cli -i <f>.json -s <f>.svg`.

BOARD OPERATING POINT (Nexys A7): DDR2-300 @ aclk=75 MHz, DFI_RATE=2, BL4 on a
x16 device with a 32-bit DRAM beat. That gives BL_PUMICE=2 beats and
**BURST_WORDS = 1 DFI word per DRAM burst**, so one column moves 8 bytes in ONE
aclk cycle and the peak is 600 MB/s. Timing in aclk cycles:
**tCCD=1** tRCD=3 tRP=3 tRAS=4 tRC=6 tWTR=2 tRTW=2 tRRD=2 tFAW=6 CL=3 CWL=2
t_rddata_en=6 write_latency(t_phy_wrlat)=0.

CORRECTED 2026-09-10: this file previously declared tCCD=2 and "BL4 (2 DFI
words/burst)", and drew the streaming diagrams with a column every OTHER cycle
while labelling them "~100% bus util". Both cannot be true, and the RTL settles
it: pumice_core.sv:255 clamps t_ccd_i up to BURST_WORDS, which is 1 here
(pumice_core.sv:76). The board sustains 571.3 MB/s read and 570.3 write, i.e.
~0.95 columns per cycle, so a column EVERY cycle is the ideal these diagrams
must show. The streaming waves are redrawn; the structural ones (03-09) depict
ordering rather than throughput and are unaffected by the spacing.

    python3 gen_waves.py     # writes design/waves/*.json
"""
from __future__ import annotations
import json, os

HERE = os.path.dirname(os.path.abspath(__file__))
OUT = os.path.join(HERE, "waves")

# shared timing (aclk cycles)
tCCD, tRCD, tRP, tRAS, tRRD, tRDEN = 1, 3, 3, 4, 2, 6


def save(name, obj):
    with open(os.path.join(OUT, name), "w") as f:
        json.dump(obj, f, indent=2)
    print("  waves/" + name)


# 1) IDEAL open-page READ stream -- the throughput target ------------------
def open_read_stream():
    # tCCD=1 at this geometry, so the ideal is a column EVERY cycle. Data
    # returns t_rddata_en+CL later and then streams one word per cycle
    # (BURST_WORDS=1), so rvalid never drops once the pipeline has filled.
    return {
        "signal": [
            {"name": "aclk",             "wave": "p................."},
            ["command",
             {"name": "cmd_valid_o",     "wave": "01......0........."},
             {"name": "cmd_op_o",        "wave": "x2222222x.........",
              "data": ["RD b0", "RD b0", "RD b0", "RD b0", "RD b0", "RD b0", "RD b0"]},
             {"name": "cmd_col_o",       "wave": "x2222222x.........",
              "data": ["c0", "c1", "c2", "c3", "c4", "c5", "c6"]},
            ],
            ["dfi rd",
             {"name": "dfi_rddata_en",   "wave": "0........1......0."},
             {"name": "dfi_rddata_valid","wave": "0........1......0."},
             {"name": "dfi_rddata",      "wave": "x........3333333x.",
              "data": ["d0", "d1", "d2", "d3", "d4", "d5", "d6"]},
            ],
            ["axi return",
             {"name": "s_axi_rvalid",    "wave": "0........1......0."},
             {"name": "s_axi_rready",    "wave": "1................."},
             {"name": "s_axi_rlast",     "wave": "0........1......0."},
            ],
        ],
        "head": {"text": "IDEAL open-page READ stream -- a column every cycle (tCCD=1)"},
        "config": {"hscale": 1},
    }


# 2) IDEAL open-page WRITE stream ------------------------------------------
def open_write_stream():
    # Mirror of the read stream. The write DATA must LEAD the command (the DFI
    # staged-token invariant), which is why wdata is already streaming when the
    # first WR column fires -- not a drawing artefact.
    return {
        "signal": [
            {"name": "aclk",             "wave": "p..........."},
            ["command",
             {"name": "cmd_valid_o",     "wave": "01......0..."},
             {"name": "cmd_op_o",        "wave": "x4444444x...",
              "data": ["WR b0", "WR b0", "WR b0", "WR b0", "WR b0", "WR b0", "WR b0"]},
             {"name": "cmd_col_o",       "wave": "x4444444x...",
              "data": ["c0", "c1", "c2", "c3", "c4", "c5", "c6"]},
            ],
            ["dfi wr",
             {"name": "dfi_wrdata_en",   "wave": "01......0..."},
             {"name": "dfi_wrdata",      "wave": "x4444444x...",
              "data": ["d0", "d1", "d2", "d3", "d4", "d5", "d6"]},
            ],
            ["axi",
             {"name": "s_axi_wvalid",    "wave": "1......0...."},
             {"name": "s_axi_wready",    "wave": "1......0...."},
             {"name": "s_axi_bvalid",    "wave": "0.......1..0"},
            ],
        ],
        "head": {"text": "IDEAL open-page WRITE stream -- a column every cycle, data leads"},
        "config": {"hscale": 1},
    }


def act_rd():
    return {
        "signal": [
            {"name": "aclk",         "wave": "p........"},
            {"name": "cmd_op_o",     "wave": "x3..2.2.x",
             "data": ["ACT b0", "RD b0", "RD b0"]},
            {"name": "cmd_valid_o",  "wave": "01..1...0"},
            {"name": "bank_row_active","wave": "0.1......"},
            {"name": "bank_rdwr_ready\n(tRCD=3)", "wave": "0...1...."},
            {"name": "note",         "wave": "x3..2...x",
             "data": ["ACT opens row", "column only after tRCD"]},
        ],
        "head": {"text": "Page MISS: ACT -> tRCD -> first column"},
        "config": {"hscale": 1},
    }


# 4) cross-bank ACT pipelining (tRRD / tFAW) ------------------------------
def bank_parallel_act():
    return {
        "signal": [
            {"name": "aclk",        "wave": "p.........."},
            {"name": "cmd_op_o",    "wave": "x1.1.1.1.x.",
             "data": ["ACT b0", "ACT b1", "ACT b2", "ACT b3"]},
            {"name": "cmd_valid_o", "wave": "01......0.."},
            {"name": "trrd_ok\n(=2)","wave": "1.0101010.."},
            {"name": "tfaw_ok\n(<=4/win)","wave": "1.......0.."},
            {"name": "b0 rows",     "wave": "0.1........"},
            {"name": "b1 rows",     "wave": "0...1......"},
            {"name": "note",        "wave": "x3......2x.",
             "data": ["ACTs pipeline across banks @tRRD", "5th ACT waits tFAW"]},
        ],
        "head": {"text": "Bank-parallel ACT pipelining (tRRD, tFAW)"},
        "config": {"hscale": 1},
    }


# 5) page CONFLICT: PRE -> tRP -> ACT -> tRCD -> RD -----------------------
def pre_act_rd():
    return {
        "signal": [
            {"name": "aclk",        "wave": "p.........."},
            {"name": "cmd_op_o",    "wave": "x6..3..2.x.",
             "data": ["PRE b0", "ACT b0", "RD b0"]},
            {"name": "cmd_valid_o", "wave": "01..1..1.0."},
            {"name": "bank_pre_ready\n(tRAS=4)", "wave": "1.0........"},
            {"name": "bank_act_ready\n(tRP=3)",  "wave": "0...1......"},
            {"name": "bank_rdwr_ready\n(tRCD=3)","wave": "0......1..."},
        ],
        "head": {"text": "Page CONFLICT: PRE -> tRP -> ACT -> tRCD -> RD"},
        "config": {"hscale": 1},
    }


# 6) REFRESH insertion -----------------------------------------------------
def refresh():
    return {
        "signal": [
            {"name": "aclk",        "wave": "p..........."},
            {"name": "refresh_due", "wave": "01.....0...."},
            {"name": "cmd_op_o",    "wave": "x2.7.8...3.x",
             "data": ["RD", "PREA", "REF", "ACT"]},
            {"name": "cmd_valid_o", "wave": "01........0."},
            {"name": "any_row_active","wave": "1..0....1..."},
            {"name": "trfc_ok\n(tRFC)","wave": "1...0...1..."},
        ],
        "head": {"text": "Refresh insertion: PREA -> REF -> tRFC -> resume"},
        "config": {"hscale": 1},
    }


# 7) the pick pipeline as a TRUE pipeline -- the CORRECTION ----------------
def pick_pipeline():
    return {
        "signal": [
            {"name": "aclk",          "wave": "p.........."},
            ["pick pipe",
             {"name": "stage1 snapshot", "wave": "x2222x.....",
              "data": ["A", "B", "C", "D"]},
             {"name": "stage2 pre-pick", "wave": "x.2222x....",
              "data": ["A", "B", "C", "D"]},
             {"name": "stage3 output",   "wave": "x..2222x...",
              "data": ["A", "B", "C", "D"]},
            ],
            {"name": "cmd_valid_o",   "wave": "0..11110..."},
            {"name": "cmd_op_o",      "wave": "x..2222x...",
             "data": ["A", "B", "C", "D"]},
            {"name": "issue rate",    "wave": "x..3...x...",
             "data": ["ONE command PER CYCLE"]},
        ],
        "head": {"text": "Pick pipeline is LATENCY, not rate -- one issue per cycle"},
        "config": {"hscale": 1},
    }


# 8) same-bank outstanding -- the deadlock fix spec -----------------------
def same_bank_outstanding():
    return {
        "signal": [
            {"name": "aclk",           "wave": "p................"},
            ["issue",
             {"name": "cmd_op_o",      "wave": "x2.2.2.2.x.......",
              "data": ["RD b0 c0", "RD b0 c1", "RD b0 c2", "RD b0 c3"]},
             {"name": "tccd_ok",       "wave": "1.0101010.1......"},
             {"name": "outstanding[b0]","wave": "=.=.=.=.=.=.=.=.=",
              "data": ["0","1","2","3","4","3","2","1","0"]},
             {"name": "can_issue (cnt<D=5 & tccd)", "wave": "1.......1........"},
            ],
            ["return",
             {"name": "dfi_rddata_valid","wave": "0........1....0.."},
             {"name": "s_axi_rvalid",   "wave": "0........1....0.."},
             {"name": "s_axi_rlast",    "wave": "0.........10.10.1"},
            ],
        ],
        "head": {"text": "Same-bank columns in flight, forward state + tagged return"},
        "config": {"hscale": 1},
    }


# 9) the CURRENT failure chain -- reference for what NOT to do --------------
def failure_stale_image_wedge():
    return {
        "signal": [
            {"name": "aclk",              "wave": "p................"},
            ["arbiter",
             {"name": "r_bank_row_active\n(STALE 1-3cyc)", "wave": "1......0........."},
             {"name": "actual row (closing)","wave": "1....0..........."},
             {"name": "cmd_op_o",         "wave": "x2.2.x...........",
              "data": ["RD b0 c0", "RD b0 c1 (on stale img!)"]},
            ],
            ["rd return",
             {"name": "dfi_rddata_valid", "wave": "0.......10......."},
             {"name": "RD c1 data",       "wave": "x........4.......",
              "data": ["never returns (wrong row)"]},
             {"name": "rd_cam AR-drain\n(oldest r_ready)", "wave": "1........0.......",
              "data": []},
            ],
            ["cmd FIFO",
             {"name": "u_cmd_fifo head",  "wave": "x2.......5.......",
              "data": ["RD(stuck)", "WR blocked behind"]},
             {"name": "wr drain / commit", "wave": "1.........0......"},
             {"name": "s_axi_bvalid (gen_wr_done)", "wave": "0................"},
            ],
        ],
        "head": {"text": "PATHOLOGICAL: stale bank image -- the wedge this design closed"},
        "config": {"hscale": 1},
    }



# ===========================================================================
# PERFORMANCE CASES -- what "slow" and "pathological" actually look like.
#
# Every diagram above is an IDEAL. A spec made only of ideals cannot be used to
# recognise a bad trace on an ILA, which is the job these do. Each one below is
# a shape that has actually been measured on this board, with the number it
# produced, so a capture can be matched against it by eye.
# ===========================================================================

# --- BAD PERF: correct, just slow ------------------------------------------
def bad_admit_gate_half_rate():
    """The AR admit gate (PUMICE-025, fixed 2026-09-10). Correct data, half
    the command rate -- the hardest class to notice, because nothing fails."""
    return {
        "signal": [
            {"name": "aclk",                "wave": "p..........."},
            ["AR intake",
             {"name": "fub_arvalid",        "wave": "1..........."},
             {"name": "r_armed (OLD)",      "wave": "01010101010."},
             {"name": "w_admit (OLD)",      "wave": "0.10101010.."},
             {"name": "w_admit (FIXED)",    "wave": "01.........."},
            ],
            ["command",
             {"name": "cmd_valid_o (OLD)",  "wave": "0.1.0.1.0.1."},
             {"name": "cmd_valid_o (FIXED)","wave": "01.........."},
            ],
        ],
        "head": {"text": "BAD PERF: AR admit at HALF rate -- 291.7 MB/s, integrity clean"},
        "config": {"hscale": 1},
    }


def bad_ring_depth_bound():
    """Reads bounded by RD_RET_DEPTH / round-trip rather than by tCCD."""
    return {
        "signal": [
            {"name": "aclk",                "wave": "p................."},
            ["issue",
             {"name": "cmd_valid_o",        "wave": "01....0....1....0."},
             {"name": "rt_alloc_ready",     "wave": "1.....0....1....0."},
             {"name": "ring occupancy",     "wave": "2.2.2.2....2.2.2..",
              "data": ["0", "16", "32 FULL", "32 FULL", "16", "32 FULL", "32"]},
            ],
            ["return",
             {"name": "dfi_rddata_valid",   "wave": "0.........1......."},
             {"name": "s_axi_rvalid",       "wave": "0.........1......."},
            ],
        ],
        "head": {"text": "BAD PERF: reads bounded by ring depth / round-trip -- 470.9 MB/s"},
        "config": {"hscale": 1},
    }


def bad_page_thrash():
    """col_major: every access a different row in the SAME bank."""
    return {
        "signal": [
            {"name": "aclk",             "wave": "p................"},
            ["command",
             {"name": "cmd_valid_o",     "wave": "01..0.1.0.1.0.1.."},
             {"name": "cmd_op_o",        "wave": "x5.x.2x3x.5x2x3x.",
              "data": ["PRE", "ACT", "RD", "PRE", "ACT", "RD"]},
            ],
            ["bank timers",
             {"name": "tRP (3)",         "wave": "0.1..0....1..0..."},
             {"name": "tRCD (3)",        "wave": "0....1..0....1..."},
             {"name": "safe_rd_o",       "wave": "0.......10......."},
            ],
            ["bus",
             {"name": "dfi_rddata_valid","wave": "0........10......"},
            ],
        ],
        "head": {"text": "BAD PERF: page thrash -- PRE+ACT per column, 102.4 MB/s"},
        "config": {"hscale": 1},
    }


def bad_rw_turnaround():
    """Alternating direction: tWTR/tRTW paid on every switch."""
    return {
        "signal": [
            {"name": "aclk",             "wave": "p................"},
            ["command",
             {"name": "cmd_valid_o",     "wave": "010.10.10.10.10.."},
             {"name": "cmd_op_o",        "wave": "x2x4x2x4x2x4x2x4.",
              "data": ["RD", "WR", "RD", "WR", "RD", "WR", "RD", "WR"]},
            ],
            ["turnaround",
             {"name": "twtr_ok_i",       "wave": "1.0.1.0.1.0.1.0.."},
             {"name": "trtw_ok_i",       "wave": "0.1.0.1.0.1.0.1.."},
             {"name": "w_rd_turn_block", "wave": "0.1.0.1.0.1.0.1.."},
            ],
            ["bus",
             {"name": "DQ occupancy",    "wave": "2x2x2x2x2x2x2x2x.",
              "data": ["RD", "WR", "RD", "WR", "RD", "WR", "RD", "WR"]},
            ],
        ],
        "head": {"text": "BAD PERF: read/write turnaround thrash -- tWTR/tRTW every switch"},
        "config": {"hscale": 1},
    }


def bad_refresh_storm():
    """tREFI cranked down: refresh takes a visible share of the bus."""
    return {
        "signal": [
            {"name": "aclk",             "wave": "p................"},
            ["refresh",
             {"name": "refresh_req_o",   "wave": "01..0.1..0.1..0.."},
             {"name": "w_ref_safe",      "wave": "0.1.0..1.0..1.0.."},
             {"name": "cmd_op_o",        "wave": "x5x6x2x5x6x2x5x6.",
              "data": ["PREA", "REF", "RD", "PREA", "REF", "RD", "PREA", "REF"]},
            ],
            ["recovery",
             {"name": "w_rfc_busy (tRFC)","wave": "0..1..0..1..0..1."},
             {"name": "dfi_rddata_valid","wave": "0......10........"},
            ],
        ],
        "head": {"text": "BAD PERF: refresh storm -- PREA+REF+tRFC, every row closed"},
        "config": {"hscale": 1},
    }


# --- PATHOLOGICAL: the shapes that mean something is WRONG ------------------
def patho_all_banks_same_row_conflict():
    """Every generator targeting a different row of the SAME banks."""
    return {
        "signal": [
            {"name": "aclk",             "wave": "p................"},
            ["gen0 bk0 rA",
             {"name": "req",             "wave": "1................"},
             {"name": "granted",         "wave": "0.10......10....."},
            ],
            ["gen1 bk0 rB",
             {"name": "req",             "wave": "1................"},
             {"name": "granted",         "wave": "0.....10......10."},
            ],
            ["bank 0",
             {"name": "cmd_op_o",        "wave": "x3x5x2x3x5x2x3x5.",
              "data": ["ACT A", "PRE", "ACT B", "PRE", "ACT A", "PRE", "ACT B", "PRE"]},
             {"name": "open_row",        "wave": "2.2.2.2.2.2.2.2..",
              "data": ["A", "-", "B", "-", "A", "-", "B", "-"]},
            ],
        ],
        "head": {"text": "PATHOLOGICAL: row ping-pong between masters -- 570 -> 224 MB/s"},
        "config": {"hscale": 1},
    }


def patho_inorder_serialization():
    """order_mode=1: the CAM may only issue its head."""
    return {
        "signal": [
            {"name": "aclk",             "wave": "p................"},
            ["CAM",
             {"name": "sch_valid_i[7:0]","wave": "2................",
              "data": ["FF (all eligible)"]},
             {"name": "head entry",      "wave": "2....2....2......",
              "data": ["e0 (row A)", "e1 (row B)", "e2 (row A)"]},
            ],
            ["issue",
             {"name": "cmd_op_o",        "wave": "x2x5x3x2x5x3x2x..",
              "data": ["RD A", "PRE", "ACT B", "RD B", "PRE", "ACT A", "RD A"]},
             {"name": "w_rfc_busy",      "wave": "0................"},
            ],
        ],
        "head": {"text": "PATHOLOGICAL: in_order -- only the CAM head may issue (~17x)"},
        "config": {"hscale": 1},
    }


def rd_return_ring():
    """Reads in flight beyond the scheduling window (pumice_rd_return_ring).

    Folded into the generator 2026-09-10. It had been committed as a
    hand-written JSON -- the only wave in the set with no generator, so it
    sat outside every check the others get, and its bus labels outnumbered
    its slots (the last one rendered nowhere).
    """
    return {
        "signal": [
            {
                "name": "aclk",
                "wave": "p................"
            },
            [
                "admit",
                {
                    "name": "ar_push (AR k)",
                    "wave": "x3333x...........",
                    "data": [
                        "k0",
                        "k1",
                        "k2",
                        "k3"
                    ]
                },
                {
                    "name": "ring alloc_ticket",
                    "wave": "x3333x...........",
                    "data": [
                        "t0",
                        "t1",
                        "t2",
                        "t3"
                    ]
                },
                {
                    "name": "cam ins (slot,ticket)",
                    "wave": "x3333x...........",
                    "data": [
                        "s0:t0",
                        "s1:t1",
                        "s2:t2",
                        "s3:t3"
                    ]
                }
            ],
            [
                "issue",
                {
                    "name": "arbiter rd issue slot",
                    "wave": "x.....2.2.2.2....",
                    "data": [
                        "s1",
                        "s0",
                        "s3",
                        "s2"
                    ]
                },
                {
                    "name": "cam sch_valid",
                    "wave": "=.=.=.=.=.=.=.=..",
                    "data": [
                        "0",
                        "1",
                        "3",
                        "7",
                        "F",
                        "D",
                        "C",
                        "4"
                    ]
                },
                {
                    "name": "ring issue_q push",
                    "wave": "x.....2.2.2.2....",
                    "data": [
                        "t1",
                        "t0",
                        "t3",
                        "t2"
                    ]
                }
            ],
            [
                "return",
                {
                    "name": "dfi_ret burst",
                    "wave": "x..........2.2.2.",
                    "data": [
                        "t1",
                        "t0",
                        "t3"
                    ]
                },
                {
                    "name": "ring ready[t]",
                    "wave": "=..........=.=.=.",
                    "data": [
                        "0000",
                        "0010",
                        "0011",
                        "1011"
                    ]
                }
            ],
            [
                "drain",
                {
                    "name": "drain (head)",
                    "wave": "x............2.2.",
                    "data": [
                        "t0",
                        "t1"
                    ]
                },
                {
                    "name": "ring head/free",
                    "wave": "=............=.=.",
                    "data": [
                        "t0",
                        "t1",
                        "t2"
                    ]
                }
            ]
        ],
        "head": {
            "text": "Read return ring -- reads in flight beyond the CAM window"},
        "config": {
            "hscale": 1
        }
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
    "12_rd_return_ring.json": rd_return_ring,
    # performance cases: bad-but-correct, then pathological
    "13_bad_admit_gate_half_rate.json": bad_admit_gate_half_rate,
    "14_bad_ring_depth_bound.json": bad_ring_depth_bound,
    "15_bad_page_thrash_col_major.json": bad_page_thrash,
    "16_bad_rw_turnaround_thrash.json": bad_rw_turnaround,
    "17_bad_refresh_storm.json": bad_refresh_storm,
    "18_patho_row_pingpong_masters.json": patho_all_banks_same_row_conflict,
    "19_patho_inorder_serialization.json": patho_inorder_serialization,
}


def main():
    os.makedirs(OUT, exist_ok=True)
    print("wrote:")
    for name, fn in WAVES.items():
        save(name, fn())


if __name__ == "__main__":
    main()
    # WaveDrom fails SILENTLY on a malformed diagram -- a short data list just
    # leaves buses blank, ragged rows just render out of step -- so the check
    # runs here rather than in a step someone can skip.
    import sys as _sys
    _sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
    import check_waves
    _sys.exit(check_waves.main())
