#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""WRITE-PATH drain/commit/serializer WaveJSON timing diagrams.

The truth tables that used to live here moved into the single signal-contract
workbook on 2026-09-10 (docs/gen_pumice_signal_contracts.py, sheets
DRAIN_HANDSHAKE / CM_RD_STALL_CANDIDATES / SERIALIZER_OWED / B_CONSOLIDATION).
This file now emits only the waves. Four workbooks in two directories, three
generators, overlapping content and no way to tell which was current -- that is
what the merge fixed.

Spec-first: define the ideal drain/commit/serializer signalling so the RTL fix is
written to a spec. Grounded in the RTL:
  * pumice_wr_data_cam.sv : u_drain_q (DEPTH=NUM_ENTRIES=8), commit_ready_o =
    drain-FIFO room; commit_done (B) = w_cm_fire && w_hd_blast && (!w_hd_agg ||
    w_hd_slast); cm_rd_ready_i backpressures the drain read-engine.
  * pumice_dfi_wr_serializer.sv : r_owed counts matured (wr_fire_i) bursts;
    w_drive = (owed!=0) && wd_valid_i; POSITIONAL (Nth wr_fire drives Nth
    wrdata burst) -- correct only while issue order == drain order.
  * pumice_cmd_arbiter.sv : WR column gated on wr_commit_ready_i (drain-FIFO room).

    python3 gen_write_path.py  # -> waves/10, waves/11
"""
from __future__ import annotations
import json, os

HERE = os.path.dirname(os.path.abspath(__file__))
WV = os.path.join(HERE, "waves")





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
            {"name": "aclk", "wave": "p................"},
            ["arbiter (same-bank WR pipelined)",
             {"name": "commit_valid",  "wave": "01............0.."},
             {"name": "commit_ready\n(drain room)", "wave": "1........0.......",
              "data": []},
             {"name": "drain FIFO cnt", "wave": "=.======......=..",
              "data": ["0","1","2","3","4","8","8","8"]},
            ],
            ["DFI stops accepting (ROOT to MEASURE)",
             {"name": "cm_rd_ready\n(DFI wr_fire)", "wave": "1......0........."},
             {"name": "wr_fire_i",    "wave": "01.....0........."},
             {"name": "dfi_wrdata_en","wave": "01.....0........."},
            ],
            ["result",
             {"name": "arbiter WR issue", "wave": "1........0......."},
             {"name": "gen_wr_done",      "wave": "0................"},
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
    os.makedirs(WV, exist_ok=True)
    print("wrote:")
    waves()


if __name__ == "__main__":
    main()
    # WaveDrom fails SILENTLY on a malformed diagram -- a short data list just
    # leaves buses blank, ragged rows just render out of step -- so the check
    # runs here rather than in a step someone can skip.
    import sys as _sys
    _sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
    import check_waves
    _sys.exit(check_waves.main())
