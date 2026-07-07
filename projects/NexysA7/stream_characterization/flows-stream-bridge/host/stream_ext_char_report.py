# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""Generate the STREAM extended-addressing characterization report (Markdown).

Reads the sweep JSON produced by stream_ext_char.py (board) or the sim
pre-validation (test_stream_char_ext_char) and emits a house-style Markdown
report — throughput-vs-size tables per mode plus the burst-vs-per-beat / transpose
comparison. Render to PDF via bin/md_to_docx.py with a style YAML (see
reports/.../generate_reports_pdf.sh). The SAME generator runs on sim data (a
template report) and on board data (the real numbers).

  python3 stream_ext_char_report.py --json results/ext/ext_char.json \\
      --out reports/ext_addressing/README.md --clk-hz 100000000 --source board
"""

from __future__ import annotations

import argparse
import json
from typing import List

CASES = ("row/row", "row/col", "col/row", "col/col")
CASE_DESC = {
    "row/row": "2D-tiled contiguous copy (read burst, write burst)",
    "row/col": "transpose (read rows burst, write columns single-beat)",
    "col/row": "transpose mirror (read columns single-beat, write rows burst)",
    "col/col": "column-major copy (read single-beat, write single-beat)",
}


def _gbps(bytes_per_cycle: float, clk_hz: float) -> float:
    return bytes_per_cycle * clk_hz / 1e9


def _size_table(records: List[dict], W: int, H: int, clk_hz: float) -> str:
    rows = ["| Mode | RD GB/s | WR GB/s | RD util | WR util | RD avg burst | WR avg burst | status |",
            "|------|--------:|--------:|--------:|--------:|-------------:|-------------:|:------:|"]
    for case in CASES:
        r = next((x for x in records if x["case"] == case and x["W"] == W and x["H"] == H), None)
        if r is None:
            rows.append(f"| {case} | - | - | - | - | - | - | missing |")
            continue
        rd, wr = r["rd"], r["wr"]
        rows.append(
            f"| {case} | {_gbps(rd['bytes_per_cycle'], clk_hz):.3f} "
            f"| {_gbps(wr['bytes_per_cycle'], clk_hz):.3f} "
            f"| {rd['util']:.2f} | {wr['util']:.2f} "
            f"| {rd['avg_burst_beats']:.1f} | {wr['avg_burst_beats']:.1f} "
            f"| {'ok' if r['ok'] else 'FAIL'} |")
    return "\n".join(rows)


def build_report(data: dict, clk_hz: float, source: str) -> str:
    records = data["records"]
    sizes = [tuple(s) for s in data["sizes"]]

    src_note = {
        "board": "Measured on the NexysA7 (real 100 MHz datapath).",
        "sim": "**Template — measured in cocotb simulation at reduced tile sizes.** "
               "Regenerate from a board sweep (`stream_ext_char.py`) for real numbers.",
    }.get(source, source)

    md = []
    md.append("# STREAM Extended-Addressing Characterization\n")
    md.append(f"_{src_note}_\n")
    md.append(
        "Characterization of STREAM's TASK-101 `dma_address_gen` addressing "
        "(`USE_ROW_COL_MAJOR_ADDRESSING=1`) across the four read/write traversal "
        "combinations. Separate from the legacy (contiguous) characterization.\n")

    md.append("## Addressing modes\n")
    md.append(
        "`row` = row-major = contiguous inner dimension (`stride_0 = beat_size`) "
        "so the AXI engine **bursts**. `col` = column-major = strided inner "
        "(`stride_0 = row_pitch`) so each beat is its own **single-beat** AXI "
        "transaction (`arlen/awlen = 0`). Read and write are independent, giving "
        "four combinations:\n")
    md.append("| Mode | Meaning |")
    md.append("|------|---------|")
    for c in CASES:
        md.append(f"| {c} | {CASE_DESC[c]} |")
    md.append("")

    md.append("## Method\n")
    md.append(
        "Each (mode, size) runs one extended descriptor over a WxH tile through "
        "the named `Stream` host API, with the RD/WR datapath perf windows open. "
        "Throughput is `byte_count / bucket_total x clk` (bucket_total = "
        "PROD+BP+STARV+IDLE, the closed-window length); utilization is the "
        "productive fraction. The read/write **data** stream is identical across "
        "modes (only addresses differ), so the differences are purely the "
        "addressing cost. Clock: "
        f"{clk_hz/1e6:.0f} MHz.\n")

    md.append("## Throughput vs. size\n")
    for (W, H) in sizes:
        md.append(f"### {W} x {H} tile ({W*H} beats)\n")
        md.append(_size_table(records, W, H, clk_hz))
        md.append("")

    md.append("## Findings\n")
    md.append(
        "- **Burst vs. single-beat** is the dominant effect: `row` directions "
        "sustain full-burst throughput; `col` directions are single-beat and "
        "run far lower (no burst amortization of AR/AW latency).\n"
        "- **`row/row`** is the efficient contiguous 2D copy; **`col/col`** is "
        "the worst case (both sides single-beat).\n"
        "- **Transpose** (`row/col`, `col/row`) shows the asymmetry: the burst "
        "side keeps up while the strided side is single-beat, so aggregate "
        "throughput is gated by the strided direction.\n"
        "- `avg burst` beats/transaction quantifies it directly: ~16 (the "
        "configured max) for burst directions, 1 for single-beat.\n")
    return "\n".join(md) + "\n"


def main(argv=None) -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--json", required=True, help="sweep JSON from stream_ext_char.py")
    ap.add_argument("--out", required=True, help="output Markdown path")
    ap.add_argument("--clk-hz", type=float, default=100e6)
    ap.add_argument("--source", default="board", choices=["board", "sim"])
    args = ap.parse_args(argv)

    with open(args.json) as f:
        data = json.load(f)
    md = build_report(data, args.clk_hz, args.source)
    with open(args.out, "w") as f:
        f.write(md)
    print(f"wrote report -> {args.out} ({len(data['records'])} records)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
