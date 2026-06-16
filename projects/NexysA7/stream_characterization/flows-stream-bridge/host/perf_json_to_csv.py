#!/usr/bin/env python3
"""Convert a run_characterization.py perf-matrix JSON into the current-runner CSV.

Emits one row per result dict using the column set documented in
reports/perf/README.md ("Columns (current runner)").

Usage:
    python3 perf_json_to_csv.py matrix.json [--date YYYY-MM-DD] [--time HH:MM:SS]
    # writes matrix.csv next to the JSON

The bus-side columns come straight from the on-chip harness timer +
axi_bus_meter counters (no UART / wall-clock contamination). The two
host-side columns (dma_time_s, throughput_MBps) are kept for transparency
only -- do NOT use them as efficiency metrics.
"""
import argparse
import csv
import json
import os
import sys

COLUMNS = [
    "date", "time", "config", "channels", "descriptors", "desc_KB", "mb_moved",
    # bus-side (authoritative)
    "bus_time_s", "bus_throughput_MBps", "bus_max_one_dir_MBps",
    "bus_max_net_moved_MBps", "bus_e2e_util_pct",
    "datapath_R_pct", "datapath_W_pct", "datapath_E2E_pct",
    "R_prod_pct", "R_bp_pct", "R_starv_pct",
    "W_prod_pct", "W_bp_pct", "W_starv_pct",
    # host-side (transparency only)
    "dma_time_s", "throughput_MBps",
]


def pct(x):
    return round(x * 100.0, 4)


def row_from_record(rec, date, time_str):
    m = rec.get("metrics", {}) or {}
    rb = m.get("r_buckets_pct", {}) or {}
    wb = m.get("w_buckets_pct", {}) or {}
    total_bytes = rec.get("total_bytes", 0)
    xfer = rec.get("transfer_bytes", 0)
    return {
        "date": date,
        "time": time_str,
        "config": rec.get("name", ""),
        "channels": rec.get("num_channels", ""),
        "descriptors": rec.get("descriptors_per_channel", ""),
        "desc_KB": round(xfer / 1024, 3) if xfer else "",
        "mb_moved": round(total_bytes / (1024 * 1024), 3) if total_bytes else "",
        "bus_time_s": round(rec.get("bus_time_s", 0), 9),
        "bus_throughput_MBps": round(rec.get("bus_throughput_mbps", 0), 3),
        "bus_max_one_dir_MBps": round(rec.get("bus_max_one_dir_mbps", 0), 3),
        "bus_max_net_moved_MBps": round(rec.get("bus_max_net_moved_mbps", 0), 3),
        "bus_e2e_util_pct": round(rec.get("bus_e2e_util_pct", 0), 4),
        "datapath_R_pct": pct(m.get("datapath_utilization_r", 0)),
        "datapath_W_pct": pct(m.get("datapath_utilization_w", 0)),
        "datapath_E2E_pct": pct(m.get("end_to_end_utilization", 0)),
        "R_prod_pct": pct(rb.get("productive", 0)),
        "R_bp_pct": pct(rb.get("backpressure", 0)),
        "R_starv_pct": pct(rb.get("starvation", 0)),
        "W_prod_pct": pct(wb.get("productive", 0)),
        "W_bp_pct": pct(wb.get("backpressure", 0)),
        "W_starv_pct": pct(wb.get("starvation", 0)),
        "dma_time_s": round(rec.get("dma_time_s", 0), 6),
        "throughput_MBps": round(rec.get("throughput_mbps", 0), 3),
    }


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("json_path")
    ap.add_argument("--out", default=None, help="output CSV (default: <json>.csv)")
    ap.add_argument("--date", default="", help="run date YYYY-MM-DD for date column")
    ap.add_argument("--time", default="", help="run time HH:MM:SS for time column")
    args = ap.parse_args()

    with open(args.json_path) as f:
        data = json.load(f)
    if not isinstance(data, list):
        sys.exit(f"expected a JSON list of result dicts, got {type(data).__name__}")

    out = args.out or os.path.splitext(args.json_path)[0] + ".csv"
    with open(out, "w", newline="") as f:
        w = csv.DictWriter(f, fieldnames=COLUMNS)
        w.writeheader()
        for i, rec in enumerate(data):
            w.writerow(row_from_record(rec, args.date, args.time))
            print(f"  [{i + 1}/{len(data)}] {rec.get('name', '?')}", file=sys.stderr)
    print(f"Wrote {len(data)} rows -> {out}", file=sys.stderr)


if __name__ == "__main__":
    main()
