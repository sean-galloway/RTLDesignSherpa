#!/usr/bin/env python3
"""capture_raw_trace.py — drain the monbus debug_sram and save raw
(packet, timestamp) pairs as JSON for offline codec analysis.

Works around dump_monbus_sram.py's __main__ bug (it indexes __doc__ which is
None) by calling its library functions directly.

    source env_python
    python3 host/capture_raw_trace.py --port /dev/ttyUSB2 -o trace.json
"""
import argparse
import json
import sys
from pathlib import Path

script_dir = Path(__file__).resolve().parent
repo_root = Path(__import__("os").environ.get("REPO_ROOT",
              script_dir.parents[4]))
sys.path.insert(0, str(repo_root / "projects" / "components" / "converters" / "bin"))
sys.path.insert(0, str(script_dir))

from uart_axi_bridge import UARTAxiBridge          # noqa: E402
from dump_monbus_sram import (                     # noqa: E402
    read_sram_region, parse_records, _rec_to_raw_pair,
)


def main():
    p = argparse.ArgumentParser()
    p.add_argument("--port", required=True)
    p.add_argument("--baud", type=int, default=115200)
    p.add_argument("--base", type=lambda s: int(s, 0), default=0x40000)
    p.add_argument("--bytes", dest="n_bytes", type=lambda s: int(s, 0),
                   default=0x40000)
    p.add_argument("--output", "-o", required=True)
    p.add_argument("--label", default="")
    args = p.parse_args()

    HARNESS_CSR_BASE = 0x0001_0000
    CSR_DBG_WR_PTR   = HARNESS_CSR_BASE + 0x08   # write pointer (in 32-bit words)
    CSR_DBG_OVERFLOW = HARNESS_CSR_BASE + 0x0C

    with UARTAxiBridge(port=args.port, baudrate=args.baud) as bridge:
        wr_ptr = bridge.read(CSR_DBG_WR_PTR) & 0xFFFF_FFFF
        overflow = bridge.read(CSR_DBG_OVERFLOW) & 0x1
        # Only drain the populated region (round up to whole 24-byte records),
        # unless the circular buffer wrapped (overflow) -> drain the full window.
        if overflow:
            n_bytes = args.n_bytes
        else:
            n_bytes = min(args.n_bytes, ((wr_ptr * 4 + 23) // 24) * 24)
        print(f"# wr_ptr={wr_ptr} words overflow={overflow} -> draining "
              f"{n_bytes} bytes", file=sys.stderr)
        words = read_sram_region(bridge.read, args.base, n_bytes)
    records = parse_records(words)
    # Emit the canonical capture schema consumed by plot_compression_report.py
    # / monbus_halfbeat_model.load_capture: one {"packet","timestamp"} dict per
    # record with 0x-prefixed hex (128-bit packet, 64-bit timestamp). The older
    # [int, int] list form is not readable by the codec model.
    pairs = []
    for r in records:
        pkt, ts = _rec_to_raw_pair(r)
        pairs.append({"packet": f"0x{pkt:032x}", "timestamp": f"0x{ts:016x}"})
    doc = {"label": args.label, "count": len(pairs), "records": pairs}
    with open(args.output, "w") as f:
        json.dump(doc, f)
    print(f"# {len(pairs)} records -> {args.output}", file=sys.stderr)


if __name__ == "__main__":
    main()
