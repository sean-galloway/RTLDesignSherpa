#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""run_observer_ab.py -- the iface-observer A/B campaign for utility-ip/misc
TASK-003's board leg (Genesys 2, rs_loop_genesys2.bit).

One clean run per iteration through the SAME program the board CLI and the
cosim run (progs.iface_observers), then the FULL per-port observer metric set
is read directly: cycle buckets (0-3), bytes lo/hi (11/12), beats (13),
packets (14), tap_dropped (15), tap_packets (16) -- the last two are the
honesty pair the default readout leaves behind, and metric 15 is the
acceptance metric of the record. OBS_STICKY.TAP_BLOCKED is captured after
every run as the since-clear drop indicator.

Results land in observer_ab.json next to this script; the printed table is
the per-iteration class matrix.
"""
import argparse
import hashlib
import json
import subprocess
import sys
import time
from datetime import datetime, timezone
from pathlib import Path

HERE = Path(__file__).resolve().parent          # the results/<campaign> dir
HOST = HERE.parents[2] / "build-loop" / "host"    # reed-solomon/build-loop/host
sys.path.insert(0, str(HOST))

import rs_loop as rl                 # noqa: E402
import rs_loop_programs as progs     # noqa: E402

METRICS = {
    0: "productive", 1: "backpressure", 2: "starvation", 3: "idle",
    11: "bytes_lo", 12: "bytes_hi", 13: "beats", 14: "packets",
    15: "tap_dropped", 16: "tap_packets",
}

# The matrix: (label, mode, count, blocks, throttle). Two identical clean
# 16-block iterations prove the per-iteration isolation (meters clear with
# the run); e=t and e=t+1 are the codec's ordinary regimes; the 64-block run
# is the MANIFEST's board-proven arithmetic point (3776/4032 beats).
MATRIX = [
    ("clean16_a", rl.RsLoopDriver.INJ_COUNT, 0, 16, False),
    ("clean16_b", rl.RsLoopDriver.INJ_COUNT, 0, 16, False),
    ("e_eq_t_16", rl.RsLoopDriver.INJ_COUNT, 8, 16, False),
    ("e_gt_t_16", rl.RsLoopDriver.INJ_COUNT, 9, 16, False),
    ("clean64",   rl.RsLoopDriver.INJ_COUNT, 0, 64, False),
]


def full_port_read(drv):
    """Every readable AXIS observer metric, per port, in one dict."""
    out = {}
    for tap, name in enumerate(drv.AXIS_PORTS):
        d = {label: drv._obs_stat(drv.obs_axis, tap=tap, metric=m)
             for m, label in METRICS.items()}
        d["bytes"] = (d.pop("bytes_hi") << 32) | d.pop("bytes_lo")
        out[name] = d
    return out


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--port", required=True)
    ap.add_argument("--baud", type=int, default=115200)
    ap.add_argument("--bitstream", required=True,
                    help="the .bit programmed on the board; sha256 recorded")
    ap.add_argument("--git-head", default="")
    ap.add_argument("--out", default=str(HERE / "observer_ab.json"))
    args = ap.parse_args()

    sha = hashlib.sha256(Path(args.bitstream).read_bytes()).hexdigest()
    head = args.git_head or subprocess.run(
        ["git", "rev-parse", "HEAD"], capture_output=True, text=True,
        cwd=str(HERE.parents[2])).stdout.strip()

    drv = rl.RsLoopDriver(port=args.port, baudrate=args.baud)
    meta = {
        "date": datetime.now(timezone.utc).isoformat(),
        "board": "Genesys 2 (jtag 200300B818A0, uart AU05X8RM)",
        "port": args.port,
        "bitstream": Path(args.bitstream).name,
        "bitstream_sha256": sha,
        "git_head": head,
        "build_id": f"0x{drv.build_id():08X}",
        "profile": drv.profile(),
        "topology": drv.topology(),
        "caps": drv.observer_caps(),
    }
    print(f"== observer A/B on {meta['board']} @ {args.port} ==")
    print(f"   bitstream {meta['bitstream']} sha256 {sha[:16]}..")
    print(f"   HEAD {head}  BUILD_ID {meta['build_id']}  "
          f"caps axis {meta['caps']['axis']}")

    iterations = []
    for label, mode, count, blocks, throttle in MATRIX:
        t0 = time.monotonic()
        r = progs.run(drv, mode, count=count, blocks=blocks,
                      throttle=throttle, iface_obs=True)
        stats = full_port_read(drv)
        sticky = drv.obs_axis.read("OBS_STICKY")
        entry = {
            "label": label, "blocks": blocks, "mode": mode, "count": count,
            "throttle": throttle,
            "cycles": r.cycles, "cycles_per_block": r.cycles_per_block,
            "run_ok": not progs.verdict(r),
            "cmp_beats": r.cmp_beats,
            "cmp_data_mismatch": r.cmp_data_mismatch,
            "cmp_status_mismatch": r.cmp_status_mismatch,
            "tap_blocked_sticky": bool(sticky & 0x2),
            "ports": stats,
        }
        iterations.append(entry)
        print(f"  {label:>10}: {blocks} blk e={count} -> {r.cycles} cyc "
              f"({r.cycles_per_block:.1f}/blk) run_ok={entry['run_ok']} "
              f"A=B beats={r.cmp_beats} mm={r.cmp_data_mismatch}/{r.cmp_status_mismatch} "
              f"[{time.monotonic()-t0:.1f}s]")
        for port, d in stats.items():
            print(f"    {port:>7}: prod={d['productive']:>6} bp={d['backpressure']:>5} "
                  f"starv={d['starvation']:>5} idle={d['idle']:>6} "
                  f"beats={d['beats']:>5} pkts={d['packets']:>4} bytes={d['bytes']:>7} "
                  f"tap_pkts={d['tap_packets']:>4} tap_dropped={d['tap_dropped']:>3}")

    report = {"meta": meta, "iterations": iterations}
    Path(args.out).write_text(json.dumps(report, indent=1))
    print(f"== wrote {args.out}")
    return 0 if all(i["run_ok"] for i in iterations) else 1


if __name__ == "__main__":
    sys.exit(main())
