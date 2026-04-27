#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway
#
# host/characterize.py
#
# Sweep DMA configurations on the FPGA and report measured cycles + MB/s
# per run. Reuses the descriptor builder + the CharacterizationRunner from
# run_characterization.py for the per-test setup; replaces its broken
# CSR_STATUS.irq polling with the new harness timer (CSR_TIMER_*).
#
# Output is a single CSV row per config:
#
#   name, num_channels, descriptors, total_bytes, cycles,
#   seconds, throughput_MBps, pass
#
# USAGE:
#   python3 host/characterize.py                          # default sweep
#   python3 host/characterize.py --csv host/sim_suite.csv # custom matrix
#   python3 host/characterize.py --configs 1desc_1ch_4KB --size 4KB
#   python3 host/characterize.py --output results.csv     # log to CSV file

import argparse
import csv
import os
import sys
import time
from typing import Optional

# Reuse everything the existing runner uses.
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)

from descriptor_builder import (  # noqa: E402
    DescriptorBuilder, build_char_matrix, load_configs_from_csv,
    _parse_size, _size_label,
    HARNESS_CSR_BASE,
)
import run_characterization as runner_mod  # noqa: E402

# UART bridge — same module the main runner imports lazily.
sys.path.insert(0, os.path.abspath(os.path.join(
    HERE, "../../../components/converters/bin")))
from uart_axi_bridge import UARTAxiBridge  # noqa: E402

# ---------------------------------------------------------------------------
# Timer CSR map (matches harness_csr.sv 0x28-0x34)
# ---------------------------------------------------------------------------
CSR_TIMER_CTRL          = HARNESS_CSR_BASE + 0x28  # W: bit 0 = clear pulse
CSR_TIMER_STATUS        = HARNESS_CSR_BASE + 0x2C  # R: [0]=done [1]=running [2]=pass
CSR_TIMER_CYCLES_LO     = HARNESS_CSR_BASE + 0x30
CSR_TIMER_CYCLES_HI     = HARNESS_CSR_BASE + 0x34
CSR_TIMER_EXPECTED_BEATS = HARNESS_CSR_BASE + 0x38  # RW: stop when sink beat count >= this

CLK_PERIOD_NS = 10.0  # 100 MHz aclk
DATA_WIDTH_BYTES = 16  # 128 b data path -> 16 B per beat


def run_one(runner, bridge, cfg, timeout_s: float, verbose: bool) -> dict:
    """Run a single test config and return measurement results."""
    test = runner.builder.build_test(cfg)
    total_bytes = test["total_bytes"]
    expected_beats = total_bytes // DATA_WIDTH_BYTES

    # Clear the timer and program the expected beat count for the stop
    # trigger BEFORE clearing the slave CRC stats — once a clear-stats
    # pulse fires, the slave's beat counter resets to 0, so any timer
    # bookkeeping that depended on a non-zero count would be invalidated.
    bridge.write(CSR_TIMER_CTRL, 0x01)
    bridge.write(CSR_TIMER_EXPECTED_BEATS, expected_beats)

    # Existing per-test setup: load descriptors, configure STREAM.
    runner.clear_stats()
    runner.load_descriptors(test["descriptor_writes"])
    runner.configure_stream(num_channels=cfg.num_channels)

    # Kick — this is what causes the scheduler to issue its first AR on the
    # descriptor RAM bus, which is the timer's start trigger.
    runner.kick_channels(test["kick_addresses"])

    # Poll TIMER_STATUS for done. Don't ride the slow 100 ms cadence — the
    # harness timer captures the result on the cycle it happens, so we just
    # need to read it back faster than the wall-clock timeout.
    start = time.time()
    while (time.time() - start) < timeout_s:
        sts = bridge.read(CSR_TIMER_STATUS)
        if sts is None:
            time.sleep(0.01)
            continue
        if sts & 0x1:
            cycles_lo = bridge.read(CSR_TIMER_CYCLES_LO) or 0
            cycles_hi = bridge.read(CSR_TIMER_CYCLES_HI) or 0
            cycles = (cycles_hi << 32) | cycles_lo
            seconds = cycles * CLK_PERIOD_NS * 1e-9
            mbps = (total_bytes / seconds) / (1024 * 1024) if seconds > 0 else 0.0
            return {
                "name":         cfg.name,
                "num_channels": cfg.num_channels,
                "descriptors":  cfg.descriptors_per_channel,
                "total_bytes":  total_bytes,
                "cycles":       cycles,
                "seconds":      seconds,
                "throughput_MBps": mbps,
                "pass":         bool(sts & 0x4),
                "timeout":      False,
            }
        time.sleep(0.01)

    return {
        "name":         cfg.name,
        "num_channels": cfg.num_channels,
        "descriptors":  cfg.descriptors_per_channel,
        "total_bytes":  total_bytes,
        "cycles":       None,
        "seconds":      None,
        "throughput_MBps": None,
        "pass":         False,
        "timeout":      True,
    }


def fmt_row(r: dict) -> str:
    if r["timeout"]:
        return (f"  {r['name']:<24} {r['num_channels']:>3}ch "
                f"{r['descriptors']:>3}d  {_size_label(r['total_bytes']):>10}  "
                f"TIMEOUT")
    return (f"  {r['name']:<24} {r['num_channels']:>3}ch "
            f"{r['descriptors']:>3}d  {_size_label(r['total_bytes']):>10}  "
            f"{r['cycles']:>10} cyc  {r['seconds']*1e6:>9.1f} us  "
            f"{r['throughput_MBps']:>7.1f} MB/s  "
            f"{'PASS' if r['pass'] else 'FAIL'}")


def parse_args():
    p = argparse.ArgumentParser(
        description="Sweep STREAM DMA configurations on the FPGA and "
                    "measure cycles + throughput via the harness timer.")
    p.add_argument("--port", default="/dev/ttyUSB1")
    p.add_argument("--baud", type=int, default=115200)
    p.add_argument("--csv", default=None,
                   help="Load test configs from CSV (default: built-in matrix)")
    p.add_argument("--configs", nargs="+",
                   help="Run only the named configs from the matrix")
    p.add_argument("--channels", type=int, nargs="+",
                   help="Limit to specific channel counts")
    p.add_argument("--size", default="1MB",
                   help="Per-descriptor transfer size for the built-in matrix "
                        "(ignored when --csv is used)")
    p.add_argument("--timeout", type=float, default=60.0,
                   help="Per-test timeout in seconds (default: 60)")
    p.add_argument("--output", "-o", default=None,
                   help="Write results to a CSV file in addition to stdout")
    p.add_argument("--verbose", "-v", action="store_true")
    return p.parse_args()


def main() -> int:
    args = parse_args()

    # Build config list (same logic the existing runner uses).
    if args.csv:
        configs = load_configs_from_csv(args.csv)
    else:
        configs = build_char_matrix(transfer_bytes=_parse_size(args.size))
        if args.configs:
            configs = [c for c in configs if c.name in args.configs]
        if args.channels:
            configs = [c for c in configs if c.num_channels in args.channels]

    if not configs:
        print("No configurations match the filter.", file=sys.stderr)
        return 1

    print(f"Sweeping {len(configs)} configurations on {args.port}\n")
    results = []
    with UARTAxiBridge(args.port, args.baud) as bridge:
        runner = runner_mod.CharacterizationRunner(
            bridge, data_width=128, verbose=args.verbose)
        if not runner.ping():
            print("ERROR: harness ping failed.", file=sys.stderr)
            return 2

        for i, cfg in enumerate(configs, 1):
            print(f"[{i}/{len(configs)}] {cfg.name}")
            r = run_one(runner, bridge, cfg, args.timeout, args.verbose)
            results.append(r)
            print(fmt_row(r))

    # Summary
    n_pass = sum(1 for r in results if r["pass"])
    n_fail = len(results) - n_pass
    print(f"\nSummary: {n_pass} passed, {n_fail} failed, {len(results)} total")

    if args.output:
        fieldnames = ["name", "num_channels", "descriptors", "total_bytes",
                      "cycles", "seconds", "throughput_MBps",
                      "pass", "timeout"]
        with open(args.output, "w", newline="") as f:
            w = csv.DictWriter(f, fieldnames=fieldnames)
            w.writeheader()
            for r in results:
                w.writerow(r)
        print(f"Wrote {args.output}")

    return 0 if n_fail == 0 else 3


if __name__ == "__main__":
    sys.exit(main())
