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
# REPO_ROOT must be set in the environment (source env_python).
_repo_root = os.environ.get("REPO_ROOT")
if not _repo_root:
    raise RuntimeError(
        "REPO_ROOT is not set. Source env_python (or export REPO_ROOT) "
        "before running this script."
    )
sys.path.insert(0, os.path.join(_repo_root, "projects/components/converters/bin"))
from uart_axi_bridge import UARTAxiBridge  # noqa: E402

# ---------------------------------------------------------------------------
# Timer CSR map (matches harness_csr.sv 0x28-0x34)
# ---------------------------------------------------------------------------
CSR_TIMER_CTRL          = HARNESS_CSR_BASE + 0x28  # W: bit 0 = clear pulse
CSR_TIMER_STATUS        = HARNESS_CSR_BASE + 0x2C  # R: [0]=done [1]=running [2]=pass
CSR_TIMER_CYCLES_LO     = HARNESS_CSR_BASE + 0x30
CSR_TIMER_CYCLES_HI     = HARNESS_CSR_BASE + 0x34
CSR_TIMER_EXPECTED_BEATS = HARNESS_CSR_BASE + 0x38  # RW: stop when sink beat count >= this
CSR_RESP_DELAY           = HARNESS_CSR_BASE + 0x3C  # RW: [15:0]=rd_cyc, [31:16]=wr_cyc

# Per-engine first/last beat cycle stamps (sampled from the same 64-bit
# timer base as CSR_TIMER_CYCLES_*). r2r = R_LAST - R_FIRST, w2w likewise.
CSR_TIMER_R_FIRST_LO     = HARNESS_CSR_BASE + 0x40
CSR_TIMER_R_FIRST_HI     = HARNESS_CSR_BASE + 0x44
CSR_TIMER_R_LAST_LO      = HARNESS_CSR_BASE + 0x48
CSR_TIMER_R_LAST_HI      = HARNESS_CSR_BASE + 0x4C
CSR_TIMER_W_FIRST_LO     = HARNESS_CSR_BASE + 0x50
CSR_TIMER_W_FIRST_HI     = HARNESS_CSR_BASE + 0x54
CSR_TIMER_W_LAST_LO      = HARNESS_CSR_BASE + 0x58
CSR_TIMER_W_LAST_HI      = HARNESS_CSR_BASE + 0x5C


def _read64(bridge, lo_addr: int, hi_addr: int) -> int:
    lo = bridge.read(lo_addr) or 0
    hi = bridge.read(hi_addr) or 0
    return (hi << 32) | lo

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
            cycles = _read64(bridge, CSR_TIMER_CYCLES_LO, CSR_TIMER_CYCLES_HI)
            r_first = _read64(bridge, CSR_TIMER_R_FIRST_LO, CSR_TIMER_R_FIRST_HI)
            r_last  = _read64(bridge, CSR_TIMER_R_LAST_LO,  CSR_TIMER_R_LAST_HI)
            w_first = _read64(bridge, CSR_TIMER_W_FIRST_LO, CSR_TIMER_W_FIRST_HI)
            w_last  = _read64(bridge, CSR_TIMER_W_LAST_LO,  CSR_TIMER_W_LAST_HI)

            r2r_cycles = r_last - r_first if r_last >= r_first else 0
            w2w_cycles = w_last - w_first if w_last >= w_first else 0

            seconds      = cycles     * CLK_PERIOD_NS * 1e-9
            r2r_seconds  = r2r_cycles * CLK_PERIOD_NS * 1e-9
            w2w_seconds  = w2w_cycles * CLK_PERIOD_NS * 1e-9

            def _mbps(t): return (total_bytes / t) / (1024 * 1024) if t > 0 else 0.0
            return {
                "name":         cfg.name,
                "num_channels": cfg.num_channels,
                "descriptors":  cfg.descriptors_per_channel,
                "total_bytes":  total_bytes,
                "cycles":       cycles,
                "seconds":      seconds,
                "throughput_MBps": _mbps(seconds),
                "r2r_cycles":      r2r_cycles,
                "r2r_MBps":        _mbps(r2r_seconds),
                "w2w_cycles":      w2w_cycles,
                "w2w_MBps":        _mbps(w2w_seconds),
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
        "r2r_cycles":      None,
        "r2r_MBps":        None,
        "w2w_cycles":      None,
        "w2w_MBps":        None,
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
            f"tot={r['throughput_MBps']:>7.1f}  "
            f"r2r={r['r2r_MBps']:>7.1f}  "
            f"w2w={r['w2w_MBps']:>7.1f} MB/s  "
            f"{'PASS' if r['pass'] else 'FAIL'}")


def parse_args():
    p = argparse.ArgumentParser(
        description="Sweep STREAM DMA configurations on the FPGA and "
                    "measure cycles + throughput via the harness timer.")
    p.add_argument("--port", default="/dev/ttyUSB1")
    p.add_argument("--baud", type=int, default=115200)

    # Two ways to pick configs:
    #   (a) --csv FILE: load a list of named configs from a CSV file
    #   (b) --channels N --descriptors N --size SIZE: build one config inline
    # If none of those are given we fall back to the built-in matrix
    # (filterable with --configs / --channels) for backward compatibility.
    p.add_argument("--csv", default=None,
                   help="Load test configs from CSV (default: built-in matrix)")
    p.add_argument("--configs", nargs="+",
                   help="Run only the named configs from the matrix")
    p.add_argument("--channels", type=int, default=None,
                   help="Number of active channels for this run "
                        "(scalar; combine with --descriptors and --size to "
                        "describe one config without naming a matrix entry)")
    p.add_argument("--descriptors", type=int, default=None,
                   help="Descriptors per channel for this run "
                        "(combine with --channels and --size)")
    p.add_argument("--size", default="1MB",
                   help="Per-descriptor transfer size (e.g. 4KB, 512KB, 1MB). "
                        "Total bytes moved = channels * descriptors * size.")
    p.add_argument("--timeout", type=float, default=60.0,
                   help="Per-test timeout in seconds (default: 60)")
    p.add_argument("--output", "-o", default=None,
                   help="CSV file to record results in. If the file already "
                        "exists, rows are appended (no header rewrite); if "
                        "missing, the file is created with a header. Use the "
                        "same path across multiple invocations to accumulate "
                        "a sweep into one CSV.")
    p.add_argument("--verbose", "-v", action="store_true")
    p.add_argument("--rd-delay", type=int, default=None,
                   help="Read-response per-beat delay in cycles "
                        "(0 = bypass; programs CSR RESP_DELAY[15:0]). "
                        "If --wr-delay is omitted, the same value is used.")
    p.add_argument("--wr-delay", type=int, default=None,
                   help="Write-response per-beat delay in cycles "
                        "(0 = bypass; programs CSR RESP_DELAY[31:16]). "
                        "Defaults to --rd-delay if omitted.")
    return p.parse_args()


def main() -> int:
    args = parse_args()

    # Import here so the CharConfig dataclass is available for the inline
    # build path below.
    from descriptor_builder import CharConfig  # noqa: E402

    # Build config list. Three input modes (in priority order):
    #   1. --csv FILE: explicit list of named configs.
    #   2. --channels + --descriptors: build a single config inline.
    #   3. Otherwise: built-in matrix, filterable with --configs / --channels.
    inline_mode = (args.channels is not None) or (args.descriptors is not None)

    if args.csv:
        configs = load_configs_from_csv(args.csv)
    elif inline_mode:
        if args.channels is None or args.descriptors is None:
            print("ERROR: --channels and --descriptors must be used together.",
                  file=sys.stderr)
            return 1
        xfer_bytes = _parse_size(args.size)
        cfg = CharConfig(
            name=f"{args.descriptors}desc_{args.channels}ch_"
                 f"{_size_label(xfer_bytes)}",
            num_channels=args.channels,
            descriptors_per_channel=args.descriptors,
            transfer_bytes=xfer_bytes,
        )
        configs = [cfg]
    else:
        configs = build_char_matrix(transfer_bytes=_parse_size(args.size))
        if args.configs:
            configs = [c for c in configs if c.name in args.configs]
        # In matrix mode --channels would have already been a list, but
        # we narrowed --channels to a scalar above. If a scalar was given
        # without --descriptors, treat it as a filter.
        if args.channels is not None:
            configs = [c for c in configs if c.num_channels == args.channels]

    if not configs:
        print("No configurations match the filter.", file=sys.stderr)
        return 1

    # Resolve response-delay knobs (per-beat hold cycles on the R / B
    # channels, programmed via CSR RESP_DELAY @ 0x3C). Either flag alone
    # is fine; the other defaults to the first one's value so the common
    # case "I just want N cycles on both" stays one flag.
    rd_delay = args.rd_delay
    wr_delay = args.wr_delay
    if rd_delay is None and wr_delay is None:
        delay_word = None
    else:
        if rd_delay is None:
            rd_delay = wr_delay
        if wr_delay is None:
            wr_delay = rd_delay
        if not (0 <= rd_delay <= 0xFFFF and 0 <= wr_delay <= 0xFFFF):
            print(f"ERROR: --rd-delay/--wr-delay must be in 0..65535",
                  file=sys.stderr)
            return 1
        delay_word = ((wr_delay & 0xFFFF) << 16) | (rd_delay & 0xFFFF)

    print(f"Sweeping {len(configs)} configurations on {args.port}")
    if delay_word is not None:
        print(f"Response-delay programming: rd={rd_delay} cyc, "
              f"wr={wr_delay} cyc (RESP_DELAY=0x{delay_word:08X})")
    print()
    results = []
    with UARTAxiBridge(args.port, args.baud) as bridge:
        runner = runner_mod.CharacterizationRunner(
            bridge, data_width=128, verbose=args.verbose)
        if not runner.ping():
            print("ERROR: harness ping failed.", file=sys.stderr)
            return 2

        # Program response-delay CSR once up front; it persists across
        # configs in the sweep (the harness only resets it on aresetn).
        if delay_word is not None:
            bridge.write(CSR_RESP_DELAY, delay_word)

        # Tag every result with the delay programming so the CSV can carry
        # bandwidth-vs-delay context per row. Default 0 when no flag was given.
        rd_tag = rd_delay if rd_delay is not None else 0
        wr_tag = wr_delay if wr_delay is not None else 0

        for i, cfg in enumerate(configs, 1):
            print(f"[{i}/{len(configs)}] {cfg.name}")
            r = run_one(runner, bridge, cfg, args.timeout, args.verbose)
            r["rd_delay_cyc"] = rd_tag
            r["wr_delay_cyc"] = wr_tag
            results.append(r)
            print(fmt_row(r))

    # Summary
    n_pass = sum(1 for r in results if r["pass"])
    n_fail = len(results) - n_pass
    print(f"\nSummary: {n_pass} passed, {n_fail} failed, {len(results)} total")

    if args.output:
        fieldnames = ["name", "num_channels", "descriptors", "total_bytes",
                      "rd_delay_cyc", "wr_delay_cyc",
                      "cycles",     "seconds",     "throughput_MBps",
                      "r2r_cycles", "r2r_MBps",
                      "w2w_cycles", "w2w_MBps",
                      "pass", "timeout"]
        # Append if the file already has content (so multiple invocations
        # accumulate into one CSV); otherwise create with a header.
        write_header = (not os.path.exists(args.output)) \
                       or (os.path.getsize(args.output) == 0)
        with open(args.output, "a", newline="") as f:
            w = csv.DictWriter(f, fieldnames=fieldnames)
            if write_header:
                w.writeheader()
            for r in results:
                # Subset to declared fields; ignore anything extra.
                w.writerow({k: r.get(k) for k in fieldnames})
        action = "Created" if write_header else "Appended to"
        print(f"{action} {args.output} ({len(results)} row(s))")

    return 0 if n_fail == 0 else 3


if __name__ == "__main__":
    sys.exit(main())
