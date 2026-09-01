#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway
#
# build-perf/host/host_characterize.py
#
# Sweep DMA configurations on the FPGA and report measured cycles + MB/s
# per run. Reuses the descriptor builder + the CharacterizationRunner from
# bin/characterization.py for the per-test setup; replaces its broken
# CSR_STATUS.irq polling with the new harness timer (CSR_TIMER_*).
#
# Output is a single CSV row per config:
#
#   name, num_channels, descriptors, total_bytes, cycles,
#   seconds, throughput_MBps, pass
#
# USAGE:
#   make host-characterize                                 # default sweep
#   make host-characterize ARGS="--csv csv/sim_suite.csv"  # custom matrix
#   make host-characterize ARGS="--configs 1desc_1ch_4KB --size 4KB"
#   make host-characterize ARGS="--output results.csv"     # log to CSV file

import argparse
import csv
import os
import sys
import time
from typing import Optional

_here = os.path.dirname(os.path.abspath(__file__))
# One bootstrap to reach the area's env module; stream_env owns every other
# path (shared FPGA layer, this area's bin/, this build's host/). Replaces the
# hand-counted walks to a sibling flow and to converters/bin.
sys.path.insert(0, os.path.abspath(os.path.join(_here, "..", "..", "bin")))
import stream_env  # noqa: F401,E402  (import side effect: sys.path setup)

from descriptor_builder import (  # noqa: E402
    DescriptorBuilder, build_char_matrix, load_configs_from_csv,
    _parse_size, _size_label,
    HARNESS_CSR_BASE,
)
from harness_addrs import H, harness_regs  # noqa: E402  (by-name harness CSR access)
from harness_addrs import autodetect_port  # noqa: E402 (shared ttyUSB probe)
import characterization as runner_mod  # noqa: E402  (shared runner, bin/)
from uart_axi_bridge import UARTAxiBridge  # noqa: E402  (shared FPGA layer)

# ---------------------------------------------------------------------------
# Timer CSR map (matches harness_csr.sv 0x28-0x34)
# ---------------------------------------------------------------------------
CSR_TIMER_CTRL          = H("TIMER_CTRL") # W: bit 0 = clear pulse
CSR_TIMER_STATUS        = H("TIMER_STATUS") # R: [0]=done [1]=running [2]=pass
CSR_TIMER_CYCLES_LO     = H("TIMER_CYCLES_LO")
CSR_TIMER_CYCLES_HI     = H("TIMER_CYCLES_HI")
CSR_TIMER_EXPECTED_BEATS = H("TIMER_EXPECTED_BEATS") # RW: stop when sink beat count >= this
CSR_RESP_DELAY           = H("RESP_DELAY") # RW: [15:0]=rd_cyc, [31:16]=wr_cyc

# Per-engine first/last beat cycle stamps (sampled from the same 64-bit
# timer base as CSR_TIMER_CYCLES_*). r2r = R_LAST - R_FIRST, w2w likewise.
CSR_TIMER_R_FIRST_LO     = H("TIMER_R_FIRST_LO")
CSR_TIMER_R_FIRST_HI     = H("TIMER_R_FIRST_HI")
CSR_TIMER_R_LAST_LO      = H("TIMER_R_LAST_LO")
CSR_TIMER_R_LAST_HI      = H("TIMER_R_LAST_HI")
CSR_TIMER_W_FIRST_LO     = H("TIMER_W_FIRST_LO")
CSR_TIMER_W_FIRST_HI     = H("TIMER_W_FIRST_HI")
CSR_TIMER_W_LAST_LO      = H("TIMER_W_LAST_LO")
CSR_TIMER_W_LAST_HI      = H("TIMER_W_LAST_HI")


def _read64(bridge, lo_addr: int, hi_addr: int) -> int:
    lo = bridge.read(lo_addr) or 0
    hi = bridge.read(hi_addr) or 0
    return (hi << 32) | lo

CLK_PERIOD_NS = 10.0  # 100 MHz aclk
# 128 b data path -> 16 B per beat, the current build. Overwritten at runtime
# from BUILD_CONFIG.DATA_WIDTH_B so the beat/throughput maths follows whatever
# the bitstream was actually built with rather than this literal.
DATA_WIDTH_BYTES = 16


def run_one(runner, bridge, cfg, timeout_s: float, verbose: bool) -> dict:
    """Run a single test config and return measurement results."""
    test = runner.builder.build_test(cfg)
    total_bytes = test["total_bytes"]
    expected_beats = total_bytes // DATA_WIDTH_BYTES

    # Clear the timer and program the expected beat count for the stop
    # trigger BEFORE clearing the slave CRC stats — once a clear-stats
    # pulse fires, the slave's beat counter resets to 0, so any timer
    # bookkeeping that depended on a non-zero count would be invalidated.
    harness_regs(bridge).TIMER_CTRL.write(CLEAR=1)
    bridge.write(CSR_TIMER_EXPECTED_BEATS, expected_beats)

    # Existing per-test setup: load descriptors, configure STREAM.
    runner.clear_stats()
    runner.load_descriptors(test["descriptor_writes"])
    runner.configure_stream(list(range(cfg.num_channels)))

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

    # A timeout is the ONE moment the board's state is worth reading, and the
    # only moment it is still the failing state: re-running or reprogramming to
    # investigate later returns stale counters and sticky bits belonging to a
    # different attempt. Every register below is already implemented and
    # already read by host_status.py -- printing "TIMEOUT" and discarding them
    # cost a full debug cycle on exactly this test.
    print(f"  !! {cfg.name} TIMED OUT -- dumping board state at failure:")
    try:
        from host_status import dump_status
        dump_status(bridge)
    except Exception as e:                     # diagnostics must never mask
        print(f"  (status dump unavailable: {e})")   # the original failure

    # Bus meters too: the status registers say WHAT stopped, the meters say
    # WHY -- productive vs backpressure vs starvation vs idle. Reading them
    # here is the only chance to see the split for the FAILING window; the
    # window is one-shot and a later read gets whatever the next run leaves.
    try:
        from bus_meters import read_bus_meters, format_snapshot, close_windows
        close_windows(bridge)          # freeze, or the read races the design
        format_snapshot(read_bus_meters(bridge, cfg.num_channels))
    except Exception as e:
        print(f"  (bus meters unavailable: {e})")

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
    p.add_argument("--port", default='auto')
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
    p.add_argument("--resp-delays", default=None,
                   help="Delay sweep BY NAME (fine|coarse|knee, see "
                        "characterization.DELAY_SWEEPS) or an explicit "
                        "'0,16,32,...' list. Runs every config once per point "
                        "in ONE UART session. Use --json-output to name the "
                        "analysis-ready JSON file.")
    p.add_argument("--resp-delays-wr", default=None,
                   help="Write-side delay points, paired index-wise with "
                        "--resp-delays. Omit for a symmetric (rd=wr) sweep.")
    p.add_argument("--json-output", default=None,
                   help="Write results as JSON in the schema "
                        "bin/plot_char_reports.py consumes: "
                        "[{rd_delay,wr_delay,config,result}, ...]. The CSV "
                        "--output is unchanged and can be used alongside.")
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
        delay_word = (rd_delay, wr_delay)   # programmed BY FIELD NAME below

    print(f"Sweeping {len(configs)} configurations on {args.port}")
    if delay_word is not None:
        print(f"Response-delay programming: rd={rd_delay} cyc, "
              f"wr={wr_delay} cyc (RESP_DELAY.RD_DELAY/WR_DELAY)")
    print()
    results = []
    json_records = []
    args.port = autodetect_port(args.baud, want=args.port)
    with UARTAxiBridge(args.port, args.baud) as bridge:
        # Ask the board its datapath width instead of asserting 128. Every beat
        # count and MB/s below is scaled by it, so a mismatch between this
        # literal and the bitstream silently rescales every number reported --
        # and a wrong throughput figure looks exactly like a real one.
        global DATA_WIDTH_BYTES
        from characterization import data_width_bytes
        DATA_WIDTH_BYTES = data_width_bytes(bridge)
        if DATA_WIDTH_BYTES != 16:
            print(f"  datapath width from board: {DATA_WIDTH_BYTES} B/beat "
                  f"({DATA_WIDTH_BYTES*8} b)")
        runner = runner_mod.CharacterizationRunner(
            bridge, data_width=DATA_WIDTH_BYTES * 8, verbose=args.verbose)
        if not runner.ping():
            print("ERROR: harness ping failed.", file=sys.stderr)
            return 2

        # Program response-delay CSR once up front; it persists across
        # configs in the sweep (the harness only resets it on aresetn).
        if delay_word is not None:
            # BY NAME, not a hand-packed word. This used to be
            # ((wr & 0xFFFF) << 16) | (rd & 0xFFFF) -- the regmap already
            # defines RESP_DELAY.RD_DELAY[15:0] / WR_DELAY[31:16], and
            # restating the layout here is how the two drift apart silently.
            harness_regs(bridge).RESP_DELAY.write(
                RD_DELAY=delay_word[0] & 0xFFFF, WR_DELAY=delay_word[1] & 0xFFFF)

        # Tag every result with the delay programming so the CSV can carry
        # bandwidth-vs-delay context per row. Default 0 when no flag was given.
        rd_tag = rd_delay if rd_delay is not None else 0
        wr_tag = wr_delay if wr_delay is not None else 0

        # Delay points to sweep. Without --resp-delays this is the single
        # (possibly None) point the old flags gave, so behaviour is unchanged.
        if args.resp_delays:
            rd_points = runner_mod.resolve_delay_sweep(args.resp_delays)
            if args.resp_delays_wr:
                wr_points = runner_mod.resolve_delay_sweep(args.resp_delays_wr)
                if len(wr_points) != len(rd_points):
                    print("ERROR: --resp-delays-wr must pair index-wise with "
                          "--resp-delays", file=sys.stderr)
                    return 1
            else:
                wr_points = list(rd_points)
            print(f"=== RESP_DELAY sweep: {len(rd_points)} points x "
                  f"{len(configs)} configs = {len(rd_points)*len(configs)} runs ===\n")
        else:
            rd_points, wr_points = [rd_tag], [wr_tag]

        total = len(rd_points) * len(configs)
        n = 0
        for rd_pt, wr_pt in zip(rd_points, wr_points):
            if args.resp_delays:
                # Same by-name write as above; the regmap owns the layout.
                harness_regs(bridge).RESP_DELAY.write(
                    RD_DELAY=rd_pt & 0xFFFF, WR_DELAY=wr_pt & 0xFFFF)
                time.sleep(0.005)   # let it propagate before the next run
            for cfg in configs:
                n += 1
                print(f"[{n}/{total}] {cfg.name}"
                      + (f"  rd_delay={rd_pt} wr_delay={wr_pt}" if args.resp_delays else ""))
                r = run_one(runner, bridge, cfg, args.timeout, args.verbose)
                r["rd_delay_cyc"] = rd_pt
                r["wr_delay_cyc"] = wr_pt
                results.append(r)
                json_records.append({"config": cfg.name, "rd_delay": rd_pt,
                                     "wr_delay": wr_pt, "result": r})
                print(fmt_row(r))

    # Summary
    if args.json_output and json_records:
        import json as _json
        with open(args.json_output, "w") as jf:
            _json.dump(json_records, jf, indent=2, default=str)
        print(f"JSON results -> {args.json_output} ({len(json_records)} record(s))")

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
