#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""Long monitor packet-coverage soak on the board (build-mon), CAM-tally model.

The tally is the CAM-always dense histogram: the legal-set CAM routes each
monbus packet's {agent,protocol,pkt_type,event_code} tuple to a DENSE bin (its
position in the loaded legal set), or to the single UNEXPECTED bin on a miss.
So coverage = "load the tuples you want to watch into the CAM, run traffic, read
the dense bins." A bin > 0 means that exact tuple was observed on silicon; the
UNEXPECTED bin counts every packet NOT in the loaded set (proof that other
traffic is flowing, even before its exact tuple is enumerated here).

Each iteration is one call to the board's program (CharacterizationRunner
.run_config) with the monitor program and the CAM applied inside it -- after
the reset that would otherwise clear them. This file used to route the
monbus to comp_sram while sweeping the tally, so it could never bin anything.

Usage:
    source env_python
    python3 host/host_mon_coverage.py --minutes 10
    python3 host/host_mon_coverage.py --iters 200 --port /dev/ttyUSB1
"""
import argparse
import os
import sys
import time

_here = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.abspath(os.path.join(_here, "..", "..", "bin")))
import stream_env  # noqa: F401,E402  (import side effect: sys.path setup)
from harness_addrs import H, autodetect_port, compose, describe_build  # noqa: E402
from characterization import CharacterizationRunner, CharConfig  # noqa: E402
from stream_monitors import (MonitorProgram, route_monbus, arm_addr_ranges,  # noqa: E402
                             run_perf_windows, PKT_COMPL, PKT_PERF, PKT_ADDRMATCH)
import tally  # noqa: E402

MON_N_PROFILE = 32               # legal-set capacity; the hardware value overrides

# Coverage legal set: (agent, protocol, pkt_type, event_code, label). Dense bin
# index = position here. AXI(proto 0) rd=agent 9 / wr=agent 10; CORE(proto 4)
# scheduler=48 / descriptor-engine=16.
STREAM_LEGAL = [
    (9,  0, 0x8, 0x01, "rd_addrmatch"),
    (10, 0, 0x8, 0x01, "wr_addrmatch"),
    (9,  0, 0x1, 0x00, "rd_completion"),
    (10, 0, 0x1, 0x00, "wr_completion"),
    (9,  0, 0x4, 0x07, "rd_perf"),
    (10, 0, 0x4, 0x07, "wr_perf"),
    (48, 4, 0x1, 0x01, "sched_desc_complete"),
    (16, 4, 0x1, 0x40, "desc_loaded"),
]
CLASSES = {PKT_COMPL, PKT_PERF, PKT_ADDRMATCH}


def run_coverage(bridge, runner, *, channel=0, minutes=10.0, iters=None,
                 xfer_bytes=4096, per_run_timeout_s=15.0):
    rd, cfgw = tally.windows()
    tally_rd, tally_cfg = rd["stream"], cfgw["stream"]
    unexpected = tally.check_capacity(bridge, tally_cfg, STREAM_LEGAL, MON_N_PROFILE)
    labels = tally.labels(STREAM_LEGAL, unexpected)
    os.environ["CHAR_POLL_TIMEOUT_S"] = str(per_run_timeout_s)

    runner.mon_config = MonitorProgram(CLASSES, name="coverage")
    runner.compression = False                     # the tally reassembles RAW records

    def pre_kick(br):
        arm_addr_ranges(br, "match_all")           # every AR/AW emits AddrMatch
        run_perf_windows(br)                       # PERF flows
        route_monbus(br, "stream_tally")
        tally.program_cam(br, tally_cfg, STREAM_LEGAL)

    cfg = CharConfig(name="coverage", num_channels=1, channels=[channel],
                     descriptors_per_channel=2, transfer_bytes=xfer_bytes)
    seen = {}          # dense bin -> cumulative count over the whole soak
    deadline = time.time() + minutes * 60.0
    it = passed = 0
    while (iters is None and time.time() < deadline) or (iters is not None and it < iters):
        res = runner.run_config(cfg, pre_kick=pre_kick)
        done = bool(res.get("pass"))
        # FREEZE for a coherent read boundary; reads are live (no cache).
        bridge.write(H("CTRL"), compose("CTRL", FREEZE_TRACE=1))
        time.sleep(0.02)
        counts = tally.sweep_dense(bridge, tally_rd, len(STREAM_LEGAL), unexpected)
        for b, c in counts.items():
            seen[b] = seen.get(b, 0) + c
        passed += int(done and bool(counts))
        print(f"cov[{it:04d}] pass={done} bins: {tally.format_counts(counts, labels)}")
        it += 1

    print(f"\nmon_coverage: {it} workloads, {passed} with tally hits")
    print("legal-set tuples observed on silicon:")
    for i, (ag, pr, ty, ec, label) in enumerate(STREAM_LEGAL):
        c = seen.get(i, 0)
        print(f"  bin{i:2d} {label:22s} (ag{ag},p{pr},t{ty},e{ec:#04x}): {c}  "
              f"{'OK' if c else 'not seen'}")
    unexp = seen.get(unexpected, 0)
    print(f"  UNEXPECTED (tuples not in the legal set): {unexp}")
    covered = sum(1 for i in range(len(STREAM_LEGAL)) if seen.get(i))
    print(f"\ntuples seen: {covered}/{len(STREAM_LEGAL)}; UNEXPECTED={unexp} "
          f"({'other packets flowing' if unexp else 'none outside the set'})")
    return 0 if passed else 1


def main(argv=None):
    ap = argparse.ArgumentParser(description="STREAM monitor CAM-tally coverage soak")
    ap.add_argument("--port", default="auto")
    ap.add_argument("--baud", type=int, default=115200)
    ap.add_argument("--channel", type=int, default=0)
    ap.add_argument("--minutes", type=float, default=10.0)
    ap.add_argument("--iters", type=int, default=None)
    ap.add_argument("--bytes", type=int, default=4096)
    args = ap.parse_args(argv)

    from uart_axi_bridge import UARTAxiBridge
    port = autodetect_port(args.baud, want=args.port)
    print(f"mon_coverage: port={port} "
          f"{'iters=' + str(args.iters) if args.iters else str(args.minutes) + ' min'}")
    with UARTAxiBridge(port, args.baud) as bridge:
        print(f"  {describe_build(bridge)}")
        runner = CharacterizationRunner(bridge)
        return run_coverage(bridge, runner, channel=args.channel,
                            minutes=args.minutes, iters=args.iters, xfer_bytes=args.bytes)


if __name__ == "__main__":
    raise SystemExit(main())
