#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""Observer -> tally binning campaign for the observers-only bitstream (build-obs).

This build arms the two interface OBSERVERS and leaves the in-core monitors
out (they do not fit alongside: 217,761 LUTs vs 203,800 on the xc7k325t).
Each observer's monbus group drives its tally's record port DIRECTLY, so the
tallies are fed by observer packets -- NOT by the in-core monitors the
build-mon host programs arm, which is why those bin nothing here.

Observer agent ids come from the RTL (axi4_intf_master_observer.sv):
    read  monitors: AGENT_ID = {8'h00, 4'h0, port_index}  -> 0x00 + idx
    write monitors: AGENT_ID = {8'h00, 4'h1, port_index}  -> 0x10 + idx
Both observers use the same scheme, so with one rd and one wr port each the
live agents are 0 (reads) and 16 (writes).

Only classes this build can actually emit are keyed, derived per observer at
runtime from that observer's OWN OBS_CAPS0 (BUG-019): the candidates in LEGAL
below are filtered through the register, and MON_CTRL arms exactly the keyed
cones -- arming an unkeyed cone floods UNEXPECTED (measured 2026-10-03: with
the perf cone retired, threshold packets the campaign armed but never keyed
were ~89% of live traffic). On the current lite taps caps bit4/bit5 (perf/
debug) read 0, so the perf candidates drop out and the arm word loses
THRESHOLD/PERF along with them.

Every iteration calls the BOARD'S PROGRAM, CharacterizationRunner.run_config
-- the sequence the cosim runs via tb.run_dma_via_runner(): reset_stream,
load_descriptors, configure_stream, setup_timer, kick, poll, CRC. The
observers and the tally CAM are armed in its pre_kick hook: both sit on the
unit_aresetn line that reset_stream() pulses, so arming them BEFORE the call
(as an earlier version did) is silently undone. Hand-rolling the steps instead
is exactly what lets sim and silicon diverge with neither side reporting it.
"""

import argparse
import os
import sys
import time

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)),
                                os.pardir, os.pardir, "bin"))

import stream_env  # noqa: F401,E402  (import side effect: sys.path setup)
from harness_addrs import H, autodetect_port, compose, describe_build  # noqa: E402
from uart_axi_bridge import UARTAxiBridge  # noqa: E402
from characterization import CharacterizationRunner, CharConfig  # noqa: E402
import obs_addrs as OBS                                 # noqa: E402
import tally                                            # noqa: E402

AGENT_RD, AGENT_WR = 0x00, 0x10        # from the observer RTL, see docstring
PROTO_AXI = 0

# (agent, proto, packet_type, event_code, label) -- the CANDIDATE set. Each
# observer's effective set is this list filtered by its OWN OBS_CAPS0 at
# runtime (see _campaign); packet_type -> required caps state lives in
# obs_addrs.filter_legal_by_caps.
LEGAL = [
    (AGENT_RD, PROTO_AXI, 1, 0,  "rd_compl"),
    (AGENT_WR, PROTO_AXI, 1, 0,  "wr_compl"),
    (AGENT_RD, PROTO_AXI, 0, 0,  "rd_err_slverr"),
    (AGENT_WR, PROTO_AXI, 0, 0,  "wr_err_slverr"),
    (AGENT_RD, PROTO_AXI, 3, 1,  "rd_timeout"),
    (AGENT_WR, PROTO_AXI, 3, 1,  "wr_timeout"),
    (AGENT_RD, PROTO_AXI, 4, 7,  "rd_perf"),
    (AGENT_WR, PROTO_AXI, 4, 7,  "wr_perf"),
]
MON_N_PROFILE = 32          # CAM depth as built; the hardware value overrides


def configure_observers(bridge, arm_by_tally):
    """Arm BOTH observers, each with the MON_CTRL derived from its OWN caps.

    `arm_by_tally` maps tally "stream" -> the master observer and "slave" ->
    the slave observer. MONITOR_EN (bit 7) is the runtime arm: clearing it
    disarms the tap WITHOUT rebuilding -- which is exactly how to tell "the
    instrument is stalling the DMA" from "the DMA never launched" ($OBS_TAPS=0
    exercises that path).
    """
    for tally_key, label, base in (("stream", "master", OBS.OBS_APB_BASE),
                                   ("slave",  "slave",  OBS.SLAVE_OBS_APB_BASE)):
        # OBS_CTRL: FLUSH_WATERMARK at the RDL default (16 beats = 5 raw
        # records per drain cycle).  Watermark 0 (per-record flushes) was
        # tried here too and made no measurable difference to the campaign
        # (amba BUG-039 bring-up, 2026-10-09): the chain ceiling is the
        # record-ingest arbiter's 2-cycles-per-transfer structural rate,
        # and the campaign's offered rate runs ~8% above what the chain
        # sustains during bursts -- the residual shows up as EVENT_DROPPED
        # reports in UNEXPECTED.  The default watermark is kept because it
        # is the intended operating point for long workloads.
        bridge.write(OBS.O("OBS_CTRL", base), 16)
        bridge.write(OBS.O("MON_CTRL", base), arm_by_tally[tally_key])
        caps = OBS.read_caps0(bridge, base)
        print(f"  {label:6s} observer caps0=0x{caps:08X} "
              f"cones[err={caps & 1} tmo={(caps >> 1) & 1} compl={(caps >> 2) & 1} "
              f"thr={(caps >> 3) & 1} perf={(caps >> 4) & 1} dbg={(caps >> 5) & 1} "
              f"ranges={(caps >> 12) & 0xF}] taps={(caps >> 6) & 1}")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--port", default=None)
    ap.add_argument("--iters", type=int, default=20)
    ap.add_argument("--channel", type=int, default=0)
    ap.add_argument("--xfer-bytes", type=int, default=65536)
    ap.add_argument("--descriptors", type=int, default=8)
    args = ap.parse_args()

    port = args.port or autodetect_port()
    with UARTAxiBridge(port, 115200) as bridge:
        print(f"obs_campaign: port={port}  {describe_build(bridge)}")
        return _campaign(bridge, args)


def _campaign(bridge, args):
    runner = CharacterizationRunner(bridge, verbose=True)
    tally_rd, tally_cfg = tally.windows()

    # Derive each observer's effective legal set AND its MON_CTRL arm from its
    # OWN OBS_CAPS0, read live (BUG-019): the lite taps build no perf/debug
    # cone, and the two observers are free to differ (measured 2026-10-03:
    # master 0x42CF vs slave 0x424F). Arm exactly the keyed cones -- arming an
    # unkeyed cone floods UNEXPECTED (threshold packets, measured at ~89% of
    # live traffic once the perf packets that used to dwarf them retired).
    monitor_en = os.environ.get("OBS_TAPS", "1") == "1"
    legal_by_tally, arm_by_tally, retired = {}, {}, {}
    for k, base in (("stream", OBS.OBS_APB_BASE), ("slave", OBS.SLAVE_OBS_APB_BASE)):
        caps = OBS.read_caps0(bridge, base)
        kept, ret = OBS.filter_legal_by_caps(LEGAL, caps)
        legal_by_tally[k] = kept
        arm_by_tally[k] = OBS.mon_ctrl_arm((t[2] for t in kept), monitor_en=monitor_en)
        for t, why in ret:
            retired[t[4]] = why
    for label, why in retired.items():
        print(f"  class retired by caps: {label:<12s} -- {why}")

    unexpected = tally.check_capacity(bridge, tally_cfg["stream"],
                                      legal_by_tally["stream"], MON_N_PROFILE)
    labels_by_tally = {k: tally.labels(legal_by_tally[k], unexpected)
                       for k in legal_by_tally}

    def pre_kick(br):
        configure_observers(br, arm_by_tally)
        for k in tally_cfg:
            tally.program_cam(br, tally_cfg[k], legal_by_tally[k])

    cfg = CharConfig(name="obs", num_channels=1, channels=[args.channel],
                     descriptors_per_channel=args.descriptors,
                     transfer_bytes=args.xfer_bytes)
    totals = {k: {} for k in tally_rd}
    for it in range(args.iters):
        res = runner.run_config(cfg, pre_kick=pre_kick)
        done = bool(res.get("pass"))
        if not done:
            print(f"      run_config: {dict(list(res.items())[:6])}")

        bridge.write(H("CTRL"), compose("CTRL", FREEZE_TRACE=1))
        time.sleep(0.02)
        for k in tally_rd:
            counts = tally.sweep_dense(bridge, tally_rd[k], len(legal_by_tally[k]), unexpected)
            for b, c in counts.items():
                totals[k][b] = totals[k].get(b, 0) + c
            print(f"[{it:03d}] {k:6s} pass={done} {tally.format_counts(counts, labels_by_tally[k])}")

    print("\n==== cumulative ====")
    grand = unexp_total = 0
    for k in totals:
        tot = sum(totals[k].values())
        grand += tot
        unexp_total += totals[k].get(unexpected, 0)
        print(f"{k:6s} total={tot:>8}  {tally.format_counts(totals[k], labels_by_tally[k])}")
    print(f"\nTOTAL PACKETS BINNED: {grand}")
    if unexp_total:
        print(f"UNEXPECTED={unexp_total}: tuples outside the caps-derived legal set "
              f"reached the tallies (the tally's first-event capture identifies "
              f"which). Under BUG-019's re-pin this is a FAIL, not a rounding "
              f"error: arm-what-you-key leaves no legitimate source of "
              f"unexpected packets.")
        return 1
    return 0 if grand else 1


if __name__ == "__main__":
    sys.exit(main())
