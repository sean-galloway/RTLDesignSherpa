#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""Per-CLASS packet matrix for the observers-only bitstream.

host_obs_campaign.py proves the tally bins at volume, but it runs ONE
configuration: a clean DMA with every cone enabled. A clean transfer produces
Completion and Perf and nothing else, so of the seven classes the observers can
emit, that campaign exercises two. Error and Timeout sit in its legal set and
bin zero forever; Threshold, AddrMatch and Debug are not in it at all.

This drives one CLASS PER RUN, each with stimulus that actually provokes it.

Why one class per run: the tally is a bounded dense histogram (N_PROFILE bins).
Enabling every cone at once floods it and the counts stop meaning what a test
reads them as -- so each row here enables the cone under test and little else,
and the matrix as a whole covers what a single run cannot.

Classes NOT here, deliberately:
  PerfWin (0xD) and PerfHist (0xE) are defined in monitor_common_pkg but have
  NO RTL emit site anywhere in the tree -- PktTypePerfWin appears only inside a
  comment. They are CSR-readable concepts, not packets. A row for them would
  fail forever and look like a defect.

Three of these rows became possible only recently:
  AddrMatch   needed N_ADDR_RANGES > 0; the checker was compiled out.
  Threshold   needed TAP_ENABLE_THRESHOLD_LOGIC; the reporter was not built.
  Debug       needed TAP_ENABLE_DEBUG_LOGIC; likewise.
  Error/ADDR_RANGE needed ADDR_RANGE_IS_ERROR; every range was DEBUG-flavoured.
"""

import argparse
import os
import sys
import time

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "bin"))
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "..", "bin"))

import stream_env  # noqa: F401,E402
from harness_addrs import H, autodetect_port, compose  # noqa: E402
from uart_axi_bridge import UARTAxiBridge  # noqa: E402
from bridge_windows import W  # noqa: E402
from characterization import CharacterizationRunner  # noqa: E402
from stream_device import build_stream_bus  # noqa: E402
import obs_addrs as OBS  # noqa: E402

CAM_CLEAR_OFF, CAM_KEY_OFF, CAM_LOAD_OFF = 0x100, 0x108, 0x110
AGENT_RD, AGENT_WR = 0x00, 0x10
PROTO_AXI = 0
UNEXPECTED = 64

# MON_CTRL bit positions (obs_regs.rdl)
ERROR_EN, TIMEOUT_EN, COMPL_EN, THRESHOLD_EN = 0, 1, 2, 3
PERF_EN, DEBUG_EN, ADDR_CHECK_EN, MONITOR_EN = 4, 5, 6, 7


def _b(*bits):
    v = 0
    for b in bits:
        v |= (1 << b)
    return v


# name -> (mon_ctrl, cam legal set, range programming, description)
# Each legal entry is (agent, proto, pkt_type, event_code, label).
MATRIX = {
    "compl": (
        _b(COMPL_EN, MONITOR_EN),
        [(AGENT_RD, PROTO_AXI, 1, 0, "rd_compl"),
         (AGENT_WR, PROTO_AXI, 1, 0, "wr_compl")],
        None,
        "one Completion per transaction on a clean DMA",
    ),
    "perf": (
        _b(PERF_EN, MONITOR_EN),
        [(AGENT_RD, PROTO_AXI, 4, 7, "rd_perf"),
         (AGENT_WR, PROTO_AXI, 4, 7, "wr_perf")],
        None,
        "periodic Perf metrics; the highest-rate class by far",
    ),
    "addrmatch": (
        _b(ADDR_CHECK_EN, DEBUG_EN, MONITOR_EN),
        [(AGENT_RD, PROTO_AXI, 8, 0x01, "rd_addrmatch"),
         (AGENT_WR, PROTO_AXI, 8, 0x01, "wr_addrmatch")],
        # range0 DEBUG-flavoured, match-all: every accepted AR/AW is a HIT.
        # AddrMatch rides the DEBUG path, so DEBUG_EN is required, not optional.
        {"range": 0, "low": 0x00000000, "high": 0xFFFFFFFF, "en": 0x1},
        "every AR/AW is a range HIT -> AddrMatch",
    ),
    "error": (
        _b(ADDR_CHECK_EN, ERROR_EN, MONITOR_EN),
        [(AGENT_RD, PROTO_AXI, 0, 0x0D, "rd_err_addrrange"),
         (AGENT_WR, PROTO_AXI, 0, 0x0D, "wr_err_addrrange")],
        # range2 is ERROR-flavoured (ADDR_RANGE_IS_ERROR=4'b1100). Point it at a
        # window the DMA never touches, so EVERY command is an allowlist MISS.
        {"range": 2, "low": 0xFFFF_FFF0, "high": 0xFFFF_FFFF, "en": 0x4},
        "every command MISSES the allowlist -> Error/ADDR_RANGE",
    ),
    "timeout": (
        _b(TIMEOUT_EN, MONITOR_EN),
        [(AGENT_RD, PROTO_AXI, 3, 1, "rd_timeout"),
         (AGENT_WR, PROTO_AXI, 3, 1, "wr_timeout")],
        None,
        "slave response delayed 2048 cyc so transactions genuinely expire",
    ),
    "threshold": (
        _b(THRESHOLD_EN, MONITOR_EN),
        [(AGENT_RD, PROTO_AXI, 2, 0, "rd_threshold"),
         (AGENT_WR, PROTO_AXI, 2, 0, "wr_threshold")],
        None,
        "slave delayed 64 cyc against a 1-cycle latency threshold",
    ),
    "debug": (
        _b(DEBUG_EN, MONITOR_EN),
        [(AGENT_RD, PROTO_AXI, 15, 0, "rd_debug"),
         (AGENT_WR, PROTO_AXI, 15, 0, "wr_debug")],
        None,
        "one Debug packet per (slot, state change)",
    ),
}

# Per-class observer knobs, applied alongside MON_CTRL.
TUNING = {
    # Leave MON_TIMEOUT at its reset value and make the TRAFFIC slow instead --
    # see SLAVE_DELAY below. Shrinking the monitor's own window would prove the
    # comparator fires, not that a real slow slave produces a timeout.
    "threshold": {"MON_LATENCY": 0x0001},  # any measurable latency crosses it
}

# HARNESS response delay (RESP_DELAY @ 0x3C: RD_DELAY[15:0], WR_DELAY[31:16]),
# driving the axi_response_delay blocks in front of the DMA slaves.
#
# This is the honest way to provoke Timeout and Threshold: delay the SLAVE so
# transactions genuinely take a long time, rather than narrowing the monitor's
# window until it complains about normal traffic. The first tests the thing the
# instrument exists to detect; the second tests the comparator.
#
# Cleared back to 0 for every other class so one row's stimulus cannot leak into
# the next -- these persist across a SOFT_RESET's register clear otherwise.
SLAVE_DELAY = {
    "timeout":   (0x0800, 0x0800),   # 2048 cycles: far beyond MON_TIMEOUT's reset
    "threshold": (0x0040, 0x0040),   # 64 cycles: over the latency floor, no timeout
}


def cam_key(agent, proto, ptype, evc):
    return (((agent & 0xFFFF) << 16) | ((proto & 0xF) << 12)
            | ((ptype & 0xF) << 8) | (evc & 0xFF))


def program_cam(bridge, cfg_base, legal):
    bridge.write(cfg_base + CAM_CLEAR_OFF, 0)
    for i, t in enumerate(legal):
        bridge.write(cfg_base + CAM_KEY_OFF, cam_key(*t[:4]))
        bridge.write(cfg_base + CAM_LOAD_OFF, (1 << 31) | i)


def sweep_dense(bridge, rd_base, n_legal):
    counts = {}
    for b in list(range(n_legal)) + [UNEXPECTED]:
        v = bridge.read(rd_base + b * 8) or 0
        if v:
            counts[b] = v
    return counts


def configure_observers(bridge, mon_ctrl, rng, tuning):
    """Arm BOTH observers for ONE class."""
    for base in (OBS.OBS_APB_BASE, OBS.SLAVE_OBS_APB_BASE):
        bridge.write(OBS.O("OBS_CTRL", base), 0)      # flush every record
        for reg, val in (tuning or {}).items():
            bridge.write(OBS.O(reg, base), val)
        if rng is not None:
            n = rng["range"]
            bridge.write(OBS.O(f"ADDR_RANGE{n}_LOW", base), rng["low"])
            bridge.write(OBS.O(f"ADDR_RANGE{n}_HIGH", base), rng["high"])
            bridge.write(OBS.O("ADDR_RANGE_CTRL", base), rng["en"])
        bridge.write(OBS.O("MON_CTRL", base), mon_ctrl)


def run_class(bridge, name, args):
    mon_ctrl, legal, rng, why = MATRIX[name]
    runner = CharacterizationRunner(bridge)
    tally_rd = {"stream": W("stream_tally")[0], "slave": W("slave_tally")[0]}
    tally_cfg = {"stream": W("stream_tally_cfg")[0], "slave": W("slave_tally_cfg")[0]}
    labels = {i: t[4] for i, t in enumerate(legal)}
    labels[UNEXPECTED] = "UNEXPECTED"

    totals = {k: {} for k in tally_rd}
    for _ in range(args.iters):
        bridge.write(H("CTRL"), compose("CTRL", SOFT_RESET=1))
        time.sleep(0.01)
        runner.clear_stats()
        runner.configure_stream([args.channel])
        # AFTER the soft reset: it clears the register blocks, so anything
        # programmed before it is silently lost.
        rd_dly, wr_dly = SLAVE_DELAY.get(name, (0, 0))
        bridge.write(H("RESP_DELAY"), ((wr_dly & 0xFFFF) << 16) | (rd_dly & 0xFFFF))
        configure_observers(bridge, mon_ctrl, rng, TUNING.get(name))
        for k in tally_cfg:
            program_cam(bridge, tally_cfg[k], legal)

        stream = build_stream_bus(bridge)["stream"]
        kick = stream.load_chain(args.channel, num_descriptors=args.descriptors,
                                 transfer_bytes=args.xfer_bytes)
        runner.setup_timer(args.descriptors * args.xfer_bytes)
        runner.kick_channels({args.channel: kick})
        runner.poll_completion(timeout_s=30.0)

        bridge.write(H("CTRL"), compose("CTRL", FREEZE_TRACE=1))
        time.sleep(0.02)
        for k in tally_rd:
            for b, c in sweep_dense(bridge, tally_rd[k], len(legal)).items():
                totals[k][b] = totals[k].get(b, 0) + c

    keyed = sum(v for k in totals for b, v in totals[k].items() if b != UNEXPECTED)
    unexp = sum(totals[k].get(UNEXPECTED, 0) for k in totals)
    detail = ", ".join(f"{labels.get(b, b)}={v}"
                       for k in ("stream",) for b, v in sorted(totals[k].items()))
    status = "OK " if keyed >= args.min_packets else "LOW"
    print(f"  [{status}] {name:<10} keyed={keyed:<9} unexpected={unexp:<7} {detail[:56]}")
    print(f"           {why}")
    return name, keyed, unexp


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--port", default=None)
    ap.add_argument("--iters", type=int, default=3)
    ap.add_argument("--channel", type=int, default=0)
    ap.add_argument("--xfer-bytes", type=int, default=65536)
    ap.add_argument("--descriptors", type=int, default=8)
    ap.add_argument("--min-packets", type=int, default=1000,
                    help="per-class floor for an OK verdict")
    ap.add_argument("--only", nargs="+", choices=sorted(MATRIX),
                    help="run just these classes")
    args = ap.parse_args()

    classes = args.only or list(MATRIX)
    port = args.port or autodetect_port()
    print(f"packet-class matrix: {len(classes)} classes, {args.iters} iterations each")
    print(f"floor for OK: {args.min_packets} packets\n")

    results = []
    with UARTAxiBridge(port, 115200) as bridge:
        for name in classes:
            results.append(run_class(bridge, name, args))

    print("\n==== summary ====")
    ok = [r for r in results if r[1] >= args.min_packets]
    for name, keyed, unexp in results:
        print(f"  {name:<10} {keyed:>9} keyed  {unexp:>7} unexpected")
    print(f"\n{len(ok)}/{len(results)} classes above the {args.min_packets}-packet floor")
    return 0 if len(ok) == len(results) else 1


if __name__ == "__main__":
    sys.exit(main())
