#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""Observer -> tally binning campaign for the observers-only bitstream.

This build arms the two interface OBSERVERS and leaves the in-core monitors
out (they do not fit alongside: 217,761 LUTs vs 203,800 on the xc7k325t).
Each observer's monbus group drives its tally's record port DIRECTLY, so the
tallies are fed by observer packets -- NOT by the agents the older host
scripts program into the CAM, which is why those bin nothing here.

Observer agent ids come from the RTL (axi4_intf_master_observer.sv):
    read  monitors: AGENT_ID = {8'h00, 4'h0, port_index}  -> 0x00 + idx
    write monitors: AGENT_ID = {8'h00, 4'h1, port_index}  -> 0x10 + idx
Both observers use the same scheme, so with one rd and one wr port each the
live agents are 0 (reads) and 16 (writes).

Only classes this build can actually emit are programmed: the harness builds
ERROR / TIMEOUT / COMPL cones, and MON_CTRL enables them at reset. PERF is
enabled here explicitly since its cone is built too.
"""

import argparse
import os
import sys
import time

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)),
                                os.pardir, os.pardir, "bin"))

import stream_env  # noqa: F401,E402  (import side effect: sys.path setup)
from harness_addrs import H, autodetect_port, compose  # noqa: E402
from uart_axi_bridge import UARTAxiBridge  # noqa: E402
from bridge_windows import W                            # noqa: E402
from characterization import CharacterizationRunner, CharConfig  # noqa: E402
from stream_device import build_stream_bus              # noqa: E402
import obs_addrs as OBS                                 # noqa: E402

CAM_CLEAR_OFF, CAM_KEY_OFF, CAM_LOAD_OFF = 0x100, 0x108, 0x110

AGENT_RD, AGENT_WR = 0x00, 0x10        # from the observer RTL, see docstring
PROTO_AXI = 0

# (agent, proto, packet_type, event_code, label) -- ONLY what this build emits.
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
UNEXPECTED = 64          # == N_PROFILE


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


def configure_observers(bridge):
    """Arm BOTH observers. Nothing else in the tree does this."""
    for label, base in (("master", OBS.OBS_APB_BASE),
                        ("slave",  OBS.SLAVE_OBS_APB_BASE)):
        # OBS_CTRL = 0 -> flush watermark 0 (emit every complete record).
        # The default is 16 records, and a short workload never reaches it.
        bridge.write(OBS.O("OBS_CTRL", base), 0)
        # All emittable cones on. Reset already enables ERROR/TIMEOUT/COMPL;
        # PERF is off at reset, and its cone IS built, so turn it on.
        # MONITOR_EN (bit 7) is the runtime arm. Clearing it disarms the tap
        # WITHOUT rebuilding -- which is exactly how to tell "the instrument is
        # stalling the DMA" from "the DMA never launched".
        _mon = 0x9F if os.environ.get("OBS_TAPS", "1") == "1" else 0x1F
        bridge.write(OBS.O("MON_CTRL", base), _mon)
        caps = bridge.read(OBS.O("OBS_CAPS0", base)) or 0
        print(f"  {label:6s} observer caps0=0x{caps:08X} "
              f"cones[err={caps & 1} tmo={(caps >> 1) & 1} compl={(caps >> 2) & 1} "
              f"perf={(caps >> 4) & 1}] taps={(caps >> 6) & 1}")


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
        return _campaign(bridge, args)


def _campaign(bridge, args):
    runner = CharacterizationRunner(bridge, verbose=True)

    tally_rd = {"stream": W("stream_tally")[0], "slave": W("slave_tally")[0]}
    tally_cfg = {"stream": W("stream_tally_cfg")[0], "slave": W("slave_tally_cfg")[0]}
    labels = {i: t[4] for i, t in enumerate(LEGAL)}
    labels[UNEXPECTED] = "UNEXPECTED"

    totals = {k: {} for k in tally_rd}
    for it in range(args.iters):
        # Call the BOARD'S PROGRAM, not a reimplementation of it. run_config
        # is what the cosim runs via tb.run_dma_via_runner(), so sim and
        # silicon exercise the identical sequence -- reset_stream(),
        # load_descriptors(), configure_stream(), setup_timer(), kick, poll.
        # Hand-rolling those steps here is exactly what the cosim comment
        # warns lets sim and silicon diverge with neither side reporting it,
        # and it is what I did: I substituted a harness SOFT_RESET for
        # reset_stream() and a different descriptor loader, then spent a long
        # time concluding the board was broken.
        configure_observers(bridge)
        for k in tally_cfg:
            program_cam(bridge, tally_cfg[k], LEGAL)

        cfg = CharConfig(name=f"obs{it}",
                         num_channels=1,
                         descriptors_per_channel=args.descriptors,
                         transfer_bytes=args.xfer_bytes)
        res = runner.run_config(cfg)
        done = bool(res.get("pass"))
        if not done:
            print(f"      run_config: {dict(list(res.items())[:6])}")

        bridge.write(H("CTRL"), compose("CTRL", FREEZE_TRACE=1))
        time.sleep(0.02)
        for k in tally_rd:
            counts = sweep_dense(bridge, tally_rd[k], len(LEGAL))
            for b, c in counts.items():
                totals[k][b] = totals[k].get(b, 0) + c
            tags = " ".join(f"{labels[b]}={c}" for b, c in sorted(counts.items()))
            print(f"[{it:03d}] {k:6s} pass={done} {tags or '(empty)'}")

    print("\n==== cumulative ====")
    grand = 0
    for k in totals:
        tot = sum(totals[k].values())
        grand += tot
        tags = " ".join(f"{labels[b]}={c}" for b, c in sorted(totals[k].items()))
        print(f"{k:6s} total={tot:>8}  {tags or '(nothing binned)'}")
    print(f"\nTOTAL PACKETS BINNED: {grand}")
    return 0 if grand else 1


if __name__ == "__main__":
    sys.exit(main())
