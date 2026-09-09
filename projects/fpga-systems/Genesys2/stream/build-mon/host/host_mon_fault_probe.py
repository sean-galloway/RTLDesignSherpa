#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""FAULT-INJECTION probe for the STREAM monitor tally (build-mon).

Error/timeout/threshold packets are FAULT conditions -- in correct operation they
never occur, so they cannot be covered by healthy traffic (that is
host_mon_matrix.py's job). This tool is the single place that deliberately
misbehaves the slaves/traffic and checks the monitor catches each fault:

  FAULT               INJECTION                              MONITORS -> tally
  ------------------  -------------------------------------  ----------------------
  no_response  ->     slave holds R/B beats (RESP_DELAY hi)  TIMEOUT  (type 3)
                      past the TIMEOUT window
  slow         ->     slave latency past LATENCY_THRESH but  THRESHOLD(type 2)
                      under TIMEOUT (RESP_DELAY moderate)
  addr_range   ->     access outside the ERROR allowlist     ERROR    (type 0, 0x0D)
                      (range2 exclude window; every cmd miss)

(SLVERR/DECERR error EVENTS need a slave forced to return a bad response; the data
slaves have no such hook today -- a bad-address DECERR responder exists for the
control path -- so that event is a documented extension, not yet injected here.)

Each launch is one call to the board's program (CharacterizationRunner
.run_config); the fault's monitor program is applied inside configure_stream and
its ranges / timeouts / slave delay in pre_kick -- after the reset that clears
them. ENABLE is composed BY FIELD NAME through the regmap (stream_monitors),
never as a hand-assembled bitmask: an earlier version hardcoded the layout from
a stale comment and "enable the threshold cone" quietly enabled something else.

Usage:
    source env_python
    python3 host/host_mon_fault_probe.py                       # all faults
    python3 host/host_mon_fault_probe.py --only addr_range --port /dev/ttyUSB1
"""
import argparse
import os
import sys
import time

_here = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.abspath(os.path.join(_here, "..", "..", "bin")))
import stream_env  # noqa: F401,E402  (import side effect: sys.path setup)
from harness_addrs import H, autodetect_port, compose, build_info, describe_build  # noqa: E402
from characterization import CharacterizationRunner, CharConfig  # noqa: E402
from stream_monitors import (MonitorProgram, route_monbus, arm_addr_ranges,  # noqa: E402
                             set_timeouts, DATAPATH_MONITORS, PKT_ERROR, PKT_COMPL,
                             PKT_THRESHOLD, PKT_TIMEOUT, PKT_ADDRMATCH)
import tally  # noqa: E402
from uart_axi_bridge import UARTAxiBridge  # noqa: E402

MON_N_PROFILE = 32

# Dense CAM: every fault packet gets a bin. Position = dense index.
CAM = [
    (9,  0, 8, 0x01, "rd_addrmatch"),   # 0 rd AddrMatch          (healthy reference)
    (10, 0, 8, 0x01, "wr_addrmatch"),   # 1 wr AddrMatch
    (9,  0, 0, 0x0D, "rd_err"),         # 2 rd ERROR/ADDR_RANGE
    (10, 0, 0, 0x0D, "wr_err"),         # 3 wr ERROR/ADDR_RANGE
    (9,  0, 3, 0x00, "rd_to_cmd"),      # 4 rd TIMEOUT cmd
    (10, 0, 3, 0x00, "wr_to_cmd"),      # 5 wr TIMEOUT cmd
    (9,  0, 3, 0x02, "rd_to_resp"),     # 6 rd TIMEOUT resp
    (10, 0, 3, 0x02, "wr_to_resp"),     # 7 wr TIMEOUT resp
    (9,  0, 2, 0x00, "rd_thresh"),      # 8 rd THRESHOLD active-count
    (10, 0, 2, 0x00, "wr_thresh"),      # 9 wr THRESHOLD active-count
    (9,  0, 2, 0x01, "rd_thresh_lat"),  # 10 rd THRESHOLD latency
    (10, 0, 2, 0x01, "wr_thresh_lat"),  # 11 wr THRESHOLD latency
]
LBL = [t[4] for t in CAM]
# Which dense bins prove each fault class fired.
FAULT_BINS = {
    "no_response": (4, 5, 6, 7),       # any TIMEOUT bin
    "slow":        (8, 9, 10, 11),     # any THRESHOLD bin
    "addr_range":  (2, 3),             # any ERROR bin
}

# The delay faults keep completion + AddrMatch (a match-all DEBUG range0) so
# the healthy reference bins prove traffic flowed, and enable ONLY their own
# cone on top. THRESH_EN is a real field now -- the threshold cone used to be
# gated by PERF_EN, so arming it without PERF_EN produced no packets however
# low LATENCY_THRESH went.
_DELAY_CLASSES = {PKT_COMPL, PKT_ADDRMATCH}


# --- per-fault injection: (MonitorProgram, pre_kick hook) ----------------------
def inject_no_response(runner):
    """Slave holds responses past the timeout window -> TIMEOUT packets.

    UNITS DIFFER: TIMEOUT counts the monitor's 1 us frequency-invariant tick;
    LATENCY_THRESH and set_resp_delay() count raw aclk clocks. This once read
    `TIMEOUT=50` against `resp_delay=500` believing both were clocks -- 50 us
    is 5000 clocks at 100 MHz, ten times the injected stall, so no timeout
    could fire. 2 us (~200 clocks) sits under the 500-clock delay.

    If this produces nothing on a board where host_mon_matrix's addr_error
    (a wedged DMA) does see TIMEOUT, the question is whether
    set_resp_delay(500,500) REALISES 500 clocks on silicon -- measure it with
    the observer latency histogram before touching the monitor."""
    prog = MonitorProgram(_DELAY_CLASSES | {PKT_TIMEOUT}, name="no_response")

    def pre_kick(br):
        arm_addr_ranges(br, "match_all")
        set_timeouts(br, timeout_us=2, latency_thresh_clk=0x0FFF_FFFF)   # thresh quiet
        runner.set_resp_delay(500, 500)                                  # 500 clk >> 2 us
    return prog, pre_kick


def inject_slow(runner):
    """Slave latency past LATENCY_THRESH but under TIMEOUT -> THRESHOLD packets."""
    prog = MonitorProgram(_DELAY_CLASSES | {PKT_THRESHOLD}, name="slow")

    def pre_kick(br):
        arm_addr_ranges(br, "match_all")
        set_timeouts(br, timeout_us=100_000, latency_thresh_clk=20)     # far beyond / trips
        runner.set_resp_delay(200, 200)                                  # 200 clk > 20 clk
    return prog, pre_kick


def inject_addr_range(runner):
    """Every command lands outside the ERROR allowlist -> ADDR_RANGE error.
    ERROR class alone on the datapath monitors, no match-all range: addr_check
    is the lowest-priority monbus source and a simultaneous AddrMatch flood
    starves its own error stream (measured: match+miss 0, miss alone 384)."""
    prog = MonitorProgram({PKT_ERROR}, monitors=DATAPATH_MONITORS, name="addr_range")

    def pre_kick(br):
        arm_addr_ranges(br, "miss")
        runner.set_resp_delay(0, 0)
    return prog, pre_kick


# name -> (inject fn, launches, ndesc, xbytes). Delay faults use a small transfer
# that drains cleanly; addr_range kicks a few larger chains so the low-priority
# miss/error stream stays sustained.
FAULTS = {
    "no_response": (inject_no_response, 1, 2, 2048),
    "slow":        (inject_slow,        1, 2, 2048),
    "addr_range":  (inject_addr_range,  3, 4, 4096),
}


def run_fault(br, runner, name, tally_rd, tally_cfg, unexpected):
    inject, launches, ndesc, xbytes = FAULTS[name]
    os.environ["XFER_BEATS"] = "16"
    os.environ["CHAR_POLL_TIMEOUT_S"] = "20"
    prog, hook = inject(runner)
    runner.mon_config = prog
    runner.compression = False                     # the tally reassembles RAW records

    def pre_kick(b):
        runner.set_resp_delay(0, 0)                # a prior fault's delay must not leak
        route_monbus(b, "stream_tally")
        hook(b)
        tally.program_cam(b, tally_cfg, CAM)

    cfg = CharConfig(name=name, num_channels=1, channels=[0],
                     descriptors_per_channel=ndesc, transfer_bytes=xbytes)
    # Report the DELTA per launch: a fault that wedges the DMA keeps the monbus
    # busy, so a count that survives into the next run cannot be attributed.
    delta = [0] * (len(CAM) + 1)
    for _ in range(launches):
        base = None

        def pre_kick_snap(b, _pk=pre_kick):
            nonlocal base
            _pk(b)
            base = tally.snapshot(b, tally_rd, len(CAM), unexpected)   # after config, before traffic

        runner.run_config(cfg, pre_kick=pre_kick_snap)
        br.write(H("CTRL"), compose("CTRL", FREEZE_TRACE=1))
        time.sleep(0.02)
        fin = tally.snapshot(br, tally_rd, len(CAM), unexpected)
        d = tally.delta(base or [0] * len(fin), fin)
        delta = [x + y for x, y in zip(delta, d)]
    counts = {LBL[i]: delta[i] for i in range(len(LBL)) if delta[i]}
    unexp = delta[len(LBL)]
    caught = sum(delta[b] for b in FAULT_BINS[name])
    return counts, unexp, caught


def main(argv=None):
    ap = argparse.ArgumentParser(description="STREAM monitor fault-injection probe")
    ap.add_argument("--port", default="auto")
    ap.add_argument("--baud", type=int, default=115200)
    ap.add_argument("--only", default=None, help="comma list of fault names")
    args = ap.parse_args(argv)
    only = set(args.only.split(",")) if args.only else set(FAULTS)

    port = autodetect_port(args.baud, want=args.port)
    rc = 0
    with UARTAxiBridge(port, args.baud) as br:
        # ASK THE BOARD which build it is rather than assuming. The error cone
        # and the timeout/threshold cones can be compiled into different
        # bitstreams, and running every fault against either reports some as
        # NOT SEEN -- a bitstream mismatch that reads as a monitor failure.
        info = build_info(br)
        print(f"mon_fault_probe: port={port}  {describe_build(br)}")
        err, main_cones = info["error_flavor"], info["main_cones"]
        if err and main_cones:
            can, why = {"addr_range", "no_response", "slow"}, ""
        elif err:
            can, why = {"addr_range"}, "error-only build: timeout/threshold cones absent"
        else:
            can, why = {"no_response", "slow"}, "all-except-error build: error cone absent"
        skipped = sorted(only - can)
        faults = [f for f in FAULTS if f in only and f in can]
        if skipped:
            print(f"  SKIPPING {', '.join(skipped)} -- {why}")
            print("  (rebuild with MON_ERROR_FLAVOR=2 for a single bitstream covering all of them)")
        print(f"  running: {faults}")
        runner = CharacterizationRunner(br)
        rd, cfgw = tally.windows()
        tally_rd, tally_cfg = rd["stream"], cfgw["stream"]
        unexpected = tally.check_capacity(br, tally_cfg, CAM, MON_N_PROFILE)
        results = {}
        for name in faults:
            counts, unexp, caught = run_fault(br, runner, name, tally_rd, tally_cfg, unexpected)
            results[name] = (counts, unexp, caught)
            tags = " ".join(f"{k}={v}" for k, v in counts.items()) or "(no packets)"
            print(f"  [{name:12s}] caught={caught:<4d} {tags}  UNEXPECTED={unexp}")

        print("\n================ FAULT-INJECTION COVERAGE ================")
        classes = {"no_response": "TIMEOUT (type 3)", "slow": "THRESHOLD (type 2)",
                   "addr_range": "ERROR/ADDR_RANGE (type 0)"}
        # Credit a class if its bins fired in ANY scenario, not only the one
        # meant to provoke it: `no_response` fires the ACTIVE-COUNT threshold
        # while `slow` targets the LATENCY one, so a strictly per-scenario
        # check printed "THRESHOLD NOT SEEN" on a board that had just emitted
        # nine of them. The question is "can the hardware produce this packet
        # class at all"; the scenario it came from is still printed.
        for name in faults:
            bins = FAULT_BINS[name]
            total, where = 0, []
            for sc in faults:
                counts, _, _ = results[sc]
                n = sum(counts.get(LBL[b], 0) for b in bins)
                if n:
                    total += n
                    where.append(f"{sc}={n}")
            ok = total > 0
            rc |= (0 if ok else 1)
            intended = results[name][2] > 0
            note = "" if intended or not ok else "   [not from its own injection]"
            print(f"  {classes[name]:28s} "
                  f"{'COVERED' if ok else 'NOT SEEN'} ({total} packets"
                  + (f": {','.join(where)}" if where else "") + f"){note}")
    return rc


if __name__ == "__main__":
    raise SystemExit(main())
