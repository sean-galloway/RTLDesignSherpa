#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""ADDR_RANGE error-coverage probe for the STREAM monitor tally (build-mon).

The in-core rd/wr AXI monitors' address-range checker (axi_monitor_addr_check,
built whenever N_ADDR_RANGES>0 -- =4 in this harness, INDEPENDENT of the error
reporter cone) emits an Error/ADDR_RANGE packet (type 0, event 0x0D) whenever an
accepted AR/AW address is OUTSIDE every enabled ERROR-flavored range (an
allowlist MISS). Ranges 2,3 are ERROR-flavored (MON_ADDR_RANGE_IS_ERROR=4'b1100).

This drives every command into a miss (range2 = tiny high window the DMA never
touches) and reads the ADDR_RANGE error back out of the dense tally. It exists
as a dedicated tool because the error is the LOWEST-priority monbus source, so
it is starved by any other class in flight; here the ERROR class alone is keyed
on the datapath monitors, with no match-all range (stream_monitors.arm_addr_ranges
records the measurement: match+miss -> 0 packets, miss alone -> 384).

Each chain is one call to the board's program (run_config); the tally is swept
after every chain because the next run's reset clears it.

Usage:
    source env_python
    python3 host/host_mon_err_probe.py                 # default 3 chains x 4 desc x 4 KB
    python3 host/host_mon_err_probe.py --reps 5 --port /dev/ttyUSB1
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
                             DATAPATH_MONITORS, PKT_ERROR)
import tally  # noqa: E402
from uart_axi_bridge import UARTAxiBridge  # noqa: E402

MON_N_PROFILE = 32

# Dense CAM: addrmatch rd/wr (0,1), ADDR_RANGE error rd/wr (2,3), timeout rd/wr (4,5).
CAM = [(9, 0, 8, 0x01, "rd_addrmatch"), (10, 0, 8, 0x01, "wr_addrmatch"),
       (9, 0, 0, 0x0D, "rd_err_addrrange"), (10, 0, 0, 0x0D, "wr_err_addrrange"),
       (9, 0, 3, 0x00, "rd_timeout_cmd"), (10, 0, 3, 0x00, "wr_timeout_cmd")]


def main(argv=None):
    ap = argparse.ArgumentParser(description="STREAM monitor ADDR_RANGE error probe")
    ap.add_argument("--port", default="auto")
    ap.add_argument("--baud", type=int, default=115200)
    ap.add_argument("--reps", type=int, default=3, help="DMA chains launched")
    ap.add_argument("--ndesc", type=int, default=4)
    ap.add_argument("--bytes", type=int, default=4096)
    args = ap.parse_args(argv)

    port = autodetect_port(args.baud, want=args.port)
    print(f"mon_err_probe: port={port} reps={args.reps} ndesc={args.ndesc} bytes={args.bytes}")
    os.environ["XFER_BEATS"] = "16"
    os.environ["CHAR_POLL_TIMEOUT_S"] = "20"
    with UARTAxiBridge(port, args.baud) as br:
        print(f"  {describe_build(br)}")
        runner = CharacterizationRunner(br)
        rd, cfgw = tally.windows()
        tally_rd, tally_cfg = rd["stream"], cfgw["stream"]
        unexpected = tally.check_capacity(br, tally_cfg, CAM, MON_N_PROFILE)
        labels = tally.labels(CAM, unexpected)

        runner.mon_config = MonitorProgram({PKT_ERROR}, monitors=DATAPATH_MONITORS,
                                           name="err_probe")
        runner.compression = False

        def pre_kick(b):
            runner.set_resp_delay(0, 0)
            arm_addr_ranges(b, "miss")
            route_monbus(b, "stream_tally")
            tally.program_cam(b, tally_cfg, CAM)

        cfg = CharConfig(name="err_probe", num_channels=1, channels=[0],
                         descriptors_per_channel=args.ndesc, transfer_bytes=args.bytes)
        counts = {}
        done_any = False
        for rep in range(args.reps):
            res = runner.run_config(cfg, pre_kick=pre_kick)
            done_any |= bool(res.get("pass"))
            print(f"  rep{rep} DMA pass={bool(res.get('pass'))}")
            br.write(H("CTRL"), compose("CTRL", FREEZE_TRACE=1))
            time.sleep(0.02)
            for b, c in tally.sweep_dense(br, tally_rd, len(CAM), unexpected).items():
                counts[b] = counts.get(b, 0) + c

        print("\n=== ADDR_RANGE error tally ===")
        print("  " + tally.format_counts(counts, labels))
        err = counts.get(2, 0) + counts.get(3, 0)
        ok = err > 0
        print(f"\nERROR class (type 0 ADDR_RANGE): {'COVERED' if ok else 'NOT SEEN'} "
              f"(total error packets={err}; DMA pass on any chain={done_any})")
        return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
