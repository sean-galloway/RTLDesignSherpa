#!/usr/bin/env python3
"""ADDR_RANGE error-coverage probe for the STREAM monitor tally (board + cosim).

The in-core rd/wr AXI monitors' address-range checker (axi_monitor_addr_check,
built whenever N_ADDR_RANGES>0 -- =4 in this harness, INDEPENDENT of the error
reporter cone) emits an Error/ADDR_RANGE packet (type 0, event 0x0D) whenever an
accepted AR/AW address is OUTSIDE every enabled ERROR-flavored range (an allowlist
MISS). Ranges 2,3 are ERROR-flavored (MON_ADDR_RANGE_IS_ERROR=4'b1100).

This drives every command into a miss (range2 = tiny high window the DMA never
touches) and reads the ADDR_RANGE error back out of the dense tally. It exists as
a dedicated tool because the error is the LOWEST-priority monbus source, so in the
full mon_matrix flow it is starved by completion/timeout traffic unless the DMA
wedges; here the config isolates it for a reliable count.

Validated: cosim dv/tests/test_stream_mon.py (TEST_MISS=1) emits the error in the
integrated design; on the Genesys 2 board this yields wr_err > 0 (type 0 confirmed).

Key config (mirrors run_characterization ENABLE layout -- bit0=ERR_EN):
  ENABLE=0x0F, PKT_MASK=0xFEF0 (allow types 0-3 + 8), range0 match-all (debug),
  range2 = [0xFFFF_FFF0, 0xFFFF_FFFF] (exclude), CTRL=0x75 (r0+r2+CHECK+MATCH+MISS).

Usage:
    source env_python
    python3 host/mon_err_probe.py                 # default 3 chains x 4 desc x 4 KB
    python3 host/mon_err_probe.py --reps 5 --port /dev/ttyUSB1
"""
import argparse
import os
import sys
import time

_here = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.abspath(os.path.join(_here, "..", "..", "flows-stream-bridge", "host")))
sys.path.insert(0, _here)
for up in range(3, 9):
    cand = os.path.join(_here, *([".."] * up), "projects/components/converters/bin")
    if os.path.isdir(cand):
        sys.path.insert(0, cand)
        break

from harness_addrs import H, autodetect_port, compose
from stream_addrs import A
from run_characterization import CharacterizationRunner
from stream_device import build_stream_bus
from uart_axi_bridge import UARTAxiBridge

STREAM_TALLY_RD  = 0x0004_0000
STREAM_TALLY_CFG = 0x0010_0000
CAM_CLEAR, CAM_KEY, CAM_LOAD = 0x100, 0x108, 0x110

# Dense CAM: addrmatch rd/wr (0,1), ADDR_RANGE error rd/wr (2,3), timeout rd/wr (4,5).
CAM = [(9, 0, 8, 0x01), (10, 0, 8, 0x01),
       (9, 0, 0, 0x0D), (10, 0, 0, 0x0D),
       (9, 0, 3, 0x00), (10, 0, 3, 0x00)]
LABELS = ["rd_addrmatch", "wr_addrmatch", "rd_err_addrrange", "wr_err_addrrange",
          "rd_timeout_cmd", "wr_timeout_cmd"]


def _key(ag, pr, ty, ec):
    return ((ag & 0xFFFF) << 16) | ((pr & 0xF) << 12) | ((ty & 0xF) << 8) | (ec & 0xFF)


def program_error_config(br):
    ctrl = 0x01 | (1 << 2) | (1 << 4) | (1 << 5) | (1 << 6)   # r0+r2+CHECK+MATCH+MISS
    for m in ("RDMON", "WRMON"):
        br.write(A(f"{m}_ENABLE"),   0x0F)
        br.write(A(f"{m}_PKT_MASK"), 0xFEF0)
        br.write(A(f"{m}_ADDR_RANGE0_LOW"),  0x0000_0000)
        br.write(A(f"{m}_ADDR_RANGE0_HIGH"), 0xFFFF_FFFF)
        br.write(A(f"{m}_ADDR_RANGE2_LOW"),  0xFFFF_FFF0)
        br.write(A(f"{m}_ADDR_RANGE2_HIGH"), 0xFFFF_FFFF)
        br.write(A(f"{m}_ADDR_RANGE_CTRL"),  ctrl)


def main(argv=None):
    ap = argparse.ArgumentParser(description="STREAM monitor ADDR_RANGE error probe")
    ap.add_argument("--port", default="auto")
    ap.add_argument("--baud", type=int, default=115200)
    ap.add_argument("--reps", type=int, default=3, help="DMA chains launched before freeze")
    ap.add_argument("--ndesc", type=int, default=4)
    ap.add_argument("--bytes", type=int, default=4096)
    args = ap.parse_args(argv)

    port = autodetect_port(args.baud, want=args.port)
    print(f"mon_err_probe: port={port} reps={args.reps} ndesc={args.ndesc} bytes={args.bytes}")
    with UARTAxiBridge(port, args.baud) as br:
        runner = CharacterizationRunner(br)
        br.write(H("CTRL"), compose("CTRL", SOFT_RESET=1)); time.sleep(0.02)
        runner.clear_stats(); runner.set_resp_delay(0, 0)
        runner.configure_stream([0])
        program_error_config(br)

        br.write(STREAM_TALLY_CFG + CAM_CLEAR, 0)
        for i, t in enumerate(CAM):
            br.write(STREAM_TALLY_CFG + CAM_KEY, _key(*t))
            br.write(STREAM_TALLY_CFG + CAM_LOAD, (1 << 31) | i)

        stream = build_stream_bus(br)["stream"]
        os.environ["XFER_BEATS"] = "16"
        done_any = False
        for rep in range(args.reps):
            kick = stream.load_chain(0, num_descriptors=args.ndesc, transfer_bytes=args.bytes)
            runner.setup_timer(args.ndesc * args.bytes)
            runner.kick_channels({0: kick})
            res = runner.poll_completion(timeout_s=20)
            done_any |= bool(res.get("completed"))
            print(f"  rep{rep} DMA done={bool(res.get('completed'))}")

        br.write(H("CTRL"), compose("CTRL", FREEZE_TRACE=1)); time.sleep(0.02)
        counts = {}
        for i, lbl in enumerate(LABELS):
            v = br.read(STREAM_TALLY_RD + i * 8) or 0
            if v:
                counts[lbl] = v
        unexp = br.read(STREAM_TALLY_RD + 64 * 8) or 0
        print("\n=== ADDR_RANGE error tally ===")
        print("  " + ("  ".join(f"{k}={v}" for k, v in counts.items()) or "(no packets)"))
        print(f"  UNEXPECTED={unexp}")
        err = counts.get("rd_err_addrrange", 0) + counts.get("wr_err_addrrange", 0)
        ok = err > 0
        print(f"\nERROR class (type 0 ADDR_RANGE): {'COVERED' if ok else 'NOT SEEN'} "
              f"(total error packets={err})")
        return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
