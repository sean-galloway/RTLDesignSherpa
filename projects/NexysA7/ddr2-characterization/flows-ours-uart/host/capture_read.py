#!/usr/bin/env python3
"""Headless ILA capture orchestrator for the DDR2 char harness.

Coordinates the two processes an ILA capture needs:
  1. Vivado hw_manager (tcl/capture_ila.tcl): programs the ILA bitstream,
     arms the ILA (trigger = dfi_rddata_valid), waits, uploads to a CSV.
  2. The UART host: once the ILA is armed, drive a write-then-read so the
     read data returning from the a7ddrphy trips the trigger.

Run (needs env_python for REPO_ROOT + Vivado on PATH):
    python3 host/capture_read.py [--port /dev/ttyUSB2] [--out reports/ila_capture.csv]

Then inspect the CSV: what does dfi_rddata carry vs the write pattern?
  - stable value tracking the write pattern  -> writes land; read capture off
  - stable garbage / zeros                    -> writes not landing (analog wr)
  - varying between reads                      -> read capture metastable
"""
import argparse
import os
import subprocess
import sys
import time

_REPO = os.environ["REPO_ROOT"]
_SELF = os.path.join(_REPO, "projects/NexysA7/ddr2-characterization/flows-ours-uart")
sys.path.insert(0, os.path.join(_SELF, "host"))

import ddr2_char as dc                      # noqa: E402
from ddr2_char import DDR2CharDriver        # noqa: E402
from pumice_master import wait_engine       # noqa: E402

SEED = 0xA5A5_1234


def drive_reads(port, baud):
    """Pre-pull config, write a known pattern, then read it repeatedly so the
    ILA (armed on dfi_rddata_valid) captures a read return window."""
    d = DDR2CharDriver(port=port, baudrate=baud)
    print(f"[uart] BUILD_ID=0x{d.build_id():08X} cmd_delay={d.get_dfi_cmd_delay()}",
          flush=True)
    d.soft_reset(); time.sleep(0.01)
    d.set_controller_cfg(memtype=dc.MEMTYPE_DDR2, t_phy_wrlat=0,
                         t_rddata_en=6, rd_in_order=True)
    d.clear_stats()
    d.program_wr_engine(start_addr=0x0, burst_len=4, txn_count=4, stride_0=32,
                        lfsr_seed=SEED, data_mode=True, hash_seed0=SEED)
    d.start_wr(); wait_engine(d, "wr")
    # Read a few times so there is a read-valid window while the ILA is armed.
    for _ in range(8):
        d.program_rd_engine(start_addr=0x0, burst_len=4, txn_count=4, stride_0=32,
                            lfsr_seed=SEED, data_mode=True, hash_seed0=SEED)
        d.clear_stats(); d.start_rd(); wait_engine(d, "rd")
        time.sleep(0.05)
    print(f"[uart] drove reads; beats_mismatched={d.beats_mismatched()}", flush=True)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--port", default="/dev/ttyUSB2")
    ap.add_argument("--baud", type=int, default=115200)
    ap.add_argument("--out", default=os.path.join(_SELF, "reports/ila_capture.csv"))
    args = ap.parse_args()

    tcl = os.path.join(_SELF, "tcl/capture_ila.tcl")
    vivado = os.environ.get("VIVADO", "vivado")
    proc = subprocess.Popen(
        [vivado, "-mode", "batch", "-notrace", "-source", tcl, "-tclargs", args.out],
        cwd=_SELF, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)

    # Wait for the ILA to be armed before driving traffic.
    armed = False
    for line in proc.stdout:
        sys.stdout.write("[vivado] " + line)
        if "ILA armed" in line:
            armed = True
            break
    if not armed:
        print("ERROR: Vivado did not arm the ILA; see output above.")
        proc.wait(); sys.exit(1)

    time.sleep(1.0)  # let the arm settle
    drive_reads(args.port, args.baud)

    # Drain the rest of Vivado's output (upload + CSV write).
    for line in proc.stdout:
        sys.stdout.write("[vivado] " + line)
    proc.wait()
    print(f"\nCapture CSV: {args.out}")


if __name__ == "__main__":
    main()
