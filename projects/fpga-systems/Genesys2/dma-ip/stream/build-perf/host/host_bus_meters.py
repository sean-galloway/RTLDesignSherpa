#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""Read the axi4_intf_master_observer's 4-bucket bus meters over UART.

The observer taps STREAM's shared read/write AXI masters INLINE and is not
gated by USE_AXI_MONITORS, so these counters are live in the perf flavor --
that is the whole point of this build. Buckets are productive / backpressure /
starvation / idle per direction; the harness auto-windows them (opens on DMA
busy, freezes 16 idle cycles after the last beat) so a read is a clean
per-run measurement rather than a free-running total.

The implementation is `bin/bus_meters.py`, at COMPONENT level because it is a
LIBRARY as well as a program -- host_ext_char and the cosim tests import its
readers. Entry points are `host_*` and live in a build; anything imported by
more than one of them lives in bin/. This file is the CLI half of that split.

Usage:
    make host-bus_meters                 ARGS="--port /dev/ttyUSB1"
"""
import os
import sys

_here = os.path.dirname(os.path.abspath(__file__))
# One bootstrap to reach the area's env module; stream_env owns every other
# path (shared FPGA layer, this area's bin/, this build's host/).
sys.path.insert(0, os.path.abspath(os.path.join(_here, "..", "..", "bin")))
import stream_env  # noqa: F401,E402  (import side effect: sys.path setup)

from bus_meters import main  # noqa: E402

if __name__ == "__main__":
    sys.exit(main())
