#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""Read the in-core RDMON/WRMON perf windows + per-channel buckets + latency
histograms.

These come from the DUT's OWN monitors, so unlike host_bus_meters this needs a
bitstream built with USE_AXI_MONITORS=1 -- on the perf flavor the windows read
zero because the cones are not compiled in. Use it to cross-check the external
observer against the in-core view on the monitor build; the two measure the
same traffic from opposite sides.

The implementation is `bin/rw_perf.py`, at COMPONENT level because it is a
LIBRARY as well as a program -- host_ext_char and the cosim tests import its
readers. Entry points are `host_*` and live in a build; anything imported by
more than one of them lives in bin/. This file is the CLI half of that split.

Usage:
    make host-rw_perf                 ARGS="--port /dev/ttyUSB1"
"""
import os
import sys

_here = os.path.dirname(os.path.abspath(__file__))
# One bootstrap to reach the area's env module; stream_env owns every other
# path (shared FPGA layer, this area's bin/, this build's host/).
sys.path.insert(0, os.path.abspath(os.path.join(_here, "..", "..", "bin")))
import stream_env  # noqa: F401,E402  (import side effect: sys.path setup)

from rw_perf import main  # noqa: E402

if __name__ == "__main__":
    sys.exit(main())
