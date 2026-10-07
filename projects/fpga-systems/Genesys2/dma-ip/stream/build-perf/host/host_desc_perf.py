#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""Read the descriptor-fetch monitor's perf window.

The descriptor path is the usual suspect when throughput is fine per-burst but
poor per-descriptor: a long chain of small descriptors spends its time in
fetch, not in data movement. Same USE_AXI_MONITORS=1 caveat as host_rw_perf.

The implementation is `bin/desc_perf.py`, at COMPONENT level because it is a
LIBRARY as well as a program -- host_ext_char and the cosim tests import its
readers. Entry points are `host_*` and live in a build; anything imported by
more than one of them lives in bin/. This file is the CLI half of that split.

Usage:
    make host-desc_perf                 ARGS="--port /dev/ttyUSB1"
"""
import os
import sys

_here = os.path.dirname(os.path.abspath(__file__))
# One bootstrap to reach the area's env module; stream_env owns every other
# path (shared FPGA layer, this area's bin/, this build's host/).
sys.path.insert(0, os.path.abspath(os.path.join(_here, "..", "..", "bin")))
import stream_env  # noqa: F401,E402  (import side effect: sys.path setup)

from desc_perf import main  # noqa: E402

if __name__ == "__main__":
    sys.exit(main())
