#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""Measure MonBus bulk-trace compression on the BOARD.

The CLI half only. The program is bin/mon_compress.py, which the cosim
(test_stream_mon_compress) runs over its UART channel with the same code.

    source env_python
    python3 host/host_mon_compress.py                       # 4 desc x 16 KB
    python3 host/host_mon_compress.py --descriptors 8 --bytes 65536 --port /dev/ttyUSB1
"""
import os
import sys

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "..", "bin"))
import stream_env  # noqa: F401,E402  (import side effect: sys.path setup)
from mon_compress import main  # noqa: E402

if __name__ == "__main__":
    raise SystemExit(main())
