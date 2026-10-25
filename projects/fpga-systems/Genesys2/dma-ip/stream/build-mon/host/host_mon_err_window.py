#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""Prove the monbus ERROR WINDOW on the BOARD (stream TASK-019).

The CLI half only. The program is bin/mon_err_window.py, which the cosim
(test_stream_mon_err_window) runs over its UART channel with the same code:
Completions routed to the error window, MON_ERR_REC_COUNT against the records
read back out of comp_sram's top 4 KB.

    source env_python
    python3 host/host_mon_err_window.py                       # 4 desc x 16 KB
    python3 host/host_mon_err_window.py --descriptors 8 --bytes 65536 --port /dev/ttyUSB3
"""
import os
import sys

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "..", "bin"))
import stream_env  # noqa: F401,E402  (import side effect: sys.path setup)
from mon_err_window import main  # noqa: E402

if __name__ == "__main__":
    raise SystemExit(main())
