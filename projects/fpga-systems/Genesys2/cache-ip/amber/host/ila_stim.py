# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""ILA-capture stimulus for the amber pair-rig Genesys2 bring-up.

Drives the wedge the ILA should snapshot, then exits so the capture tcl can
immediate-trigger:

  injector -- configure + start both cycle injectors; they wedge (busy high,
              done never comes) within seconds on the current board.
  read     -- one CSR read over the UART-AXIL bridge; it never returns
              (the bridge times out and we swallow the IOError).
  both     -- injectors first, then the read attempt.

Writes-only except for the deliberate read attempt, so the script itself
never blocks past the bridge timeout. Transport: the common harness
composition (UartLink -> MarginalUartChannel -> UARTAxiBridge -> AmberDriver);
port is given explicitly because read-based discovery cannot succeed on the
wedged board.
"""

from __future__ import annotations

import logging
import os
import sys
import time

_HERE = os.path.dirname(os.path.abspath(__file__))
_REPO_ROOT = os.path.normpath(os.path.join(_HERE, "..", "..", "..", "..", "..", ".."))
sys.path.insert(0, os.path.join(_HERE, "..", "bin"))
sys.path.insert(0, os.path.join(_REPO_ROOT, "bin"))

import amber_env  # noqa: F401  (path setup)

from amber_board import (AmberDriver, HARNESS_CSR_BASE, build_amber_bridge,
                         build_default_profile, open_amber_link)
from uart_axi_bridge import UARTAxiBridge  # noqa: F401  (composition check)

log = logging.getLogger("ila_stim")


def main(argv=None) -> int:
    argv = list(sys.argv[1:] if argv is None else argv)
    port = argv[0] if len(argv) > 0 else "/dev/ttyUSB1"
    mode = argv[1] if len(argv) > 1 else "both"
    if mode not in ("injector", "read", "both"):
        print("usage: ila_stim.py <port> <injector|read|both>")
        return 2

    link = open_amber_link(port, board_name="genesys2")
    bridge = build_amber_bridge(link)
    drv = AmberDriver(bridge, log=log)

    if mode in ("injector", "both"):
        print("[ila_stim] configuring + starting both cycle injectors")
        drv.clear_and_load_profile(build_default_profile())
        mask = 0x0000_0FFF
        drv.configure_ci("ci0", seed=0x1234_5678, addr_base=0, addr_mask=mask,
                         count=2000, we_mix=64)
        drv.configure_ci("ci1", seed=0xDEAD_BEEF, addr_base=0, addr_mask=mask,
                         count=2000, we_mix=64)
        drv.start_all()
        print("[ila_stim] injectors running; giving them time to wedge")
        time.sleep(3.0)

    if mode in ("read", "both"):
        print("[ila_stim] attempting one CSR read (expected to hang/timeout)")
        try:
            val = bridge.read(HARNESS_CSR_BASE)
            print(f"[ila_stim] UNEXPECTED read success: {val:#x}")
        except (IOError, OSError) as e:
            print(f"[ila_stim] read wedged as expected: {e}")

    print("[ila_stim] stimulus complete; fabric state is frozen for the ILA")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
