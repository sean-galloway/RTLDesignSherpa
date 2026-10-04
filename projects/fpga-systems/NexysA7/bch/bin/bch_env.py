# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""The one place this area knows where the shared layers are.

Import for its side effect: puts projects/fpga-systems/bin (board registry,
uart_link, uart_axi_bridge, sequence) and this area's build-loop/host (the
driver + programs) on sys.path. Anchors by searching upward for
projects/fpga-systems/bin/uart_link.py, honouring REPO_ROOT first -- never by
counting directory levels (handbook: fpga/cmn-infra/flow-layout).
"""
from __future__ import annotations

import os
import sys

_MARKER = os.path.join("projects", "fpga-systems", "bin", "uart_link.py")


def _repo_root() -> str:
    env = os.environ.get("REPO_ROOT")
    if env and os.path.isfile(os.path.join(env, _MARKER)):
        return env
    here = os.path.dirname(os.path.abspath(__file__))
    while True:
        if os.path.isfile(os.path.join(here, _MARKER)):
            return here
        parent = os.path.dirname(here)
        if parent == here:
            raise RuntimeError("cannot find the repo root (no projects/fpga-systems/bin/uart_link.py above here)")
        here = parent


REPO_ROOT = _repo_root()
os.environ.setdefault("REPO_ROOT", REPO_ROOT)
FPGA_BIN = os.path.join(REPO_ROOT, "projects", "fpga-systems", "bin")
HOST_DIR = os.path.join(REPO_ROOT, "projects", "fpga-systems", "NexysA7", "bch", "build-loop", "host")
for p in (FPGA_BIN, HOST_DIR):
    if p not in sys.path:
        sys.path.insert(0, p)
