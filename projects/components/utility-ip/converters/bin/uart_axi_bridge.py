#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway
"""Compatibility shim -- `uart_axi_bridge` now lives in the shared FPGA layer.

The module moved to `projects/fpga-systems/bin/uart_axi_bridge.py`, next to
`uart_link` and `board`, so the whole host-transport stack sits in one place
instead of being reached by a `sys.path` insert from twenty-odd flows.

This file re-exports it so the not-yet-migrated flows under
`projects/NexysA7/` keep working during the port. There is exactly ONE
implementation; nothing here is a copy, and nothing here should be edited.

New code must not import through this path. Use either:

    from uart_link import open_bridge          # preferred: port discovery too
    from uart_axi_bridge import UARTAxiBridge  # with fpga-systems/bin on path

Delete this shim when `projects/NexysA7/` is retired.
"""

from __future__ import annotations

import os
import sys

_HERE = os.path.dirname(os.path.abspath(__file__))
# converters/bin -> repo root is four levels up.
_ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.dirname(_HERE))))
_SHARED = os.path.join(
    os.environ.get("REPO_ROOT", _ROOT), "projects", "fpga-systems", "bin"
)

if not os.path.isdir(_SHARED):
    raise ImportError(
        f"shared FPGA layer not found at {_SHARED}; set REPO_ROOT to the "
        f"repository root so uart_axi_bridge can be located"
    )
if _SHARED not in sys.path:
    sys.path.insert(0, _SHARED)

# Load the real module by path rather than by name: this file shadows it on
# sys.path for any caller that put converters/bin first, so a plain
# `import uart_axi_bridge` here would re-enter this shim.
#
# It is registered in sys.modules under the CANONICAL name before executing, so
# a later `import uart_axi_bridge` from the shared layer gets this same module
# object. Without that, the two import paths would produce two distinct
# UARTAxiBridge classes and any isinstance check spanning them would fail --
# a trap that only springs once sim and board code meet in one process.
import importlib.util as _ilu  # noqa: E402

_spec = _ilu.spec_from_file_location(
    "uart_axi_bridge", os.path.join(_SHARED, "uart_axi_bridge.py")
)
_impl = _ilu.module_from_spec(_spec)
sys.modules["uart_axi_bridge"] = _impl
_spec.loader.exec_module(_impl)

UARTAxiBridge = _impl.UARTAxiBridge

__all__ = ["UARTAxiBridge"]
