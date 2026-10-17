# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# Where the generator finds the RTL library and its helper tools.
#
# Two homes, one answer per question:
#   - inside an RTL Design Sherpa checkout, everything comes from the tree;
#   - installed from the wheel, from the copies bundled under bridge_pkg/
#     at build time (bridge_pkg/ip/ mirrors the repo-relative layout, so the
#     $REPO_ROOT paths the generator emits resolve against it unchanged).

"""Locate the RDS checkout, the RTL IP root and the bundled helper tools."""

from __future__ import annotations

from pathlib import Path
from typing import Optional

PKG_DIR = Path(__file__).resolve().parent
VENDOR_DIR = PKG_DIR / '_vendor'
BUNDLED_IP_DIR = PKG_DIR / 'ip'


def rds_root() -> Optional[Path]:
    """The RTL Design Sherpa checkout this package runs from, or None.

    Identified by the filelist registry and the amba RTL, not by `.git`: a
    user's own repository also has a `.git`, and treating it as the IP root
    is exactly the confusion this module exists to prevent.
    """
    for candidate in PKG_DIR.parents:
        if (candidate / 'bin' / 'filelists.toml').is_file() and \
                (candidate / 'rtl' / 'amba').is_dir():
            return candidate
    return None


def ip_root() -> Path:
    """The directory to export as REPO_ROOT when compiling a generated bridge."""
    root = rds_root()
    if root is not None:
        return root
    if BUNDLED_IP_DIR.is_dir():
        return BUNDLED_IP_DIR
    raise RuntimeError(
        "No RTL IP root: not running from an RTL Design Sherpa checkout and "
        f"no bundled IP at {BUNDLED_IP_DIR} (the wheel was built without it).")


def regmap_tool() -> Path:
    """bin/peakrdl_generate.py, from the checkout or the bundled copy."""
    root = rds_root()
    tool = (root / 'bin' / 'peakrdl_generate.py') if root is not None \
        else VENDOR_DIR / 'peakrdl_generate.py'
    if not tool.is_file():
        raise RuntimeError(f"peakrdl_generate.py not found at {tool}")
    return tool
