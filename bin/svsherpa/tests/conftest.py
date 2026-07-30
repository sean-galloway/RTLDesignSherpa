# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: svsherpa.tests.conftest
# Purpose: Make the package importable regardless of where pytest is invoked
#
# Documentation: docs/markdown/svsherpa/index.md
# Subsystem: svsherpa
#
# Author: sean galloway
# Created: 2026-07-30
"""Test configuration.

Puts ``bin/`` on the path so ``import svsherpa`` works whether pytest is run
from the repo root, from ``bin/``, or from this directory.
"""

from __future__ import annotations

import shutil
import sys
from pathlib import Path

import pytest

BIN_DIR = Path(__file__).resolve().parents[2]
if str(BIN_DIR) not in sys.path:
    sys.path.insert(0, str(BIN_DIR))


def pytest_configure(config):
    config.addinivalue_line(
        "markers", "toolchain: requires verilator/verible/yosys on PATH"
    )


@pytest.fixture(scope="session")
def has_verilator() -> bool:
    return shutil.which("verilator") is not None


@pytest.fixture(scope="session")
def has_yosys() -> bool:
    return shutil.which("yosys") is not None
