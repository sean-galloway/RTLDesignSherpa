# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""Build-local pytest config.

Everything shared with the other build lives in the AREA conftest
(../../../conftest.py) -- log capture, collection guards, the component
dv/tbclasses and bin/ paths, the TEST_LEVEL fixture. Keep this file to what is
specific to build-mon, which is only its own dv/ dir for build-local tbclasses.
"""
import os
import sys


def pytest_configure(config):
    dv_path = os.path.abspath(os.path.join(os.path.dirname(__file__), '..'))
    if dv_path not in sys.path:
        sys.path.insert(0, dv_path)
