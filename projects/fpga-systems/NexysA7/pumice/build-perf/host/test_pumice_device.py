#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""Board-less proof: the pumice char flow composes each regmap as its own Device.

`build_ddr2_bus()` loads the generated pumice controller regmap and the harness
regmap as SEPARATE named devices over one (mock) bridge -- by name, field sugar,
no hand-merge, no hardcoded offsets.

    source env_python && pytest test_pumice_device.py -q
"""

import os
import sys

import pytest

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

if not os.environ.get("REPO_ROOT"):
    pytest.skip("REPO_ROOT not set (source env_python)", allow_module_level=True)

import pumice_device as pd  # noqa: E402


class _MockBridge:
    def __init__(self):
        self.mem = {}

    def write(self, addr, val):
        self.mem[addr] = val & 0xFFFF_FFFF
        return True

    def read(self, addr):
        return self.mem.get(addr, 0)


def test_bus_composes_pumice_and_harness_by_name():
    bus = pd.build_ddr2_bus(_MockBridge())
    assert set(bus.names()) == {"pumice", "harness"}
    # each regmap at its own window
    assert bus["pumice"].addr("DFI_PHASE") == pd.DDR2_APB_BASE + 0x60
    assert bus["harness"].addr("STATUS") == pd.HARNESS_CSR_BASE + 0x04
    assert isinstance(bus["pumice"], pd.Pumice)


def test_pumice_device_field_ops():
    b = _MockBridge()
    bus = pd.build_ddr2_bus(b)
    p = bus["pumice"]
    p.set_dfi_phase(rd_phase=1, wr_phase=0)
    assert p.field("DFI_PHASE", "rd_phase") == 1
    p.set_page_policy(2)                       # CLOSE, via read-modify-write
    assert p.field("REFRESH_TUNING", "page_policy_or") == 2
    p.set_scheduler(force_inorder=1)
    assert p.field("SCHED_TUNING", "force_inorder") == 1
    # attribute sugar reaches the same word
    b.mem[p.addr("STATUS")] = 1 << 0           # init_done (pumice STATUS bit 0)
    assert p.init_done() is True


if __name__ == "__main__":
    sys.exit(pytest.main([__file__, "-q"]))
