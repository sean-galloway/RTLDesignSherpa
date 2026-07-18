#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""Board-less proof: the stream char flow composes each regmap as its own Device.

`build_stream_bus()` loads the generated STREAM controller regmap (which already
includes the monitor block @0x1000, instantiated by stream_regs.rdl) and the
harness regmap as SEPARATE named devices over one (mock) bridge -- by name, no
hand-merge. Notably the monitor regs resolve at their CURRENT 0x1000 addresses,
not the stale pre-relocation 0x180.

    source env_python && pytest test_stream_device.py -q
"""

import os
import sys

import pytest

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

if not os.environ.get("REPO_ROOT"):
    pytest.skip("REPO_ROOT not set (source env_python)", allow_module_level=True)

import stream_device as sd  # noqa: E402


class _MockBridge:
    def __init__(self):
        self.mem = {}

    def write(self, addr, val):
        self.mem[addr] = val & 0xFFFF_FFFF
        return True

    def read(self, addr):
        return self.mem.get(addr, 0)


def test_bus_composes_stream_and_harness_by_name():
    bus = sd.build_stream_bus(_MockBridge())
    assert set(bus.names()) == {"stream", "harness"}
    # controller config @ base 0
    assert bus["stream"].addr("SCHED_CONFIG") == sd.STREAM_APB_BASE + 0x204
    # monitor block lives at 0x1000 in the SAME generated stream regmap
    assert bus["stream"].addr("MON_FIFO_STATUS") == sd.STREAM_APB_BASE + 0x1000
    # harness window
    assert bus["harness"].addr("KICK_GO") == sd.HARNESS_CSR_BASE + 0xC0
    assert isinstance(bus["stream"], sd.Stream)


def test_stream_device_by_name_ops():
    b = _MockBridge()
    bus = sd.build_stream_bus(b)
    s = bus["stream"]
    # channel enable is a named RMW field, not a hardcoded mask write
    s.enable_channel(3, True)
    assert s.field("CHANNEL_ENABLE", "CH_EN") & (1 << 3)
    # harness field sugar
    bus["harness"].KICK_GO.write_word(0x5)
    assert b.mem[bus["harness"].addr("KICK_GO")] == 0x5


if __name__ == "__main__":
    sys.exit(pytest.main([__file__, "-q"]))
