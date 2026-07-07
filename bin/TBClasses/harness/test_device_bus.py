# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""Framework test: the unified by-name multi-IP DeviceBus.

Board-less (mock bridge) proof that the NexysA7 char-harness framework gives
by-name register access to MULTIPLE IP instances -- including several instances
of the SAME IP (two pumice controllers) -- over one bridge, using the real
PeakRDL-generated regmaps. No RTL / cocotb needed.
"""

import os
import sys
from pathlib import Path

import pytest

_REPO = Path(os.environ.get("REPO_ROOT",
                            Path(__file__).resolve().parents[3]))
sys.path.insert(0, str(_REPO / "bin"))

from TBClasses.harness.device import Device, DeviceBus   # noqa: E402

PUMICE_REGMAP = str(_REPO / "projects/components/memory-controllers/"
                    "pumice-ddr2-lpddr2/dv/tbclasses/pumice_regmap.py")
HARNESS_REGMAP = str(_REPO / "projects/NexysA7/ddr2-characterization/"
                     "ddr2_char_framework/dv/tbclasses/harness_csr_regmap.py")


class MockBridge:
    """32-bit word memory implementing the bridge contract
    (read(addr)->int|None, write(addr,val)->bool)."""

    def __init__(self):
        self.mem = {}

    def write(self, addr: int, val: int) -> bool:
        self.mem[addr] = val & 0xFFFF_FFFF
        return True

    def read(self, addr: int):
        return self.mem.get(addr, 0)


def test_device_bus_multiple_pumice():
    """Two pumice instances on one bridge, addressed by name, fully isolated."""
    bus = DeviceBus(MockBridge())
    p0 = bus.add("pumice0", base=0x0000, regmap_file=PUMICE_REGMAP)
    p1 = bus.add("pumice1", base=0x2000, regmap_file=PUMICE_REGMAP)

    # Same register name resolves to different absolute addresses per instance.
    assert p0.addr("DFI_PHASE") == 0x0060
    assert p1.addr("DFI_PHASE") == 0x2060

    # By-name writes to two instances of the SAME IP -- no offsets anywhere.
    bus["pumice0"].write("DFI_PHASE", rd_phase=1, wr_phase=0)
    bus["pumice1"].write("DFI_PHASE", rd_phase=0, wr_phase=2)
    # And a perf-config register by name, per instance.
    bus["pumice0"].write("SCHED_TUNING", force_inorder=1, lookahead_active=0)
    bus["pumice1"].write("SCHED_TUNING", force_inorder=0, lookahead_active=4)

    # Read-back is per-instance and isolated.
    assert bus["pumice0"].field("DFI_PHASE", "rd_phase") == 1
    assert bus["pumice0"].field("DFI_PHASE", "wr_phase") == 0
    assert bus["pumice1"].field("DFI_PHASE", "rd_phase") == 0
    assert bus["pumice1"].field("DFI_PHASE", "wr_phase") == 2
    assert bus["pumice0"].field("SCHED_TUNING", "force_inorder") == 1
    assert bus["pumice1"].field("SCHED_TUNING", "lookahead_active") == 4
    # pumice1's writes did not disturb pumice0's window and vice versa.
    assert bus["pumice0"].field("SCHED_TUNING", "lookahead_active") == 0
    assert bus["pumice1"].field("SCHED_TUNING", "force_inorder") == 0


def test_device_bus_heterogeneous_ip():
    """Different IP (harness_csr + pumice) compose on one bus, by name."""
    bus = DeviceBus(MockBridge())
    bus.add("harness", base=0x0001_0000, regmap_file=HARNESS_REGMAP)
    bus.add("pumice", base=0x0000_0000, regmap_file=PUMICE_REGMAP)

    bus["harness"].write_word("SCRATCH", 0x00C0_FFEE)
    bus["pumice"].write("DFI_PHASE", rd_phase=1)
    assert bus["harness"].read("SCRATCH") == 0x00C0_FFEE
    assert bus["pumice"].field("DFI_PHASE", "rd_phase") == 1
    assert set(bus.names()) == {"harness", "pumice"}
    assert "pumice" in bus and "nope" not in bus


def test_device_bus_subclass_and_dup_guard():
    """A Device subclass adds IP ops; duplicate names are rejected."""
    class Pumice(Device):
        def set_rd_phase(self, phase: int) -> None:
            self.write("DFI_PHASE", rd_phase=phase)

    bus = DeviceBus(MockBridge())
    p = bus.add("pumice0", base=0x0, regmap_file=PUMICE_REGMAP, cls=Pumice)
    p.set_rd_phase(3)
    assert isinstance(bus["pumice0"], Pumice)
    assert bus["pumice0"].field("DFI_PHASE", "rd_phase") == 3

    with pytest.raises(ValueError):
        bus.add("pumice0", base=0x2000, regmap_file=PUMICE_REGMAP)
