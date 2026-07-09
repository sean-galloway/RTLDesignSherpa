#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""Guards for by-name harness CSR access in the STREAM char host tools.

Three checks:
  1. The generated `harness_csr_regmap.py` offsets match the hand-written
     `harness_csr.sv` header table (RDL/RTL/regmap drift guard — mirrors the
     ddr2 test_harness_regmap_consistency.py).
  2. `harness_addrs.H()` + the `harness_regs()` field sugar resolve/round-trip
     correctly against a mock bridge.
  3. NO host tool hardcodes `HARNESS_CSR_BASE + 0x..` register offsets anymore —
     every register is resolved by name from the regmap.

    source env_python && pytest test_harness_regmap.py -q
"""

import glob
import importlib.util
import os
import re
import sys

import pytest

_HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, _HERE)

_REPO = os.environ.get("REPO_ROOT")
if not _REPO:
    pytest.skip("REPO_ROOT not set (source env_python)", allow_module_level=True)

_FW = os.path.join(_REPO, "projects/NexysA7/stream_characterization/stream_char_framework")
_SV = os.path.join(_FW, "rtl/harness_csr.sv")
_REGMAP = os.path.join(_FW, "rtl/harness_csr_regmap.py")

import harness_addrs as ha  # noqa: E402


def _regmap_offsets() -> dict:
    spec = importlib.util.spec_from_file_location("_stream_harness_regmap", _REGMAP)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return {n: int(i["offset"], 16) for n, i in mod.top_block.items()}


def _sv_header_offsets() -> dict:
    row = re.compile(r"^//\s+(0x[0-9A-Fa-f]{2,3})\s+([A-Z][A-Z0-9_]+)\s+(RW|R|W)\b")
    out = {}
    with open(_SV) as f:
        for line in f:
            m = row.match(line.rstrip("\n"))
            if m:
                out[m.group(2)] = int(m.group(1), 16)
    return out


def test_regmap_matches_sv_header():
    regmap = _regmap_offsets()
    sv = _sv_header_offsets()
    assert sv, "parsed no registers from harness_csr.sv header — format drift?"
    missing = [n for n in sv if n not in regmap]
    assert not missing, f"in SV header but absent from regmap: {missing}"
    bad = {n: (hex(sv[n]), hex(regmap[n])) for n in sv if sv[n] != regmap[n]}
    assert not bad, f"offset mismatch (sv, regmap): {bad}"


class _MockBridge:
    def __init__(self):
        self.mem = {}

    def write(self, addr, val):
        self.mem[addr] = val & 0xFFFF_FFFF
        return True

    def read(self, addr):
        return self.mem.get(addr, 0)


def test_H_resolves_absolute_addresses():
    base = ha.HARNESS_CSR_BASE
    assert ha.H("CTRL") == base + 0x00
    assert ha.H("KICK_GO") == base + 0xC0
    # per-channel kick shadow regs encode the split-around-0xC0 layout
    assert ha.H("CH0_KICK_ADDR") == base + 0xB0
    assert ha.H("CH4_KICK_ADDR") == base + 0xC4
    assert ha.H("CH7_KICK_ADDR") == base + 0xD0
    with pytest.raises(KeyError):
        ha.H("NOT_A_REGISTER")


def test_harness_regs_by_name_and_field_sugar():
    b = _MockBridge()
    regs = ha.harness_regs(b)
    # whole-word write by name
    regs.KICK_GO.write_word(0x5)
    assert b.mem[ha.H("KICK_GO")] == 0x5
    # per-channel by name (dynamic name), addresses match H()
    for ch in range(8):
        regs.write_word(f"CH{ch}_KICK_ADDR", 0x1000 + ch)
        assert b.mem[ha.H(f"CH{ch}_KICK_ADDR")] == 0x1000 + ch
    # field-level pulse + read-modify-write preserve the rest of the word
    regs.CTRL.write(START=1)
    assert b.mem[ha.H("CTRL")] & 0x1
    b.mem[ha.H("CTRL")] = 0xF0
    regs.CTRL.CLEAR_STATS = 1                       # RMW one field
    assert b.mem[ha.H("CTRL")] & 0xF0 == 0xF0       # other bits preserved
    # attribute address matches the module-level resolver
    assert regs.addr("KICK_GO") == ha.H("KICK_GO")


def test_no_hardcoded_harness_offsets_in_host_tools():
    """No host .py may compute a register address as HARNESS_CSR_BASE + 0x..
    (the base itself and comments are fine — only offset arithmetic is banned)."""
    offender = re.compile(r"HARNESS_CSR_BASE\s*\+\s*0x[0-9A-Fa-f]+")
    hits = []
    for path in glob.glob(os.path.join(_HERE, "*.py")):
        name = os.path.basename(path)
        if name in ("harness_addrs.py",):   # the resolver is allowed the base
            continue
        for i, line in enumerate(open(path), 1):
            code = line.split("#", 1)[0]     # ignore comments
            if offender.search(code):
                hits.append(f"{name}:{i}: {line.strip()}")
    assert not hits, "hardcoded harness offsets remain:\n" + "\n".join(hits)


if __name__ == "__main__":
    sys.exit(pytest.main([__file__, "-q"]))
