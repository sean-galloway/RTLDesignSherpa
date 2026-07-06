#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""Guard: the generated cdc_demo regmap must match the hand-written RTL.

`cdc_demo_harness.sv` is hand-written; `cdc_demo_csr.rdl` is a descriptor of it,
from which `cdc_demo_csr_regmap.py` is generated. Nothing enforces they stay in
sync, so this test cross-checks the regmap against two independent sources of
truth in the SV:

  1. The GLOBAL register table in the `cdc_demo_harness.sv` header comment.
  2. The per-counter `CTR_OFF_* = 6'hNN` localparams, expanded to the four
     counter blocks at base 0x40 + i*0x40 (regmap keys COUNTER{i}_<NAME>).

If this fails, regenerate the regmap from the RDL (`make regmap`) and/or fix
whichever source drifted.

    pytest test_cdc_demo_regmap_consistency.py -q
"""

import importlib.util
import os
import re
import sys

import pytest

_REPO = os.environ.get("REPO_ROOT")
if not _REPO:
    pytest.skip("REPO_ROOT not set (source env_python)", allow_module_level=True)

_PROJ = os.path.join(_REPO, "projects/NexysA7/cdc_counter_display")
_SV = os.path.join(_PROJ, "rtl/cdc_demo_harness.sv")
_REGMAP = os.path.join(_PROJ, "dv/tbclasses/cdc_demo_csr_regmap.py")

CTR_BASE, CTR_STRIDE, NUM_COUNTERS = 0x40, 0x40, 4

# Map the SV per-counter localparam suffix -> regmap register name.
CTR_OFF_TO_REG = {
    "DIVISOR": "DIVISOR", "INIT": "INIT", "INCREMENT": "INCREMENT",
    "CFG_LOAD": "CFG_LOAD", "HOST_PRESS": "HOST_PRESS", "VALUE": "VALUE",
    "PRESS_CNT": "PRESS_COUNT", "CLK_TICKS": "CTR_CLK_TICKS",
    "CDC_MODE": "CDC_MODE", "AUTO_INC": "AUTO_INC",
}


def _load_regmap_offsets() -> dict:
    spec = importlib.util.spec_from_file_location("cdc_demo_csr_regmap", _REGMAP)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return {name: int(info["offset"], 16) for name, info in mod.top_block.items()}


def _parse_sv_global_offsets() -> dict:
    """Pull `//   0xNN  REG_NAME  RW/R/W ...` rows from the SV header table."""
    row = re.compile(r"^//\s+(0x[0-9A-Fa-f]{2,3})\s+([A-Z][A-Z0-9_]+)\s+(RW|R|W)\b")
    out = {}
    with open(_SV) as f:
        for line in f:
            m = row.match(line.strip() if line.startswith("//") else "\x00")
            if m:
                out[m.group(2)] = int(m.group(1), 16)
    return out


def _parse_sv_ctr_offsets() -> dict:
    """Pull `localparam ... CTR_OFF_NAME = 6'hNN;` from the SV body."""
    pat = re.compile(r"CTR_OFF_([A-Z_]+)\s*=\s*6'h([0-9A-Fa-f]+)")
    out = {}
    with open(_SV) as f:
        for line in f:
            m = pat.search(line)
            if m:
                out[m.group(1)] = int(m.group(2), 16)
    return out


def test_globals_match_sv_header():
    regmap = _load_regmap_offsets()
    sv = _parse_sv_global_offsets()
    assert sv, "parsed no globals from cdc_demo_harness.sv header — format drift?"
    missing = [n for n in sv if n not in regmap]
    assert not missing, f"globals in SV header but absent from regmap: {missing}"
    bad = {n: (hex(sv[n]), hex(regmap[n])) for n in sv if sv[n] != regmap[n]}
    assert not bad, f"global offset mismatch (sv, regmap): {bad}"


def test_per_counter_offsets_match_sv_localparams():
    regmap = _load_regmap_offsets()
    ctr_off = _parse_sv_ctr_offsets()
    assert set(ctr_off) == set(CTR_OFF_TO_REG), (
        f"CTR_OFF_* set drift: SV={sorted(ctr_off)} "
        f"expected={sorted(CTR_OFF_TO_REG)}")
    checked = 0
    for suffix, off in ctr_off.items():
        reg = CTR_OFF_TO_REG[suffix]
        for i in range(NUM_COUNTERS):
            key = f"COUNTER{i}_{reg}"
            assert key in regmap, f"missing regmap key {key}"
            want = CTR_BASE + i * CTR_STRIDE + off
            assert regmap[key] == want, (
                f"{key}: regmap=0x{regmap[key]:X} sv-derived=0x{want:X}")
            checked += 1
    assert checked == NUM_COUNTERS * len(CTR_OFF_TO_REG), checked


if __name__ == "__main__":
    sys.exit(pytest.main([__file__, "-q"]))
