#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""Guard: the generated harness regmap must match the hand-written RTL + driver.

`harness_csr.sv` is hand-written; `harness_csr.rdl` is a descriptor of it, from
which `harness_csr_regmap.py` is generated. Nothing enforces they stay in sync,
so this test cross-checks the regmap against two independent sources of truth:

  1. The register offset table in the `harness_csr.sv` header comment (the RTL).
  2. The `<NAME> = 0x..` offset constants in `ddr2_char.py` (the driver), which
     also cover the PHY-CSR window (0x80..0x8C) that the SV header omits.

If this fails, regenerate the regmap from the RDL (see harness_csr.rdl header)
and/or fix whichever source drifted.

    pytest test_harness_regmap_consistency.py -q
"""

import importlib.util
import os
import re
import sys

import pytest

_REPO = os.environ.get("REPO_ROOT")
if not _REPO:
    pytest.skip("REPO_ROOT not set (source env_python)", allow_module_level=True)

_CHAR = os.path.join(_REPO, "projects/NexysA7/ddr2-characterization")
_SV = os.path.join(_CHAR, "ddr2_char_framework/rtl/harness_csr.sv")
_REGMAP = os.path.join(_CHAR, "ddr2_char_framework/dv/tbclasses/harness_csr_regmap.py")

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import ddr2_char as dc  # noqa: E402


def _load_regmap_offsets() -> dict:
    spec = importlib.util.spec_from_file_location("harness_csr_regmap", _REGMAP)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return {name: int(info["offset"], 16) for name, info in mod.top_block.items()}


def _parse_sv_header_offsets() -> dict:
    """Pull `//   0xNN  REG_NAME   RW/R/W ...` rows from the SV header table."""
    row = re.compile(r"^//\s+(0x[0-9A-Fa-f]{2,3})\s+([A-Z][A-Z0-9_]+)\s+(RW|R|W)\b")
    out = {}
    with open(_SV) as f:
        for line in f:
            m = row.match(line.strip() if line.startswith("//") else "\x00")
            if m:
                out[m.group(2)] = int(m.group(1), 16)
    return out


def test_regmap_matches_sv_header():
    regmap = _load_regmap_offsets()
    sv = _parse_sv_header_offsets()
    assert sv, "parsed no registers from harness_csr.sv header — regex/format drift?"
    missing = [n for n in sv if n not in regmap]
    assert not missing, f"registers in SV header but absent from regmap: {missing}"
    mismatched = {n: (hex(sv[n]), hex(regmap[n])) for n in sv if sv[n] != regmap[n]}
    assert not mismatched, f"offset mismatch (sv, regmap): {mismatched}"


def test_regmap_has_phy_csr_window():
    """The driver accesses the indirect PHY-CSR window BY NAME (it holds no
    offset constants — all register access goes through UartRegisterMap). This
    guards that the regmap actually defines that window, which the SV header
    table omits, so the by-name access the driver relies on resolves."""
    regmap = _load_regmap_offsets()
    for phy in ("PHY_CSR_ADDR", "PHY_CSR_WDATA", "PHY_CSR_CTRL", "PHY_CSR_RDATA"):
        assert phy in regmap, f"{phy} missing from harness regmap"


def test_driver_accesses_are_all_by_name():
    """The driver must not carry hardcoded CSR offset constants (everything is
    resolved by name from the regmaps). Any UPPER_CASE int attr on ddr2_char
    that collides with a register name but isn't the regmap offset would be a
    stale hardcoded copy."""
    regmap = _load_regmap_offsets()
    stale = {
        name: val for name, val in vars(dc).items()
        if name in regmap and isinstance(val, int) and not name.startswith("_")
        and val != regmap[name]
    }
    assert not stale, f"stale hardcoded offset constants in ddr2_char: {stale}"


if __name__ == "__main__":
    sys.exit(pytest.main([__file__, "-q"]))
