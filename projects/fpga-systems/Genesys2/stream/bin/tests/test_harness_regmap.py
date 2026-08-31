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

_FW = os.path.join(_REPO, "projects/fpga-systems/Genesys2/stream")
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
    # NOTE: this test used to pin KICK_GO at base+0xC0 and the per-channel
    # CHn_KICK_ADDR shadows split around it. Commits 9cdd860d / c16b2041
    # retired that whole scheme: harness_csr no longer shadows descriptor
    # addresses, and the launch moved INTO stream (stage CHx_CTRL_LOW, then
    # one write to KICK_ENABLE). Asserting the retired layout was pinning the
    # design we deliberately removed, so the check is re-aimed at what H()
    # actually has to do -- resolve a real register to base + its offset.
    assert ha.has("CTRL")
    assert not ha.has("KICK_GO"), "KICK_GO was retired; see test_harness_kick.py"
    with pytest.raises(KeyError):
        ha.H("NOT_A_REGISTER")


def test_harness_regs_by_name_and_field_sugar():
    b = _MockBridge()
    regs = ha.harness_regs(b)
    # whole-word write by name (CTRL, since KICK_GO was retired)
    regs.CTRL.write_word(0x5)
    assert b.mem[ha.H("CTRL")] == 0x5
    # field-level pulse + read-modify-write preserve the rest of the word
    regs.CTRL.write(START=1)
    assert b.mem[ha.H("CTRL")] & 0x1
    b.mem[ha.H("CTRL")] = 0xF0
    regs.CTRL.CLEAR_STATS = 1                       # RMW one field
    assert b.mem[ha.H("CTRL")] & 0xF0 == 0xF0       # other bits preserved
    # attribute address matches the module-level resolver
    assert regs.addr("CTRL") == ha.H("CTRL")


def test_no_hardcoded_harness_offsets_in_host_tools():
    """No host .py may compute a register address as HARNESS_CSR_BASE + 0x..
    (the base itself and comments are fine — only offset arithmetic is banned)."""
    offender = re.compile(r"HARNESS_CSR_BASE\s*\+\s*0x[0-9A-Fa-f]+")
    hits = []
    for path in glob.glob(os.path.join(_HERE, "*.py")):
        name = os.path.basename(path)
        # harness_addrs.py owns the base constant; test_*.py legitimately
        # compute expected addresses as base + offset.
        if name == "harness_addrs.py" or name.startswith("test_"):
            continue
        for i, line in enumerate(open(path), 1):
            code = line.split("#", 1)[0]     # ignore comments
            if offender.search(code):
                hits.append(f"{name}:{i}: {line.strip()}")
    assert not hits, "hardcoded harness offsets remain:\n" + "\n".join(hits)


if __name__ == "__main__":
    sys.exit(pytest.main([__file__, "-q"]))


# ---------------------------------------------------------------------------
# The guard that actually matters: does the RTL DECODE what the map promises?
# ---------------------------------------------------------------------------

def _sv_decode_offsets() -> set:
    """Every offset harness_csr.sv has a case label for, read or write path.

    Labels are written both 8'hXX (0x000-0x0FF) and 9'hXXX (the 0x100+ meter
    region), so normalise on the hex value rather than the width.
    """
    out = set()
    with open(_SV) as f:
        for m in re.finditer(r"\d'h([0-9A-Fa-f]+)\s*:", f.read()):
            out.add(int(m.group(1), 16))
    return out


def test_every_regmap_register_is_actually_decoded():
    """A register in the map that the RTL does not decode reads back as the
    decoder default -- zero -- with no bus error.

    This is not hypothetical. harness_csr.sv retired the observer's flat
    telemetry window when the observer grew its own regblock, keeping only
    0x120 (the histogram selector). harness_csr_regmap.py kept declaring all
    eleven OBS_* registers. So H("OBS_RD_PROD") answered, the bridge answered,
    the decoder returned 0, and THREE host tools -- bus_meters, ext_char and
    every consumer of their readers -- reported clean, complete, entirely zero
    measurements of a DMA that was moving 1.5 GB/s. Found on silicon
    2026-08-31, not in any test.

    The pre-existing drift guard could not catch it: it compares the regmap to
    the SV HEADER COMMENT table. Both were updated together and both were
    wrong; only the decode was right. Comparing two documents to each other
    passes happily while the hardware disagrees with both.
    """
    regmap = _regmap_offsets()
    decoded = _sv_decode_offsets()
    assert decoded, "parsed no case labels from harness_csr.sv -- format drift?"
    orphans = {n: hex(off) for n, off in regmap.items() if off not in decoded}
    assert not orphans, (
        "declared in harness_csr_regmap.py but NOT decoded by harness_csr.sv -- "
        "these read back 0 with no error:\n  " +
        "\n  ".join(f"{n} @ {o}" for n, o in sorted(orphans.items(),
                                                    key=lambda kv: kv[1])))
