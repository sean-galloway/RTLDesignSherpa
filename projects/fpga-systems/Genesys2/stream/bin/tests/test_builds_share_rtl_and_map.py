# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""The three build flavours differ ONLY in generics and host programming.

perf, obs and mon exist to compare instruments against each other. That
comparison is only meaningful if the thing being instrumented is bit-identical
between them: same RTL, same address map, same top, same constraints. The
moment a flavour compiles a different source set or resolves a different
window, a difference in board behaviour stops being evidence about the
instrument and becomes evidence about the build system.

That is not hypothetical here. A master was removed from the shared bridge
because one flavour had stopped using it; the address map did not move, but
dropping the master rewrote 493 lines of xbar arbitration underneath
stream_desc -- the descriptor fetch path -- and only the flavour built on the
respun xbar hung. One bridge, one harness, one map: the differences live in
the generics and nowhere else.

What has to hold, and none of it checks itself:
    TOP + FILELIST      identical -> identical RTL by construction
    PREBUILD bridge     identical -> one address map, generated once
    instrument generics pinned EXPLICITLY in every flavour, so a change to
                        stream_cfg_pkg's defaults cannot silently re-arm an
                        instrument in a build that never mentions it
"""

import re
from pathlib import Path

import pytest

STREAM_ROOT = Path(__file__).resolve().parents[2]
BUILDS = ("build-perf", "build-obs", "build-mon")

# Knobs that select which instrument a flavour carries. Every flavour must
# state every one of these, even when it is setting the package default.
INSTRUMENT_GENERICS = ("USE_AXI_MONITORS", "OBS_ENABLE_MON_TAPS")

# The design point these three builds are meant to cover: exactly one
# instrument each, and perf carries none.
EXPECTED = {
    "build-perf": {"USE_AXI_MONITORS": "0", "OBS_ENABLE_MON_TAPS": "0"},
    "build-obs": {"USE_AXI_MONITORS": "0", "OBS_ENABLE_MON_TAPS": "1"},
    "build-mon": {"USE_AXI_MONITORS": "1", "OBS_ENABLE_MON_TAPS": "0"},
}


def _makefile(build: str) -> str:
    path = STREAM_ROOT / build / "Makefile"
    assert path.is_file(), f"{build} has no Makefile at {path}"
    return path.read_text()


def _simple_assign(text: str, var: str) -> str | None:
    """Value of `VAR := x` / `VAR ?= x`, ignoring commented-out lines."""
    pat = re.compile(rf"^\s*(?:export\s+)?{re.escape(var)}\s*[:?]?=\s*(.+?)\s*$", re.M)
    for line in text.splitlines():
        if line.lstrip().startswith("#"):
            continue
        m = pat.match(line)
        if m:
            return m.group(1)
    return None


@pytest.mark.parametrize("var", ("TOP", "FILELIST"))
def test_all_builds_compile_the_same_rtl(var):
    """Same top and same filelist => the three flavours compile one design."""
    values = {b: _simple_assign(_makefile(b), var) for b in BUILDS}
    assert all(v is not None for v in values.values()), (
        f"{var} not set in every build: {values}"
    )
    assert len(set(values.values())) == 1, (
        f"the flavours do not share {var}, so they are not the same design:\n"
        + "\n".join(f"  {b}: {v}" for b, v in values.items())
    )


def test_all_builds_share_one_bridge_and_one_address_map():
    """One PREBUILD bridge => one generated map for all three flavours."""
    bridges = {}
    for b in BUILDS:
        prebuild = _simple_assign(_makefile(b), "PREBUILD")
        assert prebuild, f"{b} has no PREBUILD, so its bridge is unpinned"
        names = re.findall(r"regen_bridges\.sh\s+(\S+)", prebuild)
        assert len(names) == 1, f"{b} PREBUILD does not name exactly one bridge: {prebuild}"
        bridges[b] = names[0]

    assert len(set(bridges.values())) == 1, (
        "the flavours generate different bridges, so their address maps can "
        "diverge:\n" + "\n".join(f"  {b}: {n}" for b, n in bridges.items())
    )

    name = next(iter(bridges.values()))
    toml = STREAM_ROOT / "rtl" / "bridges" / "configs" / f"{name}.toml"
    assert toml.is_file(), f"the shared bridge config is missing: {toml}"


@pytest.mark.parametrize("build", BUILDS)
def test_every_flavour_pins_every_instrument_generic(build):
    """A flavour that does not state a knob inherits it from stream_cfg_pkg.

    That is the coupling worth preventing: editing a package default would
    silently change the instrument in a build whose Makefile never mentions
    it, and the bitstream would still look correct.
    """
    text = _makefile(build)
    for var in INSTRUMENT_GENERICS:
        value = _simple_assign(text, var)
        assert value is not None, (
            f"{build}/Makefile does not pin {var}; it would inherit the "
            f"stream_cfg_pkg default instead of stating this flavour's choice"
        )
        assert value == EXPECTED[build][var], (
            f"{build} sets {var}={value}, expected {EXPECTED[build][var]}. "
            f"Each flavour carries exactly one instrument: perf none, "
            f"obs the observers, mon the in-core monitors."
        )


def test_generic_values_carry_no_trailing_whitespace():
    """`?= 8   # note` sets the value to "8   " and Vivado's elaborator hangs.

    The scar is documented in build-perf/Makefile; this keeps it from coming
    back in any flavour.
    """
    for build in BUILDS:
        for var in INSTRUMENT_GENERICS + ("STREAM_NUM_CHANNELS", "MON_N_PROFILE"):
            value = _simple_assign(_makefile(build), var)
            if value is None:
                continue
            assert value == value.strip() and "#" not in value, (
                f"{build}/Makefile {var} has a trailing comment or whitespace "
                f"({value!r}); make keeps it and Vivado spins on the generic"
            )
