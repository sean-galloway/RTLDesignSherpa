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

# The harness clock is a legitimate per-flavour DIFFERENCE -- perf carries no
# instrument so it runs faster -- but it must be STATED. An unpinned clock
# follows the RTL default (1350/15 = 90 MHz), so a build can silently change
# frequency because someone edited a parameter in stream_genesys2_top.
CLOCK_GENERICS = ("STREAM_VCO_MHZ", "STREAM_CLKOUT0_DIVIDE")

EXPECTED_CLOCK_MHZ = {
    "build-perf": 100,
    "build-obs": 90,
    "build-mon": 90,
}

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


@pytest.mark.parametrize("build", BUILDS)
def test_every_flavour_pins_its_clock(build):
    """Frequency is the knob for fitting; an inherited one is not a choice."""
    text = _makefile(build)
    values = {}
    for var in CLOCK_GENERICS:
        raw = _simple_assign(text, var)
        assert raw is not None, (
            f"{build}/Makefile does not pin {var}; it would inherit the "
            f"stream_genesys2_top default (1350/15 = 90 MHz) rather than "
            f"stating the frequency this flavour is built and timed at"
        )
        assert raw.isdigit(), f"{build} {var}={raw!r} is not a plain integer"
        values[var] = int(raw)

    vco, div = values["STREAM_VCO_MHZ"], values["STREAM_CLKOUT0_DIVIDE"]

    assert vco % 25 == 0, (
        f"{build} VCO_MHZ={vco} is not a multiple of 25; MULT_F moves in "
        f"0.125 steps off the 200 MHz sysclk, so the MMCM cannot hit it"
    )
    assert vco % div == 0, (
        f"{build} {vco}/{div} is not an integer frequency"
    )
    assert vco // div == EXPECTED_CLOCK_MHZ[build], (
        f"{build} resolves to {vco // div} MHz, expected "
        f"{EXPECTED_CLOCK_MHZ[build]} MHz"
    )


def test_perf_runs_faster_than_the_instrumented_flavours():
    """perf carries no instrument, so it is the flavour that gets the clock.

    If perf ever drops to the instrumented frequency, either it grew an
    instrument or someone matched the clocks by hand -- both worth a failure
    rather than a silently slower throughput number.
    """
    def mhz(build):
        text = _makefile(build)
        return int(_simple_assign(text, "STREAM_VCO_MHZ")) // int(
            _simple_assign(text, "STREAM_CLKOUT0_DIVIDE")
        )

    perf = mhz("build-perf")
    for build in ("build-obs", "build-mon"):
        assert perf > mhz(build), (
            f"build-perf is at {perf} MHz, not above {build}'s {mhz(build)} MHz"
        )


# The instrumentation lists. Everything that is not a bridge belongs to the
# shared one, so a source common to all three flavours is written down once.
_FILELISTS = STREAM_ROOT / "rtl" / "filelists"
_COMMON = "instrumentation_common.f"


@pytest.mark.parametrize("variant", ("instrumentation.f", "instrumentation_mon.f"))
def test_instrumentation_variants_only_add_a_bridge(variant):
    """A per-bridge list may add its bridge and nothing else.

    These two were once identical except for one line -- fourteen duplicated
    entries, the harness registers among them. Adding the generated harness_csr
    regblock meant editing both, and editing only one would have left two builds
    compiling different register sets, silently, because each list is
    internally valid on its own.
    """
    path = _FILELISTS / variant
    assert path.is_file(), f"missing {path}"
    lines = [ln.strip() for ln in path.read_text().splitlines()]
    body = [ln for ln in lines if ln and not ln.startswith("#")]

    assert any(_COMMON in ln for ln in body), (
        f"{variant} does not pull {_COMMON}; the shared sources would be "
        f"written down twice again"
    )
    bridges = [ln for ln in body if "bridges/filelists/" in ln]
    assert len(bridges) == 1, (
        f"{variant} should name exactly one bridge, found {len(bridges)}: "
        f"{bridges}. The two bridges' adapter modules collide by name."
    )
    extra = [ln for ln in body if _COMMON not in ln and "bridges/filelists/" not in ln]
    assert not extra, (
        f"{variant} lists sources of its own: {extra}. Anything shared by the "
        f"flavours belongs in {_COMMON}, not in one variant."
    )


def test_the_harness_registers_are_listed_once():
    """The generated harness_csr regblock lives in the shared list only."""
    hits = {
        f.name: f.read_text().count("harness_csr_regs_top.sv")
        for f in _FILELISTS.glob("instrumentation*.f")
    }
    assert hits.get(_COMMON, 0) >= 1, (
        f"{_COMMON} does not list the generated harness regblock: {hits}"
    )
    dupes = {n: c for n, c in hits.items() if n != _COMMON and c}
    assert not dupes, (
        f"the harness registers are also listed in {dupes} -- they must be in "
        f"ONE list shared by all three builds"
    )
