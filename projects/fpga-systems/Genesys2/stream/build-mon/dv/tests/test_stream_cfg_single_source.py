# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""Guard: stream_char_cfg_pkg stays the ONE source of the STREAM geometry.

This suite exists because the geometry had four owners and they disagreed.
Measured 2026-08-25, before the package was widened:

    param                  board   build-mon   build-perf   pkg
    AR/AW_MAX_OUTSTANDING     2         2          16        8 (unread)
    RESP_DELAY_R_CAPACITY   256       512         512      256
    RESP_DELAY_B_CAPACITY    16       512          32       16
    SRAM_DEPTH              256       512         512        -
    DESC_RAM_ENTRIES        256      2048         128        -
    DEBUG_SRAM_WORDS       4096     65536        4096        -

build-perf was therefore characterizing an engine with 8x the outstanding depth
the board builds, and every one of those runs was green. Nothing compared them,
so nothing caught it -- which is the point: a config divergence does not fail a
test, it silently changes what the test means.

These are cheap static checks (no elaboration, no simulator). They fail when
someone reintroduces a literal, not when a value legitimately changes.
"""

import os
import re
import sys

import pytest

_TESTS = os.path.dirname(os.path.abspath(__file__))
_AREA = os.path.abspath(os.path.join(_TESTS, "..", "..", ".."))
for _p in (os.path.join(_AREA, "dv"),):
    if _p not in sys.path:
        sys.path.insert(0, _p)

from stream_cfg import cfg, cfg_int, num_channels  # noqa: E402

_RTL = os.path.join(_AREA, "rtl")
_HARNESS = os.path.join(_RTL, "stream_harness.sv")
_TOP = os.path.join(_RTL, "stream_genesys2_top.sv")

# Geometry that must default from the package in stream_harness, never from a
# literal. Deliberately excludes per-BUILD flavor (USE_AXI_MONITORS,
# DATA_MON_CONE_MODE) and sim-only knobs (FPGA_CLK_HZ, UART_BAUD).
_PKG_BACKED = [
    "DATA_WIDTH",
    "ADDR_WIDTH",
    "NUM_CHANNELS",
    "SRAM_DEPTH",
    "DESC_RAM_ENTRIES",
    "DEBUG_SRAM_WORDS",
    "AR_MAX_OUTSTANDING",
    "AW_MAX_OUTSTANDING",
    "RESP_DELAY_R_CAPACITY",
    "RESP_DELAY_B_CAPACITY",
    "OBS_MAX_TRANSACTIONS",
    "OBS_NUM_BANKS",
    "OBS_USE_WDATA_ORDER_Q",
    "USE_ROW_COL_MAJOR_ADDRESSING",
    "MON_N_PROFILE",
    "GEN_MON",
    "USE_MON_COMPRESSION",
    "USE_MON_HALFBEAT",
]


def _read(path):
    with open(path, encoding="utf-8") as fh:
        return fh.read()


def test_package_parses():
    """stream_cfg.py can still read the package (format has not drifted)."""
    values = cfg()
    assert len(values) >= 18, f"expected the full geometry, parsed {len(values)}"
    # Internal coherence: the response-delay models must not back-pressure the
    # engine, or a perf run measures the model instead of the design.
    ar = cfg_int("CFG_AR_MAX_OUTSTANDING")
    assert cfg_int("CFG_RESP_DELAY_R_CAPACITY") >= ar * 16, (
        "R capacity < outstanding x max_burst -- the modeled memory will "
        "back-pressure and mask the engine"
    )
    assert cfg_int("CFG_RESP_DELAY_B_CAPACITY") >= cfg_int("CFG_AW_MAX_OUTSTANDING"), (
        "B capacity < outstanding -- BRESPs will stall the write path"
    )


@pytest.mark.parametrize("param", _PKG_BACKED)
def test_harness_default_comes_from_package(param):
    """Each geometry parameter defaults from stream_char_cfg_pkg, not a literal."""
    text = _read(_HARNESS)
    m = re.search(
        rf"^\s*parameter\s+(?:int|bit|logic)\s+{param}\s*=\s*(.+?),\s*$",
        text,
        re.MULTILINE | re.DOTALL,
    )
    assert m, f"{param} not found as a parameter in stream_harness.sv"
    default = " ".join(m.group(1).split())
    assert "stream_char_cfg_pkg::" in default, (
        f"stream_harness.{param} defaults to `{default}` instead of the package. "
        "A literal here is invisible to the board top and to every cosim that "
        "does not override it -- which is how sim and silicon drifted apart."
    )


@pytest.mark.parametrize("param", _PKG_BACKED)
def test_board_top_does_not_restate_geometry(param):
    """stream_genesys2_top passes flavor and generics, never a geometry literal."""
    text = _read(_TOP)
    # Only look inside the stream_harness instantiation.
    start = text.index("stream_harness #(")
    body = text[start : text.index(") u_harness", start)]
    body = re.sub(r"//[^\n]*", "", body)  # strip comments

    m = re.search(rf"\.{param}\s*\(\s*([^)]*?)\s*\)", body)
    if m is None:
        return  # inherited from the harness default = the package. Correct.
    value = " ".join(m.group(1).split())
    # If it IS passed, it must be a generic/parameter name or the package --
    # never a bare number.
    assert not re.fullmatch(r"\d+'?[bdh]?[0-9_]*", value), (
        f"stream_genesys2_top passes {param}=({value}) as a literal. Board "
        "geometry belongs in stream_char_cfg_pkg so the cosim builds it too; "
        "this is exactly how AR/AW ended up 2 on silicon and 16 in build-perf."
    )


@pytest.mark.parametrize(
    "path",
    [
        os.path.join(_TESTS, "test_stream_mon.py"),
        os.path.join(_TESTS, "test_stream_mon_perf.py"),
        os.path.join(_AREA, "build-perf", "dv", "tests", "test_stream_perf.py"),
    ],
    ids=["mon", "mon_perf", "perf"],
)
def test_no_cosim_hardcodes_sram_depth(path):
    """The SRAM depth is ONE number: the board's, from the package.

    build-mon and build-perf both used to pin 512 while the board built 256.
    An env A/B override (SIM_SRAM_DEPTH) is fine -- an unset run must land on
    the board's depth, so a bare literal in a parameter dict is not.
    """
    code = "\n".join(re.sub(r"#.*$", "", line) for line in _read(path).splitlines())
    hit = re.search(r"""['"]SRAM_DEPTH['"]\s*:\s*['"]?\d+""", code)
    assert hit is None, (
        f"{os.path.basename(path)} hardcodes {hit.group(0)!r}. SRAM_DEPTH comes "
        f"from CFG_SRAM_DEPTH ({cfg_int('CFG_SRAM_DEPTH')}) so board and sim "
        "build the same memory; use SIM_SRAM_DEPTH for an A/B run instead."
    )


def test_num_channels_is_not_a_python_literal():
    """The TB channel count comes from the package, not a hardcoded default.

    Regression guard: test_stream_mon.py used to hand the testbench
    `rtl_parameters.get('NUM_CHANNELS', 4)` against a dict that never contained
    NUM_CHANNELS, so the TB drove 4 channels of an 8-channel elaboration and
    said nothing.
    """
    assert num_channels() == cfg_int("CFG_NUM_CHANNELS")
    for name in ("test_stream_mon.py", "test_stream_mon_perf.py"):
        # Strip comments first -- the fix is DOCUMENTED in those files by
        # quoting the old expression, and matching that would be a false alarm.
        code = "\n".join(
            re.sub(r"#.*$", "", line) for line in _read(os.path.join(_TESTS, name)).splitlines()
        )
        assert "rtl_parameters.get('NUM_CHANNELS'" not in code, (
            f"{name} reintroduced the get()-with-default channel count"
        )
