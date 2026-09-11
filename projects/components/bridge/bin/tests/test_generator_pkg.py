# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway
#
# Unit tests for the bridge generator Python package (bin/bridge_pkg).
#
# Until now the generator had zero automated coverage — `make test` ran
# --help, and the four hand-written illegal-config fixtures in
# test_configs/ were executed by nothing. These tests are the safety
# net for refactoring the package: config validation (negative +
# positive), and a golden generation smoke that asserts the emitted
# xbar is declaration-order clean and parameterized.
#
# Run:  pytest projects/components/bridge/bin/tests -q   (or `make test`)

from __future__ import annotations

import csv
import os
import subprocess
import sys
from pathlib import Path

import pytest

BIN_DIR = Path(__file__).resolve().parents[1]
REPO_ROOT = BIN_DIR.parents[3]
sys.path.insert(0, str(BIN_DIR))

from bridge_pkg.config_loader import load_config          # noqa: E402
from bridge_pkg.config_validator import ValidationError   # noqa: E402


def _fixture(name: str) -> str:
    return str(BIN_DIR / "test_configs" / name)


# ---------------------------------------------------------------------
# Negative fixtures — designed to trip the validator, never before run
# ---------------------------------------------------------------------


def test_illegal_wr_master_to_rd_slave_rejected():
    """A write-only master wired to a read-only slave must not
    validate."""
    with pytest.raises(ValidationError):
        load_config(
            _fixture("test_illegal_wr_to_rd.toml"),
            _fixture("test_illegal_wr_to_rd_connectivity.csv"),
        )


def test_illegal_apb_write_config_rejected():
    """APB constraint violations must not validate."""
    with pytest.raises(ValidationError):
        load_config(
            _fixture("test_illegal_apb_wr.toml"),
            _fixture("test_illegal_apb_wr_connectivity.csv"),
        )


# ---------------------------------------------------------------------
# Positive coverage — every manifest config must load and validate
# ---------------------------------------------------------------------


def _batch_rows():
    rows = []
    with open(BIN_DIR / "bridge_batch.csv", newline="") as f:
        for row in csv.DictReader(
                r for r in f if not r.lstrip().startswith("#")):
            if row.get("name") and row.get("ports"):
                rows.append((row["name"], row["ports"],
                             row["connectivity"]))
    return rows


@pytest.mark.parametrize("name,ports,conn",
                         _batch_rows(),
                         ids=[r[0] for r in _batch_rows()])
def test_every_batch_config_loads_and_validates(name, ports, conn):
    cfg = load_config(str(BIN_DIR / ports), str(BIN_DIR / conn))
    assert cfg.masters, f"{name}: no masters parsed"
    assert cfg.slaves, f"{name}: no slaves parsed"
    for s in cfg.slaves:
        assert s.channels, f"{name}: slave {s.name} has no channels"


# ---------------------------------------------------------------------
# Golden generation smoke
# ---------------------------------------------------------------------


def test_generation_smoke_is_decl_order_clean(tmp_path):
    """Generate one bridge end-to-end; the emitted xbar must have the
    parameter-port-list form and every .sv must pass the repo's
    declaration-order checker."""
    env = dict(os.environ, REPO_ROOT=str(REPO_ROOT))
    r = subprocess.run(
        [sys.executable, str(BIN_DIR / "bridge_generator.py"),
         "--ports", _fixture("bridge_1x2_rd_matched.toml"),
         "--connectivity", _fixture("bridge_1x2_rd_matched_connectivity.csv"),
         "--name", "bridge_1x2_rd",
         "--output-dir", str(tmp_path)],
        cwd=str(BIN_DIR), env=env,
        capture_output=True, text=True, timeout=300,
    )
    assert r.returncode == 0, f"generator failed:\n{r.stdout}\n{r.stderr}"

    xbar = tmp_path / "bridge_1x2_rd" / "bridge_1x2_rd_xbar.sv"
    assert xbar.exists(), "xbar not emitted"
    text = xbar.read_text()
    assert "parameter int NUM_SLAVES" in text, (
        "xbar lost the parameter-port-list form"
    )
    # Package import must be in the MODULE header (LRM-portable), not
    # at $unit scope where strict front ends can't resolve ANSI-port
    # references to package types and two bridges in one compilation
    # unit collide.
    assert "module bridge_1x2_rd_xbar\n    import bridge_1x2_rd_pkg::*;" in text, (
        "xbar package import is not module-header scoped"
    )
    assert "\nimport bridge_1x2_rd_pkg" not in text, (
        "xbar still has a $unit-scope package import"
    )

    sv_files = sorted((tmp_path / "bridge_1x2_rd").glob("*.sv"))
    chk = subprocess.run(
        [sys.executable, str(REPO_ROOT / "bin" / "check_sv_decl_order.py"),
         *map(str, sv_files)],
        capture_output=True, text=True, timeout=120,
    )
    assert chk.returncode == 0, (
        f"declaration-order issues in generated RTL:\n{chk.stdout}"
    )


def test_generation_is_deterministic(tmp_path):
    """Two runs from the same config must emit identical RTL."""
    env = dict(os.environ, REPO_ROOT=str(REPO_ROOT))
    outs = []
    for sub in ("a", "b"):
        d = tmp_path / sub
        r = subprocess.run(
            [sys.executable, str(BIN_DIR / "bridge_generator.py"),
             "--ports", _fixture("bridge_1x2_rd_matched.toml"),
             "--connectivity",
             _fixture("bridge_1x2_rd_matched_connectivity.csv"),
             "--name", "bridge_1x2_rd", "--output-dir", str(d)],
            cwd=str(BIN_DIR), env=env,
            capture_output=True, text=True, timeout=300,
        )
        assert r.returncode == 0, r.stdout + r.stderr
        outs.append({
            f.name: f.read_text()
            for f in sorted((d / "bridge_1x2_rd").glob("*.sv"))
        })
    assert outs[0].keys() == outs[1].keys()
    for name in outs[0]:
        assert outs[0][name] == outs[1][name], f"{name} not deterministic"


# ---------------------------------------------------------------------
# Correctness-batch regressions (hex parse, explicit channels,
# invalid-channels rejection)
# ---------------------------------------------------------------------


def test_parse_csv_value_decimal_not_hex():
    """All-digit values are DECIMAL. The old parser tried base-16
    first, so '16' became 22 and '1000' became 4096 — silently."""
    from bridge_pkg.csv_parser import parse_csv_value
    assert parse_csv_value("16", "id_width") == 16
    assert parse_csv_value("1000", "addr_range") == 1000
    assert parse_csv_value("0x1000", "base_addr") == 0x1000
    assert parse_csv_value("0X10", "base_addr") == 16
    assert parse_csv_value("N/A", "x") is None
    assert parse_csv_value("hello", "name") == "hello"


def _write_min_toml(tmp_path, slave_extra="", master_extra=""):
    toml = tmp_path / "b.toml"
    conn = tmp_path / "c.csv"
    toml.write_text(f"""
[bridge]
name = "b"
variants = ["no"]

[[bridge.masters]]
name = "m0"
prefix = "m0_"
addr_width = 32
data_width = 32
id_width = 4
channels = "rd"
{master_extra}

[[bridge.slaves]]
name = "s0"
prefix = "s0_"
addr_width = 32
data_width = 32
id_width = 4
base_addr = "0x0000_0000"
addr_range = "0x0001_0000"
{slave_extra}
""")
    conn.write_text("master,s0\nm0,1\n")
    return str(toml), str(conn)


def test_slave_without_channels_rejected(tmp_path):
    """validate_slave_channels_explicit is finally reachable: the
    loader no longer injects a 'rw' default for slaves."""
    toml, conn = _write_min_toml(tmp_path)   # no channels on slave
    with pytest.raises(ValidationError, match="channels"):
        load_config(toml, conn)


def test_slave_with_explicit_channels_accepted(tmp_path):
    toml, conn = _write_min_toml(tmp_path, slave_extra='channels = "rd"')
    cfg = load_config(toml, conn)
    assert cfg.slaves[0].channels == "rd"


def test_invalid_channels_is_error_not_silent_downgrade(tmp_path):
    """Invalid channels used to WARN and default to 'rw'; now fatal."""
    toml, conn = _write_min_toml(tmp_path, slave_extra='channels = "bogus"')
    with pytest.raises(ValidationError, match="invalid channels"):
        load_config(toml, conn)


# ---------------------------------------------------------------------
# AXI5 master ports (BRIDGE-002 phase A5-1)
# ---------------------------------------------------------------------


def test_axi5_atomic_rejected_on_non_native_path(tmp_path):
    """A5-3a: 'atomic' is connectivity-gated like poison — a master
    whose connected slave is plain AXI4 is a config error."""
    toml, conn = _write_min_toml(
        tmp_path,
        slave_extra='channels = "rd"',
        master_extra='protocol = "axi5"\naxi5_features = ["atomic"]',
    )
    with pytest.raises(ValidationError, match="cannot carry it natively"):
        load_config(toml, conn)


def test_axi5_atomic_accepted_native_both_ends(tmp_path):
    """A5-3a: 'atomic' validates when every connected path is
    AXI5-both-ends, atomic-enabled, and width-matched (store-class
    rides natively; the boundary filter DECERRs read-return classes)."""
    toml, conn = _write_min_toml(
        tmp_path,
        master_extra='protocol = "axi5"\naxi5_features = ["atomic"]',
        slave_extra=('channels = "rd"\nprotocol = "axi5"\n'
                     'axi5_features = ["atomic"]'),
    )
    cfg = load_config(toml, conn)
    assert 'atomic' in cfg.masters[0].axi5_features


@pytest.mark.parametrize("feat", ["mte", "chunking"])
def test_axi5_data_semantics_features_rejected(tmp_path, feat):
    """mte/chunking change data semantics -- still phase-gated."""
    toml, conn = _write_min_toml(
        tmp_path,
        slave_extra='channels = "rd"',
        master_extra=f'protocol = "axi5"\naxi5_features = ["{feat}"]',
    )
    with pytest.raises(ValidationError, match="not supported in interop"):
        load_config(toml, conn)


def test_axi5_slave_accepted(tmp_path):
    """A5-2 slice 1: an AXI5 slave (interop mode) validates -- an AXI4
    master driving an AXI5 slave is the interop pairing."""
    toml, conn = _write_min_toml(
        tmp_path,
        slave_extra='channels = "rd"\nprotocol = "axi5"',
    )
    cfg = load_config(toml, conn)
    assert cfg.slaves[0].protocol == "axi5"
    assert cfg.slaves[0].axi5_features == []


def test_axi5_features_on_axi4_port_rejected(tmp_path):
    """axi5_features on a non-axi5 port is a config error, not a no-op."""
    toml, conn = _write_min_toml(
        tmp_path,
        slave_extra='channels = "rd"',
        master_extra='axi5_features = ["trace"]',
    )
    with pytest.raises(ValidationError, match="axi5_features"):
        load_config(toml, conn)


def test_axi5_unknown_feature_rejected(tmp_path):
    toml, conn = _write_min_toml(
        tmp_path,
        slave_extra='channels = "rd"',
        master_extra='protocol = "axi5"\naxi5_features = ["bogus"]',
    )
    with pytest.raises(ValidationError, match="unknown"):
        load_config(toml, conn)


def test_axi5_sideband_features_accepted(tmp_path):
    toml, conn = _write_min_toml(
        tmp_path,
        slave_extra='channels = "rd"',
        master_extra=('protocol = "axi5"\n'
                      'axi5_features = ["nsaid", "trace", "mpam", '
                      '"mecid", "unique"]'),
    )
    cfg = load_config(toml, conn)
    assert cfg.masters[0].protocol == "axi5"
    assert cfg.masters[0].axi5_features == [
        "nsaid", "trace", "mpam", "mecid", "unique"]


def test_axi5_generation_smoke(tmp_path):
    """Generate the axi5 fixture end-to-end. The bridge top must expose
    ONLY the enabled sideband signals (trace, unique) on the axi5
    master port -- no region, no disabled-feature signals -- and every
    emitted .sv (both no/mon variants) must pass the declaration-order
    checker. The adapter must instantiate axi5_slave_rd."""
    env = dict(os.environ, REPO_ROOT=str(REPO_ROOT))
    r = subprocess.run(
        [sys.executable, str(BIN_DIR / "bridge_generator.py"),
         "--ports", _fixture("bridge_1x2_rd_axi5.toml"),
         "--connectivity", _fixture("bridge_1x2_rd_axi5_connectivity.csv"),
         "--name", "bridge_1x2_rd_axi5",
         "--output-dir", str(tmp_path)],
        cwd=str(BIN_DIR), env=env,
        capture_output=True, text=True, timeout=300,
    )
    assert r.returncode == 0, f"generator failed:\n{r.stdout}\n{r.stderr}"

    top = tmp_path / "bridge_1x2_rd_axi5" / "bridge_1x2_rd_axi5.sv"
    assert top.exists(), "bridge top not emitted"
    text = top.read_text()

    # Enabled sideband features exposed on the external surface.
    assert "cpu_rd_axi_artrace" in text
    assert "cpu_rd_axi_arunique" in text
    assert "cpu_rd_axi_rtrace" in text
    # Disabled features are NOT exposed; AXI5 has no REGION.
    assert "arnsaid" not in text
    assert "armpam" not in text
    assert "armecid" not in text
    assert "rpoison" not in text
    assert "archunken" not in text
    assert "cpu_rd_axi_arregion" not in text

    adapter = (tmp_path / "bridge_1x2_rd_axi5" / "cpu_rd_adapter.sv").read_text()
    assert "axi5_slave_rd #(" in adapter, "adapter lost the axi5 wrapper"
    assert ".ENABLE_TRACE(1'b1)" in adapter
    assert ".ENABLE_UNIQUE(1'b1)" in adapter
    assert ".ENABLE_NSAID(1'b0)" in adapter
    assert ".ENABLE_CHUNKING(1'b0)" in adapter
    # Disabled-feature external inputs tie to '0. ENABLED features now
    # ride the fabric structs natively (A5-2 slice 2): the fub side
    # binds the adapter's sideband wires instead of terminating.
    assert ".s_axi_arnsaid('0)" in adapter
    assert ".fub_axi_artrace(fub_axi_artrace)" in adapter
    assert ".fub_axi_rtrace(fub_axi_rtrace)" in adapter
    assert "_ar.trace = fub_axi_artrace" in adapter
    # Disabled features still terminate on the fub side.
    assert ".fub_axi_arnsaid()" in adapter
    assert ".fub_axi_rpoison('0)" in adapter

    # Both variants (no + mon) must be decl-order clean.
    sv_files = sorted(tmp_path.glob("bridge_1x2_rd_axi5*/*.sv"))
    assert any("mon" in str(p) for p in sv_files), "mon variant missing"
    chk = subprocess.run(
        [sys.executable, str(REPO_ROOT / "bin" / "check_sv_decl_order.py"),
         *map(str, sv_files)],
        capture_output=True, text=True, timeout=120,
    )
    assert chk.returncode == 0, (
        f"declaration-order issues in generated axi5 RTL:\n{chk.stdout}"
    )


# ---------------------------------------------------------------------
# AXI5 slave ports (BRIDGE-002 phase A5-2 slice 1) -- mirror of A5-1
# ---------------------------------------------------------------------


def test_axi5_slave_sideband_features_accepted(tmp_path):
    toml, conn = _write_min_toml(
        tmp_path,
        slave_extra=('channels = "rd"\nprotocol = "axi5"\n'
                     'axi5_features = ["nsaid", "trace", "mpam", '
                     '"mecid", "unique"]'),
    )
    cfg = load_config(toml, conn)
    assert cfg.slaves[0].protocol == "axi5"
    assert cfg.slaves[0].axi5_features == [
        "nsaid", "trace", "mpam", "mecid", "unique"]


def test_axi5_slave_atomic_rejected_on_non_native_path(tmp_path):
    """A5-3a: 'atomic' on a slave whose connected master is plain AXI4
    is a config error (the master side cannot source it)."""
    toml, conn = _write_min_toml(
        tmp_path,
        slave_extra=('channels = "rd"\nprotocol = "axi5"\n'
                     'axi5_features = ["atomic"]'),
    )
    with pytest.raises(ValidationError, match="cannot carry it natively"):
        load_config(toml, conn)


@pytest.mark.parametrize("feat", ["mte", "chunking"])
def test_axi5_slave_data_semantics_features_rejected(tmp_path, feat):
    """mte/chunking change data semantics -- still phase-gated."""
    toml, conn = _write_min_toml(
        tmp_path,
        slave_extra=(f'channels = "rd"\nprotocol = "axi5"\n'
                     f'axi5_features = ["{feat}"]'),
    )
    with pytest.raises(ValidationError, match="not supported in interop"):
        load_config(toml, conn)


def test_axi5_master_to_axi5_slave_accepted(tmp_path):
    """AXI5 master -> AXI5 slave validates (sideband still terminates
    at both boundaries in this slice -- no extra rules needed)."""
    toml, conn = _write_min_toml(
        tmp_path,
        master_extra='protocol = "axi5"\naxi5_features = ["trace"]',
        slave_extra=('channels = "rd"\nprotocol = "axi5"\n'
                     'axi5_features = ["trace", "unique"]'),
    )
    cfg = load_config(toml, conn)
    assert cfg.masters[0].protocol == "axi5"
    assert cfg.slaves[0].protocol == "axi5"


def test_axi5_slave_generation_smoke(tmp_path):
    """Generate the axi5-slave fixture end-to-end. The bridge top must
    expose ONLY the enabled sideband signals (trace, unique) on the
    axi5 slave port -- ar-side extras as OUTPUTS toward the external
    slave, rtrace as an INPUT from it -- with no region and no
    disabled-feature signals; the sibling AXI4 slave port must be
    untouched. Every emitted .sv (both no/mon variants) must pass the
    declaration-order checker. The adapter must instantiate
    axi5_master_rd."""
    env = dict(os.environ, REPO_ROOT=str(REPO_ROOT))
    r = subprocess.run(
        [sys.executable, str(BIN_DIR / "bridge_generator.py"),
         "--ports", _fixture("bridge_1x2_rd_axi5s.toml"),
         "--connectivity", _fixture("bridge_1x2_rd_axi5s_connectivity.csv"),
         "--name", "bridge_1x2_rd_axi5s",
         "--output-dir", str(tmp_path)],
        cwd=str(BIN_DIR), env=env,
        capture_output=True, text=True, timeout=300,
    )
    assert r.returncode == 0, f"generator failed:\n{r.stdout}\n{r.stderr}"

    top = tmp_path / "bridge_1x2_rd_axi5s" / "bridge_1x2_rd_axi5s.sv"
    assert top.exists(), "bridge top not emitted"
    text = top.read_text()

    # Enabled sideband features exposed on the axi5 slave port, with
    # slave-port directions (bridge is the master here).
    assert "output  logic         sram_rd_axi_artrace" in text
    assert "output  logic         sram_rd_axi_arunique" in text
    assert "input  logic         sram_rd_axi_rtrace" in text
    # Disabled features are NOT exposed; AXI5 has no REGION.
    assert "arnsaid" not in text
    assert "armpam" not in text
    assert "armecid" not in text
    assert "rpoison" not in text
    assert "archunken" not in text
    # No EXTERNAL region port on the axi5 slave. The internal
    # xbar_sram_rd_axi_arregion net legitimately exists -- the fabric
    # side stays AXI4 -- so exclude the xbar_-prefixed occurrences.
    assert not any("sram_rd_axi_arregion" in ln and "xbar_" not in ln
                   for ln in text.splitlines()), (
        "external region port leaked onto the axi5 slave surface")
    # The sibling AXI4 slave port keeps its full AXI4 surface.
    assert "ddr_rd_axi_arregion" in text
    assert "ddr_rd_axi_artrace" not in text

    adapter = (tmp_path / "bridge_1x2_rd_axi5s" / "sram_rd_adapter.sv").read_text()
    assert "axi5_master_rd #(" in adapter, "adapter lost the axi5 wrapper"
    assert ".ENABLE_TRACE(1'b1)" in adapter
    assert ".ENABLE_UNIQUE(1'b1)" in adapter
    assert ".ENABLE_NSAID(1'b0)" in adapter
    assert ".ENABLE_CHUNKING(1'b0)" in adapter
    # Enabled external extras pass through with the slave prefix.
    assert ".m_axi_artrace(sram_rd_axi_artrace)" in adapter
    assert ".m_axi_rtrace(sram_rd_axi_rtrace)" in adapter
    # Disabled-feature external INPUTS (b/r-side, from the external
    # slave) tie to '0; fabric-side req-direction extras (fub inputs
    # from the AXI4 fabric) tie to '0 as well.
    assert ".m_axi_rpoison('0)" in adapter
    assert ".fub_axi_arnsaid('0)" in adapter
    # ENABLED features ride the fabric natively (A5-2 slice 2):
    # the fub side binds the xbar sideband nets.
    assert ".fub_axi_artrace(xbar_sram_rd_axi_artrace)" in adapter
    assert ".fub_axi_rtrace(xbar_sram_rd_axi_rtrace)" in adapter
    # The sibling AXI4 slave adapter keeps axi4_master_rd.
    ddr_adapter = (tmp_path / "bridge_1x2_rd_axi5s" / "ddr_rd_adapter.sv").read_text()
    assert "axi4_master_rd #(" in ddr_adapter
    # (the bridge name itself contains 'axi5', so match the module family)
    assert "axi5_master" not in ddr_adapter

    # Both variants (no + mon) must be decl-order clean.
    sv_files = sorted(tmp_path.glob("bridge_1x2_rd_axi5s*/*.sv"))
    assert any("mon" in str(p) for p in sv_files), "mon variant missing"
    chk = subprocess.run(
        [sys.executable, str(REPO_ROOT / "bin" / "check_sv_decl_order.py"),
         *map(str, sv_files)],
        capture_output=True, text=True, timeout=120,
    )
    assert chk.returncode == 0, (
        f"declaration-order issues in generated axi5-slave RTL:\n{chk.stdout}"
    )


# ---------------------------------------------------------------------
# Dead-code sweep / helper-consolidation locks
# ---------------------------------------------------------------------


def test_width_utils_pure_functions():
    """width_utils is the single source of truth for the width /
    connectivity queries every generator must agree on. Pure: config
    objects in, plain values out."""
    from bridge_pkg.width_utils import (
        get_connected_slave_widths,
        get_masters_connecting_to_slave,
    )
    from bridge_pkg.generators.adapter_generator import MasterConfig, SlaveInfo

    slaves = [
        SlaveInfo("s0", "s0_", 0x0000_0000, 0x1000, 64, 32),
        SlaveInfo("s1", "s1_", 0x0001_0000, 0x1000, 32, 32, protocol="apb"),
        SlaveInfo("s2", "s2_", 0x0002_0000, 0x1000, 64, 32),
    ]
    m0 = MasterConfig("m0", "m0_", 64, 32, 4, "rd", [0, 1, 2])
    m1 = MasterConfig("m1", "m1_", 32, 32, 4, "rd", [1])
    masters = [m0, m1]

    # Duplicate slave widths collapse; result is sorted and always uses
    # slave.data_width (never the retired LCD-for-APB width).
    assert get_connected_slave_widths(m0, slaves) == [32, 64]
    assert get_connected_slave_widths(m1, slaves) == [32]

    assert get_masters_connecting_to_slave(slaves[0], masters, slaves) == [m0]
    assert get_masters_connecting_to_slave(slaves[1], masters, slaves) == [m0, m1]
    # A slave object not in the list -> no masters, not an exception.
    orphan = SlaveInfo("sx", "sx_", 0xF000_0000, 0x1000, 32, 32)
    assert get_masters_connecting_to_slave(orphan, masters, slaves) == []


def test_pre_consolidation_components_are_gone():
    """The orphaned pre-consolidation components were deleted; the
    package must no longer export them."""
    with pytest.raises(ImportError):
        from bridge_pkg.components import ArbiterComponent  # noqa: F401


def test_parse_bulk_csv_tolerates_expose_column_absence_and_presence(tmp_path):
    """The retired expose_arbiter_signals column must be ignored when
    present (old manifests) and not required when absent (new ones)."""
    from bridge_generator import parse_bulk_csv

    without = tmp_path / "without.csv"
    without.write_text(
        "name,ports,connectivity,output_dir,output_tb,output_test\n"
        "b1,p.toml,c.csv,out,tb,tst\n"
    )
    with_col = tmp_path / "with.csv"
    with_col.write_text(
        "name,ports,connectivity,output_dir,output_tb,output_test,"
        "expose_arbiter_signals\n"
        "b1,p.toml,c.csv,out,tb,tst,true\n"
    )
    for manifest in (without, with_col):
        rows = parse_bulk_csv(str(manifest))
        assert len(rows) == 1, f"{manifest.name}: row not parsed"
        assert rows[0]["name"] == "b1"
        assert rows[0]["ports"] == "p.toml"
        assert "expose_arbiter" not in rows[0]


def test_axi5_poison_rejected_on_non_native_path(tmp_path):
    """A5-2 slice 2: poison on a master whose connected slave is plain
    AXI4 is a config ERROR (silently dropping POISON would launder
    corrupted data), with a self-documenting message."""
    toml, conn = _write_min_toml(
        tmp_path,
        slave_extra='channels = "rd"',
        master_extra='protocol = "axi5"\naxi5_features = ["poison"]',
    )
    with pytest.raises(ValidationError, match="cannot carry it natively"):
        load_config(toml, conn)


def test_axi5_slave_poison_rejected_on_non_native_path(tmp_path):
    """A5-2 slice 2: poison on a slave whose connected master is plain
    AXI4 is a config ERROR (the master side cannot source/sink it)."""
    toml, conn = _write_min_toml(
        tmp_path,
        slave_extra=('channels = "rd"\nprotocol = "axi5"\n'
                     'axi5_features = ["poison"]'),
    )
    with pytest.raises(ValidationError, match="cannot carry it natively"):
        load_config(toml, conn)


def test_axi5_poison_accepted_native_both_ends(tmp_path):
    """A5-2 slice 2: poison validates when every connected path is
    AXI5-both-ends, poison-enabled, and width-matched."""
    toml, conn = _write_min_toml(
        tmp_path,
        master_extra='protocol = "axi5"\naxi5_features = ["poison"]',
        slave_extra=('channels = "rd"\nprotocol = "axi5"\n'
                     'axi5_features = ["poison"]'),
    )
    cfg = load_config(toml, conn)
    assert 'poison' in cfg.masters[0].axi5_features
    assert 'poison' in cfg.slaves[0].axi5_features


# ---------------------------------------------------------------------
# AXI5-Lite slaves (protocol="axil5")
# ---------------------------------------------------------------------

def test_axil5_forwardable_features_accepted(tmp_path):
    toml, conn = _write_min_toml(
        tmp_path,
        slave_extra=('channels = "rd"\nprotocol = "axil5"\n'
                     'axi5_features = ["user", "exclusive"]'),
    )
    cfg = load_config(toml, conn)
    assert cfg.slaves[0].protocol == "axil5"
    assert cfg.slaves[0].axi5_features == ["user", "exclusive"]


@pytest.mark.parametrize("feat", ["trace", "loop", "mpam", "mecid",
                                  "nsaid", "poison"])
def test_axil5_tied_features_rejected(tmp_path, feat):
    """A tied group named in axi5_features would read as a request that
    changes something. It cannot: axi4_to_axil5_* drives those to zero
    unconditionally, and their ports exist either way. Rejected rather
    than ignored, so the config cannot lie about what the design does."""
    toml, conn = _write_min_toml(
        tmp_path,
        slave_extra=(f'channels = "rd"\nprotocol = "axil5"\n'
                     f'axi5_features = ["{feat}"]'),
    )
    with pytest.raises(ValidationError, match="no AXI4 source"):
        load_config(toml, conn)


def test_axil5_unknown_feature_rejected(tmp_path):
    toml, conn = _write_min_toml(
        tmp_path,
        slave_extra=('channels = "rd"\nprotocol = "axil5"\n'
                     'axi5_features = ["telepathy"]'),
    )
    with pytest.raises(ValidationError, match="unknown axi5_features"):
        load_config(toml, conn)


def test_axil5_generation_smoke(tmp_path):
    """Generate the axil5 fixture end-to-end.

    The bridge top must expose the FULL AXI5-Lite surface on the axil5
    port -- every sideband group, enabled or not, because a boundary
    whose shape depends on a config knob cannot be wired to a fixed
    external slave. Request-side groups are outputs, response-side ones
    inputs. The adapter must instantiate the AXI5-Lite converters, not
    the AXI4-Lite ones, and the sibling AXI4 slave port must be
    untouched."""
    env = dict(os.environ, REPO_ROOT=str(REPO_ROOT))
    r = subprocess.run(
        [sys.executable, str(BIN_DIR / "bridge_generator.py"),
         "--ports", _fixture("bridge_1x2_rw_axil5.toml"),
         "--connectivity", _fixture("bridge_1x2_rw_axil5_connectivity.csv"),
         "--name", "bridge_1x2_rw_axil5",
         "--output-dir", str(tmp_path)],
        cwd=str(BIN_DIR), env=env,
        capture_output=True, text=True, timeout=300,
    )
    assert r.returncode == 0, f"generator failed:\n{r.stdout}\n{r.stderr}"

    top = (tmp_path / "bridge_1x2_rw_axil5" / "bridge_1x2_rw_axil5.sv").read_text()

    # Request-side sideband: outputs toward the external AXI5-Lite slave.
    for base in ("awlock", "awuser", "awloop", "awmpam", "awmecid",
                 "awnsaid", "awtrace", "wuser", "wpoison",
                 "arlock", "aruser", "arloop", "armpam", "armecid",
                 "arnsaid", "artrace"):
        assert f"output logic" in top and f"cfg_axil_{base}" in top, base

    # Response-side sideband: inputs from it.
    for base in ("buser", "bloop", "btrace", "ruser", "rloop", "rtrace",
                 "rpoison"):
        assert f"cfg_axil_{base}" in top, base

    # The AXI4 sibling keeps its own surface; no sideband leaked onto it.
    assert "ddr_axi_awid" in top
    assert "ddr_axi_awmpam" not in top

    # Widths come from the shared table, not from a retyped literal.
    from bridge_pkg.axil5_sideband import MPAM_WIDTH, MECID_WIDTH, NSAID_WIDTH
    assert f"[{MPAM_WIDTH-1}:0] cfg_axil_awmpam" in top
    assert f"[{MECID_WIDTH-1}:0] cfg_axil_awmecid" in top
    assert f"[{NSAID_WIDTH-1}:0] cfg_axil_arnsaid" in top

    adapter = (tmp_path / "bridge_1x2_rw_axil5" / "cfg_adapter.sv").read_text()
    assert "axi4_to_axil5_wr" in adapter
    assert "axi4_to_axil5_rd" in adapter
    # The AXI4-Lite modules are wrapped BY those, never instantiated here.
    assert "axi4_to_axil4_wr #(" not in adapter
    assert "axi4_to_axil4_rd #(" not in adapter

    # Only the two gating parameters exist on the converter -- the tied
    # groups deliberately have none (see axil5_sideband.FEATURE_TO_ENABLE).
    assert ".ENABLE_USER(1)" in adapter
    assert ".ENABLE_LOCK(1)" in adapter
    for absent in ("ENABLE_TRACE", "ENABLE_LOOP", "ENABLE_MPAM",
                   "ENABLE_MECID", "ENABLE_NSAID", "ENABLE_POISON"):
        assert absent not in adapter, f"{absent} is a parameter that does not exist"


def test_axil5_sideband_table_matches_converter_ports():
    """The generator's table and the RTL it drives must name the same
    ports. A mismatch here is a PINMISSING in every generated bridge --
    the failure this table exists to prevent, so it is worth asserting
    directly rather than waiting for a lint run to notice."""
    from bridge_pkg.axil5_sideband import sideband_ports

    rtl = REPO_ROOT / "projects/components/converters/rtl"
    text = ((rtl / "axi4_to_axil5_wr.sv").read_text()
            + (rtl / "axi4_to_axil5_rd.sv").read_text())
    for base, _width_key, _direction in sideband_ports("rw"):
        assert f"m_axil_{base}" in text, (
            f"axil5_sideband names m_axil_{base}, the RTL does not")


# ---------------------------------------------------------------------
# AXI5 read-return atomics (BRIDGE-002 phase A5-3b)
# ---------------------------------------------------------------------


def _write_rw_atomic_toml(tmp_path, slave_channels="rw", slave_extra=""):
    """One rw AXI5 atomic master to one AXI5 atomic slave."""
    toml = tmp_path / "b.toml"
    conn = tmp_path / "c.csv"
    toml.write_text(f"""
[bridge]
name = "b"
variants = ["no"]

[[bridge.masters]]
name = "m0"
prefix = "m0_"
addr_width = 32
data_width = 32
id_width = 4
channels = "rw"
protocol = "axi5"
axi5_features = ["atomic"]

[[bridge.slaves]]
name = "s0"
prefix = "s0_"
addr_width = 32
data_width = 32
id_width = 4
channels = "{slave_channels}"
base_addr = "0x0000_0000"
addr_range = "0x0001_0000"
protocol = "axi5"
axi5_features = ["atomic"]
{slave_extra}
""")
    conn.write_text("master,s0\nm0,1\n")
    return str(toml), str(conn)


def test_axi5_rr_atomic_master_needs_rw_slave(tmp_path):
    """A5-3b: an rw atomic master has no boundary filter, so its read-return
    atomics reach the slave and answer on R. A write-only slave cannot
    return read data: config error, not a hang."""
    toml, conn = _write_rw_atomic_toml(tmp_path, slave_channels="wr")
    with pytest.raises(ValidationError, match="cannot return read data"):
        load_config(toml, conn)


def test_axi5_rr_atomic_with_ooo_slave_accepted(tmp_path):
    """A5-3b + BRIDGE-015: the per-ID return tracker sits beside whichever
    read tracker the slave uses, so an enable_ooo slave is accepted."""
    toml, conn = _write_rw_atomic_toml(tmp_path, slave_extra="enable_ooo = true")
    cfg = load_config(toml, conn)
    assert cfg.slaves[0].enable_ooo


def test_ooo_slave_adapter_generates_and_gates(tmp_path):
    """BRIDGE-015: CAM-mode tracking lost its not-full nets in c64660f47 and
    could not elaborate. The CAM paths must declare wr_trk_full / rd_trk_full
    and drive them from tags_full, and an atomic slave must get the return
    tracker beside the CAM."""
    out = _generate(tmp_path, "bridge_2x2_ooo")
    for slave in ("ddr", "sram"):
        sv = (out / f"{slave}_adapter.sv").read_text()
        assert "u_wr_cam" in sv and "u_rd_cam" in sv, f"{slave}: CAM tracking not selected"
        assert "logic wr_trk_full;" in sv and "logic rd_trk_full;" in sv, f"{slave}: not-full nets undeclared (the c64660f47 regression)"
        assert ".tags_full(wr_trk_full)" in sv and ".tags_full(rd_trk_full)" in sv, f"{slave}: full flags not driven by the CAM"
        assert "&& !wr_trk_full" in sv and "&& !rd_trk_full" in sv, f"{slave}: readies not gated on the CAM being full"
    sv_files = sorted(tmp_path.glob("bridge_2x2_ooo*/*.sv"))
    chk = subprocess.run(
        [sys.executable, str(REPO_ROOT / "bin" / "check_sv_decl_order.py"), *map(str, sv_files)],
        capture_output=True, text=True, timeout=120)
    assert chk.returncode == 0, f"declaration-order issues:\n{chk.stdout}"


# ---------------------------------------------------------------------
# Master-unique transaction IDs (BRIDGE-016)
# ---------------------------------------------------------------------


def test_id_prefix_slave_too_narrow_rejected(tmp_path):
    """Two 4-bit masters give 5-bit IDs at every slave; a slave declaring 4
    would truncate the master index and let two masters alias again."""
    toml = tmp_path / "b.toml"
    conn = tmp_path / "c.csv"
    toml.write_text("""
[bridge]
name = "b"
variants = ["no"]
[[bridge.masters]]
name = "m0"
prefix = "m0_"
addr_width = 32
data_width = 32
id_width = 4
channels = "rw"
[[bridge.masters]]
name = "m1"
prefix = "m1_"
addr_width = 32
data_width = 32
id_width = 4
channels = "rw"
[[bridge.slaves]]
name = "s0"
prefix = "s0_"
addr_width = 32
data_width = 32
id_width = 4
channels = "rw"
base_addr = "0x0000_0000"
addr_range = "0x0001_0000"
""")
    conn.write_text("master,s0\nm0,1\nm1,1\n")
    with pytest.raises(ValidationError, match="carries 5-bit IDs"):
        load_config(str(toml), str(conn))


def test_id_prefix_generated_on_multi_master(tmp_path):
    """The master adapter forms {BRIDGE_ID, id} on its fabric-facing nets,
    the package exports the widths, and the slave ports carry them."""
    out = _generate(tmp_path, "bridge_2x2_ooo")
    pkg = (out / "bridge_2x2_ooo_pkg.sv").read_text()
    assert "MASTER_ID_WIDTH = 4" in pkg and "ID_PREFIX_WIDTH = 1" in pkg and "XBAR_ID_WIDTH   = 5" in pkg
    for m in ("cpu", "dma"):
        sv = (out / f"{m}_adapter.sv").read_text()
        assert "assign xbar_axi_awid = {BRIDGE_ID_WIDTH'(BRIDGE_ID), MASTER_ID_WIDTH'(fub_axi_awid)};" in sv
        assert "_aw.id     = xbar_axi_awid;" in sv and "_ar.id     = xbar_axi_arid;" in sv
    top = (out / "bridge_2x2_ooo.sv").read_text()
    assert "[4:0]" in top and "ddr_axi_awid" in top, "slave ports not widened"


def test_multi_master_axi_slaves_track_by_id(tmp_path):
    """BRIDGE-015/016: with more than one master a real AXI slave tracks by
    ID in bridge_cam even without enable_ooo (the FIFO needs the slave to
    complete in request order across all IDs); the subtractive slave and a
    single-master bridge keep the FIFO."""
    out = _generate(tmp_path, "bridge_2x2_rw")
    for slave in ("ddr", "sram"):
        assert "u_rd_cam" in (out / f"{slave}_adapter.sv").read_text(), f"{slave}: expected CAM tracking"
    assert "u_rd_cam" not in (out / "subtractive_adapter.sv").read_text()
    out1 = _generate(tmp_path / "single", "bridge_1x2_rd_axi5")
    assert "u_rd_cam" not in (out1 / "ddr_rd_adapter.sv").read_text()


def test_id_prefix_absent_on_single_master(tmp_path):
    """One master: nothing to disambiguate, no prefix, and the pre-existing
    single-master bridges stay byte-identical apart from the package."""
    out = _generate(tmp_path, "bridge_1x2_rd_axi5")
    pkg = (out / "bridge_1x2_rd_axi5_pkg.sv").read_text()
    assert "ID_PREFIX_WIDTH = 0" in pkg
    assert "xbar_axi_arid" not in (out / "cpu_rd_adapter.sv").read_text()


def test_axi5_rr_atomic_accepted(tmp_path):
    toml, conn = _write_rw_atomic_toml(tmp_path)
    cfg = load_config(toml, conn)
    assert cfg.masters[0].channels == "rw"
    assert 'atomic' in cfg.slaves[0].axi5_features


def _generate(tmp_path, name):
    env = dict(os.environ, REPO_ROOT=str(REPO_ROOT))
    r = subprocess.run(
        [sys.executable, str(BIN_DIR / "bridge_generator.py"),
         "--ports", _fixture(f"{name}.toml"),
         "--connectivity", _fixture(f"{name}_connectivity.csv"),
         "--name", name,
         "--output-dir", str(tmp_path)],
        cwd=str(BIN_DIR), env=env,
        capture_output=True, text=True, timeout=300,
    )
    assert r.returncode == 0, f"generator failed:\n{r.stdout}\n{r.stderr}"
    return tmp_path / name


def test_axi5_rr_atomic_generation(tmp_path):
    """A5-3b fixture: the rw atomic master has NO boundary filter and its
    AR->R tracker takes a slot at the atomic AW; the atomic slaves route the
    R beat by ID through axi5_atomic_rr_tracker; the filelist pulls the
    tracker and not the filter."""
    out = _generate(tmp_path, "bridge_1x2_rw_axi5a")

    cpu = (out / "cpu_adapter.sv").read_text()
    assert "u_atomic_filter" not in cpu, "rw atomic master must not filter read-return atomics"
    assert "ar_trk_push_aw" in cpu, "atomic AW must claim an AR->R tracker slot"
    assert "aw_rr_gate_ok" in cpu, "atomic AW must pass the read-side single-target gate"
    assert "ar_trk_wptr + (AR_TRK_AW+1)'(2)" in cpu, "dual push (AR + atomic AW in one cycle) missing"

    for slave in ("ddr", "sram"):
        sv = (out / f"{slave}_adapter.sv").read_text()
        assert "u_atom_rd" in sv, f"{slave}: per-ID read-return tracker missing"
        assert "aw_rr_blocked" in sv, f"{slave}: AW not held while the tracker is full"
        assert "&& !atom_hit" in sv, f"{slave}: tracked R beats must not pop the in-order FIFO"
        assert "atom_hit ? atom_bridge_id" in sv, f"{slave}: R routing does not consult the tracker"

    # The generator writes the bridge filelist at <output-dir>/../filelists/,
    # a sibling of the RTL dir, mirroring rtl/generated -> rtl/filelists.
    filelists = list((tmp_path.parent / "filelists").glob("bridge_1x2_rw_axi5a*.f"))
    assert filelists, "no filelist emitted"
    text = "\n".join(p.read_text() for p in filelists)
    assert "axi5_atomic_rr_tracker.f" in text
    assert "axi5_atomic_filter.f" not in text

    sv_files = sorted(tmp_path.glob("bridge_1x2_rw_axi5a*/*.sv"))
    chk = subprocess.run(
        [sys.executable, str(REPO_ROOT / "bin" / "check_sv_decl_order.py"),
         *map(str, sv_files)],
        capture_output=True, text=True, timeout=120,
    )
    assert chk.returncode == 0, f"declaration-order issues:\n{chk.stdout}"


def test_axi5_wr_atomic_keeps_filter(tmp_path):
    """Regression guard for A5-3a: a write-only atomic master has no R path,
    so it must still terminate read-return atomics at the boundary."""
    out = _generate(tmp_path, "bridge_1x2_wr_axi5a")
    cpu = (out / "cpu_wr_adapter.sv").read_text()
    assert "u_atomic_filter" in cpu
    assert "u_atom_rd" not in (out / "ddr_wr_adapter.sv").read_text()
    text = "\n".join(p.read_text()
                     for p in (tmp_path.parent / "filelists").glob("bridge_1x2_wr_axi5a*.f"))
    assert "axi5_atomic_filter.f" in text
    assert "axi5_atomic_rr_tracker.f" not in text
