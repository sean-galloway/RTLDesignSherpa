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
# Run:  pytest projects/components/fabric-gen-ip/bridge/bin/tests -q   (or `make test`)

from __future__ import annotations

import csv
import os
import re
import subprocess
import sys
from pathlib import Path

import pytest

BIN_DIR = Path(__file__).resolve().parents[1]
REPO_ROOT = BIN_DIR.parents[4]
sys.path.insert(0, str(BIN_DIR))

from bridge_pkg.config import PortSpec                   # noqa: E402
from bridge_pkg.config_loader import load_config          # noqa: E402
from bridge_pkg.config_validator import (                 # noqa: E402
    ValidationError, validate_axi3, validate_axi5,
)


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


def test_illegal_axi3_zero_id_rejected():
    """AXI3 master with id_width=0 must not validate."""
    with pytest.raises(ValidationError, match="id_width must be > 0"):
        load_config(
            _fixture("test_illegal_axi3_zero_id.toml"),
            _fixture("test_illegal_axi3_zero_id_connectivity.csv"),
        )


def test_illegal_axi3_bad_width_rejected():
    """AXI3 port with an unsupported data width must not validate."""
    with pytest.raises(ValidationError, match="data_width"):
        load_config(
            _fixture("test_illegal_axi3_bad_width.toml"),
            _fixture("test_illegal_axi3_bad_width_connectivity.csv"),
        )


def test_illegal_axi3_cdc_rejected():
    """AXI3 slave with cdc = true must not validate."""
    with pytest.raises(ValidationError, match="CDC is not supported"):
        load_config(
            _fixture("test_illegal_axi3_cdc.toml"),
            _fixture("test_illegal_axi3_cdc_connectivity.csv"),
        )


def test_illegal_axi3_axi5_features_rejected():
    """axi5_features on an AXI3 port must not validate."""
    with pytest.raises(ValidationError, match="axi5_features"):
        load_config(
            _fixture("test_illegal_axi3_axi5_features.toml"),
            _fixture("test_illegal_axi3_axi5_features_connectivity.csv"),
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
# Positive coverage -- every CONSUMER config in the repo, not just the
# batch. bridge_stream_char_axil.toml (Genesys 2) carried id_width=8 on
# two AXI-Lite masters from 2026-09-11, when bridge TASK-004 (was BRIDGE-014) added the rule
# forbidding it, until 2026-09-26. Nothing exercised the file: the batch
# test above only sees bridge_batch.csv, and the board flow regenerates
# only the bridge it builds. Every agent that tried it in those two weeks
# concluded the generator was broken. A config that lives in the repo
# must load and validate against the generator that lives in the repo.
# ---------------------------------------------------------------------


def _consumer_configs():
    """(id, toml, csv-or-None) for every hand-written bridge config.

    Covers projects/fpga-systems/**/rtl/bridges/configs/ and the
    test_configs/ fixtures the batch does not reference. Generated
    copies (under a generated/ directory) and the deliberately illegal
    fixtures are excluded. The CSV is optional: a TOML may carry an
    inline [connectivity] table instead (bridge_2x2_simple.toml does).
    """
    in_batch = {r[1] for r in _batch_rows()}
    found = []
    for t in sorted(REPO_ROOT.glob(
            "projects/fpga-systems/**/rtl/bridges/configs/*.toml")):
        if "generated" in t.parts or t.name.endswith("_connectivity.toml"):
            continue
        found.append(t)
    for t in sorted((BIN_DIR / "test_configs").glob("*.toml")):
        rel = t.relative_to(BIN_DIR).as_posix()
        if rel in in_batch or t.name.startswith("test_illegal_"):
            continue
        found.append(t)
    rows = []
    for t in found:
        csv_path = t.with_name(t.stem + "_connectivity.csv")
        rows.append((t.relative_to(REPO_ROOT).as_posix(), str(t),
                     str(csv_path) if csv_path.exists() else None))
    return rows


@pytest.mark.parametrize("rel,ports,conn",
                         _consumer_configs(),
                         ids=[Path(r[0]).stem for r in _consumer_configs()])
def test_every_consumer_config_loads_and_validates(rel, ports, conn):
    cfg = load_config(ports, conn)
    assert cfg.masters, f"{rel}: no masters parsed"
    assert cfg.slaves, f"{rel}: no slaves parsed"


def test_consumer_config_sweep_found_the_board_configs():
    # The sweep above is only a gate if it actually reaches the board
    # areas; an empty glob would pass forever.
    rels = {r[0] for r in _consumer_configs()}
    # Post board-matrix reorg the Genesys2 area is grouped by IP area:
    # stream lives under Genesys2/dma-ip/stream (see projects/fpga-systems).
    assert any("Genesys2/dma-ip/stream" in r for r in rels), sorted(rels)
    assert any("NexysA7" in r for r in rels), sorted(rels)


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


def _write_min_toml(tmp_path, slave_extra="", master_extra="", data_width=32,
                    master_channels="rd"):
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
data_width = {data_width}
id_width = 4
channels = "{master_channels}"
{master_extra}

[[bridge.slaves]]
name = "s0"
prefix = "s0_"
addr_width = 32
data_width = {data_width}
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
# AXI5 master ports (bridge TASK-002 (was BRIDGE-002) phase A5-1)
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
def test_axi5_wide_features_need_128_bits(tmp_path, feat):
    """bridge TASK-007 (was BRIDGE-018): mte/chunking are native now, but tags are per 16 bytes
    and chunks are 128 bits -- a 32-bit port asking for them is an error."""
    toml, conn = _write_min_toml(
        tmp_path,
        slave_extra='channels = "rd"',
        master_extra=f'protocol = "axi5"\naxi5_features = ["{feat}"]',
    )
    with pytest.raises(ValidationError, match="data_width >= 128"):
        load_config(toml, conn)


def test_axi5_mte_rejected_on_non_native_path(tmp_path):
    """mte is connectivity-gated: a 128-bit MTE master into an AXI4 slave
    would drop the tag operation silently."""
    toml, conn = _write_min_toml(
        tmp_path,
        slave_extra='channels = "rd"',
        master_extra='protocol = "axi5"\naxi5_features = ["mte"]',
        data_width=128,
    )
    with pytest.raises(ValidationError, match="cannot carry it natively"):
        load_config(toml, conn)


def test_axi5_chunking_drops_to_axi4_slave(tmp_path, capsys):
    """chunking is droppable: the AXI4 slave simply never chunks, and the
    build log says so."""
    toml, conn = _write_min_toml(
        tmp_path,
        slave_extra='channels = "rd"',
        master_extra='protocol = "axi5"\naxi5_features = ["chunking"]',
        data_width=128,
    )
    cfg = load_config(toml, conn)
    assert 'chunking' in cfg.masters[0].axi5_features
    assert "sideband 'chunking' terminates" in capsys.readouterr().out


def test_axi5_mte_chunking_accepted_native_both_ends(tmp_path):
    toml, conn = _write_min_toml(
        tmp_path,
        slave_extra=('channels = "rd"\nprotocol = "axi5"\n'
                     'axi5_features = ["mte", "chunking"]'),
        master_extra='protocol = "axi5"\naxi5_features = ["mte", "chunking"]',
        data_width=128,
    )
    cfg = load_config(toml, conn)
    assert set(cfg.slaves[0].axi5_features) == {"mte", "chunking"}


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
    assert "cpu_rd_axi_aridunq" in text   # AxIDUNQ (IHI 0022L A5.2), #102 item 5
    assert "cpu_rd_axi_ridunq" in text    # RIDUNQ, regenerated at the boundary
    assert "cpu_rd_axi_rtrace" in text
    assert "unique" not in text.replace("ENABLE_UNIQUE", "")
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
# AXI5 slave ports (bridge TASK-002 (was BRIDGE-002) phase A5-2 slice 1) -- mirror of A5-1
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
def test_axi5_slave_wide_features_need_128_bits(tmp_path, feat):
    """The 128-bit rule applies to slave ports too."""
    toml, conn = _write_min_toml(
        tmp_path,
        slave_extra=(f'channels = "rd"\nprotocol = "axi5"\n'
                     f'axi5_features = ["{feat}"]'),
    )
    with pytest.raises(ValidationError, match="data_width >= 128"):
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
    assert "output  logic         sram_rd_axi_aridunq" in text
    assert "input  logic         sram_rd_axi_ridunq" in text
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
# AXI3 ports (bridge GitHub #97)
# ---------------------------------------------------------------------

def _make_axi3_port(direction, name, **overrides):
    defaults = dict(
        port_name=name,
        direction=direction,
        protocol="axi3",
        channels="rw",
        prefix=f"{name}_axi_",
        data_width=64,
        addr_width=32,
        id_width=4,
    )
    if direction == "slave":
        defaults["base_addr"] = 0
        defaults["addr_range"] = 0x1000
    defaults.update(overrides)
    return PortSpec(**defaults)


def test_axi3_legal_port_validates_directly():
    """A legal AXI3 master + slave must pass validate_axi3 with no raise."""
    master = _make_axi3_port("master", "m0")
    slave = _make_axi3_port("slave", "s0")
    validate_axi3([master], [slave])


def test_axi5_features_rejected_on_axi3_port():
    """validate_axi5 still rejects axi5_features on an axi3 port."""
    master = _make_axi3_port("master", "m0", axi5_features=["trace"])
    slave = _make_axi3_port("slave", "s0")
    with pytest.raises(ValidationError, match="axi5_features"):
        validate_axi5([master], [slave])


def test_axi3_master_generation_smoke(tmp_path):
    """bridge_1x2_axi3: an AXI3 master drives the fabric through
    axi3_to_axi4, and an AXI3 slave uses axi4_to_axi3. The bridge top
    must expose the AXI3 signal set (wid, 4-bit len, no qos/region) on
    both sides, the filelist must pull both converters, and every
    emitted .sv must be declaration-order clean."""
    env = dict(os.environ, REPO_ROOT=str(REPO_ROOT))
    r = subprocess.run(
        [sys.executable, str(BIN_DIR / "bridge_generator.py"),
         "--ports", _fixture("bridge_1x2_axi3.toml"),
         "--connectivity", _fixture("bridge_1x2_axi3_connectivity.csv"),
         "--name", "bridge_1x2_axi3",
         "--output-dir", str(tmp_path)],
        cwd=str(BIN_DIR), env=env,
        capture_output=True, text=True, timeout=300,
    )
    assert r.returncode == 0, f"generator failed:\n{r.stdout}\n{r.stderr}"

    top = tmp_path / "bridge_1x2_axi3" / "bridge_1x2_axi3.sv"
    assert top.exists(), "bridge top not emitted"
    top_text = top.read_text()

    # AXI3 master port surface on the bridge top.
    assert "cpu_axi_wid" in top_text, "AXI3 WID missing from top-level ports"
    assert "input  logic [3:0]  cpu_axi_awlen" in top_text, (
        "AXI3 awlen not 4-bit on top-level")
    assert "cpu_axi_awqos" not in top_text, "AXI3 master leaked qos port"
    assert "cpu_axi_awregion" not in top_text, "AXI3 master leaked region port"

    # AXI3 slave port surface on the bridge top.
    assert "s0_axi_wid" in top_text, "AXI3 slave WID missing from top-level ports"
    assert "output logic [3:0]  s0_axi_awlen" in top_text, (
        "AXI3 slave awlen not 4-bit on top-level")
    assert "output logic [3:0]  s0_axi_awqos" not in top_text, (
        "AXI3 slave leaked qos port")
    assert "output logic [3:0]  s0_axi_awregion" not in top_text, (
        "AXI3 slave leaked region port")

    cpu_adapter = (tmp_path / "bridge_1x2_axi3" / "cpu_adapter.sv").read_text()
    assert "axi3_to_axi4 #(" in cpu_adapter, (
        "adapter missing axi3_to_axi4 converter")
    assert ".s_axi3_awid(cpu_axi_awid)" in cpu_adapter, (
        "converter slave side not bound to AXI3 master ports")
    assert ".m_axi_awvalid(a3x_axi_awvalid)" in cpu_adapter, (
        "converter master side not bound to internal AXI4 nets")

    s0_adapter = (tmp_path / "bridge_1x2_axi3" / "s0_adapter.sv").read_text()
    assert "axi4_to_axi3 #(" in s0_adapter, (
        "slave adapter missing axi4_to_axi3 converter")
    assert ".m_axi3_awid" in s0_adapter and "s0_axi_awid" in s0_adapter, (
        "converter AXI3 master side not bound to slave ports")
    assert ".s_axi_awvalid" in s0_adapter and "xbar_s0_axi_awvalid" in s0_adapter, (
        "converter AXI4 slave side not bound to crossbar nets")

    # Filelist must include both converter families.
    filelist = tmp_path / "filelists" / "bridge_1x2_axi3.f"
    if not filelist.exists():
        filelist = tmp_path / ".." / "filelists" / "bridge_1x2_axi3.f"
    fl_text = filelist.read_text()
    assert "axi3_to_axi4.f" in fl_text, "filelist missing axi3_to_axi4"
    assert "axi4_to_axi3.f" in fl_text, "filelist missing axi4_to_axi3"

    sv_files = sorted(tmp_path.glob("bridge_1x2_axi3*/*.sv"))
    chk = subprocess.run(
        [sys.executable, str(REPO_ROOT / "bin" / "check_sv_decl_order.py"),
         *map(str, sv_files)],
        capture_output=True, text=True, timeout=120,
    )
    assert chk.returncode == 0, (
        f"declaration-order issues in generated AXI3 RTL:\n{chk.stdout}")


def test_pure_axi4_filelist_has_no_axi3_converters(tmp_path):
    """#99 negative half of the axi3 smoke's positive check: a bridge with
    no axi3 ports must not pull either axi3 converter filelist."""
    _generate(tmp_path, "bridge_1x2_rd_matched")
    filelists = list((tmp_path.parent / "filelists").glob("bridge_1x2_rd_matched*.f"))
    assert filelists, "no filelist emitted"
    text = "\n".join(p.read_text() for p in filelists)
    assert "axi3_to_axi4.f" not in text, (
        "pure-AXI4 bridge pulled the AXI3 requester converter filelist")
    assert "axi4_to_axi3.f" not in text, (
        "pure-AXI4 bridge pulled the AXI3 completer converter filelist")


def test_axi3_tb_dispatches_axi3_bfms(tmp_path):
    """#99: the generated TB must instantiate AXI3 BFMs on axi3 ports — the
    AXI3 write master drives WID from AWID and the BFM clamps bursts to the
    AXI3 16-beat ceiling — not AXI4 BFMs with wid left undriven and 8-bit
    len silently truncated onto 4-bit pins."""
    tb_dir = tmp_path / "tb"
    test_dir = tmp_path / "tests"
    rtl_dir = tmp_path / "rtl"
    env = dict(os.environ, REPO_ROOT=str(REPO_ROOT))
    r = subprocess.run(
        [sys.executable, str(BIN_DIR / "bridge_generator.py"),
         "--ports", _fixture("bridge_1x2_axi3.toml"),
         "--connectivity", _fixture("bridge_1x2_axi3_connectivity.csv"),
         "--name", "bridge_1x2_axi3",
         "--output-dir", str(rtl_dir),
         "--generate-tests",
         "--output-tb", str(tb_dir),
         "--output-test", str(test_dir)],
        cwd=str(BIN_DIR), env=env,
        capture_output=True, text=True, timeout=300,
    )
    assert r.returncode == 0, f"generator failed:\n{r.stdout}\n{r.stderr}"

    tb_files = list(tb_dir.glob("*_tb.py"))
    assert tb_files, "no TB class emitted"
    tb = tb_files[0].read_text()

    # The only master (cpu) is axi3, so it must be driven by the WID-driving,
    # len-clamping AXI3 master BFMs — never an AXI4 master BFM.
    assert "self.master_rd[0] = AXI3MasterRead(" in tb, (
        "axi3 master read not driven by AXI3MasterRead")
    assert "self.master_wr[0] = AXI3MasterWrite(" in tb, (
        "axi3 master write not driven by AXI3MasterWrite")
    assert "AXI4MasterRead(" not in tb and "AXI4MasterWrite(" not in tb, (
        "AXI4 master BFM instantiated on the axi3 master port")
    # Slave 0 (s0) is axi3, slave 1 (s1) is axi4: each must get its own
    # protocol's slave BFM.
    assert "self.slave_rd[0] = AXI3SlaveRead(" in tb, (
        "axi3 slave s0 read not driven by AXI3SlaveRead")
    assert "self.slave_wr[0] = AXI3SlaveWrite(" in tb, (
        "axi3 slave s0 write not driven by AXI3SlaveWrite")
    assert "self.slave_rd[1] = AXI4SlaveRead(" in tb, (
        "axi4 slave s1 read must keep AXI4SlaveRead")
    assert "self.slave_wr[1] = AXI4SlaveWrite(" in tb, (
        "axi4 slave s1 write must keep AXI4SlaveWrite")
    # Generator-emitted knob so hand-synced copies can check their BFM
    # id_widths against the fabric width without re-deriving it.
    assert "XBAR_ID_WIDTH" in tb, "generated TB missing the XBAR_ID_WIDTH knob"


def _write_axi3_channel_toml(tmp_path, master_channels=None, slave_channels=None):
    """Write a minimal TOML + CSV pair with an optional AXI3 master and/or
    AXI3 slave. When supplied, a channel string makes that port AXI3 with the
    requested channels; the omitted port remains AXI4 with channels="rw"."""
    toml = tmp_path / "b.toml"
    conn = tmp_path / "c.csv"
    master_lines = [
        '[[bridge.masters]]',
        'name = "m0"',
        'prefix = "m0_"',
        'addr_width = 32',
        'data_width = 32',
        'id_width = 4',
    ]
    if master_channels is not None:
        master_lines += [
            f'channels = "{master_channels}"',
            'protocol = "axi3"',
        ]
    else:
        master_lines += ['channels = "rw"']
    slave_lines = [
        '[[bridge.slaves]]',
        'name = "s0"',
        'prefix = "s0_"',
        'addr_width = 32',
        'data_width = 32',
        'id_width = 4',
        'base_addr = "0x0000_0000"',
        'addr_range = "0x0001_0000"',
    ]
    if slave_channels is not None:
        slave_lines += [
            f'channels = "{slave_channels}"',
            'protocol = "axi3"',
        ]
    else:
        slave_lines += ['channels = "rw"']
    toml.write_text("\n".join([
        '[bridge]',
        'name = "b"',
        'variants = ["no"]',
        '',
        *master_lines,
        '',
        *slave_lines,
        '',
    ]))
    conn.write_text("master,s0\nm0,1\n")
    return str(toml), str(conn)


@pytest.mark.parametrize("channels", ["wr", "rd"])
def test_axi3_master_channel_edge_cases(tmp_path, channels):
    """AXI3 master front end must not reference read/write signals that
    are absent for a channel-limited master."""
    toml, conn = _write_axi3_channel_toml(tmp_path, master_channels=channels)
    env = dict(os.environ, REPO_ROOT=str(REPO_ROOT))
    r = subprocess.run(
        [sys.executable, str(BIN_DIR / "bridge_generator.py"),
         "--ports", toml, "--connectivity", conn,
         "--name", "b", "--output-dir", str(tmp_path)],
        cwd=str(BIN_DIR), env=env,
        capture_output=True, text=True, timeout=300,
    )
    assert r.returncode == 0, f"generator failed:\n{r.stdout}\n{r.stderr}"

    adapter = (tmp_path / "b" / "m0_adapter.sv").read_text()
    assert "axi3_to_axi4 #(" in adapter
    if channels == "wr":
        assert ".s_axi3_arid(m0_arid)" not in adapter, (
            "write-only AXI3 master referenced non-existent arid")
        assert ".s_axi3_rid(m0_rid)" not in adapter, (
            "write-only AXI3 master referenced non-existent rid")
    else:
        assert ".s_axi3_awid(m0_awid)" not in adapter, (
            "read-only AXI3 master referenced non-existent awid")
        assert ".s_axi3_wid(m0_wid)" not in adapter, (
            "read-only AXI3 master referenced non-existent wid")

    sv_files = sorted(tmp_path.glob("b*/*.sv"))
    chk = subprocess.run(
        [sys.executable, str(REPO_ROOT / "bin" / "check_sv_decl_order.py"),
         *map(str, sv_files)],
        capture_output=True, text=True, timeout=120,
    )
    assert chk.returncode == 0, (
        f"declaration-order issues for AXI3 {channels} master:\n{chk.stdout}")


@pytest.mark.parametrize("channels", ["wr", "rd"])
def test_axi3_slave_channel_edge_cases(tmp_path, channels):
    """AXI3 slave converter must not reference converter_b/r nets that
    are undeclared for a channel-limited slave."""
    master_channels = "wr" if channels == "wr" else "rd"
    toml, conn = _write_axi3_channel_toml(
        tmp_path, master_channels=master_channels, slave_channels=channels)
    env = dict(os.environ, REPO_ROOT=str(REPO_ROOT))
    r = subprocess.run(
        [sys.executable, str(BIN_DIR / "bridge_generator.py"),
         "--ports", toml, "--connectivity", conn,
         "--name", "b", "--output-dir", str(tmp_path)],
        cwd=str(BIN_DIR), env=env,
        capture_output=True, text=True, timeout=300,
    )
    assert r.returncode == 0, f"generator failed:\n{r.stdout}\n{r.stderr}"

    adapter = (tmp_path / "b" / "s0_adapter.sv").read_text()
    assert "axi4_to_axi3 #(" in adapter
    if channels == "wr":
        assert "converter_rvalid" not in adapter, (
            "write-only AXI3 slave referenced converter_rvalid")
        assert "converter_rready" not in adapter, (
            "write-only AXI3 slave referenced converter_rready")
    else:
        assert "converter_bvalid" not in adapter, (
            "read-only AXI3 slave referenced converter_bvalid")
        assert "converter_bready" not in adapter, (
            "read-only AXI3 slave referenced converter_bready")

    sv_files = sorted(tmp_path.glob("b*/*.sv"))
    chk = subprocess.run(
        [sys.executable, str(REPO_ROOT / "bin" / "check_sv_decl_order.py"),
         *map(str, sv_files)],
        capture_output=True, text=True, timeout=120,
    )
    assert chk.returncode == 0, (
        f"declaration-order issues for AXI3 {channels} slave:\n{chk.stdout}")


# ---------------------------------------------------------------------
# AXI5-Lite slaves (protocol="axil5")
# ---------------------------------------------------------------------

def test_axil5_forwardable_features_accepted(tmp_path):
    toml, conn = _write_min_toml(
        tmp_path,
        slave_extra=('channels = "rd"\nprotocol = "axil5"\n'
                     'axi5_features = ["user"]'),
    )
    cfg = load_config(toml, conn)
    assert cfg.slaves[0].protocol == "axil5"
    assert cfg.slaves[0].axi5_features == ["user"]


@pytest.mark.parametrize("feat", ["exclusive", "loop", "mpam", "mecid",
                                  "nsaid"])
def test_axil5_absent_features_rejected(tmp_path, feat):
    """GitHub #102 item 3: AXI5-Lite has no AxLOCK (no exclusive access),
    AxMPAM, AxMECID, AxNSAID or xLOOP (IHI 0022L B2.1.5). Naming one is a
    spec error, reported as such."""
    toml, conn = _write_min_toml(
        tmp_path,
        slave_extra=(f'channels = "rd"\nprotocol = "axil5"\n'
                     f'axi5_features = ["{feat}"]'),
    )
    with pytest.raises(ValidationError, match="does not exist on AXI5-Lite"):
        load_config(toml, conn)


@pytest.mark.parametrize("feat", ["trace", "poison"])
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

    # Request-side ID + sideband: outputs toward the external AXI5-Lite slave.
    for base in ("awid", "awuser", "awtrace", "wuser", "wpoison",
                 "arid", "aruser", "artrace"):
        assert f"cfg_axil_{base}" in top, base

    # Response-side ID + sideband: inputs from it.
    for base in ("bid", "buser", "btrace", "rid", "ruser", "rtrace",
                 "rpoison"):
        assert f"cfg_axil_{base}" in top, base

    # GitHub #102 item 3: the groups AXI5-Lite does not have are gone.
    for gone in ("awlock", "arlock", "awloop", "bloop", "arloop", "rloop",
                 "awmpam", "armpam", "awmecid", "armecid", "awnsaid",
                 "arnsaid"):
        assert f"cfg_axil_{gone}" not in top, gone

    # The ID is the fabric ID width ({master index, id}; one master, 4 bits).
    assert "output logic [3:0] cfg_axil_awid" in top
    assert "input  logic [3:0] cfg_axil_rid" in top

    # The AXI4 sibling keeps its own surface; no sideband leaked onto it.
    assert "ddr_axi_awid" in top
    assert "ddr_axi_awtrace" not in top

    adapter = (tmp_path / "bridge_1x2_rw_axil5" / "cfg_adapter.sv").read_text()
    assert "axi4_to_axil5_wr" in adapter
    assert "axi4_to_axil5_rd" in adapter
    # The AXI4-Lite modules are wrapped BY those, never instantiated here.
    assert "axi4_to_axil4_wr #(" not in adapter
    assert "axi4_to_axil4_rd #(" not in adapter

    # Only the one gating parameter exists on the converter -- the tied
    # groups deliberately have none (see axil5_sideband.FEATURE_TO_ENABLE),
    # and ENABLE_LOCK went with AxLOCK (#102 item 3).
    assert ".ENABLE_USER(1)" in adapter
    for absent in ("ENABLE_LOCK", "ENABLE_TRACE", "ENABLE_LOOP", "ENABLE_MPAM",
                   "ENABLE_MECID", "ENABLE_NSAID", "ENABLE_POISON"):
        assert absent not in adapter, f"{absent} is a parameter that does not exist"


def test_axil5_sideband_table_matches_converter_ports():
    """The generator's table and the RTL it drives must name the same
    ports. A mismatch here is a PINMISSING in every generated bridge --
    the failure this table exists to prevent, so it is worth asserting
    directly rather than waiting for a lint run to notice."""
    from bridge_pkg.axil5_sideband import sideband_ports

    rtl = REPO_ROOT / "projects/components/utility-ip/converters/rtl"
    text = ((rtl / "axi4_to_axil5_wr.sv").read_text()
            + (rtl / "axi4_to_axil5_rd.sv").read_text())
    for base, _width_key, _direction in sideband_ports("rw"):
        assert f"m_axil_{base}" in text, (
            f"axil5_sideband names m_axil_{base}, the RTL does not")


# ---------------------------------------------------------------------
# AXI5 read-return atomics (bridge TASK-002 (was BRIDGE-002) phase A5-3b)
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
    """A5-3b + bridge BUG-012 (was BRIDGE-015): the per-ID return tracker sits beside whichever
    read tracker the slave uses, so an enable_ooo slave is accepted."""
    toml, conn = _write_rw_atomic_toml(tmp_path, slave_extra="enable_ooo = true")
    cfg = load_config(toml, conn)
    assert cfg.slaves[0].enable_ooo


def test_ooo_slave_adapter_generates_and_gates(tmp_path):
    """bridge BUG-012 (was BRIDGE-015): by-ID tracking lost its not-full nets in c64660f47 and
    could not elaborate. The by-ID paths must declare wr_trk_full / rd_trk_full
    and drive them from their outstanding counters (bridge_cam's tags_full
    until bridge W12)."""
    out = _generate(tmp_path, "bridge_2x2_ooo")
    for slave in ("ddr", "sram"):
        sv = (out / f"{slave}_adapter.sv").read_text()
        assert "wr_out_cnt" in sv and "rd_out_cnt" in sv, f"{slave}: by-ID tracking not selected"
        assert "logic wr_trk_full;" in sv and "logic rd_trk_full;" in sv, f"{slave}: not-full nets undeclared (the c64660f47 regression)"
        assert "assign wr_trk_full = (wr_out_cnt ==" in sv and "assign rd_trk_full = (rd_out_cnt ==" in sv, f"{slave}: full flags not driven by the counters"
        assert "&& !wr_trk_full" in sv and "&& !rd_trk_full" in sv, f"{slave}: readies not gated on the tracker being full"
    sv_files = sorted(tmp_path.glob("bridge_2x2_ooo*/*.sv"))
    chk = subprocess.run(
        [sys.executable, str(REPO_ROOT / "bin" / "check_sv_decl_order.py"), *map(str, sv_files)],
        capture_output=True, text=True, timeout=120)
    assert chk.returncode == 0, f"declaration-order issues:\n{chk.stdout}"


# ---------------------------------------------------------------------
# Master-unique transaction IDs (bridge TASK-005, was BRIDGE-016)
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


def test_axi3_slave_too_narrow_rejected(tmp_path):
    """#99: validate_slave_id_widths covers AXI3 slaves directly. Two 4-bit
    masters give 5-bit IDs at every slave; an axi3 slave declaring 4 would
    truncate the master index and let two masters alias again."""
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
data_width = 64
id_width = 4
channels = "rw"
[[bridge.masters]]
name = "m1"
prefix = "m1_"
addr_width = 32
data_width = 64
id_width = 4
channels = "rw"
[[bridge.slaves]]
name = "s0"
prefix = "s0_"
addr_width = 32
data_width = 64
id_width = 4
channels = "rw"
protocol = "axi3"
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
    """bridge BUG-012 (was BRIDGE-015)/016: with more than one master a real AXI slave tracks by
    ID even without enable_ooo (the FIFO needs the slave to complete in
    request order across all IDs); the subtractive slave and a single-master
    bridge keep the FIFO. By ID means routed by the response ID's
    master-index bits with an outstanding counter -- no CAM (bridge W12)."""
    out = _generate(tmp_path, "bridge_2x2_rw")
    for slave in ("ddr", "sram"):
        ad = (out / f"{slave}_adapter.sv").read_text()
        assert "rd_out_cnt" in ad and "wr_out_cnt" in ad, f"{slave}: expected by-ID tracking"
        assert "assign rid_bridge_id = xbar_" in ad and "rid[ID_WIDTH-1 -: BRIDGE_ID_WIDTH];" in ad
        assert "assign bid_bridge_id = xbar_" in ad and "bid[ID_WIDTH-1 -: BRIDGE_ID_WIDTH];" in ad
        assert "bridge_cam" not in ad
    assert "rd_out_cnt" not in (out / "subtractive_adapter.sv").read_text()
    out1 = _generate(tmp_path / "single", "bridge_1x2_rd_axi5")
    assert "rd_out_cnt" not in (out1 / "ddr_rd_adapter.sv").read_text()


def test_id_prefix_absent_on_single_master(tmp_path):
    """One master: nothing to disambiguate, no prefix, and the pre-existing
    single-master bridges stay byte-identical apart from the package."""
    out = _generate(tmp_path, "bridge_1x2_rd_axi5")
    pkg = (out / "bridge_1x2_rd_axi5_pkg.sv").read_text()
    assert "ID_PREFIX_WIDTH = 0" in pkg
    assert "xbar_axi_arid" not in (out / "cpu_rd_adapter.sv").read_text()


def test_id_remap_width_rules():
    """width_utils decides which masters remap and how wide the fabric ID
    is; every generator sizes IDs from it. A master remaps when its ID is
    wider than a slot ($clog2(max_outstanding)); a read-return atomic port
    keeps its own ID."""
    from bridge_pkg.width_utils import (
        remap_slot_width, id_remapped, fabric_local_id_width, xbar_id_width)
    from bridge_pkg.generators.adapter_generator import MasterConfig

    def m(idw, mo=16, ch="rw", proto="axi4", feats=None):
        return MasterConfig("m", "m_", 64, 32, idw, ch, [0], protocol=proto,
                            axi5_features=feats, max_outstanding=mo)

    assert remap_slot_width(m(8)) == 4 and remap_slot_width(m(8, 64)) == 6
    assert remap_slot_width(m(8, 2)) == 1
    assert id_remapped(m(8)) and id_remapped(m(5))
    assert not id_remapped(m(4)) and not id_remapped(m(6, 64)) and not id_remapped(m(0))
    assert not id_remapped(m(8, proto="axi5", feats=["atomic"]))           # rr atomic
    assert id_remapped(m(8, ch="wr", proto="axi5", feats=["atomic"]))      # filtered at the port
    # Five 8-bit masters at 16 outstanding: 3 index bits + a 4-bit slot.
    assert xbar_id_width([m(8)] * 5) == 7
    # The local part is the widest of slots and kept IDs.
    assert fabric_local_id_width([m(8), m(6, 64)]) == 6
    assert xbar_id_width([m(1)]) == 1


def test_id_remap_generated(tmp_path):
    """bridge_5x3_channels (five 8-bit masters, 16 outstanding): every master
    adapter remaps both directions, the fabric ID is {BRIDGE_ID, slot}, the
    width converters run at the 7-bit fabric ID instead of 11, and the
    slot in a response restores the ID. bridge_2x2_ooo's 4-bit masters
    are no wider than a slot and keep their IDs."""
    out = _generate(tmp_path, "bridge_5x3_channels")
    pkg = (out / "bridge_5x3_channels_pkg.sv").read_text()
    assert "MASTER_ID_WIDTH = 4" in pkg and "XBAR_ID_WIDTH   = 7" in pkg
    cpu = (out / "cpu_master_adapter.sv").read_text()
    for chan, resp in (("aw", "b"), ("ar", "r")):
        assert f"u_{chan}_id_remap" in cpu
        assert (f"assign xbar_axi_{chan}id = {{BRIDGE_ID_WIDTH'(BRIDGE_ID), "
                f"MASTER_ID_WIDTH'({chan}_rmp_slot)}};") in cpu
        assert f".rsp_id   (fub_axi_{resp}id)," in cpu
        assert f"{resp}_rmp_slot = conv_32b_{resp}id[3:0];" in cpu
        assert f"{chan}_idt_cnt" not in cpu, "the per-ID target table should be gone"
    assert ".AXI_ID_WIDTH(7)," in cpu and ".AXI_ID_WIDTH(11)," not in cpu
    assert "[6:0]  sram_buffer_axi_awid" in (out / "bridge_5x3_channels.sv").read_text()
    # Slave-port checkers bind at the pins' width, not the declared id_width (11).
    chk = (out / "bridge_5x3_channels_checkers.sv").read_text()
    assert "u_chk_sram_buffer" in chk and ".ID_WIDTH(11)" not in chk and chk.count(".ID_WIDTH(7)") == 2
    for wr_only in ("descr_wr_master", "sink_wr_master"):
        sv = (out / f"{wr_only}_adapter.sv").read_text()
        assert "u_aw_id_remap" in sv and "u_ar_id_remap" not in sv
    fl = tmp_path / "filelists" / "bridge_5x3_channels.f"
    if fl.exists():
        assert "bridge_id_remap.f" in fl.read_text()

    out2 = _generate(tmp_path / "ooo", "bridge_2x2_ooo")
    for mname in ("cpu", "dma"):
        sv = (out2 / f"{mname}_adapter.sv").read_text()
        assert "bridge_id_remap" not in sv and "aw_idt_cnt" in sv


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
    AR per-ID table counts the atomic AW under its AWID (GitHub #119 L1b --
    this was an AR->R slot FIFO with a dual push); the atomic slaves route the
    R beat by ID through axi5_atomic_rr_tracker; the filelist pulls the
    tracker and not the filter."""
    out = _generate(tmp_path, "bridge_1x2_rw_axi5a")

    cpu = (out / "cpu_adapter.sv").read_text()
    assert "u_atomic_filter" not in cpu, "rw atomic master must not filter read-return atomics"
    assert "ar_idt_push_aw" in cpu, "atomic AW must be counted in the AR per-ID table"
    assert "aw_rr_gate_ok = ar_id_ok_aw" in cpu, "atomic AW must pass the read-side per-ID gate"
    assert "+ (AR_TRK_AW+1)'(ar_idt_push_aw)" in cpu, "AR outstanding count misses the atomic AW"
    assert "ar_idt_trace[ar_idt_widx_aw] <= fub_axi_awtrace" in cpu, "atomic R must echo the AW trace"
    assert "ar_trk_wptr" not in cpu, "the one-target AR->R FIFO is gone"

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


def test_axi5_wr_atomic_filter_r_channel_drained(tmp_path):
    """GitHub #102 item 2: the filter now owes R beats for a swallowed
    load-class atomic and needs AWLEN to count them. A write-only port has
    no R path upstream, so the beats are accepted and discarded
    (s_rready=1) -- otherwise the read-return queue fills after DEPTH
    atomics and stalls AW -- and the downstream R input is idle."""
    out = _generate(tmp_path, "bridge_1x2_wr_axi5a")
    cpu = (out / "cpu_wr_adapter.sv").read_text()
    for conn in (".s_awlen(pref_axi_awlen)", ".s_rready(1'b1)", ".s_rvalid()",
                 ".m_rvalid(1'b0)", ".m_rready()", ".m_rlast(1'b0)"):
        assert conn in cpu, conn
    # 'unique' on this master: BIDUNQ regenerated on the PRE-filter side, so
    # a local DECERR carries its own AWIDUNQ.
    assert "r_awidunq_by_id[pref_axi_awid] <= pref_axi_awidunq" in cpu
    assert "assign pref_axi_bidunq = r_awidunq_by_id[pref_axi_bid];" in cpu


def test_axi5_idunq_regenerated_at_master_boundary(tmp_path):
    """GitHub #102 item 5: BIDUNQ/RIDUNQ are a function of the request
    (A5.2), regenerated per ID at the master boundary rather than ridden
    back from a slave that may never have seen AxIDUNQ (the AXI4 ddr path
    here). They are not struct fields; AWIDUNQ/ARIDUNQ are."""
    out = _generate(tmp_path, "bridge_2x2_axi5")
    pkg = (out / "bridge_2x2_axi5_pkg.sv").read_text()
    assert "idunq;" in pkg and "uniq;" not in pkg
    cpu = (out / "cpu_adapter.sv").read_text()
    assert "r_awidunq_by_id[fub_axi_awid] <= fub_axi_awidunq" in cpu
    assert "assign fub_axi_bidunq = r_awidunq_by_id[fub_axi_bid];" in cpu
    assert "r_aridunq_by_id[fub_axi_arid] <= fub_axi_aridunq" in cpu
    assert "assign fub_axi_ridunq = r_aridunq_by_id[fub_axi_rid];" in cpu
    top = (out / "bridge_2x2_axi5.sv").read_text()
    for port in ("cpu_axi_awidunq", "cpu_axi_bidunq", "cpu_axi_aridunq", "cpu_axi_ridunq",
                 "sram_axi_awidunq", "sram_axi_bidunq"):
        assert re.search(rf"\b{port}\b", top), port
    assert "awunique" not in top and "arunique" not in top


def test_axi5_rr_atomic_ridunq_follows_awidunq(tmp_path):
    """A read-return atomic's R carries the AW ID, and A5.2 ties its RIDUNQ
    to AWIDUNQ: on an rw atomic+unique port the read table learns from the
    atomic AW too."""
    toml, conn = _write_min_toml(
        tmp_path,
        slave_extra=('channels = "rw"\nprotocol = "axi5"\n'
                     'axi5_features = ["atomic", "unique"]'),
        master_extra=('protocol = "axi5"\n'
                      'axi5_features = ["atomic", "unique"]'),
        master_channels="rw",
    )
    env = dict(os.environ, REPO_ROOT=str(REPO_ROOT))
    r = subprocess.run(
        [sys.executable, str(BIN_DIR / "bridge_generator.py"),
         "--ports", toml, "--connectivity", conn,
         "--name", "b", "--output-dir", str(tmp_path / "o")],
        cwd=str(BIN_DIR), env=env, capture_output=True, text=True, timeout=300)
    assert r.returncode == 0, f"generator failed:\n{r.stdout}\n{r.stderr}"
    adapters = [p for p in (tmp_path / "o" / "b").glob("*_adapter.sv")
                if "u_timing_wrapper_wr" in p.read_text()]
    assert adapters
    cpu = adapters[0].read_text()
    assert ("fub_axi_awvalid && fub_axi_awready && fub_axi_awatop[5]" in cpu
            and "r_aridunq_by_id[fub_axi_awid] <= fub_axi_awidunq" in cpu)


def test_axi5_wakeup_ports_and_forwarding(tmp_path):
    """GitHub #102 item 5 / IHI 0022L A14.1.1: AWAKEUP is ONE signal for
    both request channels -- declared once on an rw port, present on a
    read-only port. A master port's wake request reaches every connected
    wake-capable slave port; a slave port ORs its wr and rd wrapper copies."""
    out = _generate(tmp_path, "bridge_2x2_axi5")
    top = (out / "bridge_2x2_axi5.sv").read_text()
    assert len(re.findall(r"input\s+logic\s+cpu_axi_awakeup\b", top)) == 1
    assert len(re.findall(r"output\s+logic\s+sram_axi_awakeup\b", top)) == 1
    assert "dma_axi_awakeup" not in top        # dma does not carry the feature
    assert "ddr_axi_awakeup" not in top        # AXI4 slave
    assert ".wakeup_req(cpu_wakeup_req)" in top
    sram = (out / "sram_adapter.sv").read_text()
    assert "assign sram_axi_awakeup = w_awakeup_wr | w_awakeup_rd;" in sram
    assert ".fub_axi_awakeup(wakeup_req)" in sram
    assert ".ENABLE_WAKEUP(1'b1)" in sram
    cpu = (out / "cpu_adapter.sv").read_text()
    assert "assign wakeup_req = w_awakeup_wr | w_awakeup_rd;" in cpu
    assert ".s_axi_awakeup(cpu_axi_awakeup)" in cpu
    assert ".ENABLE_WAKEUP(1'b0)" in (out / "dma_adapter.sv").read_text()

    rd = _generate(tmp_path / "rd", "bridge_1x2_rd_axi5n")
    rtop = (rd / "bridge_1x2_rd_axi5n.sv").read_text()
    assert re.search(r"input\s+logic\s+cpu_rd_axi_awakeup\b", rtop)
    assert re.search(r"output\s+logic\s+sram_rd_axi_awakeup\b", rtop)


# ---------------------------------------------------------------------
# Lite and APB REQUESTER ports (bridge TASK-004, was BRIDGE-014)
# ---------------------------------------------------------------------

def _write_req_toml(tmp_path, master_block, slave_block=None):
    """A one-master, one-slave TOML whose master block is supplied whole,
    so the Lite/APB master rules (id_width, addr_width) can be exercised
    without colliding with _write_min_toml's fixed keys."""
    toml = tmp_path / "r.toml"
    conn = tmp_path / "r.csv"
    slave_block = slave_block or """
[[bridge.slaves]]
name = "s0"
prefix = "s0_"
addr_width = 32
data_width = 32
id_width = 4
channels = "rw"
protocol = "axi4"
base_addr = "0x0000_0000"
addr_range = "0x0001_0000"
"""
    toml.write_text(f"""
[bridge]
name = "r"
variants = ["no"]

[[bridge.masters]]
name = "m0"
prefix = "m0_"
{master_block}
{slave_block}
""")
    conn.write_text("master,s0\nm0,1\n")
    return str(toml), str(conn)


def test_lite_master_id_width_rejected(tmp_path):
    """AXI-Lite has no transaction IDs; a non-zero id_width would size
    ports that do not exist on the boundary."""
    toml, conn = _write_req_toml(tmp_path, """
addr_width = 32
data_width = 32
id_width = 4
channels = "rw"
protocol = "axil"
""")
    with pytest.raises(ValidationError, match="must have id_width=0"):
        load_config(toml, conn)


def test_apb_master_addr_width_rejected(tmp_path):
    """An APB requester supplies the full fabric address, unlike an APB
    slave port whose PADDR is a window offset."""
    toml, conn = _write_req_toml(tmp_path, """
addr_width = 16
data_width = 32
id_width = 0
channels = "rw"
protocol = "apb5"
""")
    with pytest.raises(ValidationError, match="must have addr_width=32"):
        load_config(toml, conn)


def test_axi3_master_addr_width_rejected(tmp_path):
    """#99: the AXI3 requester front end hardcodes 32-bit internal address
    nets, so a non-32-bit axi3 master must fail validation the same way
    apb/wb4 masters already do."""
    toml, conn = _write_req_toml(tmp_path, """
addr_width = 16
data_width = 64
id_width = 4
channels = "rw"
protocol = "axi3"
""")
    with pytest.raises(ValidationError, match="must have addr_width=32"):
        load_config(toml, conn)


@pytest.mark.parametrize("feat", ["trace", "poison"])
def test_axil5_master_tied_feature_rejected(tmp_path, feat):
    """On a master port the tied groups have no AXI4 DESTINATION: the bridge
    top terminates them whether or not they are named. Rejected, same as
    the slave side, so the config cannot claim a feature the design drops."""
    toml, conn = _write_req_toml(tmp_path, f"""
addr_width = 32
data_width = 32
id_width = 1
channels = "rw"
protocol = "axil5"
axi5_features = ["{feat}"]
""")
    with pytest.raises(ValidationError, match="no AXI4 destination"):
        load_config(toml, conn)


def test_axil5_master_forwardable_features_accepted(tmp_path):
    toml, conn = _write_req_toml(tmp_path, """
addr_width = 32
data_width = 32
id_width = 1
channels = "rw"
protocol = "axil5"
axi5_features = ["user"]
""")
    cfg = load_config(toml, conn)
    assert cfg.masters[0].protocol == "axil5"
    assert cfg.masters[0].axi5_features == ["user"]


def test_axil5_master_needs_an_id(tmp_path):
    """GitHub #102 item 3: AWID/BID and ARID/RID are required on an AXI5-Lite
    Subordinate (IHI 0022L B2.1.5), and the bridge is the Subordinate on a
    master port -- so id_width 0 is rejected there (it stays the rule for
    AXI4-Lite masters, which have no ID)."""
    toml, conn = _write_req_toml(tmp_path, """
addr_width = 32
data_width = 32
id_width = 0
channels = "rw"
protocol = "axil5"
""")
    with pytest.raises(ValidationError, match="must have id_width > 0"):
        load_config(toml, conn)


def _generate_fixture(tmp_path, name):
    env = dict(os.environ, REPO_ROOT=str(REPO_ROOT))
    out = tmp_path / "rtl"
    r = subprocess.run(
        [sys.executable, str(BIN_DIR / "bridge_generator.py"),
         "--ports", _fixture(f"{name}.toml"),
         "--connectivity", _fixture(f"{name}_connectivity.csv"),
         "--name", name,
         "--output-dir", str(out)],
        cwd=str(BIN_DIR), env=env,
        capture_output=True, text=True, timeout=300,
    )
    assert r.returncode == 0, f"generator failed:\n{r.stdout}\n{r.stderr}"
    # Filelists land beside the output dir, in <parent>/filelists.
    return out / name, tmp_path / "filelists" / f"{name}.f"


def test_lane_slave_monitor_on_its_own_clock(tmp_path):
    """bridge W9: a cdc slave several masters share has no aclk-side stream,
    so its monitors run on s_aclk after bridge_cdc_slave_arb and cross into
    the group through bridge_mon_cdc (the mon variant of
    bridge_3x2_rw_mcdc, whose ddr all three masters reach)."""
    gen, fl = _generate_fixture(tmp_path, "bridge_3x2_rw_mcdc")
    mon = gen.parent / "bridge_3x2_rw_mcdc_mon"
    ddr = (mon / "ddr_adapter.sv").read_text()
    # the arbiter drives the s_aclk nets, the wrappers take them to the pins
    assert ".m_axi_awvalid(lmon_ddr_axi_awvalid)" in ddr
    assert ".fub_axi_awvalid(lmon_ddr_axi_awvalid)" in ddr
    for chan in ("wr", "rd"):
        i = ddr.index(f") u_master_{chan} (")
        assert ".aclk(s_aclk)" in ddr[i:i + 200]
        assert f".i_mon_time(lmon_{chan}_mon_time)" in ddr
        assert f"u_mon_cdc_{chan}" in ddr
        assert f".monbus_valid(monbus_{chan}_valid)" in ddr
    mfl = (fl.parent / "bridge_3x2_rw_mcdc_mon.f").read_text()
    assert "bridge_mon_cdc.f" in mfl and "bridge_cdc_slave_arb.f" in mfl
    # the unmonitored variant is unchanged: the arbiter drives the pins
    plain = (gen / "ddr_adapter.sv").read_text()
    assert "lmon_" not in plain and "bridge_mon_cdc" not in plain
    assert "bridge_mon_cdc.f" not in fl.read_text()


def test_monitor_table_covers_port_outstanding(tmp_path):
    """bridge BUG-021: every port's monitor tracks as many transactions as the
    port can have outstanding. With the wrapper default (8) a port running 16
    deep counts the 9th command untracked and reports its beats as ORPHAN
    errors; the generator passes MAX_TRANSACTIONS = max_outstanding."""
    import re
    gen, _ = _generate_fixture(tmp_path, "bridge_3x2_rw_mcdc")
    mon = gen.parent / "bridge_3x2_rw_mcdc_mon"
    seen = 0
    for f in sorted(mon.glob("*_adapter.sv")):
        src = f.read_text()
        n_mon = len(re.findall(r"\b(axi[45]_(?:master|slave)_(?:rd|wr)_mon\w*) #\(", src))
        tables = re.findall(r"\.MAX_TRANSACTIONS\((\d+)\)", src)
        assert len(tables) == n_mon, f"{f.name}: {n_mon} monitors, {len(tables)} MAX_TRANSACTIONS"
        assert all(int(t) == 16 for t in tables), f"{f.name}: {tables}"   # max_outstanding default
        seen += n_mon
    assert seen == 9      # cpu, dma, ddr, sram rw (2 each) + lfsr rd
    # an unmonitored wrapper has no such parameter
    assert "MAX_TRANSACTIONS" not in "".join(f.read_text() for f in gen.glob("*_adapter.sv"))


def test_lite_req_generation_smoke(tmp_path):
    """bridge_2x2_lite_req: an AXI4-Lite and an AXI5-Lite REQUESTER.

    The AXI5-Lite master exposes its ID and the full sideband with
    master-port directions (requester-driven groups are bridge INPUTS), the
    ID and the enabled forwardable group reach its adapter, and every other
    group is terminated at the top -- inputs consumed, outputs driven to 0.
    Both Lite masters take the wide-slave aligner toward the 64-bit memory;
    only the AXI5-Lite one has an ID on the boundary (#102 item 3)."""
    gen, filelist = _generate_fixture(tmp_path, "bridge_2x2_lite_req")
    top = (gen / "bridge_2x2_lite_req.sv").read_text()

    # Requester-driven sideband: INPUTS on a master port (the slave-port
    # table says 'out' for these; the direction flips).
    for base in ("awid", "awuser", "awtrace", "wuser", "wpoison",
                 "arid", "aruser", "artrace"):
        assert re.search(rf"input\s+logic[^\n]*lite5_axil_{base},", top), base
    for base in ("bid", "buser", "btrace", "rid", "ruser", "rtrace", "rpoison"):
        assert re.search(rf"output logic[^\n]*lite5_axil_{base},", top), base

    # The ID and the forwardable group ('user') are wired into the adapter.
    for base in ("awid", "bid", "arid", "rid",
                 "awuser", "wuser", "buser", "aruser", "ruser"):
        assert f".lite5_axil_{base}(lite5_axil_{base})" in top, base
    # Everything else is terminated at the top, not left floating.
    for base in ("btrace", "rtrace", "rpoison"):
        assert f"assign lite5_axil_{base} = '0;" in top, base
    assert "_unused_lite5_axil5_sb" in top
    for base in ("awtrace", "wpoison", "artrace"):
        assert re.search(rf"_unused_lite5_axil5_sb[^\n]*lite5_axil_{base}", top), base

    # GitHub #102 item 3: the groups AXI5-Lite does not have are gone from the
    # boundary. (awlock/arlock still appear as the adapter's AXI4-face pins,
    # tied `.lite5_axil_awlock(1'b0)` -- there is no such port.)
    for gone in ("awlock", "arlock", "awloop", "bloop", "awmpam", "armecid",
                 "arnsaid"):
        assert not re.search(rf"(input|output)\s+logic[^\n]*\blite5_axil_{gone}\b", top), gone
    assert ".lite5_axil_awlock(1'b0)" in top

    # No ID PORT on the AXI4-Lite boundary, and no sideband port on it.
    # (The names do appear inside the top, as the tied-off connections to
    # the adapter's AXI4 face -- `.lite4_axil_awid(1'h0)` -- which is
    # exactly the point: the boundary has no such pin.)
    for name in ("lite4_axil_awid", "lite4_axil_awuser",
                 "lite4_axil_awlock", "lite4_axil_awlen"):
        assert not re.search(rf"(input|output)\s+logic[^\n]*\b{name}\b", top), name

    # Both Lite masters take the aligner toward the 64-bit slave.
    for m in ("lite4", "lite5"):
        adapter = (gen / f"{m}_adapter.sv").read_text()
        assert "axil_to_axi4_wide_align_wr" in adapter, m
        assert "axil_to_axi4_wide_align_rd" in adapter, m
        assert "apb4_to_axi4" not in adapter and "apb5_to_axi4" not in adapter

    fl = filelist.read_text()
    assert "axil_to_axi4_wide_align_wr.f" in fl
    assert "apb4_to_axi4.f" not in fl and "apb5_to_axi4.f" not in fl


def test_apb_req_generation_smoke(tmp_path):
    """bridge_2x3_apb_req: an APB4 and an APB5 REQUESTER.

    The bridge top is the APB completer (PSEL..PPROT in, PREADY/PRDATA/
    PSLVERR out; apb5 adds PAUSER/PWUSER/PWAKEUP in, PRUSER/PBUSER out),
    each adapter puts apb{4,5}_to_axi4 in front of the same axi4_slave_*
    timing wrapper an AXI4 master gets, and the filelist pulls both
    converter closures."""
    gen, filelist = _generate_fixture(tmp_path, "bridge_2x3_apb_req")
    top = (gen / "bridge_2x3_apb_req.sv").read_text()

    for m in ("apb4m", "apb5m"):
        for sig in ("PSEL", "PENABLE", "PADDR", "PWRITE", "PWDATA", "PSTRB", "PPROT"):
            assert re.search(rf"input\s+logic[^\n]*{m}_apb_{sig},", top), (m, sig)
        for sig in ("PREADY", "PRDATA", "PSLVERR"):
            assert re.search(rf"output logic[^\n]*{m}_apb_{sig},", top), (m, sig)
        # No AXI signal of any kind on an APB requester boundary.
        assert f"{m}_apb_awaddr" not in top and f"{m}_apb_awvalid" not in top
    for sig in ("PAUSER", "PWUSER", "PWAKEUP"):
        assert re.search(rf"input\s+logic[^\n]*apb5m_apb_{sig},", top), sig
    for sig in ("PRUSER", "PBUSER"):
        assert re.search(rf"output logic[^\n]*apb5m_apb_{sig},", top), sig
    assert "apb4m_apb_PWAKEUP" not in top

    a4 = (gen / "apb4m_adapter.sv").read_text()
    a5 = (gen / "apb5m_adapter.sv").read_text()
    assert "apb4_to_axi4 #(" in a4 and "apb5_to_axi4 #(" not in a4
    assert "apb5_to_axi4 #(" in a5 and "apb4_to_axi4 #(" not in a5
    for adapter in (a4, a5):
        # The front end feeds the ordinary timing wrapper on the internal
        # AXI4 face: same wrapper, different connector prefix.
        assert ".m_axi_awvalid(apbx_axi_awvalid)" in adapter
        assert ".s_axi_awvalid(apbx_axi_awvalid)" in adapter
        assert "axi4_slave_wr" in adapter and "axi4_slave_rd" in adapter
    assert ".s_apb_PWAKEUP(apb5m_apb_PWAKEUP)" in a5

    fl = filelist.read_text()
    assert "converters/rtl/filelists/apb4_to_axi4.f" in fl
    assert "converters/rtl/filelists/apb5_to_axi4.f" in fl


# ---------------------------------------------------------------------
# Wishbone B4 ports, both sides (bridge TASK-008, was BRIDGE-019)
# ---------------------------------------------------------------------

def test_wb4_port_must_be_rw(tmp_path):
    toml, conn = _write_req_toml(tmp_path, """
addr_width = 32
data_width = 32
id_width = 0
channels = "rd"
protocol = "wb4"
""")
    with pytest.raises(ValidationError, match="must have channels='rw'"):
        load_config(toml, conn)


def test_wb4_port_data_width_rejected(tmp_path):
    toml, conn = _write_req_toml(tmp_path, """
addr_width = 32
data_width = 128
id_width = 0
channels = "rw"
protocol = "wb4"
""")
    with pytest.raises(ValidationError, match="8, 16, 32 or 64"):
        load_config(toml, conn)


def test_wb4_master_addr_width_rejected(tmp_path):
    toml, conn = _write_req_toml(tmp_path, """
addr_width = 16
data_width = 32
id_width = 0
channels = "rw"
protocol = "wb4"
""")
    with pytest.raises(ValidationError, match="WB4 master 'm0' must have addr_width=32"):
        load_config(toml, conn)


def test_wb4_signal_table_matches_rtl_ports():
    """The generator's table and the converters it drives must name the same
    Wishbone signals, or the instantiation dies on PINMISSING."""
    from bridge_pkg.wb4_signals import wb4_names
    conv = REPO_ROOT / "projects/components/utility-ip/converters/rtl"
    a2w = (conv / "axi4_to_wb4.sv").read_text()
    w2a = (conv / "wb4_to_axi4.sv").read_text()
    for base in wb4_names():
        assert re.search(rf"\bm_wb_{base}\b", a2w), f"axi4_to_wb4 lacks m_wb_{base}"
        assert re.search(rf"\bs_wb_{base}\b", w2a), f"wb4_to_axi4 lacks s_wb_{base}"


def test_wb4_generation_smoke(tmp_path):
    """bridge_2x2_wb4: a Wishbone requester and a Wishbone completer.

    Master port: the bridge is the completer (CYC/STB/... in, STALL/ACK/
    ERR/RTY/DAT_R out), the adapter puts wb4_to_axi4 in front of the AXI4
    timing wrapper. Slave port: the bridge drives the bus (CYC/STB/... out),
    the adapter converts with axi4_to_wb4. Both closures in the filelist."""
    gen, filelist = _generate_fixture(tmp_path, "bridge_2x2_wb4")
    top = (gen / "bridge_2x2_wb4.sv").read_text()

    for sig in ("CYC", "STB", "WE", "ADR", "DAT_W", "SEL", "CTI", "BTE"):
        assert re.search(rf"input\s+logic[^\n]*wbm_wb_{sig},", top), ("master in", sig)
        assert re.search(rf"output logic[^\n]*wbp_wb_{sig},", top), ("slave out", sig)
    for sig in ("STALL", "ACK", "ERR", "RTY", "DAT_R"):
        assert re.search(rf"output logic[^\n]*wbm_wb_{sig},", top), ("master out", sig)
        assert re.search(rf"input\s+logic[^\n]*wbp_wb_{sig}", top), ("slave in", sig)
    assert "wbm_wb_awvalid" not in top and "wbp_wb_awvalid" not in top

    adapter = (gen / "wbm_adapter.sv").read_text()
    assert "wb4_to_axi4 #(" in adapter
    assert ".s_wb_CYC(wbm_wb_CYC)" in adapter
    assert ".m_axi_awvalid(wbx_axi_awvalid)" in adapter
    assert ".s_axi_awvalid(wbx_axi_awvalid)" in adapter     # the timing wrapper's external side
    assert "axil_to_axi4_wide_align_wr" in adapter          # 32b requester -> 64b memory

    slave = (gen / "wbp_adapter.sv").read_text()
    assert "axi4_to_wb4 #(" in slave
    assert ".m_wb_CYC(wbp_wb_CYC)" in slave
    assert "converter_bvalid" in slave and "converter_rlast" in slave

    fl = filelist.read_text()
    assert "converters/rtl/filelists/wb4_to_axi4.f" in fl
    assert "converters/rtl/filelists/axi4_to_wb4.f" in fl


# ---------------------------------------------------------------------
# Registered crossbar (bridge TASK-006 (was BRIDGE-017) xbar_pipeline)
# ---------------------------------------------------------------------

def test_xbar_pipeline_off_by_default(tmp_path):
    toml, conn = _write_min_toml(tmp_path, slave_extra='channels = "rd"')
    cfg = load_config(toml, conn)
    assert cfg.xbar_pipeline is False


def test_xbar_pipeline_generation_smoke(tmp_path):
    """bridge_2x2_rw_pipe: every slave-side channel is registered inside the
    xbar -- W, B and R by an xs_* skid stage; AW and AR of an arbitrated slave
    by its per-master request slots, which replace the stage (W3: the pick is
    made at the slave's pins from the slots, so no granted request queues in
    a stage behind the arbiter). The routing drives xs_* nets, and the bridge
    id rides in the request payload. The baseline fixture's xbar has none of
    it."""
    gen, _fl = _generate_fixture(tmp_path, "bridge_2x2_rw_pipe")
    xbar = (gen / "bridge_2x2_rw_pipe_xbar.sv").read_text()
    for slave in ("ddr", "sram"):
        for ch in ("w", "b", "r"):
            assert f"u_xs_{slave}_{ch} (" in xbar, (slave, ch)
        for ch in ("aw", "ar"):
            assert f"u_xs_{slave}_{ch} (" not in xbar, (slave, ch)
            for m in ("cpu_32b", "dma_32b"):
                assert f"u_{m}_{ch}_slot_{slave} (" in xbar, (m, ch, slave)
        # The routing targets the pre-stage nets ...
        assert f"assign xs_{slave}_axi_awvalid" in xbar
        # ... and the bridge id travels with the AW/AR beats.
        assert f"xs_{slave}_axi_bridge_id_aw" in xbar and f"xs_{slave}_axi_bridge_id_ar" in xbar
        # Response mux keys on the STAGED id/valid, never the raw port flag.
        assert f"xs_{slave}_axi_bid_valid" in xbar and f"xs_{slave}_axi_rid_valid" in xbar
    # Per slave port, the internal subtractive slave included: three stages
    # (W, B, R) and four slots (two masters x AW, AR).
    assert "u_xs_subtractive_w (" in xbar and "u_cpu_32b_aw_slot_subtractive (" in xbar
    assert xbar.count("gaxi_skid_buffer #(.DEPTH(2)") == 3 * (3 + 4)

    base, _ = _generate_fixture(tmp_path / "base", "bridge_2x2_rw")
    base_xbar = (base / "bridge_2x2_rw_xbar.sv").read_text()
    # The baseline has the request slots (every arbitrated slave does) but
    # none of the registered crossbar's stages.
    assert "u_xs_" not in base_xbar and "xs_ddr_axi_" not in base_xbar
    assert "u_cpu_32b_aw_slot_ddr (" in base_xbar


# ---------------------------------------------------------------------
# QoS-with-aging arbitration (bridge TASK-006 (was BRIDGE-017) arbitration = "qos")
# ---------------------------------------------------------------------

def test_arbitration_defaults_to_rr(tmp_path):
    toml, conn = _write_min_toml(tmp_path, slave_extra='channels = "rd"')
    cfg = load_config(toml, conn)
    assert cfg.arbitration == 'rr' and cfg.qos_aging_shift == 4


def test_arbitration_bad_value_rejected(tmp_path):
    toml = tmp_path / "b.toml"
    conn = tmp_path / "c.csv"
    toml.write_text("""
[bridge]
name = "b"
variants = ["no"]
arbitration = "lottery"

[[bridge.masters]]
name = "m0"
prefix = "m0_"
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
    conn.write_text("master,s0\nm0,1\n")
    with pytest.raises(ValueError, match="arbitration must be 'rr' or 'qos'"):
        load_config(str(toml), str(conn))


def test_qos_generation_smoke(tmp_path):
    """bridge_2x2_rw_qos: every multi-master slave arbiter carries the
    effective-priority compare and the per-master age counters; the
    round-robin baseline carries none of it."""
    gen, _fl = _generate_fixture(tmp_path, "bridge_2x2_rw_qos")
    xbar = (gen / "bridge_2x2_rw_qos_xbar.sv").read_text()
    for slave in ("ddr", "sram"):
        for ch in ("aw", "ar"):
            arb = f"{slave}_{ch}_arb"
            assert f"{arb}_age_0" in xbar and f"{arb}_age_1" in xbar, arb
            assert f"{arb}_best" in xbar and f"{arb}_elig" in xbar, arb
            # AxQOS is the priority source -- read from the master's request
            # slot at this slave (W3) -- and aging shifts by the configured amount.
            assert re.search(rf"5'\(cpu_32b_{ch}_slot_{slave}\.qos\)", xbar), (slave, ch)
            assert f"{arb}_age_0 >> 4" in xbar
    base, _ = _generate_fixture(tmp_path / "base", "bridge_2x2_rw")
    base_xbar = (base / "bridge_2x2_rw_xbar.sv").read_text()
    assert "_age_0" not in base_xbar and "_elig" not in base_xbar


# ---------------------------------------------------------------------
# CDC slave ports (bridge TASK-006 (was BRIDGE-017) cdc = true)
# ---------------------------------------------------------------------

def test_cdc_on_axi5_master_rejected(tmp_path):
    """A CDC master port (GitHub #119 L2) must be AXI4: axi4_cdc_{wr,rd}
    carry the AXI4 signal set and would drop an AXI5 port's sideband."""
    toml, conn = _write_req_toml(tmp_path, """
addr_width = 32
data_width = 32
id_width = 4
channels = "rw"
protocol = "axi5"
cdc = true
""")
    with pytest.raises(ValidationError, match=r"Master 'm0': cdc = true needs protocol = \"axi4\""):
        load_config(toml, conn)


def test_cdc_master_latency_mode_rejected(tmp_path):
    """A CDC master keeps cut_all: the latency modes are same-clock only."""
    toml, conn = _write_req_toml(tmp_path, """
addr_width = 32
data_width = 32
id_width = 4
channels = "rw"
protocol = "axi4"
cdc = true
latency = "cut_none"
""")
    with pytest.raises(ValueError, match="same-clock"):
        load_config(toml, conn)


def test_cdc_needs_axi4_slave(tmp_path):
    toml, conn = _write_req_toml(tmp_path, """
addr_width = 32
data_width = 32
id_width = 4
channels = "rw"
protocol = "axi4"
""", slave_block="""
[[bridge.slaves]]
name = "s0"
prefix = "s0_"
addr_width = 32
data_width = 32
id_width = 0
channels = "rw"
protocol = "apb"
cdc = true
base_addr = "0x0000_0000"
addr_range = "0x0001_0000"
""")
    with pytest.raises(ValidationError, match='needs protocol = "axi4"'):
        load_config(toml, conn)


def test_cdc_generation_smoke(tmp_path):
    """bridge_2x2_rw_cdc: ddr has its own clock pins on the top, and its
    adapter takes s_aclk/s_aresetn. Two masters share ddr, so the adapter
    crosses per-master lanes and arbitrates on s_aclk (bridge W9; see
    test_cdc_slave_arbitrates_on_its_own_clock); sram is unchanged."""
    gen, fl = _generate_fixture(tmp_path, "bridge_2x2_rw_cdc")
    top = (gen / "bridge_2x2_rw_cdc.sv").read_text()
    assert re.search(r"input\s+logic[^\n]*ddr_aclk,", top) and re.search(r"input\s+logic[^\n]*ddr_aresetn,", top)
    assert "sram_aclk" not in top
    assert ".s_aclk(ddr_aclk)" in top and ".s_aresetn(ddr_aresetn)" in top
    ddr = (gen / "ddr_adapter.sv").read_text()
    assert "input  logic s_aclk" in ddr
    assert ".s_aclk(s_aclk), .s_aresetn(s_aresetn)," in ddr
    assert ".m_axi_awvalid(ddr_s_axi_awvalid)" in ddr            # the pick drives the port
    sram = (gen / "sram_adapter.sv").read_text()
    assert "axi4_cdc" not in sram and "s_aclk" not in sram
    assert "bridge_cdc_slave_arb.f" in fl.read_text()


def test_single_master_cdc_slave_keeps_one_crossing(tmp_path):
    """With one master there is nothing to arbitrate: the cdc slave keeps the
    timing wrapper on aclk and one axi4_cdc_{wr,rd} to the port."""
    toml, conn = _write_min_toml(tmp_path, slave_extra='channels = "rw"\ncdc = true',
                                 master_channels="rw")
    out = tmp_path / "gen"
    env = dict(os.environ, REPO_ROOT=str(REPO_ROOT))
    r = subprocess.run(
        [sys.executable, str(BIN_DIR / "bridge_generator.py"),
         "--ports", toml, "--connectivity", conn, "--name", "b",
         "--output-dir", str(out)],
        cwd=str(BIN_DIR), env=env, capture_output=True, text=True, timeout=300)
    assert r.returncode == 0, f"generator failed:\n{r.stdout}\n{r.stderr}"
    s0 = next((out / "b").glob("s0*adapter.sv")).read_text()
    assert "axi4_cdc_wr #(" in s0 and "axi4_cdc_rd #(" in s0
    assert ".m_axi_awvalid(cdc_s0_axi_awvalid)" in s0            # wrapper -> aclk-side net
    assert ".m_axi_awvalid(s0_awvalid)" in s0                    # crossing -> port
    assert "bridge_cdc_slave_arb" not in s0


def test_master_cdc_generation_smoke(tmp_path):
    """bridge_3x2_rw_mcdc (GitHub #119 L2): cpu (rw) and lfsr (rd) master
    ports have their own clock pins; each adapter takes ext_aclk/ext_aresetn
    and crosses the port onto aclk AHEAD of its timing wrapper, one CDC per
    direction present; dma is unchanged; the ddr slave CDC still emits."""
    gen, fl = _generate_fixture(tmp_path, "bridge_3x2_rw_mcdc")
    top = (gen / "bridge_3x2_rw_mcdc.sv").read_text()
    for port in ("cpu", "lfsr", "ddr"):
        assert re.search(rf"input\s+logic[^\n]*{port}_aclk,", top), port
        assert re.search(rf"input\s+logic[^\n]*{port}_aresetn,", top), port
    assert "dma_aclk" not in top and "sram_aclk" not in top
    assert ".ext_aclk(cpu_aclk)" in top and ".ext_aresetn(lfsr_aresetn)" in top
    cpu = (gen / "cpu_adapter.sv").read_text()
    assert "input  logic ext_aclk" in cpu
    assert "axi4_cdc_wr #(" in cpu and "axi4_cdc_rd #(" in cpu
    assert ".s_aclk(ext_aclk), .s_aresetn(ext_aresetn)" in cpu
    assert ".m_aclk(aclk), .m_aresetn(aresetn)" in cpu
    assert ".s_axi_awvalid(cpu_m_axi_awvalid)" in cpu            # the port enters the crossing ...
    assert ".m_axi_awvalid(cdcx_axi_awvalid)" in cpu             # ... which drives an aclk net
    # ... that the timing wrapper takes as its external side
    wrapper = cpu[cpu.index("u_timing_wrapper_wr"):]
    assert "(cdcx_axi_awvalid)" in wrapper and "(cpu_m_axi_awvalid)" not in wrapper
    lfsr = (gen / "lfsr_adapter.sv").read_text()
    assert "axi4_cdc_rd #(" in lfsr and "axi4_cdc_wr" not in lfsr
    assert "cdcx_axi_awvalid" not in lfsr                       # rd-only: no write-side nets
    dma = (gen / "dma_adapter.sv").read_text()
    assert "axi4_cdc" not in dma and "ext_aclk" not in dma
    text = fl.read_text()
    assert "axi4_cdc_wr.f" in text and "axi4_cdc_rd.f" in text


# ---------------------------------------------------------------------
# bridge TASK-007 (was BRIDGE-018): native AXI5 -- MTE and chunking through the fabric
# ---------------------------------------------------------------------

def test_axi5_native_generation_smoke(tmp_path):
    """bridge_2x2_axi5_native: the structs carry the tag and chunk fields
    sized for 128-bit data (one 4-bit tag, one chunk strobe), the crossbar
    drives them to the slave ports, the adapters bind them to the wrapper
    pins, and the top exposes them on every port."""
    gen, fl = _generate_fixture(tmp_path, "bridge_2x2_axi5_native")
    pkg = (gen / "bridge_2x2_axi5_native_pkg.sv").read_text()
    for field in ("tagop;", "tag;", "tagupdate;", "tagmatch;", "chunken;", "chunkv;", "chunknum;", "chunkstrb;"):
        assert field in pkg, field
    assert "logic [3:0]  tag;" in pkg and "logic [3:0]  chunknum;" in pkg
    # BTAGMATCH is 2 bits (IHI 0022L A12.2, GitHub #102 item 5).
    assert "logic [1:0]  tagmatch;" in pkg
    assert "logic         tagupdate;" in pkg and "logic         chunkstrb;" in pkg
    xbar = (gen / "bridge_2x2_axi5_native_xbar.sv").read_text()
    for sig in ("ddr_axi_awtagop", "ddr_axi_wtag", "ddr_axi_wtagupdate", "ddr_axi_archunken",
                "sram_axi_rchunkv", "sram_axi_rchunknum", "sram_axi_rtag", "sram_axi_btagmatch"):
        assert sig in xbar, sig
    assert "cpu_128b_r.chunkv" in xbar and "dma_128b_b.tagmatch" in xbar
    cpu = (gen / "cpu_adapter.sv").read_text()
    for w in ("fub_axi_awtagop", "fub_axi_wtag", "fub_axi_btagmatch", "fub_axi_archunken",
              "fub_axi_rchunknum", "fub_axi_rtag"):
        assert w in cpu, w
    # Not in the spec (A12.2): no AWTAG, BTAG or RTAGMATCH anywhere.
    for gone in ("awtag;", "awtag)", "_awtag,", "btag)", "_btag,", "rtagmatch"):
        assert gone not in cpu, gone
    assert "ENABLE_MTE(1'b1" in cpu and "ENABLE_CHUNKING(1'b1" in cpu   # wrapper parameter overrides
    top = (gen / "bridge_2x2_axi5_native.sv").read_text()
    for port in ("cpu_axi_awtagop", "cpu_axi_wtagupdate", "cpu_axi_btagmatch", "cpu_axi_archunken",
                 "cpu_axi_rchunkstrb", "ddr_axi_wtag", "ddr_axi_rtag", "sram_axi_rchunknum"):
        assert re.search(rf"\b{port}\b", top), port
    assert re.search(r"output\s+logic \[1:0\]\s+cpu_axi_btagmatch", top)
    for gone in ("cpu_axi_awtag", "cpu_axi_btag", "cpu_axi_rtagmatch", "ddr_axi_awtag"):
        assert not re.search(rf"\b{gone}\b", top), gone


def test_axi5_native_tag_widths_follow_data_width(tmp_path):
    """A 256-bit MTE port carries two tags per beat: 8-bit tag fields, 2-bit
    tagupdate and chunk strobe; the fabric sizes struct and port alike."""
    toml, conn = _write_min_toml(
        tmp_path,
        slave_extra=('channels = "rd"\nprotocol = "axi5"\naxi5_features = ["mte", "chunking"]'),
        master_extra='protocol = "axi5"\naxi5_features = ["mte", "chunking"]',
        data_width=256,
    )
    from bridge_pkg.sideband import field_width, WIDTH_TAGS, WIDTH_NTAGS, WIDTH_CHUNKSTRB
    assert field_width(WIDTH_TAGS, 256) == 8 and field_width(WIDTH_NTAGS, 256) == 2
    assert field_width(WIDTH_CHUNKSTRB, 128) == 1 and field_width(WIDTH_TAGS, 32) == 4
    load_config(toml, conn)   # accepted: both ends AXI5, mte, width-matched, wide enough


def test_two_bridges_share_no_module_names(tmp_path):
    """Two generated bridges must coexist in one design. Adapters used to be
    named after the port alone (<port>_adapter) and every bridge emits a
    subtractive_adapter, so a configuration bridge and a data bridge in one
    harness (the Genesys 2 fabric benchmark) defined the same modules twice
    with different bodies. Every generated module now carries its bridge's
    name; the files keep their <port>_adapter.sv names."""
    toml, conn = _write_min_toml(tmp_path, slave_extra='channels = "rd"')
    env = dict(os.environ, REPO_ROOT=str(REPO_ROOT))
    modules = {}
    for name in ("bridge_one", "bridge_two"):
        r = subprocess.run(
            [sys.executable, str(BIN_DIR / "bridge_generator.py"),
             "--ports", toml, "--connectivity", conn,
             "--name", name, "--output-dir", str(tmp_path / "o")],
            cwd=str(BIN_DIR), env=env, capture_output=True, text=True, timeout=300)
        assert r.returncode == 0, f"generator failed:\n{r.stdout}\n{r.stderr}"
        found = set()
        for sv in (tmp_path / "o" / name).glob("*.sv"):
            found |= set(re.findall(r"^\s*module\s+(\w+)", sv.read_text(), re.M))
        assert all(m.startswith(name) for m in found), sorted(found)
        assert f"{name}_s0_adapter" in found and f"{name}_m0_adapter" in found, sorted(found)
        assert f"{name}_subtractive_adapter" in found, sorted(found)
        assert (tmp_path / "o" / name / "s0_adapter.sv").exists()
        modules[name] = found
    assert not modules["bridge_one"] & modules["bridge_two"]


# --- bridge GitHub #119 L1: the one-target-per-master limitation, fixed ----

def _with_bridge_key(toml_path: str, line: str) -> str:
    p = Path(toml_path)
    p.write_text(p.read_text().replace('variants = ["no"]', f'variants = ["no"]\n{line}', 1))
    return toml_path


def test_id_track_bits_defaults_to_4(tmp_path):
    toml, conn = _write_min_toml(tmp_path, slave_extra='channels = "rd"')
    assert load_config(toml, conn).id_track_bits == 4


@pytest.mark.parametrize("bad", [-1, 9])
def test_id_track_bits_out_of_range_rejected(tmp_path, bad):
    toml, conn = _write_min_toml(tmp_path, slave_extra='channels = "rd"')
    _with_bridge_key(toml, f"id_track_bits = {bad}")
    with pytest.raises(ValueError, match="id_track_bits"):
        load_config(toml, conn)


@pytest.mark.parametrize("bits,entries", [(2, 4), (8, 16), (0, 1)])
def test_id_track_bits_sizes_the_adapter_table(tmp_path, bits, entries):
    """The per-ID table has 2**min(id_track_bits, master id_width) entries,
    and the one-outstanding-target register is gone."""
    toml, conn = _write_min_toml(tmp_path, slave_extra='channels = "rd"')
    _with_bridge_key(toml, f"id_track_bits = {bits}")
    out = tmp_path / "gen"
    env = dict(os.environ, REPO_ROOT=str(REPO_ROOT))
    r = subprocess.run(
        [sys.executable, str(BIN_DIR / "bridge_generator.py"),
         "--ports", toml, "--connectivity", conn, "--name", "b",
         "--output-dir", str(out)],
        cwd=str(BIN_DIR), env=env, capture_output=True, text=True, timeout=300)
    assert r.returncode == 0, f"generator failed:\n{r.stdout}\n{r.stderr}"
    adapter = next((out / "b").glob("*m0*adapter.sv")).read_text()
    assert f"localparam int AR_IDT_N = {entries};" in adapter
    assert "r_ar_active_target" not in adapter
    assert "assign ar_gate_ok = ar_id_ok && !ar_trk_full;" in adapter


# --- bridge GitHub #119 L8: DV generated anywhere is complete --------------

def _gen_with_tests(tmp_path, toml, conn):
    out = tmp_path / "gen"
    env = dict(os.environ, REPO_ROOT=str(REPO_ROOT))
    r = subprocess.run(
        [sys.executable, str(BIN_DIR / "bridge_generator.py"),
         "--ports", toml, "--connectivity", conn, "--name", "b",
         "--output-dir", str(out / "rtl"), "--generate-tests",
         "--output-tb", str(out / "tb"), "--output-test", str(out / "test")],
        cwd=str(BIN_DIR), env=env, capture_output=True, text=True, timeout=300)
    assert r.returncode == 0, f"generator failed:\n{r.stdout}\n{r.stderr}"
    return (next((out / "tb").glob("*tb.py")).read_text(),
            next((out / "test").glob("test_*.py")).read_text())


def test_generated_tb_carries_connectivity_and_shared_paths(tmp_path):
    """A TB generated outside the component must not depend on finding the
    component's CSV or on PYTHONPATH reaching bridge/dv/tbclasses."""
    toml, conn = _write_min_toml(tmp_path, slave_extra='channels = "rd"')
    tb, _ = _gen_with_tests(tmp_path, toml, conn)
    assert "self.connectivity = {" in tb and "0: {0, },  # m0" in tb
    assert "fabric-gen-ip/bridge/dv/tbclasses'" in tb


def test_alignment_test_emitted_only_for_aligner_paths(tmp_path):
    """AXIL master writing a wider slave -> the narrow-to-wide lane test;
    an AXI4 master of the same shape -> none (it is not an aligner path)."""
    def gen(sub, proto):
        d = tmp_path / sub
        d.mkdir()
        toml, conn = _write_min_toml(d, slave_extra='channels = "rw"', master_channels="rw")
        p = Path(toml)
        t = p.read_text()
        # master 32b -> slave 128b; master protocol as given
        t = t.replace('data_width = 32\nid_width = 4\nchannels = "rw"',
                      f'data_width = 32\nid_width = {0 if proto == "axil" else 4}\nchannels = "rw"\nprotocol = "{proto}"', 1)
        t = t.replace('data_width = 32\nid_width = 4\nbase_addr', 'data_width = 128\nid_width = 4\nbase_addr', 1)
        p.write_text(t)
        return _gen_with_tests(d, toml, conn)[1]
    axil = gen("axil", "axil")
    assert "def test_b_narrow_to_wide_alignment(" in axil
    assert "enumerate([0, 4, 8, 12])" in axil
    assert "narrow_to_wide_alignment" not in gen("axi4", "axi4")


# --- bridge GitHub #119 L5: configurable outstanding limits ------------------

def test_max_outstanding_defaults_and_overrides(tmp_path):
    toml, conn = _write_min_toml(tmp_path, slave_extra='channels = "rd"\nmax_outstanding = 32')
    _with_bridge_key(toml, "max_outstanding = 4")
    cfg = load_config(toml, conn)
    assert cfg.masters[0].max_outstanding == 4      # inherits [bridge]
    assert cfg.slaves[0].max_outstanding == 32      # port override


@pytest.mark.parametrize("bad", [1, 3, 24, 128, "x"])
def test_max_outstanding_rejects_non_power_of_two_or_out_of_range(tmp_path, bad):
    toml, conn = _write_min_toml(tmp_path, slave_extra='channels = "rd"')
    _with_bridge_key(toml, f"max_outstanding = {bad!r}" if isinstance(bad, str) else f"max_outstanding = {bad}")
    with pytest.raises(ValueError, match="max_outstanding"):
        load_config(toml, conn)


# --- bridge W2: rate-matching buffers on upsized paths into shared slaves ----

def test_rate_buffer_defaults_and_overrides(tmp_path):
    toml, conn = _write_min_toml(tmp_path, slave_extra='channels = "rd"',
                                 master_extra='rate_buffer = 8')
    cfg = load_config(toml, conn)
    assert cfg.masters[0].rate_buffer == 8                  # port override
    (tmp_path / "d").mkdir()
    toml2, conn2 = _write_min_toml(tmp_path / "d", slave_extra='channels = "rd"')
    assert load_config(toml2, conn2).masters[0].rate_buffer == 16   # default
    _with_bridge_key(toml2, "rate_buffer = 0")
    assert load_config(toml2, conn2).masters[0].rate_buffer == 0    # [bridge], off


@pytest.mark.parametrize("bad", [1, 257, -2, "x"])
def test_rate_buffer_rejects_out_of_range(tmp_path, bad):
    toml, conn = _write_min_toml(tmp_path, slave_extra='channels = "rd"')
    _with_bridge_key(toml, f"rate_buffer = {bad!r}" if isinstance(bad, str) else f"rate_buffer = {bad}")
    with pytest.raises(ValueError, match="rate_buffer"):
        load_config(toml, conn)


def test_rate_buffer_only_on_upsized_paths_into_shared_slaves(tmp_path):
    """bridge_4x4_rw: dma0 (32b) reaches ddr0 (64b, shared with cpu) -- a
    buffer on its 64b path; cpu (64b) reaches ddr0 width-matched -- none on
    that path. Every buffer present is on an upsized path."""
    out = tmp_path / "gen"
    env = dict(os.environ, REPO_ROOT=str(REPO_ROOT))
    r = subprocess.run(
        [sys.executable, str(BIN_DIR / "bridge_generator.py"),
         "--ports", _fixture("bridge_4x4_rw.toml"),
         "--connectivity", _fixture("bridge_4x4_rw_connectivity.csv"),
         "--name", "q", "--output-dir", str(out)],
        cwd=str(BIN_DIR), env=env, capture_output=True, text=True, timeout=300)
    assert r.returncode == 0, r.stdout + r.stderr
    d = out / "q"
    dma0 = (d / "dma0_master_adapter.sv").read_text()
    cpu = (d / "cpu_master_adapter.sv").read_text()
    assert "u_wr_rbuf_64b" in dma0 and "u_rd_rbuf_64b" in dma0
    assert "u_wr_rbuf_64b" not in cpu and "u_rd_rbuf_64b" not in cpu
    for f in d.glob("*_master_adapter.sv"):
        mw = int(re.search(r"S_AXI_DATA_WIDTH\((\d+)\)", f.read_text()).group(1)) \
            if "S_AXI_DATA_WIDTH" in f.read_text() else None
        for w in re.findall(r"u_wr_rbuf_(\d+)b", f.read_text()):
            assert mw is not None and int(w) > mw, f"{f.name}: buffer on a non-upsized {w}b path"
    fl = (out / "filelists" / "q.f") if (out / "filelists" / "q.f").exists() else None
    if fl is not None:
        assert "bridge_wr_rate_buf.f" in fl.read_text()


def test_max_outstanding_sizes_every_tracker(tmp_path):
    """bridge_2x2_rw_depth: [bridge] 4, cpu 64, ddr 32. Master trackers,
    slave trackers, and the crossbar's W-owner (per slave) and W-destination
    (per master path) FIFOs all follow the configured limits."""
    out = tmp_path / "gen"
    env = dict(os.environ, REPO_ROOT=str(REPO_ROOT))
    r = subprocess.run(
        [sys.executable, str(BIN_DIR / "bridge_generator.py"),
         "--ports", _fixture("bridge_2x2_rw_depth.toml"),
         "--connectivity", _fixture("bridge_2x2_rw_depth_connectivity.csv"),
         "--name", "d", "--output-dir", str(out)],
        cwd=str(BIN_DIR), env=env, capture_output=True, text=True, timeout=300)
    assert r.returncode == 0, r.stdout + r.stderr
    d = out / "d"
    cpu = (d / "cpu_adapter.sv").read_text()
    dma = (d / "dma_adapter.sv").read_text()
    x = (d / "d_xbar.sv").read_text()
    assert "localparam int AW_TRK_DEPTH = 64;" in cpu
    assert "localparam int AW_TRK_DEPTH = 4;" in dma
    assert "wr_trk_full = (wr_out_cnt == 6'(32));" in (d / "ddr_adapter.sv").read_text()
    assert "rd_trk_full = (rd_out_cnt == 3'(4));" in (d / "sram_adapter.sv").read_text()
    assert "ddr_wowner_mem [32];" in x and "sram_wowner_mem [4];" in x
    assert "cpu_32b_wdest_mem [64];" in x and "dma_32b_wdest_mem [4];" in x


# --- bridge GitHub #119 L7: per-port latency modes, honoured skid depths ----

def _timing_toml(tmp_path, bridge_extra="", master_extra="", slave_extra='channels = "rw"',
                 master_proto="axi4"):
    toml, conn = _write_min_toml(tmp_path, slave_extra=slave_extra,
                                 master_extra=f'protocol = "{master_proto}"\n' + master_extra,
                                 master_channels="rw")
    if master_proto in ("axil", "apb"):
        p = Path(toml)
        p.write_text(p.read_text().replace("id_width = 4\nchannels = \"rw\"",
                                           "id_width = 0\nchannels = \"rw\"", 1))
    if bridge_extra:
        _with_bridge_key(toml, bridge_extra)
    return toml, conn


def test_skid_depths_resolve_defaults_bridge_port_then_latency(tmp_path):
    toml, conn = _timing_toml(
        tmp_path,
        bridge_extra="[bridge.defaults.skid_depths]\nr = 4",
        master_extra='latency = "cut_ax"\n[bridge.masters.interface.skid_depths]\naw = 6',
    )
    cfg = load_config(toml, conn)
    m, s = cfg.masters[0], cfg.slaves[0]
    assert m.latency == "cut_ax"
    assert m.skid_depths == {'aw': 6, 'w': 0, 'b': 0, 'ar': 2, 'r': 0}
    assert s.latency == "cut_all"
    assert s.skid_depths == {'aw': 2, 'w': 4, 'b': 2, 'ar': 2, 'r': 4}


@pytest.mark.parametrize("extra,match", [
    ('latency = "fast"', "latency must be one of"),
    ('[bridge.masters.interface.skid_depths]\naw = 1', "must be an integer 2..8"),
    ('[bridge.masters.interface.skid_depths]\nq = 2', "unknown channel"),
])
def test_latency_and_skid_validation(tmp_path, extra, match):
    toml, conn = _timing_toml(tmp_path, master_extra=extra)
    with pytest.raises(ValueError, match=match):
        load_config(toml, conn)


def test_latency_rejected_on_converted_ports(tmp_path):
    """A converted port has buffers the mode does not reach -- reject, don't
    half-apply."""
    toml, conn = _timing_toml(tmp_path, master_extra='latency = "cut_none"', master_proto="axil")
    with pytest.raises(ValueError, match="only legal on a same-clock axi4/axi5 port"):
        load_config(toml, conn)


def test_latency_cut_reaches_the_rtl(tmp_path):
    toml, conn = _timing_toml(tmp_path, master_extra='latency = "cut_none"',
                              slave_extra='channels = "rw"\nlatency = "cut_ax"')
    out = tmp_path / "gen"
    env = dict(os.environ, REPO_ROOT=str(REPO_ROOT))
    r = subprocess.run(
        [sys.executable, str(BIN_DIR / "bridge_generator.py"), "--ports", toml,
         "--connectivity", conn, "--name", "b", "--output-dir", str(out)],
        cwd=str(BIN_DIR), env=env, capture_output=True, text=True, timeout=300)
    assert r.returncode == 0, r.stdout + r.stderr
    m = next((out / "b").glob("m0*adapter.sv")).read_text()
    s = next((out / "b").glob("s0*adapter.sv")).read_text()
    for ch in ("AW", "W", "B", "AR", "R"):
        assert f"parameter SKID_DEPTH_{ch} = 0" in m
    assert ".SKID_DEPTH_AW(2)" in s and ".SKID_DEPTH_W(0)" in s and ".SKID_DEPTH_R(0)" in s


# ---------------------------------------------------------------------
# Slave watchdog and protocol-checker binds (GitHub #119 L3)
# ---------------------------------------------------------------------

def test_timeout_needs_axi4_slave(tmp_path):
    toml, conn = _write_req_toml(tmp_path, """
addr_width = 32
data_width = 32
id_width = 4
channels = "rw"
protocol = "axi4"
""", slave_block="""
[[bridge.slaves]]
name = "s0"
prefix = "s0_"
addr_width = 32
data_width = 32
id_width = 0
channels = "rw"
protocol = "apb"
timeout_cycles = 64
base_addr = "0x0000_0000"
addr_range = "0x0001_0000"
""")
    with pytest.raises(ValidationError, match='timeout_cycles needs protocol = "axi4"'):
        load_config(toml, conn)


def test_timeout_minimum(tmp_path):
    toml, conn = _write_req_toml(tmp_path, """
addr_width = 32
data_width = 32
id_width = 4
channels = "rw"
protocol = "axi4"
""", slave_block="""
[[bridge.slaves]]
name = "s0"
prefix = "s0_"
addr_width = 32
data_width = 32
id_width = 4
channels = "rw"
protocol = "axi4"
timeout_cycles = 1
base_addr = "0x0000_0000"
addr_range = "0x0001_0000"
""")
    with pytest.raises(ValidationError, match="must be 0 or >= 2"):
        load_config(toml, conn)


def test_watchdog_generation_smoke(tmp_path):
    """bridge_2x2_rw_wdog: ddr's adapter carries axi4_slave_watchdog between
    its timing wrapper and the port, the top gains ddr_timeout, sram has no
    watchdog, and the filelist pulls the watchdog's closure."""
    gen, fl = _generate_fixture(tmp_path, "bridge_2x2_rw_wdog")
    top = (gen / "bridge_2x2_rw_wdog.sv").read_text()
    assert re.search(r"output\s+logic[^\n]*ddr_timeout,", top)
    assert ".o_wdog_tripped(ddr_timeout)" in top and "sram_timeout" not in top
    ddr = (gen / "ddr_adapter.sv").read_text()
    assert "axi4_slave_watchdog #(" in ddr and ".TIMEOUT_CYCLES(64)" in ddr
    assert ".m_axi_awvalid(wdg_ddr_axi_awvalid)" in ddr       # wrapper -> watchdog
    assert ".s_axi_awvalid(wdg_ddr_axi_awvalid)" in ddr       # watchdog takes it ...
    assert ".m_axi_awvalid(ddr_s_axi_awvalid)" in ddr         # ... and drives the port
    assert "axi4_slave_watchdog" not in (gen / "sram_adapter.sv").read_text()
    assert "axi4_slave_watchdog.f" in fl.read_text()


def test_checker_binds_smoke(tmp_path):
    """Every AXI4/AXI5 port gets a bind on its own clock; the checker
    filelist adds the checker and the bind file to the bridge filelist."""
    gen, fl = _generate_fixture(tmp_path, "bridge_3x2_rw_mcdc")
    binds = (gen / "bridge_3x2_rw_mcdc_checkers.sv").read_text()
    for port, clk in (("cpu", "cpu_aclk"), ("dma", "aclk"), ("lfsr", "lfsr_aclk"),
                      ("ddr", "ddr_aclk"), ("sram", "aclk")):
        block = binds[binds.index(f"u_chk_{port} ("):]
        assert f".aclk({clk})" in block.split(");")[0], port
    lfsr = binds[binds.index("u_chk_lfsr ("):].split(");")[0]
    assert ".awvalid(1'b0)" in lfsr and ".arvalid(lfsr_m_axi_arvalid)" in lfsr  # rd-only ties W
    chk_fl = (fl.parent / "bridge_3x2_rw_mcdc_checkers.f").read_text()
    assert "axi4_protocol_checker.sv" in chk_fl and "bridge_3x2_rw_mcdc_checkers.sv" in chk_fl
    assert "bridge_3x2_rw_mcdc.f" in chk_fl


def test_axi3_slave_adapter_is_axi4_shaped(tmp_path):
    """An AXI3 slave adapter is built like an AXI4 one (bridge W11): the
    timing wrapper faces the crossbar, a multi-master slave tracks responses
    by ID, the crossbar arbitrates it from request slots, and
    axi4_to_axi3 is the last stage, fed from the wrapper's a3c_* nets. (The
    converter used to face the crossbar directly: R and B were unregistered
    from the pins to the arbiter, and responses were routed by position.)"""
    gen, fl = _generate_fixture(tmp_path, "bridge_2x2_axi3_slaves")
    ad = (gen / "ddr_axi3_adapter.sv").read_text()
    assert "u_master_wr (" in ad and "u_master_rd (" in ad
    assert "rd_out_cnt" in ad and "bridge_cam" not in ad
    assert "axi4_to_axi3 #(" in ad
    assert ".s_axi_awvalid (a3c_ddr_axi3_axi_awvalid)" in ad
    assert ".s_axi_rready  (a3c_ddr_axi3_axi_rready)" in ad
    assert "converter_rvalid" not in ad
    # The wrapper sits before the converter in the file, as in the data path.
    assert ad.index("u_master_wr (") < ad.index("axi4_to_axi3 #(")
    xbar = (gen / "bridge_2x2_axi3_slaves_xbar.sv").read_text()
    assert "u_cpu_axi4_64b_aw_slot_ddr_axi3 (" in xbar
    assert "bridge_cam.f" not in fl.read_text()


def test_cdc_slave_arbitrates_on_its_own_clock(tmp_path):
    """bridge W9: a cdc slave that two masters share is arbitrated on its own
    clock. The crossbar picks nothing for it -- each master's AW / W / AR
    leaves on a lane of its own -- and the slave adapter's
    bridge_cdc_slave_arb crosses the lanes and arbitrates on s_aclk. A
    single-clock slave of the same bridge keeps the crossbar's pick."""
    gen, fl = _generate_fixture(tmp_path, "bridge_2x2_rw_cdc")
    xbar = (gen / "bridge_2x2_rw_cdc_xbar.sv").read_text()
    ddr = (gen / "ddr_adapter.sv").read_text()
    sram = (gen / "sram_adapter.sv").read_text()
    assert "output logic [1:0] ddr_axi_lane_awvalid," in xbar
    assert "ddr_aw_arb" not in xbar and "ddr_wowner" not in xbar, "ddr still picked on aclk"
    assert "sram_aw_arb" in xbar, "the single-clock slave lost its arbiter"
    assert "bridge_cdc_slave_arb #(" in ddr and ".NM(2)," in ddr
    assert "axi4_cdc_wr" not in ddr, "one crossing behind a fabric-side pick (W9)"
    assert "bridge_cdc_slave_arb" not in sram
    assert "bridge_cdc_slave_arb.f" in fl.read_text()


def test_shim_slave_is_picked_from_slots(tmp_path):
    """bridge W14: an APB / AXI4-Lite / WB4 slave that several masters share
    is picked from registered request slots, like an AXI slave. Picked from
    the masters' live requests, one master's request gate ran through the
    grant into another master's accept (bridge_mix_e's worst path)."""
    gen, _fl = _generate_fixture(tmp_path, "bridge_mix_e")
    xbar = (gen / "bridge_mix_e_xbar.sv").read_text()
    assert "u_cpu_axi3_64b_aw_slot_apb_periph (" in xbar or "_aw_slot_apb_periph (" in xbar
    assert "_ar_slot_apb_periph (" in xbar


def test_r_interleave_end_to_end(tmp_path):
    """Slaves may interleave R beats across IDs (AXI4). Every read width
    converter is built to convert per ID (R_INTERLEAVE = 1), and no R
    arbiter -- the crossbar's per master path or the master adapter's
    across its width paths -- holds a grant through RLAST: held, two
    interleaving slaves could each wait on the other's master path."""
    gen, _fl = _generate_fixture(tmp_path, "bridge_mix_e")
    files = {p.name: p.read_text() for p in gen.glob("*.sv")}
    convs = [t for t in files.values() if "axi4_dwidth_converter_rd" in t]
    assert convs, "fixture has no read width converter"
    assert all("R_INTERLEAVE     = 1" in t or ".R_INTERLEAVE(1)" in t for t in convs)
    for name, text in files.items():
        assert "hold through RLAST" not in text, name
        assert "fub_axi_rready && fub_axi_rlast)" not in text, name
