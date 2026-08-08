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
    assert "_xbar #(" in text and "parameter int NUM_SLAVES" in text, (
        "xbar lost the parameter-port-list form"
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
