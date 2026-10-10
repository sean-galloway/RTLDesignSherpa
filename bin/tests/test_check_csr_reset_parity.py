# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""Tests for bin/check_csr_reset_parity.py (pumice TASK-015 layer 0).

A gate nobody has seen fail is not known to work. Four blind checkers have
shipped in this repo (handbook: checker-verdict-needs-a-count), so every rule
this one enforces gets a test that MUTATES a fixture and asserts the rule fires,
plus one that asserts the real pumice manifest passes.
"""
from __future__ import annotations

import importlib.util
import sys
import textwrap
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parents[2]
CHECKER = ROOT / "bin" / "check_csr_reset_parity.py"
PUMICE_MANIFEST = (ROOT / "projects/components/mem-ctrl-ip/mem-ctrl-research-ip/pumice-ddr2-lpddr2"
                   / "dv/csr_reset_parity.py")

_spec = importlib.util.spec_from_file_location("ccrp", CHECKER)
ccrp = importlib.util.module_from_spec(_spec)
sys.modules["ccrp"] = ccrp
_spec.loader.exec_module(ccrp)


REGMAP_SRC = textwrap.dedent("""\
    # Auto-generated register map from: fake.rdl
    top_block = {
        'CFG': {
            'address': '0x000', 'offset': '0x000', 'size': 4, 'name': 'CFG',
            'default': '0x00000005', 'sw': 'rw', 'type': 'reg',
            'a_field': {'default': '0x05', 'offset': '7:0', 'sw': 'rw', 'type': 'field'},
            'b_field': {'default': '0x00', 'offset': '15:8', 'sw': 'rw', 'type': 'field'},
            'ro_field': {'default': '0x00', 'offset': '23:16', 'sw': 'r', 'type': 'field'},
        },
    }
    """)

MANIFEST_TMPL = textwrap.dedent("""\
    REGMAP = "fake_regmap.py"
    RDL = "fake.rdl"
    FIELDS = {{
        "CFG.a_field": dict(ships=0x05),
        {extra}
    }}
    """)


def _fixture(tmp_path: Path, extra: str, regmap: str = REGMAP_SRC) -> Path:
    (tmp_path / "fake_regmap.py").write_text(regmap)
    (tmp_path / "fake.rdl").write_text("// fake\n")
    man = tmp_path / "csr_reset_parity.py"
    man.write_text(MANIFEST_TMPL.format(extra=extra))
    return man


def _errs(man: Path) -> list[str]:
    return ccrp.check(man)


# --- the happy path -------------------------------------------------------
def test_a_fully_declared_manifest_passes(tmp_path):
    assert _errs(_fixture(tmp_path, '"CFG.b_field": dict(waived="strobe"),')) == []


# --- one test per rule, each proven by making it fire ---------------------
def test_an_undeclared_field_is_reported(tmp_path):
    errs = _errs(_fixture(tmp_path, ""))
    assert any("CFG.b_field" in e and "UNACCOUNTED" in e for e in errs), errs


def test_a_wrong_ships_value_is_reported(tmp_path):
    errs = _errs(_fixture(tmp_path, '"CFG.b_field": dict(ships=0x99),'))
    assert any("RESET PARITY BROKEN" in e and "CFG.b_field" in e for e in errs), errs


def test_swept_needs_two_distinct_values(tmp_path):
    errs = _errs(_fixture(tmp_path, '"CFG.b_field": dict(swept=(1, 1), by="bin/check_csr_reset_parity.py", oracle="x", drives="check"),'))
    assert any(">= 2 distinct" in e for e in errs), errs


def test_swept_needs_an_oracle(tmp_path):
    """The load-bearing rule: a CSR walk writes two values and proves nothing."""
    errs = _errs(_fixture(tmp_path, '"CFG.b_field": dict(swept=(1, 2), by="bin/check_csr_reset_parity.py", drives="check"),'))
    assert any("oracle=" in e for e in errs), errs


def test_swept_artifact_must_exist(tmp_path):
    errs = _errs(_fixture(tmp_path, '"CFG.b_field": dict(swept=(1, 2), by="no/such/file.py", oracle="x"),'))
    assert any("does not exist" in e for e in errs), errs


def test_swept_artifact_must_mention_the_field_or_its_port(tmp_path):
    errs = _errs(_fixture(tmp_path, '"CFG.b_field": dict(swept=(1, 2), by="bin/check_csr_reset_parity.py", oracle="x"),'))
    assert any("never mentions" in e for e in errs), errs


def test_drives_lets_a_port_level_sweep_satisfy_the_mention_check(tmp_path):
    """The scheduler matrix drives an RTL port, not the CSR field name."""
    errs = _errs(_fixture(tmp_path, '"CFG.b_field": dict(swept=(1, 2), by="bin/check_csr_reset_parity.py", oracle="x", drives="RESET PARITY BROKEN"),'))
    assert errs == [], errs


def test_an_empty_waiver_reason_is_reported(tmp_path):
    errs = _errs(_fixture(tmp_path, '"CFG.b_field": dict(waived="   "),'))
    assert any("written reason" in e for e in errs), errs


def test_two_kinds_on_one_field_is_reported(tmp_path):
    errs = _errs(_fixture(tmp_path, '"CFG.b_field": dict(ships=0, waived="both"),'))
    assert any("exactly one of" in e for e in errs), errs


def test_a_manifest_entry_for_a_vanished_field_is_reported(tmp_path):
    errs = _errs(_fixture(tmp_path, '"CFG.b_field": dict(waived="strobe"),\n    "CFG.gone": dict(ships=0),'))
    assert any("CFG.gone" in e and "not a sw=rw field" in e for e in errs), errs


def test_a_readonly_field_needs_no_entry(tmp_path):
    """sw=r fields are out of scope -- the gate is about writable config."""
    errs = _errs(_fixture(tmp_path, '"CFG.b_field": dict(waived="strobe"),'))
    assert not any("ro_field" in e for e in errs), errs


def test_a_regmap_from_a_different_rdl_is_reported(tmp_path):
    errs = _errs(_fixture(tmp_path, '"CFG.b_field": dict(waived="strobe"),',
                          regmap=REGMAP_SRC.replace("fake.rdl", "somethingelse.rdl")))
    assert any("does not name" in e for e in errs), errs


# --- the real manifest ----------------------------------------------------
def test_the_pumice_manifest_passes(tmp_path):
    assert PUMICE_MANIFEST.exists(), "pumice manifest went missing"
    assert _errs(PUMICE_MANIFEST) == []


def test_the_pumice_manifest_covers_every_writable_field(tmp_path):
    """Regression on the gate's reason for existing: no field left undeclared."""
    man = ccrp._load(PUMICE_MANIFEST, "_m")
    fields = ccrp._rw_fields((PUMICE_MANIFEST.parent / man.REGMAP).resolve())
    assert set(fields) == set(man.FIELDS), (
        f"undeclared: {sorted(set(fields) - set(man.FIELDS))}; "
        f"stale entries: {sorted(set(man.FIELDS) - set(fields))}"
    )
    assert len(fields) == man.DOCUMENTED_FIELD_COUNT, (
        f"{len(fields)} sw=rw fields vs DOCUMENTED_FIELD_COUNT="
        f"{man.DOCUMENTED_FIELD_COUNT} in dv/csr_reset_parity.py -- the count "
        f"must move with the design (BUG-023): update the constant and the "
        f"docstring composition note in the same commit that adds or retires "
        f"fields. A floor that does not move is decorative."
    )
