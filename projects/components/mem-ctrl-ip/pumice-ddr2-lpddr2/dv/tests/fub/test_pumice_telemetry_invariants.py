# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""Unit tests for the telemetry invariants (pumice TASK-015 layer 2b).

Pure Python -- no DUT. Every rule gets a case that MAKES IT FIRE, because a
checker nobody has watched fail is not known to check anything, and this repo has
shipped four of those. `test_every_rule_is_reachable` is the guard against a
rule being added without a firing case.
"""
from __future__ import annotations

import importlib.util
import sys
from pathlib import Path

import pytest

_TB = Path(__file__).resolve().parents[2] / "tbclasses"
_spec = importlib.util.spec_from_file_location(
    "pumice_telemetry_invariants", _TB / "pumice_telemetry_invariants.py")
ti = importlib.util.module_from_spec(_spec)
sys.modules["pumice_telemetry_invariants"] = ti
_spec.loader.exec_module(ti)


def clean(**over) -> dict:
    """A self-consistent counter set: 100 column ops, 40 activations (25 miss +
    15 empty), so 60 hits spread over the eight banks, 38 closes."""
    c = {
        "PAGE_STATS_HIT": 100,      # col_ops, NOT hits
        "SCHED_STATS_ACT": 40,
        "PAGE_STATS_MISS": 25,
        "PAGE_STATS_EMPTY": 15,
        "SCHED_STATS_PRE": 38,
        "REF_STATS_REF": 12,
        "REF_STATS_REF_BUSY": 5,
    }
    per_bank = [8, 8, 8, 8, 7, 7, 7, 7]             # sums to 60 == 100 - 40
    for b, v in enumerate(per_bank):
        c[f"OBS_ROW_HIT{b}_ROW_HIT"] = v
    c.update(over)
    return c


def test_a_consistent_counter_set_is_clean():
    assert ti.check_invariants(clean()) == []


def test_all_rules_arm_on_the_full_counter_set():
    assert all(ti.arming(clean()).values())


# --- one firing case per rule --------------------------------------------
def test_activation_causes_account_fires():
    v = ti.check_invariants(clean(PAGE_STATS_MISS=24))     # 24+15 != 40
    assert any(x.rule == "activation_causes_account" for x in v), v


def test_hits_within_col_ops_fires():
    """Per-bank hits totalling more than the column ops issued is impossible."""
    v = ti.check_invariants(clean(OBS_ROW_HIT0_ROW_HIT=200))
    assert any(x.rule == "hits_within_col_ops" for x in v), v


def test_hits_at_least_col_ops_minus_act_fires():
    """60 col_ops with only 10 ACTs needs >= 50 hits; 0 recorded is impossible."""
    c = clean(PAGE_STATS_HIT=60, SCHED_STATS_ACT=10,
              PAGE_STATS_MISS=10, PAGE_STATS_EMPTY=0, SCHED_STATS_PRE=10)
    for b in range(8):
        c[f"OBS_ROW_HIT{b}_ROW_HIT"] = 0
    v = ti.check_invariants(c)
    assert any(x.rule == "hits_at_least_col_ops_minus_act" for x in v), v


def test_pre_le_act_plus_open_banks_fires():
    """Only beyond the inherited-open-bank slack. PRE=41 against ACT=40 is
    LEGAL -- a window can start with up to NUM_BANKS rows already open, which
    layer 3's soak measured on correct hardware (PRE=43, ACT=42)."""
    assert ti.check_invariants(clean(SCHED_STATS_PRE=41)) == []
    assert ti.check_invariants(clean(SCHED_STATS_PRE=48)) == []      # 40 + 8
    v = ti.check_invariants(clean(SCHED_STATS_PRE=49))               # 40 + 9
    assert any(x.rule == "pre_le_act_plus_open_banks" for x in v), v


def test_refresh_busy_le_refresh_fires():
    v = ti.check_invariants(clean(REF_STATS_REF_BUSY=13))
    assert any(x.rule == "refresh_busy_le_refresh" for x in v), v


def test_every_rule_is_reachable():
    """No rule may exist without a test above that makes it fire."""
    fired = set()
    for name, fn in sorted(globals().items()):
        if name.startswith("test_") and name.endswith("_fires"):
            fired.add(name[len("test_"):-len("_fires")])
    declared = {r.name for r in ti.RULES}
    assert declared == fired, (
        f"rules with no firing test: {sorted(declared - fired)}; "
        f"tests naming no rule: {sorted(fired - declared)}"
    )


# --- arming / vacuity -----------------------------------------------------
def test_a_rule_without_its_counters_does_not_arm():
    partial = {"SCHED_STATS_ACT": 5, "PAGE_STATS_HIT": 10}
    armed = ti.arming(partial)
    assert armed["hits_at_least_col_ops_minus_act"] is False
    assert armed["hits_within_col_ops"] is False
    assert armed["refresh_busy_le_refresh"] is False


def test_assert_clean_refuses_a_vacuous_pass():
    """The failure mode this exists to stop: reporting 'clean' for a rule whose
    counters were never even read."""
    partial = {"SCHED_STATS_ACT": 5, "PAGE_STATS_HIT": 10}
    with pytest.raises(AssertionError, match="never armed"):
        ti.assert_clean(partial, require=("hits_within_col_ops",), context="unit")


def test_assert_clean_returns_the_armed_count():
    n = ti.assert_clean(clean(), require=tuple(r.name for r in ti.RULES), context="unit")
    assert n == len(ti.RULES)


def test_assert_clean_raises_on_a_violation_and_names_the_arithmetic():
    with pytest.raises(AssertionError, match="PRE\\+PREA=49"):
        ti.assert_clean(clean(SCHED_STATS_PRE=49), context="unit")


def test_skip_suppresses_a_named_rule():
    assert ti.check_invariants(clean(SCHED_STATS_PRE=49),
                               skip=("pre_le_act_plus_open_banks",)) == []


def test_sim_only_invariants_are_documented_not_silently_absent():
    """Layer 2b's gaps are written down; this pins that they stay written down."""
    assert set(ti.SIM_ONLY_INVARIANTS) == {
        "ring_occupancy_le_depth", "returned_beats_eq_issued_beats"}
    assert all(len(v) > 80 for v in ti.SIM_ONLY_INVARIANTS.values())


def test_act_exceeding_col_ops_is_legal_under_background_close():
    """MEASURED 2026-09-27: a bank-spreading pattern gave 49 ACTs for 48 column
    ops at policy_mode=3 / tr_init=2, because a row can be opened, timed out and
    reopened before its column command issues. This module asserted the opposite
    at first. Pin it, so the unsound invariant cannot come back."""
    c = clean(PAGE_STATS_HIT=48, SCHED_STATS_ACT=49, PAGE_STATS_MISS=1,
              PAGE_STATS_EMPTY=48, SCHED_STATS_PRE=49)
    for b in range(8):
        c[f"OBS_ROW_HIT{b}_ROW_HIT"] = 0
    assert ti.check_invariants(c) == [], ti.check_invariants(c)
    assert ti.derived_hits_unsound(c) == -1, "the RDL's derivation goes negative here"
