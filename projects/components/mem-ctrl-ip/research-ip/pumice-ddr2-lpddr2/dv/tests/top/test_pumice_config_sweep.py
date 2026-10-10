# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""Pairwise config covering array x hazard axes (pumice TASK-015 layer 1).

The question this exists to answer is Sean's: *"Are there another 50 bugs laying
dormant in the rtl right now??? How do I tell????"*

BUG-003 was a TWO-WAY interaction -- `policy_mode=3` crossed with `rd_gap>=8`.
Single-field coverage called it green, because policy_mode had been run at three
distinct values and the gap axis had been run too, just never together. The full
cross product of pumice's 15 runtime mode selectors is ~5.9e8 vectors, so nobody
was ever going to run it.

A pairwise covering array does: 39 vectors in which EVERY 2-way combination of
selector values appears at least once (tbclasses/pumice_config_array.py, with
its own unit tests). Crossed with the mandatory hazard axes -- the read gap and
the traffic direction -- that is the sweep:

    39 config vectors  x  gap {0,4,8,15}  x  direction {sequential, concurrent}
    = 312 cells at FULL

One pytest cell per (vector, gap, direction), so the run distributes across
workers: the task's estimate is under 2 h at `-n 16`. Nightly, never a gate --
GATE and FUNC run a subset, and `test_pumice_config_sweep_coverage` reports the
coverage NUMBER without needing any simulation at all.

THE ORACLE IS NOT "IT RAN". Each cell checks golden data integrity through the
DFI slave's MemoryModel AND the layer-2b telemetry invariants. A sweep with no
oracle cannot fail, and with layer 2a dropped (no assertions in RTL) these are
the two that remain.
"""
from __future__ import annotations

import importlib.util
import os
import sys

import pytest

_DV_DIR = os.path.abspath(os.path.join(os.path.dirname(__file__), "../.."))
if _DV_DIR not in sys.path:
    sys.path.insert(0, _DV_DIR)


def _load(name):
    spec = importlib.util.spec_from_file_location(
        name, os.path.join(_DV_DIR, "tbclasses", f"{name}.py"))
    mod = importlib.util.module_from_spec(spec)
    sys.modules[name] = mod
    spec.loader.exec_module(mod)
    return mod


ca = _load("pumice_config_array")

GAPS = (0, 4, 8, 15)          # mandatory hazard axis -- BUG-003 lived at >=8
DIRECTIONS = ("sequential", "concurrent")

# CSR home of each selector. By NAME -- offsets churn every respin.
FIELD_OF = {
    "policy_mode":    ("PAGE_POLICY_CFG", "policy_mode"),
    "tr_init":        ("PAGE_TIMEOUT_CFG", "tr_init"),
    "page_policy_or": ("REFRESH_TUNING", "page_policy_or"),
    "order_mode":     ("SCHED_POLICY", "order_mode"),
    "prio_sub":       ("SCHED_POLICY", "prio_sub"),
    "row_sel":        ("SCHED_POLICY", "row_sel"),
    "col_sel":        ("SCHED_POLICY", "col_sel"),
    "access_pref":    ("SCHED_POLICY", "access_pref"),
    "qos_en":         ("SCHED_POLICY", "qos_en"),
    "age_thresh":     ("SCHED_POLICY", "age_thresh"),
    "ref_mode":       ("REF_CTRL", "mode"),
    "postpone_limit": ("REF_CTRL", "postpone_limit"),
    "pullin_limit":   ("REF_CTRL", "pullin_limit"),
    "wr_high_wm":     ("SCHED_WR_WM", "wr_high_wm"),
    "wr_batch_max":   ("SCHED_WR_WM", "wr_batch_max"),
}


def all_cells():
    """Every (vector index, gap, direction). Deterministic and ordered."""
    return [(i, g, d)
            for i in range(len(ca.covering_array()))
            for g in GAPS
            for d in DIRECTIONS]


def cells_for_level(level: str):
    """GATE and FUNC take a STRIDED subset, not a prefix.

    A prefix would run the first vectors at every gap and the last at none,
    which reads as coverage and is not: the array's later rows are the vertical
    growth, i.e. exactly the combinations the early rows could not reach.
    """
    cells = all_cells()
    if level == "full":
        return cells
    want = 2 if level == "gate" else 16
    stride = max(1, len(cells) // want)
    return cells[::stride][:want]


_LEVEL = {"GATE": "gate", "BASIC": "gate", "FUNC": "func", "MEDIUM": "func",
          "FULL": "full"}.get(
    (os.environ.get("REG_LEVEL") or os.environ.get("TEST_LEVEL")
     or "FUNC").upper(), "func")


# --------------------------------------------------------------------------
# The coverage NUMBER. No DUT, no simulation -- this is the claim TASK-015 asks
# to be able to make, and it is checked rather than asserted in prose.
# --------------------------------------------------------------------------
def test_pumice_config_sweep_coverage():
    """'N of 105 mode-selector pairs exercised at each of 4 gaps.'"""
    vectors = ca.covering_array()
    cov, tot = ca.pair_coverage(vectors)
    assert (cov, tot) == (105, 105), ca.uncovered_pairs(vectors)

    # and every pair is covered AT EACH GAP, which is the actual claim --
    # covering the pairs once overall would leave a gap-specific interaction
    # (exactly BUG-003's shape) unreached.
    cells = all_cells()
    for gap in GAPS:
        at_gap = [vectors[i] for (i, g, _) in cells if g == gap]
        c, t = ca.pair_coverage(at_gap)
        assert (c, t) == (105, 105), f"gap {gap}: only {c} of {t} pairs"

    print(f"\nTASK-015 layer 1: {len(vectors)} config vectors, "
          f"{cov} of {tot} mode-selector pairs at each of {len(GAPS)} gaps, "
          f"{len(cells)} cells at FULL")


def test_pumice_config_sweep_cells_are_stable():
    """A failing cell must be re-runnable by index tomorrow."""
    assert all_cells() == all_cells()
    assert cells_for_level("gate") == cells_for_level("gate")
    assert set(cells_for_level("gate")) <= set(cells_for_level("full"))
    assert len(cells_for_level("full")) == len(ca.covering_array()) * 4 * 2
