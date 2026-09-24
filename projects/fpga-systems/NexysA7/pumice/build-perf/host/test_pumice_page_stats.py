#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""Board-less proof of the PageStats derivation (TASK-002 telemetry).

The arithmetic here is the whole characterization campaign's explanation
layer, and every one of these cases is a way to get a plausible-looking wrong
number out of the same registers:

  - PAGE_STATS_HIT is NOT hits. The RTL bumps it on `w_is_col` -- every column
    op (pumice_page_policy.sv:348) -- while its RDL description says "Column
    ops issued to an already-open row". Reading it the obvious way,
    hit/(hit+miss+empty), mixes one per-ACCESS count with two per-ACT counts
    and yields a number that is not a rate of anything.
  - The counters free-run and clear only on aresetn, so an absolute read
    accumulates over a whole session and every later scenario looks worse.

    source env_python && pytest test_pumice_page_stats.py -q
"""

import os
import sys

import pytest

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from pumice_char import PageStats


def mk(col_ops=0, miss=0, empty=0, acts=None, pres=0, refs=0):
    """acts defaults to miss+empty, which is the RTL's own invariant: every ACT
    is classified as exactly one of the two."""
    return PageStats(col_ops=col_ops, miss=miss, empty=empty,
                     acts=(miss + empty) if acts is None else acts,
                     pres=pres, refs=refs)


# --------------------------------------------------------------------------
# The headline derivation
# --------------------------------------------------------------------------
def test_row_hit_rate_is_accesses_that_needed_no_activate():
    # 100 accesses, 10 of which had to open a row -> 90% hit.
    s = mk(col_ops=100, miss=4, empty=6)
    assert s.acts == 10
    assert s.row_hit_rate == pytest.approx(0.90)
    # And NOT the naive reading, which would be 100/(100+4+6) = 0.909...
    naive = s.col_ops / (s.col_ops + s.miss + s.empty)
    assert s.row_hit_rate != pytest.approx(naive)


def test_every_access_opens_a_row_is_zero_hit_rate():
    """col_major: every burst walks to a new row in the same bank."""
    assert mk(col_ops=64, miss=64, empty=0).row_hit_rate == pytest.approx(0.0)


def test_never_activating_is_a_perfect_hit_rate():
    """row_major wrapped inside one page: the row is opened before the window
    and every access lands on it."""
    assert mk(col_ops=64, miss=0, empty=0).row_hit_rate == pytest.approx(1.0)


def test_hit_rate_never_goes_negative():
    """More ACTs than column ops is physically odd but arithmetically reachable
    across a window boundary (an ACT counted whose column op landed outside).
    Clamp, because a negative 'rate' propagates as a plausible small number."""
    assert mk(col_ops=4, miss=6, empty=0).row_hit_rate == pytest.approx(0.0)


# --------------------------------------------------------------------------
# Vacuity: nothing measured must NOT look like a measured zero
# --------------------------------------------------------------------------
def test_no_accesses_reports_none_not_zero():
    s = mk()
    assert s.row_hit_rate is None
    assert s.acts_per_access is None
    assert not s.counted


def test_no_activates_reports_none_thrash_not_zero():
    """0% thrash and 'we never activated, so the question does not arise' are
    different facts; only one of them is evidence about the mapping."""
    assert mk(col_ops=64).miss_frac is None
    assert mk(col_ops=64, miss=0, empty=8).miss_frac == pytest.approx(0.0)


def test_counted_is_true_when_anything_moved():
    assert mk(col_ops=1).counted
    assert mk(miss=1, empty=0).counted
    assert mk(refs=1).counted


# --------------------------------------------------------------------------
# Thrash vs cold-open split
# --------------------------------------------------------------------------
def test_miss_frac_separates_conflict_from_cold_open():
    # 8 ACTs, 6 of them after a conflict PRE -> mostly row thrash.
    assert mk(col_ops=64, miss=6, empty=2).miss_frac == pytest.approx(0.75)
    # All cold opens (close-page steady state): no thrash at all.
    assert mk(col_ops=64, miss=0, empty=8).miss_frac == pytest.approx(0.0)


# --------------------------------------------------------------------------
# Delta semantics
# --------------------------------------------------------------------------
def test_delta_subtracts_free_running_counters():
    before = mk(col_ops=1000, miss=10, empty=20, pres=30, refs=40)
    after = mk(col_ops=1064, miss=14, empty=26, pres=44, refs=41)
    d = after - before
    assert (d.col_ops, d.miss, d.empty) == (64, 4, 6)
    assert (d.acts, d.pres, d.refs) == (10, 14, 1)
    # 64 accesses in the window, 10 of which paid an ACT -> 54/64.
    assert d.row_hit_rate == pytest.approx(54 / 64)


def test_delta_masks_32bit_wrap_instead_of_going_negative():
    before = mk(col_ops=0xFFFF_FFF0)
    after = mk(col_ops=0x0000_000F)       # wrapped
    assert (after - before).col_ops == 31


def test_absolute_read_would_understate_a_later_scenario():
    """Why the delta exists. Two identical 64-access scenarios back to back:
    read absolutely, the second reports a 95% hit rate it did not earn."""
    s1 = mk(col_ops=64, miss=0, empty=64)          # first: every access opens
    s2_abs = mk(col_ops=128, miss=0, empty=70)     # cumulative after the second
    assert s1.row_hit_rate == pytest.approx(0.0)
    assert s2_abs.row_hit_rate == pytest.approx(0.453, abs=1e-3)  # fiction
    assert (s2_abs - s1).row_hit_rate == pytest.approx(0.906, abs=1e-3)  # truth
