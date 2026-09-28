# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""Unit tests for the pairwise covering array (pumice TASK-015 layer 1).

Pure Python, no DUT. The array is the thing the whole layer-1 sweep rests on --
if it does not actually cover the pairs, the coverage NUMBER is a lie and the
sweep is just 384 arbitrary cells. So the properties are tested, including that
the coverage checker itself can fail.
"""
from __future__ import annotations

import importlib.util
import math
import sys
from pathlib import Path

import pytest

_TB = Path(__file__).resolve().parents[2] / "tbclasses"
_spec = importlib.util.spec_from_file_location(
    "pumice_config_array", _TB / "pumice_config_array.py")
ca = importlib.util.module_from_spec(_spec)
sys.modules["pumice_config_array"] = ca
_spec.loader.exec_module(ca)


def test_there_are_fifteen_selectors_and_105_pairs():
    """TASK-015 asks for the number 'N of 105'. If the selector set changes,
    that denominator changes and the task's own acceptance text goes stale."""
    assert len(ca.SELECTORS) == 15
    assert ca.PAIR_TOTAL == 105 == math.comb(15, 2)


def test_every_pair_is_fully_covered():
    cov, tot = ca.pair_coverage(ca.covering_array())
    assert (cov, tot) == (105, 105)
    assert ca.uncovered_pairs(ca.covering_array()) == {}


def test_the_array_is_deterministic():
    """A cell that failed yesterday must exist again today, or it is not a
    regression. No RNG anywhere in the construction."""
    assert ca.covering_array() == ca.covering_array()


def test_every_vector_is_complete_and_legal():
    for i, v in enumerate(ca.covering_array()):
        assert set(v) == set(ca.SELECTORS), f"vector {i} is missing selectors"
        for name, val in v.items():
            assert val in ca.SELECTORS[name], f"vector {i}: {name}={val} illegal"


def test_it_is_far_smaller_than_the_cross_product():
    n = len(ca.covering_array())
    product = math.prod(len(d) for d in ca.SELECTORS.values())
    assert n < 100, f"{n} vectors is not a covering array, it is a sweep"
    assert product > 10 ** 8            # the thing we are NOT running
    assert n < product / 10 ** 6


def test_the_array_is_at_least_the_theoretical_minimum():
    """Pairwise needs at least |largest domain| x |second largest|."""
    sizes = sorted((len(d) for d in ca.SELECTORS.values()), reverse=True)
    assert len(ca.covering_array()) >= sizes[0] * sizes[1]


def test_the_coverage_checker_can_fail():
    """Guard against a checker that returns 105 no matter what it is given."""
    truncated = ca.covering_array()[:5]
    cov, tot = ca.pair_coverage(truncated)
    assert tot == 105
    assert cov < 105, "a 5-vector array cannot cover 105 pairs"
    assert ca.uncovered_pairs(truncated), "uncovered_pairs found nothing in a stub"


def test_a_pair_counts_only_when_every_combination_appears():
    """'The two fields varied' is not coverage. Both must take every value
    against every value of the other."""
    partial = [{n: d[0] for n, d in ca.SELECTORS.items()},
               {n: d[-1] for n, d in ca.SELECTORS.items()}]
    cov, _ = ca.pair_coverage(partial)
    assert cov == 0, "two opposite corners should cover no pair fully"


def test_retired_paging_encodings_are_in_the_array():
    """Modes 4 and 5 are retired and must fall through to the build default.
    A sweep that drops them stops regressing the fallthrough."""
    vals = {v["policy_mode"] for v in ca.covering_array()}
    assert {4, 5} <= vals


def test_build_geometry_is_not_a_selector():
    """Changing these at runtime mis-describes the hardware rather than
    exploring a legal config -- pumice ISSUE-016 is what that costs."""
    for forbidden in ("gear_ratio", "rd_phase", "wr_phase", "memtype",
                      "policy_scope", "bl"):
        assert forbidden not in ca.SELECTORS


def test_address_map_fields_are_not_selectors():
    """Not because the DUT cannot take them -- because the sim ORACLE cannot.

    The top TB builds its golden AddressMapping once, assuming bank_lsb ==
    col_width. Sweeping bank_lsb makes the DUT and the model decode the same
    address to different DRAM cells; measured, the reads were right and the
    golden side read zero. A cell whose oracle is invalid is worse than an
    absent cell."""
    for forbidden in ("bank_lsb", "hash_en", "hash_seed"):
        assert forbidden not in ca.SELECTORS


def test_describe_reports_the_number_the_task_asks_for():
    text = ca.describe(ca.covering_array())
    assert "105 of 105" in text and "config vectors" in text


# --------------------------------------------------------------------------
# Layer 3: seeded random vectors
# --------------------------------------------------------------------------
def test_random_vectors_are_legal():
    for v in ca.random_vectors(200, seed=7):
        assert set(v) == set(ca.SELECTORS)
        for name, val in v.items():
            assert val in ca.SELECTORS[name]


def test_random_vectors_replay_from_the_seed():
    """A soak failure that cannot be reproduced is an anecdote."""
    assert ca.random_vectors(20, seed=1234) == ca.random_vectors(20, seed=1234)


def test_different_seeds_explore_different_vectors():
    a = ca.random_vectors(30, seed=1)
    b = ca.random_vectors(30, seed=2)
    assert a != b


def test_random_eventually_reaches_beyond_the_covering_array():
    """The point of layer 3: 3-way combinations pairwise cannot promise.

    Not an assertion about defects -- just that the random stream produces
    triples the 39-vector array does not contain, which is the only reason to
    run it at all."""
    array = {tuple(sorted(v.items())) for v in ca.covering_array()}
    rand = {tuple(sorted(v.items())) for v in ca.random_vectors(200, seed=99)}
    assert rand - array, "random soak produced nothing new over the array"


def test_vector_id_is_stable_and_complete():
    v = ca.random_vectors(1, seed=5)[0]
    vid = ca.vector_id(v)
    assert vid == ca.vector_id(v)
    for name in ca.SELECTORS:
        assert f"{name}=" in vid
