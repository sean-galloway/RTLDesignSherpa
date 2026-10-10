# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""Pairwise covering array over pumice's runtime mode selectors (TASK-015 layer 1).

BUG-003 was a two-way interaction: `policy_mode=3` crossed with `rd_gap>=8`.
Single-field coverage reported it GREEN, because `policy_mode` had been
exercised at three distinct values -- just never against that gap. The full
cross product of the selectors below is ~5.9e8 vectors, which is why nobody ran
it and why "have we tried the combinations?" had no answer.

A pairwise covering array answers it. Every 2-way combination of selector values
appears in at least one vector, in `max(domain) * next(domain)`-ish rows rather
than the product -- order 40 vectors here, not 590 million. Crossed with the
mandatory hazard axes (gap, direction) that is a few hundred cells: a nightly
run, not a gate.

    from tbclasses.pumice_config_array import (
        SELECTORS, covering_array, pair_coverage, PAIR_TOTAL)

    vectors = covering_array()              # deterministic, no seed needed
    covered, total = pair_coverage(vectors) # (105, 105)

WHAT PAIRWISE DOES NOT BUY, stated because a coverage number invites over-reading:
it finds interactions between TWO selectors. BUG-003 was one. A defect needing
three specific settings at once is NOT guaranteed to appear, and that gap is
exactly what layer 3's seeded random soak exists to chip at. "105 of 105 pairs"
means every pair was tried, not that the design is correct.
"""
from __future__ import annotations

import random
from itertools import combinations
from typing import Dict, Iterator, List, Sequence, Tuple

# ---------------------------------------------------------------------------
# The selectors. RUNTIME policy fields only -- things a host can legally change
# between runs on one bitstream, which is what makes a sweep meaningful.
#
# TASK-015 listed 15 selectors including `policy_scope`, `gear_ratio`,
# `rd_phase`, `wr_phase` and `memtype`. Those are NOT here, deliberately:
#   * policy_scope was made reserved when the adaptive modes were retired
#     (2026-09-27) -- it is no longer a software-writable field at all.
#   * gear_ratio / rd_phase / wr_phase / memtype are BUILD geometry. The
#     bitstream is elaborated for one of them; changing them at runtime does
#     not explore a legal configuration, it mis-describes the hardware, and
#     pumice ISSUE-016 is what that costs when it happens by accident.
# The ADDRESS-MAP fields (bank_lsb, hash_en) are not here either, and the reason
# is the ORACLE rather than the DUT. The top TB builds its golden AddressMapping
# once at construction from row_width/col_width and assumes bank_lsb == col_width
# (pumice_top_csr_tb.py:142, and the comment at :383 says so). Sweeping bank_lsb
# therefore makes the DUT decode an address to a different DRAM cell than the
# model does, and every host-side comparison goes wrong -- measured: the reads
# came back correct and the GOLDEN side read zero. A sweep whose oracle is
# invalid for some of its cells is worse than one that leaves those cells out.
# They are covered where the oracle does follow them: test_addr_mapper at fub
# level, and on the board, where write and read share whatever map is programmed.
#
# Replaced with runtime fields that genuinely vary and that the oracle can
# follow: tr_init, age_thresh, postpone_limit, pullin_limit, wr_high_wm and
# wr_batch_max. Still 15 selectors, so still 105 pairs -- the number the task
# asks to report is unchanged.
# ---------------------------------------------------------------------------
SELECTORS: Dict[str, Tuple] = {
    # paging
    "policy_mode":     (0, 1, 2, 3, 4, 5),   # 4,5 retired -> must fall through
    "tr_init":         (0, 1, 2, 4, 8),      # background-close timeout
    "page_policy_or":  (0, 1, 2, 3),         # refresh's page-policy override
    # scheduling
    "order_mode":      (0, 1, 2, 3),         # FR-FCFS / in_order / age
    "prio_sub":        (0, 1, 2, 3),
    "row_sel":         (0, 1, 2, 3),
    "col_sel":         (0, 1, 2, 3),
    "access_pref":     (0, 1, 2, 3),
    "qos_en":          (0, 1),
    "age_thresh":      (0, 8, 64),           # only meaningful at order_mode=3
    # refresh
    "ref_mode":        (0, 1, 2, 3),
    "postpone_limit":  (0, 2, 8),
    "pullin_limit":    (0, 2, 8),
    # write path
    "wr_high_wm":      (0, 2, 4),
    "wr_batch_max":    (1, 4, 16),
}

PAIR_TOTAL = len(list(combinations(SELECTORS, 2)))     # 105


def _all_pairs() -> List[Tuple[str, str]]:
    return list(combinations(SELECTORS, 2))


def _pair_values(a: str, b: str) -> List[Tuple]:
    return [(x, y) for x in SELECTORS[a] for y in SELECTORS[b]]


def covering_array(order: Sequence[str] | None = None) -> List[Dict]:
    """Deterministic pairwise (2-way) covering array over SELECTORS.

    IPOG: seed with the full cross product of the two largest domains, then for
    each remaining parameter extend horizontally (choose the value covering the
    most still-uncovered pairs) and vertically (add rows for whatever is left).

    Deterministic by construction -- no RNG, no seed, ties broken by value
    order. An array that changed run to run could not be a regression: a cell
    that failed yesterday has to exist again today.
    """
    names = list(order) if order else sorted(
        SELECTORS, key=lambda n: (-len(SELECTORS[n]), n))

    need = {p: set(_pair_values(*p)) for p in _all_pairs()}

    def mark(row: Dict) -> None:
        for a, b in _all_pairs():
            if a in row and b in row:
                need[(a, b)].discard((row[a], row[b]))

    first, second = names[0], names[1]
    rows: List[Dict] = [{first: x, second: y}
                        for x in SELECTORS[first] for y in SELECTORS[second]]
    for r in rows:
        mark(r)

    for name in names[2:]:
        # horizontal growth
        for row in rows:
            best, best_gain = None, -1
            for v in SELECTORS[name]:
                gain = 0
                for other, oval in row.items():
                    key = (name, other) if (name, other) in need else (other, name)
                    want = (v, oval) if key == (name, other) else (oval, v)
                    if want in need[key]:
                        gain += 1
                if gain > best_gain:
                    best, best_gain = v, gain
            row[name] = best
            mark(row)
        # vertical growth: one new row per still-uncovered pair involving `name`
        placed = [n for n in names[:names.index(name) + 1]]
        for other in placed:
            if other == name:
                continue
            key = (name, other) if (name, other) in need else (other, name)
            while need[key]:
                combo = sorted(need[key])[0]
                nv, ov = (combo if key == (name, other) else (combo[1], combo[0]))
                row = {name: nv, other: ov}
                # fill the rest greedily
                for fill in placed:
                    if fill in row:
                        continue
                    bv, bg = None, -1
                    for v in SELECTORS[fill]:
                        g = 0
                        for o2, o2v in row.items():
                            k2 = (fill, o2) if (fill, o2) in need else (o2, fill)
                            w2 = (v, o2v) if k2 == (fill, o2) else (o2v, v)
                            if w2 in need[k2]:
                                g += 1
                        if g > bg:
                            bv, bg = v, g
                    row[fill] = bv
                rows.append(row)
                mark(row)

    # every row must be complete
    for r in rows:
        for n in names:
            if n not in r:
                r[n] = SELECTORS[n][0]
    return rows


def pair_coverage(vectors: Sequence[Dict]) -> Tuple[int, int]:
    """(pairs fully covered, PAIR_TOTAL). A pair counts only when EVERY one of
    its value combinations appears -- not merely 'the two fields varied'."""
    full = 0
    for a, b in _all_pairs():
        want = set(_pair_values(a, b))
        seen = {(v[a], v[b]) for v in vectors if a in v and b in v}
        if want <= seen:
            full += 1
    return full, PAIR_TOTAL


def uncovered_pairs(vectors: Sequence[Dict]) -> Dict[Tuple[str, str], set]:
    out = {}
    for a, b in _all_pairs():
        miss = set(_pair_values(a, b)) - {(v[a], v[b]) for v in vectors
                                          if a in v and b in v}
        if miss:
            out[(a, b)] = miss
    return out


def describe(vectors: Sequence[Dict]) -> str:
    cov, tot = pair_coverage(vectors)
    return (f"{len(vectors)} config vectors, {cov} of {tot} mode-selector pairs "
            f"fully covered")


# ---------------------------------------------------------------------------
# Layer 3: seeded random config vectors.
#
# Pairwise (layer 1) covers every 2-way interaction BY CONSTRUCTION and covers
# nothing deeper by construction either. A defect needing three specific
# settings at once is invisible to it. Random vectors reach those eventually and
# prove nothing in particular -- which is the trade, and why this runs nightly
# rather than in a gate.
#
# Seeded from the suite's SEED/RDS_SEED_BASE plumbing so a failure REPLAYS. A
# soak whose failing case cannot be reproduced is an anecdote
# (project_seed_rerun_masks_failures).
# ---------------------------------------------------------------------------
def random_vector(rng: random.Random) -> Dict:
    """One uniformly random LEGAL vector -- every value comes from SELECTORS,
    so a soak can never program a field out of range and blame the DUT."""
    return {name: rng.choice(domain) for name, domain in SELECTORS.items()}


def random_vectors(n: int, seed: int) -> List[Dict]:
    rng = random.Random(seed ^ 0xC0FFEE)
    return [random_vector(rng) for _ in range(n)]


def vector_id(vec: Dict) -> str:
    """Compact, stable rendering of a vector -- goes in the failure message so
    a soak failure can be turned into a pinned regression cell by hand."""
    return ",".join(f"{k}={vec[k]}" for k in sorted(vec))
