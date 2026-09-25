# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# Module: bin/kmaps/minimize.py
# Purpose: Quine-McCluskey minimal-cover derivation (criterion 6)
"""Minimal sum-of-products derivation and SOP comparison.

Criterion 6 of the methodology: derive the minimal cover mechanically and DIFF
it against the RTL as written. Three outcomes, all informative -- identical
(the RTL is minimal and the map proves it), RTL-redundant (extra terms, say
why), RTL-differs (a bug, or an unstated invariant doing work).

Promoted from the stream generator by TOOLING-KMAP step 5; bodies unchanged,
private `_names` made public since they are now an API.
"""

def norm_sop(s):
    """Compare SOP strings without tripping over spacing or term order."""
    terms = [t.strip() for t in s.replace("||", "|").split("|")]
    norm = []
    for term in terms:
        lits = sorted(x.strip() for x in term.split("&"))
        norm.append(" & ".join(lits))
    return tuple(sorted(norm))

# ---------------------------------------------------------------------------
# Minimal-cover derivation (Quine-McCluskey).
#
# THIS is what makes a grid a K-map rather than a Gray-ordered truth table. The
# grid shows what the mirrored RTL computes; the minimal cover says what the
# decision MINIMALLY IS, and the difference between the two is the finding:
#
#   identical      -> the RTL is already minimal; the map proves it
#   RTL redundant  -> extra terms. Often deliberate (timing, readability) --
#                     the map makes you say which, instead of assuming.
#   RTL differs    -> a bug, or an unstated invariant doing work. This is the
#                     case that finds defects.
#
# n <= 6 by construction (the emitter caps varnames at 6), so exact QM is cheap.
#
# Don't-cares are FREE to join implicants -- which is exactly why marking
# unreachable cells X (instead of forcing them to 0/1) changes the ANSWER and
# not just the picture.
# ---------------------------------------------------------------------------
def qm_minimize(n, ones, dcs):
    """Exact-ish minimal sum-of-products. Returns a list of cubes; each cube is
    an n-tuple of 0 / 1 / None (None = variable eliminated from that term).
    """
    ones = set(ones)
    dcs = set(dcs)
    if not ones:
        return []                          # constant 0
    if len(ones | dcs) == (1 << n):
        return [tuple([None] * n)]         # constant 1

    def bits(m):
        return tuple((m >> (n - 1 - i)) & 1 for i in range(n))

    cubes = {(bits(m), frozenset([m])) for m in sorted(ones | dcs)}
    primes = set()
    while cubes:
        merged = set()
        used = set()
        cl = list(cubes)
        for i in range(len(cl)):
            for j in range(i + 1, len(cl)):
                a, am = cl[i]
                b, bm = cl[j]
                if any((a[k] is None) != (b[k] is None) for k in range(n)):
                    continue
                diff = [k for k in range(n) if a[k] != b[k]]
                if len(diff) == 1 and a[diff[0]] is not None:
                    nc = list(a)
                    nc[diff[0]] = None
                    merged.add((tuple(nc), am | bm))
                    used.add(i)
                    used.add(j)
        for i, c in enumerate(cl):
            if i not in used:
                primes.add(c)
        cubes = merged

    # cover the ONES only -- don't-cares helped form primes, they need no cover
    prime_list = [(c, m & ones) for c, m in primes if (m & ones)]
    chosen, remaining = [], set(ones)
    for one in sorted(ones):                      # essential primes first
        covering = [p for p in prime_list if one in p[1]]
        if len(covering) == 1 and covering[0] not in chosen:
            chosen.append(covering[0])
    for _, m in chosen:
        remaining -= m
    while remaining:                              # greedy on the remainder
        best = max(prime_list, key=lambda p: (len(p[1] & remaining),
                                              sum(1 for v in p[0] if v is None)))
        if not (best[1] & remaining):
            break
        if best not in chosen:
            chosen.append(best)
        remaining -= best[1]
    return [c for c, _ in chosen]


def cube_str(cube, varnames):
    parts = [(varnames[i] if v else f"!{varnames[i]}")
             for i, v in enumerate(cube) if v is not None]
    return " & ".join(parts) if parts else "1"


def sop_str(cubes, varnames):
    return "  |  ".join(cube_str(c, varnames) for c in cubes) if cubes else "0"
