# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: stream_levels
# Purpose: one implementation of the gate/func/full test levels for this area
#
# Subsystem: fpga-systems/Genesys2/stream

"""The gate / func / full test levels, resolved once for the whole area.

Every test in this area must honour a level. Before this module they mostly
did not: of the thirteen sim tests, eleven read no level at all, and the one
that appeared to (`test_stream_mon_perf`) set TEST_LEVEL into the cocotb
environment where *nothing ever read it* -- a knob wired to nothing. Asking
that suite for its "minimum" therefore ran the maximum, which is how a
gate-level sweep came to spend over two hours in a single test.

The three levels
----------------
    gate    smoke. Must stay short enough to run on every change.
    func    the default regression depth.
    full    everything, including the slow corners. Nightly / pre-release.

Levels are ordered and cumulative: whatever runs at `gate` also runs at
`func`, and `func`'s work is a subset of `full`'s. Use `at_least()` to gate a
block and `scale()` to size one.

Resolution order
----------------
TEST_LEVEL wins, then REG_LEVEL (the older spelling, still used widely
elsewhere in the repo), then the default. Both spellings are accepted in any
case, so TEST_LEVEL=FULL and REG_LEVEL=full both work -- the repo is not
self-consistent about case, and a level that silently fails to apply is worse
than one that is strict.

An UNRECOGNISED level resolves to `gate`, never to `full`. That direction is
deliberate: a typo should under-run and be noticed, not quietly launch the
longest job in the suite. It warns so the typo is visible.
"""

from __future__ import annotations

import os
import warnings

GATE = 'gate'
FUNC = 'func'
FULL = 'full'

LEVELS = (GATE, FUNC, FULL)

#: Rank for ordering comparisons. Higher includes lower.
_RANK = {GATE: 0, FUNC: 1, FULL: 2}

#: Spellings seen in this repo and in CI invocations, mapped to the canonical
#: three. 'basic'/'medium' are the CLAUDE.md cocotb wording; 'smoke' and
#: 'nightly' show up in shell wrappers.
_ALIASES = {
    'basic': GATE,
    'smoke': GATE,
    'quick': GATE,
    'medium': FUNC,
    'regression': FUNC,
    'nightly': FULL,
    'all': FULL,
}

#: Default when neither variable is set. `gate` matches the area conftest's
#: existing `test_level` fixture, so adding this module does not silently
#: deepen any run that was already happening.
DEFAULT = GATE


def level(default: str = DEFAULT) -> str:
    """The level for this run, as one of LEVELS."""
    raw = os.environ.get('TEST_LEVEL') or os.environ.get('REG_LEVEL') or default
    value = str(raw).strip().lower()
    value = _ALIASES.get(value, value)
    if value not in _RANK:
        warnings.warn(
            f"Unrecognised test level {raw!r}; falling back to {GATE!r}. "
            f"Valid levels are {', '.join(LEVELS)} "
            f"(aliases: {', '.join(sorted(_ALIASES))}).",
            RuntimeWarning, stacklevel=2)
        return GATE
    return value


def at_least(minimum: str) -> bool:
    """True when the current level is `minimum` or deeper.

        if at_least(FUNC):
            await run_the_slower_phase()
    """
    if minimum not in _RANK:
        raise ValueError(f"unknown level {minimum!r}; expected one of {LEVELS}")
    return _RANK[level()] >= _RANK[minimum]


def scale(gate, func, full):
    """Pick the value for the current level.

        count = scale(8, 32, 128)

    Any type works -- counts, tuples of sizes, lists of test names.
    """
    return {GATE: gate, FUNC: func, FULL: full}[level()]


def describe() -> str:
    """One line naming the level and where it came from, for the test log.

    Worth logging: a run that silently picked the wrong level is otherwise
    indistinguishable from one that legitimately had little to do.
    """
    resolved = level()
    for var in ('TEST_LEVEL', 'REG_LEVEL'):
        raw = os.environ.get(var)
        if raw:
            via = f"{var}={raw}"
            if str(raw).strip().lower() != resolved:
                via += f" -> {resolved}"
            return f"test level {resolved} (from {via})"
    return f"test level {resolved} (default; neither TEST_LEVEL nor REG_LEVEL set)"


def env(extra: dict | None = None) -> dict:
    """TEST_LEVEL/REG_LEVEL to hand to `run(extra_env=...)`.

    Passes the RESOLVED level, not the raw string, so the cocotb half of a
    test cannot re-resolve an alias differently from the pytest half.
    """
    out = {'TEST_LEVEL': level(), 'REG_LEVEL': level().upper()}
    if extra:
        out.update(extra)
    return out
