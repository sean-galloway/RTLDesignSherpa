# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""Telemetry invariants over pumice's exported counters (TASK-015 layer 2b).

An oracle that needs no performance model. Every relation here is pure
arithmetic on counters the design already exports, holds for EVERY legal
configuration, and is checkable in sim AND on the board from the same code --
which is the point: a config sweep that only proves "it ran" cannot fail, and
with layer 2a dropped (Sean, 2026-09-27: no assertions in RTL) this is the only
oracle the sweep gets.

    counters = {"PAGE_STATS_HIT": ..., "SCHED_STATS_ACT": ..., ...}
    violations = check_invariants(counters)      # [] when clean
    armed = [n for n, a in arming(counters).items() if a]

READ THE REGISTER NAMES BEFORE TRUSTING THEM. `PAGE_STATS_HIT` does NOT count
hits -- the RTL increments it on EVERY column command, read or write, with or
without auto-precharge, and the RDL says so at the field. Row hits are DERIVED,
`hits = PAGE_STATS_HIT - SCHED_STATS_ACT`. TASK-015 drafted the invariant as
`hit + miss + empty == ACT`, which against the real semantics is false on
correct hardware; the relation that actually holds is `miss + empty == ACT`,
because MISS and EMPTY are the two CAUSES of an activation. Writing the drafted
form would have produced a checker that fails a working design -- the same shape
as enforcing tRAS on the auto-precharge path, where the checker was wrong and
the RTL was right.

WHY ACT CAN EXCEED COL_OPS (measured, 2026-09-27). This module first shipped
with `ACT <= col_ops` and `col_ops - ACT >= 0` as invariants, on the reasoning
that a row is only opened in order to be accessed. Correct hardware violates
both: under a background-close mode (`policy_mode=3`, `tr_init=2` -- the SHIPPING
default) a row can be opened, hit by the timeout precharge BEFORE its column
command issues, and then reopened. Two activations, one column op. Measured at
proven quiescence with golden data: a bank-spreading pattern produced 49 ACTs
for 48 column ops while two other patterns produced exactly 48/48 and 64/64, so
the excess is real, legal, and attributable to the re-activation race rather
than to a window edge.

That has a consequence beyond this file: the derivation the RDL documents at
PAGE_STATS_HIT, `hits = PAGE_STATS_HIT - SCHED_STATS_ACT`, is UNSOUND for modes
2 and 3 -- it goes negative. The board host clamps it at zero
(`test_hit_rate_never_goes_negative`) and attributes the negative case to "a
window boundary (an ACT counted whose column op landed outside)". The clamp is
right; that reason is not, and it reproduces inside a single quiescent window.
Hits should be read from the eight per-bank counters, which count hits directly.
Filed as pumice ISSUE-014.

`SCHED_STATS_PRE` is PRE **+ PREA** commands, not PRE alone.
`REF_STATS_REF` is FREE-RUNNING (refresh is autonomous), so it is excluded from
every window-relative relation here -- a host-bracketed delta on the board
counts the UART round trips too, once measured as 2584x the window.
"""
from __future__ import annotations

from typing import Callable, Dict, List, NamedTuple, Optional


class Violation(NamedTuple):
    rule: str
    detail: str

    def __str__(self) -> str:                      # pragma: no cover - display
        return f"{self.rule}: {self.detail}"


class _Rule(NamedTuple):
    name: str
    needs: tuple           # counters that must be present for the rule to apply
    holds: Callable        # (c) -> bool
    explain: Callable      # (c) -> str, showing the arithmetic
    why: str


def derived_hits_unsound(c: Dict[str, int]) -> int:
    """The derivation the RDL documents, `col_ops - ACT`. NOT used as an
    invariant: it goes negative on correct hardware under a background-close
    mode. Kept, named for what it is, so a future reader reaches for the
    per-bank counters instead of re-deriving this and re-learning it the hard
    way (pumice ISSUE-014)."""
    return c["PAGE_STATS_HIT"] - c["SCHED_STATS_ACT"]


RULES: tuple = (
    _Rule(
        "activation_causes_account",
        ("PAGE_STATS_MISS", "PAGE_STATS_EMPTY", "SCHED_STATS_ACT"),
        lambda c: c["PAGE_STATS_MISS"] + c["PAGE_STATS_EMPTY"] == c["SCHED_STATS_ACT"],
        lambda c: (f"miss={c['PAGE_STATS_MISS']} + empty={c['PAGE_STATS_EMPTY']} "
                   f"= {c['PAGE_STATS_MISS'] + c['PAGE_STATS_EMPTY']} != ACT={c['SCHED_STATS_ACT']}"),
        "every activation has exactly one cause: the bank held a different row "
        "(miss) or no row (empty). A mismatch means an activation was issued for "
        "neither reason, or a cause was counted without an activation. This is an "
        "EQUALITY and it held exactly in every measured window (48=1+47, 64=0+64, "
        "49=1+48), including the one where ACT exceeded col_ops -- which is what "
        "localised that excess to re-activation rather than to miscounting.",
    ),
    _Rule(
        "hits_within_col_ops",
        tuple(f"OBS_ROW_HIT{b}_ROW_HIT" for b in range(8)) + ("PAGE_STATS_HIT",),
        lambda c: 0 <= sum(c[f"OBS_ROW_HIT{b}_ROW_HIT"] for b in range(8)) <= c["PAGE_STATS_HIT"],
        lambda c: (f"sum(per-bank hits)={sum(c[f'OBS_ROW_HIT{b}_ROW_HIT'] for b in range(8))} "
                   f"outside [0, col_ops={c['PAGE_STATS_HIT']}]"),
        "a row hit IS a column op, so the per-bank hit counters can never total "
        "more than the column ops issued.",
    ),
    _Rule(
        "hits_at_least_col_ops_minus_act",
        tuple(f"OBS_ROW_HIT{b}_ROW_HIT" for b in range(8)) + ("PAGE_STATS_HIT", "SCHED_STATS_ACT"),
        lambda c: (sum(c[f"OBS_ROW_HIT{b}_ROW_HIT"] for b in range(8))
                   >= c["PAGE_STATS_HIT"] - c["SCHED_STATS_ACT"]),
        lambda c: (f"sum(per-bank hits)={sum(c[f'OBS_ROW_HIT{b}_ROW_HIT'] for b in range(8))} "
                   f"< col_ops({c['PAGE_STATS_HIT']}) - ACT({c['SCHED_STATS_ACT']}) "
                   f"= {c['PAGE_STATS_HIT'] - c['SCHED_STATS_ACT']}"),
        "every column op either hit an open row or was preceded by an activation, "
        "so hits >= col_ops - ACT. This is a BOUND and not an equality on "
        "purpose: see WHY ACT CAN EXCEED COL_OPS in the module docstring.",
    ),
    _Rule(
        "pre_le_act",
        ("SCHED_STATS_PRE", "SCHED_STATS_ACT"),
        lambda c: c["SCHED_STATS_PRE"] <= c["SCHED_STATS_ACT"],
        lambda c: f"PRE+PREA={c['SCHED_STATS_PRE']} > ACT={c['SCHED_STATS_ACT']}",
        "a bank cannot be closed more times than it was opened. One PREA closes "
        "up to eight banks with a single command, so the command count stays at "
        "or below ACT even under all-bank precharge.",
    ),
    _Rule(
        "refresh_busy_le_refresh",
        ("REF_STATS_REF_BUSY", "REF_STATS_REF"),
        lambda c: c["REF_STATS_REF_BUSY"] <= c["REF_STATS_REF"],
        lambda c: f"REF_BUSY={c['REF_STATS_REF_BUSY']} > REF={c['REF_STATS_REF']}",
        "refreshes that fired with work pending are a subset of refreshes that "
        "fired. Both are free-running, so this is the one relation between them "
        "that survives a host-bracketed window.",
    ),
)

# Relations that need a signal the CSR surface does not carry. Kept here so the
# list of what layer 2b does NOT cover is written down rather than implied.
SIM_ONLY_INVARIANTS = {
    "ring_occupancy_le_depth":
        "read-return ring occupancy <= RD_RET_DEPTH at all times. Not a counter: "
        "it is an instantaneous level, so it needs the RTL signal. This is the "
        "BUG-003 invariant, and the RTL check that caught BUG-003 is exactly the "
        "kind the no-assertions ruling forbids -- so it is covered by the "
        "scheduler matrix's command-stream replay instead, not by a counter.",
    "returned_beats_eq_issued_beats":
        "returned read beats == issued read beats. Checkable at the host, which "
        "knows what it asked for; the controller exports no issued-beat counter.",
}


def applicable(counters: Dict[str, int]) -> List[_Rule]:
    return [r for r in RULES if all(n in counters for n in r.needs)]


def arming(counters: Dict[str, int]) -> Dict[str, bool]:
    """Which rules had the counters they need. A rule that never armed proved
    nothing, and reporting "0 violations" without this is the blind-checker
    failure (handbook: checker-verdict-needs-a-count)."""
    return {r.name: all(n in counters for n in r.needs) for r in RULES}


def check_invariants(counters: Dict[str, int],
                     skip: tuple = ()) -> List[Violation]:
    out: List[Violation] = []
    for rule in applicable(counters):
        if rule.name in skip:
            continue
        try:
            ok = rule.holds(counters)
        except (KeyError, TypeError) as exc:       # pragma: no cover - defensive
            out.append(Violation(rule.name, f"could not evaluate: {exc!r}"))
            continue
        if not ok:
            out.append(Violation(rule.name, f"{rule.explain(counters)}  --  {rule.why}"))
    return out


def assert_clean(counters: Dict[str, int], *, require: tuple = (),
                 skip: tuple = (), context: str = "") -> int:
    """Raise on any violation, and REFUSE a vacuous pass: every rule named in
    `require` must have had its counters present."""
    armed = arming(counters)
    missing = [n for n in require if not armed.get(n)]
    if missing:
        raise AssertionError(
            f"{context}: telemetry invariants could not be checked -- required "
            f"rule(s) never armed: {missing}. Counters present: "
            f"{sorted(counters)}. A pass here would be vacuous."
        )
    bad = check_invariants(counters, skip=skip)
    if bad:
        raise AssertionError(
            f"{context}: {len(bad)} telemetry invariant violation(s):\n" +
            "\n".join(f"  - {v}" for v in bad)
        )
    return sum(1 for v in armed.values() if v)
