# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway
#
# Module: divergence
# Purpose: Post-sim tracker divergence checker for the ddr2-lpddr2 FUBs.
#
# Independent of the scoreboard: catches per-slot event-count parity
# violations by parsing the `.out` files each tracker dumps at end of
# sim and applying the contracts declared in `divergence_specs.py`.
#
# Motivating example: #31 (rd_cl_aligner). The scoreboard saw a
# TypeError three call frames downstream; the tracker's per-slot
# BEAT_WE-vs-OP_ACCEPT count divergence made the actual failure
# ("slot 6 got 0 BEAT_WE, expected 4") mechanical to state.
#
# Two entry points:
#   parse_tracker_file(path)     — raw event list (dict rows).
#   assert_no_divergence(...)    — applies specs, raises AssertionError
#                                  with a formatted message on violation.

from __future__ import annotations

from collections import defaultdict
from dataclasses import dataclass
from typing import Callable, List, Optional, Sequence, Union

# Re-exported from divergence_specs so callers can `from ...divergence import DIVERGENCE_SPECS`.
from .divergence_specs import DIVERGENCE_SPECS, ParityContract  # noqa: F401


# ---------------------------------------------------------------------------
# Parser
# ---------------------------------------------------------------------------


def _parse_data_field(s: str) -> dict:
    """Trackers emit `data` as space-separated `key=value` pairs
    (e.g. `id=0 len=4 col=0x2c`). Return a dict with ints where the
    value parses cleanly."""
    d = {}
    if not s:
        return d
    for tok in s.strip().split():
        if "=" not in tok:
            continue
        k, v = tok.split("=", 1)
        try:
            d[k] = int(v, 0)  # handles 0x… and plain ints
        except ValueError:
            d[k] = v
    return d


def parse_tracker_file(path: str) -> List[dict]:
    """Parse a tracker `.out` file into a list of event dicts.

    Format (from each tracker's TBBase.dump()):
      | time(ns) | cycle | tracker | event | rank | bank | slot | data |

    Header rows (starting with `| ---` or `| time`) are skipped.
    """
    events: List[dict] = []
    with open(path) as f:
        for raw in f:
            line = raw.rstrip("\n")
            if not line.startswith("|"):
                continue
            parts = [p.strip() for p in line.strip("|").split("|")]
            if len(parts) < 8:
                continue
            time_s, cycle_s, tracker, event, rank, bank, slot, data = parts[:8]
            # Skip header rows.
            if time_s.startswith("time") or time_s.startswith("---"):
                continue
            try:
                cycle = int(cycle_s)
            except ValueError:
                continue
            events.append({
                "time_ns": float(time_s) if time_s not in ("-", "") else 0.0,
                "cycle": cycle,
                "tracker": tracker,
                "event": event,
                "rank": rank,
                "bank": bank,
                "slot": slot,
                "data": data,
                "data_dict": _parse_data_field(data),
            })
    return events


# ---------------------------------------------------------------------------
# Contract application
# ---------------------------------------------------------------------------


@dataclass
class Violation:
    contract_name: str
    slot: str
    accept_event: str
    match_event: str
    expected: int
    actual: int

    def message(self) -> str:
        return (
            f"[{self.contract_name}] slot {self.slot}: expected "
            f"{self.expected} {self.match_event} per {self.accept_event}, "
            f"got {self.actual}"
        )


def _expected_matches_for_accept(contract: ParityContract, accept_ev: dict) -> int:
    if callable(contract.expected_per_accept):
        return int(contract.expected_per_accept(accept_ev["data_dict"]))
    if isinstance(contract.expected_per_accept, str):
        # String key into accept event's data_dict.
        return int(accept_ev["data_dict"].get(contract.expected_per_accept, 0))
    return int(contract.expected_per_accept)


def check_contract(events: Sequence[dict],
                   contract: ParityContract) -> List[Violation]:
    """Apply one contract to an event list. Returns a list of
    violations (empty means clean)."""
    accepts_by_slot: dict = defaultdict(list)
    match_counts_by_slot: dict = defaultdict(int)
    for ev in events:
        if ev["event"] == contract.accept_event:
            accepts_by_slot[ev["slot"]].append(ev)
        elif ev["event"] == contract.match_event:
            match_counts_by_slot[ev["slot"]] += 1

    violations: List[Violation] = []
    seen_slots = set(accepts_by_slot.keys()) | set(match_counts_by_slot.keys())
    for slot in sorted(seen_slots):
        expected = sum(
            _expected_matches_for_accept(contract, a)
            for a in accepts_by_slot.get(slot, [])
        )
        actual = match_counts_by_slot.get(slot, 0)
        if expected != actual:
            violations.append(Violation(
                contract_name=contract.name,
                slot=slot,
                accept_event=contract.accept_event,
                match_event=contract.match_event,
                expected=expected,
                actual=actual,
            ))
    return violations


# ---------------------------------------------------------------------------
# Assertion entry point
# ---------------------------------------------------------------------------


# ---------------------------------------------------------------------------
# Event-source adapters
# ---------------------------------------------------------------------------


def _fmt_idx(v, prefix: str) -> str:
    """Match the file-format's rendering: -1 → '-', N → '{prefix}N'."""
    try:
        n = int(v)
    except (TypeError, ValueError):
        return "-"
    return f"{prefix}{n}" if n >= 0 else "-"


def _events_from_tracker(tracker) -> List[dict]:
    """Convert a live tracker's in-memory events (list of TrackerEvent)
    to the dict shape this module works with. Used so the checker can
    run during the cocotb test — before the atexit dump — instead of
    parsing a file that only exists after the sim exits.

    TrackerEvent fields: sim_time_ns, cycle, tracker, event, rank,
    bank, slot, data. rank/bank/slot are ints (-1 = N/A). We format
    them to the same "s3"/"b0"/"r0" strings the file uses so the
    contract checker sees identical slot labels regardless of source.
    """
    out: List[dict] = []
    for ev in getattr(tracker, "events", []) or []:
        data_str = getattr(ev, "data", "") or ""
        out.append({
            "time_ns": float(getattr(ev, "sim_time_ns", 0.0) or 0.0),
            "cycle":   int(getattr(ev, "cycle", 0) or 0),
            "tracker": str(getattr(ev, "tracker", "")),
            "event":   str(getattr(ev, "event", "")),
            "rank":    _fmt_idx(getattr(ev, "rank", -1), "r"),
            "bank":    _fmt_idx(getattr(ev, "bank", -1), "b"),
            "slot":    _fmt_idx(getattr(ev, "slot", -1), "s"),
            "data":    data_str,
            "data_dict": _parse_data_field(data_str),
        })
    return out


def _resolve_events(source) -> List[dict]:
    """Accept either a filesystem path (str/pathlib.Path), a live
    tracker object with `.events`, or a pre-parsed event list."""
    if isinstance(source, (list, tuple)):
        return list(source)
    if hasattr(source, "events"):
        return _events_from_tracker(source)
    # Treat as a path.
    return parse_tracker_file(str(source))


# ---------------------------------------------------------------------------
# Assertion entry point
# ---------------------------------------------------------------------------


def check_no_divergence(
    fub_key: str,
    source,
    *,
    extra_contracts: Optional[Sequence[ParityContract]] = None,
    contract_names_skip: Sequence[str] = (),
) -> List[Violation]:
    """Non-raising variant — returns the violation list. Empty list = clean.

    `source` may be a path to a tracker .out file, a live tracker
    object (with `.events`), or a pre-parsed event list.
    """
    contracts = list(DIVERGENCE_SPECS.get(fub_key, []))
    if extra_contracts:
        contracts.extend(extra_contracts)
    contracts = [c for c in contracts if c.name not in contract_names_skip]

    events = _resolve_events(source)
    violations: List[Violation] = []
    for c in contracts:
        violations.extend(check_contract(events, c))
    return violations


def assert_no_divergence(
    fub_key: str,
    source,
    *,
    extra_contracts: Optional[Sequence[ParityContract]] = None,
    contract_names_skip: Sequence[str] = (),
) -> None:
    """Raises AssertionError with a formatted per-slot diff if any
    contract for `fub_key` is violated. Callers pass
    `contract_names_skip` to opt out of individual contracts when a
    scenario is intentionally wedged (e.g. rrdy_starvation_wedge).

    See check_no_divergence for `source` semantics (path / tracker /
    event list)."""
    violations = check_no_divergence(
        fub_key, source,
        extra_contracts=extra_contracts,
        contract_names_skip=contract_names_skip,
    )
    if violations:
        msg = "\n  ".join(v.message() for v in violations)
        raise AssertionError(
            f"Divergence in {fub_key} tracker:\n"
            f"  {msg}"
        )
