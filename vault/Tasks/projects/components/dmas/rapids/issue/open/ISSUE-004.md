# ISSUE-004: one board config reports zero ingress starvation where every other reports ~200

**Status:** open 2026-09-27. Split out of ISSUE-001 when that closed; needs board time.

`ch8_b4_bpoff_seed0xA5A5A5A5` reports `sin starv=0, util=1.000` while all 19
other configs in the same sweep report ~197-205. It reproduces EXACTLY across
two independent sweeps (deterministic, not jitter) and sits at position #7 of
20 (not first-arm-after-reset). The sink re-arm quirk documented in
`run_characterization.py` was the obvious suspect and the ordering does not
support it.

Since ISSUE-001's fix the ingress window closes on its own beat target, so the
~200-cycle tail is gone from every row; whether this config's zero was a
different mechanism (window never opening, meter cleared late, a re-arm race)
has to be re-measured on the board with the new harness before it is chased.
Do not paper over it: if it still reads differently from its neighbours after
the re-measurement, capture the meter CSRs and the observer counters for that
row and compare beat by beat.
