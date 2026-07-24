---
title: Signal contracts and K-maps
summary: Every important block gets a contracts workbook; maps are computed, never drawn.
---

# Signal contracts + K-maps (design practice)

For every substantial block (engines, schedulers, arbiters, controllers),
maintain a `*_signal_contracts.xlsx`: contract sheets per interface
(signal / width / dir / driver / legal behavior / invariant / bug history)
and Karnaugh maps for the key combinational decisions.

- Methodology (canonical): bin/SIGNAL_CONTRACTS_KMAPS.md.
- Maps are COMPUTED from a Python mirror of the verbatim RTL expression,
  file:line cited; a citation registry greps every quote on every run and
  fails on drift. The xlsx is a build artifact - never hand-edit.
- What to map: arbitration/grant terms, issue qualifications, credit and
  space accounting, cross-block drain/pop strobes, error latch/clear,
  FSM exit decisions ([[minimal-fsm]]) - and anything that ever had a
  known_issues entry.
- Why: mirroring the expressions IS a design review. The stream workbook's
  first pass surfaced six findings the test suite had not (a retractable
  arvalid, an unlatched AW address contract, a transient error gate...).
- Reference implementations: pumice + stream
  docs/gen_signal_contracts_kmaps.py. New blocks copy the pattern; the
  common machinery is being promoted to bin/ (TOOLING_TODO item 1).
