# TASK-015: Evaluate matrix arbiters vs round-robin for small port counts

**Priority:** P3
**Status:** OPEN
**Owner:** bridge
**Filed:** 2026-10-11 from the interconnect-literature deep review (bridge citations commit e0be98508)

## Motivation

The generated slave-side arbiters are round-robin (`crossbar_generator.py:608`,
grant locked through handshake). Dally & Towles, ch17 §18.5 describe the
matrix arbiter as their preferred choice for small arbiters: fast, cheap,
strongly fair, and often better timing than pointer-based RR encoders — the
relevant comparison for Bridge's typical 2–8 master port counts.

## What to do

1. Implement a matrix-arbiter variant behind the existing `arbitration`
   TOML knob (e.g. `arbitration = 'matrix'`), mirroring how `'qos'` was added.
2. Evaluate on a 2x2 and 4x4 config: timing (generated critical path),
   area, and fairness behavior vs `'rr'` under the TASK-014 traffic patterns.
3. Adopt as default only if it wins on timing without a fairness regression;
   otherwise keep `'rr'` default and document the measurement.

## Done when

- [ ] `arbitration = 'matrix'` generates and passes the bridge FULL regression
- [ ] timing/area/fairness comparison recorded in HAS ch05
- [ ] default policy decision recorded in the PRD

## References

- `projects/components/fabric-gen-ip/bridge/references/README.md` (Dally &
  Towles ch17)
