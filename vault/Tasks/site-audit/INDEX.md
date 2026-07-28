# site-audit — task rollup

The site-wide audit: one umbrella effort to prove, area by area, that the
RTL is correct, the docs match it, the docs read like a person wrote them,
and the verification actually covers the design. Newest area (2026-07-28);
scope is still clarifying as it runs — expect this task to split into
per-part children.

| State | Count |
|---|---|
| [active](active.md) | 0 |
| [open](open.md) | 1 |
| [closed](closed.md) | 0 |
| [dropped](dropped.md) | 0 |

## Open

- **AUDIT-001** — the site-wide audit, four parts: (1) RTL correctness,
  (2) docs/markdown matches RTL, (3) humanization, (4) verification coverage
  (TB / coverage / formal). Parts 2-3 subsume DOCREV-009; part 4 absorbs the
  pending `coverage` and `formal` task areas' backlogs as it reaches them.

## Relationship to other areas

This is an umbrella, not a silo. The per-part execution still lands in the
owning areas — doc findings become DOCREV work, RTL defects become amba /
common / pumice / RLB tasks, coverage gaps become val/formal work. This area
tracks the sweep itself: what has been audited, what passed, what the
evidence was.

Practice and rationale live in the [handbook](../../handbook/INDEX.md);
this directory tracks *work* only. `/GLOBAL_REQUIREMENTS.md` wins on conflict.
