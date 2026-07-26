# docs-review — task rollup

External documentation review (Kimi) and the humanization pass.
Process and rationale: [kimi-review-rounds](../../handbook/authoring/kimi-review-rounds.md).

| State | Count |
|---|---|
| [active](active.md) | 1 |
| [open](open.md) | 6 |
| [closed](closed.md) | 1 |
| [dropped](dropped.md) | 0 |

## Active

- **DOCREV-001** — integrate the Kimi accuracy findings, area by area.
  **common, cdc, and math are DONE** (2026-07-23) and verified by measurement against the
  tree, across all three rounds — including the `rtl/common` findings that hide
  inside the `cdc_part_01` unit, because the bundles were assembled by topic,
  not by directory. Remaining: shared, monitor (round_3, 70 CONFIRMED —
  the largest block), apb/apb5, axi*, axis*, and the AMBA half of cdc. Per-area
  checklist is at the top of the task. Some findings are RTL defects, not doc
  bugs — triage each.

## Recently closed

- **DOCREV-006** — math docs moved to `docs/markdown/rtl-math/` (2026-07-23),
  matching `rtl/math/` and `val/math/`. Kimi critiques deliberately left citing
  the old paths; they are evidence, not documentation.

## Open shortlist

- **DOCREV-002** — humanizer structural-preservation preamble + tag-survival test.
  Mechanism exists in `run_batch.py`; the proof does not. Gates DOCREV-003.
- **DOCREV-003** — final MD-only humanize round. Blocked on DOCREV-002 and -001.
- **DOCREV-004** — back up or retire the off-repo collateral at
  `/mnt/data/github/rtl-doc-review/`.
- **DOCREV-007** — README rollout: 105 beside-code READMEs, many 500-1000 line
  standalone guides, to link stubs (guide prose -> docs/markdown, stub written
  in voice). Pattern worked on rtl/common; 104 to go. Per-file judgement, not a
  mass sed.
- **DOCREV-009** — final per-section correctness + humanization pass over the
  WHOLE repo (rtl + all md: index/readme/overview/module pages + projects).
  Correctness first, then humanize every md. Absorbs the old final-round task
  and the README humanization. Gated on all areas integrated.
- **DOCREV-005** — cloud enablement: key as a secret + egress allowlist. Gates
  new rounds only; the 339-finding backlog needs no API call.
