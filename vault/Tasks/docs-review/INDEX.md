# docs-review — task rollup

External documentation review (Kimi) and the humanization pass.
Process and rationale: [kimi-review-rounds](../../handbook/authoring/kimi-review-rounds.md).

| State | Count |
|---|---|
| [active](active.md) | 1 |
| [open](open.md) | 4 |
| [closed](closed.md) | 0 |
| [dropped](dropped.md) | 0 |

## Active

- **DOCREV-001** — integrate the Kimi accuracy findings, area by area.
  **`common` is DONE** (2026-07-23) and verified by measurement against the
  tree, across all three rounds — including the `rtl/common` findings that hide
  inside the `cdc_part_01` unit, because the bundles were assembled by topic,
  not by directory. Remaining: math, shared, monitor (round_3, 70 CONFIRMED —
  the largest block), apb/apb5, axi*, axis*, and the AMBA half of cdc. Per-area
  checklist is at the top of the task. Some findings are RTL defects, not doc
  bugs — triage each.

## Open shortlist

- **DOCREV-002** — humanizer structural-preservation preamble + tag-survival test.
  Mechanism exists in `run_batch.py`; the proof does not. Gates DOCREV-003.
- **DOCREV-003** — final MD-only humanize round. Blocked on DOCREV-002 and -001.
- **DOCREV-004** — back up or retire the off-repo collateral at
  `/mnt/data/github/rtl-doc-review/`.
- **DOCREV-005** — cloud enablement: key as a secret + egress allowlist. Gates
  new rounds only; the 339-finding backlog needs no API call.
