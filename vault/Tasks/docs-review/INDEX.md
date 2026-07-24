# docs-review — task rollup

External documentation review (Kimi) and the humanization pass.
Process and rationale: [kimi-review-rounds](../../handbook/authoring/kimi-review-rounds.md).

| State | Count |
|---|---|
| [active](active.md) | 0 |
| [open](open.md) | 5 |
| [closed](closed.md) | 0 |
| [dropped](dropped.md) | 0 |

## Open shortlist

- **DOCREV-001** — integrate 271 outstanding accuracy findings (round_2 + round_3).
  Nothing integrated yet; some are RTL defects, not doc bugs.
- **DOCREV-002** — humanizer structural-preservation preamble + tag-survival test.
  Mechanism exists in `run_batch.py`; the proof does not. Gates DOCREV-003.
- **DOCREV-003** — final MD-only humanize round. Blocked on DOCREV-002 and -001.
- **DOCREV-004** — back up or retire the off-repo collateral at
  `/mnt/data/github/rtl-doc-review/`.
- **DOCREV-005** — cloud enablement: key as a secret + egress allowlist. Gates
  new rounds only; the 339-finding backlog needs no API call.
