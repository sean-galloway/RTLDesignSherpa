# docs-review — task rollup

External documentation review (Kimi) and the humanization pass.
Process and rationale: [kimi-review-rounds](../../handbook/authoring/kimi-review-rounds.md).

| State | Count |
|---|---|
| [active](active.md) | 0 |
| [open](open.md) | 10 |
| [closed](closed.md) | 2 |
| [dropped](dropped.md) | 1 |

## Corpus reset — 2026-07-28

Every prior round is cleared (Sean). Seven cdc rounds in two days (k3 rounds
4-10) had not converged; the backlog was being re-litigated, not closed.
Archive: `~/rtl-doc-review/archive-pre-reset-2026-07-28/`; the vendored
proxy corpus (`docs/review/kimi/`) survives in git history. **DOCREV-001 is
dropped** (its landed common/cdc/math integrations stay in the tree; the
un-integrated remainder is abandoned in favour of fresh rounds). Fresh
per-area rounds run under the tightened brief + second-model adjudication —
see **DOCREV-013** for the area order (cdc, common, math, amba,
projects/components, then assess fpga) and the per-area startup checklist
(four-line Makefiles first).

## Round log (post-reset corpus)

- **common_part_01 qc round_1** (2026-08-11, kimi via proxy, budget ladder
  fired once to 65536): targeted send after the new-arbiter pages joined the
  bundle. 4 CONFIRMED + 3 SUSPECTED, all 7 verified against RTL and
  integrated same day; the new arbiters' mechanism descriptions (DRR cost
  pipeline, token-bucket overspend gate) all validated. Notables:
  bin_to_bcd's latency formula was one cycle short (registered done); the
  WRR's "first round after reset is unweighted" narrative contradicted its
  own STABILIZE load (fixed in doc AND the RTL source comment — rule 6);
  the WRR/DRR FSM update latencies understated the constants-implied
  minimum ~2x on both pages; two dead WRR signals removed; a sibling-page
  sweep caught the same localparam-claim error on dataint_crc.md and
  verified counter_bin_load/clock_gate_ctrl as correctly stated. WRR + DRR
  re-linted, re-simmed, re-proved after the edits.
- **common_part_01 humanize round_2** (2026-08-11): all 11 pages rewritten
  and applied (99-100% length, 0 fatal tag-survival, 0 emoji); every qc fix
  verified surviving the voice pass (the +4 formula, the 10-25 latencies,
  N>=2, the fifo_sync example). The two new arbiter pages are now reviewed
  AND humanized.

## Recently closed

- **DOCREV-012** — second-model adjudication validated on reset-corpus cdc
  round_1 (2026-07-28): 3 findings, 0 FP, verifier 3/3 with human triage
  after four evidence-pack fixes; handbook rule 10 written.
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
- **DOCREV-010** — every docs/markdown book needs index.md + overview.md.
- **DOCREV-011** — fix ALL broken links, whenever they were introduced.
- **DOCREV-014** — 110 files under `docs/markdown/` carry emoji, against a rule
  that exists because they break PDF generation. The humanizer is one source;
  `check_tag_survival.py` now blocks that inflow.
- **DOCREV-013** — fresh per-area qc rounds under the adjudication pipeline.
  Order: cdc, common, math, amba (decomposed later), projects/components
  (decomposed later), then assess fpga. Per-area startup: four-line Makefiles
  (rtl/make/area.mk + make/tests.mk) before anything else.
