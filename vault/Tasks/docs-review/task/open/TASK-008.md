# TASK-008: Final per-section correctness + humanization pass (whole repo)

> Migrated 2026-09-27 from `vault/Tasks/docs-review/open.md` as **DOCREV-009** (tooling TOOL-001). The flat page did not record a lane; this item was placed by hand. Body preserved as written -- only the H1 and this line are new.
**Status:** open 2026-07-24 — the closing gate for the doc effort.
**Subsumed 2026-07-28 by AUDIT-001** (`vault/Tasks/site-audit/`): parts 2-3 of
the site-wide audit are this task, widened with RTL correctness (part 1) and
verification coverage (part 4). When AUDIT-001 goes active, cut this block
there; until then this remains the detailed statement of the docs half.
**Priority:** P2
**Owner:** TBD

Supersedes and absorbs the earlier "final Kimi round" (DOCREV-008). After every
area's findings are integrated and the reorg has settled, do ONE comprehensive
closing pass, **section by section**, across the entire repo — `rtl/*`,
`docs/markdown/RTL*`, **and** `projects/*` when we get there.

**Per section, send EVERYTHING — not just module pages:**
- [ ] Every `.md` in the section: `index.md`, `README.md`, `overview.md`,
      `quickstart.md`, the per-module pages — plus the section's RTL. The
      earlier rounds bundled module-page + RTL only; the meta-docs (index/
      readme/overview) were never reviewed and are exactly where count/structure
      drift hides (see the rtl/common 86-vs-55 case, [[doc-placement]] rule 3).
- [ ] **Correctness check** (`qc`): bundle from the CURRENT tree so paths are
      post-split (rtl-math, moved READMEs), serial, large max_tokens
      ([[kimi-review-rounds]] rules 1-4). Measure results against the tree;
      anything CONFIRMED becomes new DOCREV work. A near-empty round is the goal
      — that is the evidence the backlog is actually closed.
- [ ] **Humanization** (`humanize`) of ALL md files in the section — index,
      readme, overview, module pages — not only the prose docs. This is the
      bulk README humanization from DOCREV-007 folded in: every md, every
      section. Tooling gap to close first: `run_batch.py humanize` only globs
      `books/**/DOCS.md`, so index/readme/overview and scattered READMEs need
      bundling or a humanizer that targets them directly.

**Order:** correctness first, humanization second — never humanize an
un-corrected doc (the voice pass is prose-only and must not be handed known-wrong
content to "improve"). Run it section by section so a bad section is contained,
not smeared across one giant round.

**Gate:** do not start until the DOCREV-013 per-area rounds (cdc, common,
math, amba, projects/components) are done, AND the README rollout
(DOCREV-007) is done so the md set is stable. Needs Kimi enablement
(DOCREV-005) off-workstation. (Pre-2026-07-28 this gate listed the old
backlog areas; the corpus reset replaced backlog integration with the
DOCREV-013 fresh rounds.)
