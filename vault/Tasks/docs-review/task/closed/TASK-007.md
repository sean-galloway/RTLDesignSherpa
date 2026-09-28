# TASK-007: README rollout: convert 105 beside-code READMEs to link stubs

> Migrated 2026-09-27 from `vault/Tasks/docs-review/open.md` as **DOCREV-007** (tooling TOOL-001). The flat page did not record a lane; this item was placed by hand. Body preserved as written -- only the H1 and this line are new.
**Status:** CLOSED 2026-09-27 -- the owner confirmed the docs-review work is done. No measurement was taken in this session to support that; the basis is Sean's statement, recorded as such rather than presented as verification.
**Status (as filed):** open 2026-07-24 — pattern established (rtl/common), 104 to go
**Priority:** P2
**Owner:** TBD

The tree has **105 `README.md` files**, and many are 500-1000 line standalone
guides beside the code — `projects/components/README.md` (1062),
`converters/README.md` (719), `rtl/integ_amba/examples/README.md` (698),
`rtl/amba/README.md` (635). Every one is a second copy that rots on the next
structural change, exactly as `rtl/common/README.md` did (claimed 86 modules
after the split left 55). See [[doc-placement]].

**The pattern, already worked once (rtl/common, commit ec6bd81a):**
- [ ] For each big README: move the genuine standalone-guide prose into
      `docs/markdown/<Book>/` (a `quickstart.md` or folded into `index.md`),
      correcting staleness during the move (derive counts, drop content that
      moved elsewhere).
- [ ] Replace the beside-code `README.md` with a link stub, written in voice
      from the template in [[doc-placement]].
- [ ] Repoint referrers (the `# Documentation:` code headers, cross-links).
- [ ] Link-check the moved tree.

**Humanization (Sean, 2026-07-24): every README gets humanized eventually.**
Two phases:
- [ ] **Write in voice now.** Each stub is authored from the [[doc-placement]]
      template in voice, so it starts human. This is the floor.
- [ ] **Bulk humanization pass over ALL READMEs, later.** The stubs included,
      not only the guide prose they shed. This is a real pass, still to be run.
      **Tooling gap:** `bin/review/run_batch.py humanize` only globs
      `books/**/DOCS.md`, so it cannot see scattered `README.md` files today.
      Running the bulk pass means either bundling the READMEs as units or
      teaching the humanizer to target `README.md` directly — decide which as
      part of this task.

Guide content that moves into `docs/markdown/` becomes a bundle-able `DOCS.md`
unit and gets the normal humanize pass with every other page as a side effect.
Contract recorded in [[humanization-voice]] and [[doc-placement]].

**Do not blanket-convert.** Some READMEs legitimately stay: `known_issues/README.md`
is a bug-record index, `boards/README.md` and report-dir READMEs may be local
manifests the tooling or a human genuinely reads in place. Apply the
[[doc-placement]] test (method/second-copy vs local-instruction) per file, not a
mass `sed`.

**Sequence with the doc reviews.** Converting a README that a pending Kimi unit
cites would move the target mid-review; do the area's DOCREV-001 findings first,
then its README, the same order used for the rtl-math move.

---
