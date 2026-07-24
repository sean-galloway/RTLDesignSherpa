---
title: Doc placement
summary: What kind of documentation lives where - handbook vs docs/markdown vs beside-code vs vault/Tasks - and the rule that a beside-code file is a link, never a second copy.
---

# Doc placement

Every piece of writing in this repo has exactly one right home. Put it in the
wrong one and it becomes a second copy - and the copy nobody edits is the one
the next session reads. This note is the authority on where each kind goes.

## The four homes

| Kind of writing | Home | Example |
|---|---|---|
| **Method / practice / rationale** - how we do X here, and the failure that taught it | `vault/handbook/` | reset conventions, the review rules, a doc style guide |
| **Reader-facing product docs** - per-module pages, guides, HAS/MAS, operator manuals | `docs/markdown/` | `RTLCommon/fifo_sync.md`, `RTLCommon/quickstart.md` |
| **Work items** - anything with a beginning and an end | `vault/Tasks/<area>/` | "integrate the math findings", "fix DEPTH=6" |
| **Beside-code, agent-facing** - subsystem instructions and specs a reader of *that directory* needs | the RTL/project dir | `rtl/common/CLAUDE.md`, an area `PRD.md` |

`/GLOBAL_REQUIREMENTS.md` is the enforcement authority and outranks all of this.

## The rules, and the case each came from

1. **Methodology never lives in the RTL tree.** A style guide, a how-to, a
   canonical process doc beside code is misplaced. It goes to `vault/handbook/`.
   *Case (2026-07-24): a 17 KB `DOCUMENTATION_STYLE_GUIDE.md` sat in
   `rtl/common/`; moved to [[module-doc-template]].*

2. **A beside-code README is a link, not a standalone guide.** If a directory
   warrants a quick-start, the guide lives in `docs/markdown/` and the
   directory's `README.md` points at it in a few lines. A full guide beside the
   code is a second copy by definition. *Case: `rtl/common/README.md` was a
   14 KB quick-start that drifted (claimed 86 modules when 55 remained); the
   guide moved to `docs/markdown/RTLCommon/quickstart.md` and the RTL README
   became a pointer.*

3. **One source per fact.** The same count, spec, or port list must not be
   stated in two files. A structural change updates one and forgets the other -
   *case: after the arithmetic split, `rtl/common/README.md` said 86 modules
   and `docs/markdown/RTLCommon/overview.md` still listed a live "Arithmetic &
   Math" category; both were wrong, in different ways.* If a number must appear,
   derive it (`ls rtl/<area>/*.sv | wc -l`) or state it in exactly one place and
   link.

4. **A durable lesson goes to the handbook note, not to a skill or a CLAUDE.md.**
   Skills are signposts; `CLAUDE.md` is agent guidance. Neither is where method
   detail lives - it rots there because it is a copy of the handbook note that
   nobody reconciles. Add it to the relevant `vault/handbook/` note and let the
   skill point at it.

5. **A file the tooling *reads* is an artifact, not documentation - leave it.**
   `bin/review/REVIEWER_BRIEF.md` and `docs/kimi_humanization_style_guide.md`
   are loaded verbatim as prompts; the raw `docs/review/kimi/**` critiques are
   evidence and are regenerated, never hand-edited. These stay where the code
   expects them even though they look like docs. Check whether something is
   *read by code* before "tidying" it.

## The beside-code README template

A beside-code `README.md` is a link, and it is short. This is the shape - fill
the bracketed parts, drop lines that do not apply, and **write it in voice**
([[humanization-voice]]): plain sentences, a reason where a reason helps, no
emoji, no "comprehensive/robust/seamless" filler.

```markdown
# <Area name>

<One or two plain sentences: what lives in this directory and who it is for.>

This is a pointer, by design: a standalone guide does not live in the <RTL/
project> tree, so it cannot rot out of sync with a second copy.

- **Per-module docs:** [docs/markdown/<Book>/](<relpath>/index.md)
- **Guide** (<what it covers>): [.../quickstart.md](<relpath>/quickstart.md)
- **Agent guidance for this subsystem:** [`CLAUDE.md`](CLAUDE.md)
- **Requirements/practice:** the [vault](<relpath to vault>/INDEX.md)
```

`rtl/common/README.md` is the worked reference. Every link is checked; the count
in the first line, if any, is derived (`ls <dir>/*.sv | wc -l`), never typed.

## Humanizing READMEs

Two passes, not one.

**Write in voice now.** A stub is authored from the template above in voice
([[humanization-voice]]) so it starts human - a 16-line pointer does not need an
API round to become readable. This is the floor, not the finish.

**Humanize them all eventually.** Every README gets a humanization pass at some
point (Sean, 2026-07-24) - the stubs included, not only the guide prose they
shed. Writing-in-voice is what keeps them acceptable in the meantime; it does
not exempt them from the bulk pass. Tracked as DOCREV-007.

That bulk pass is a tooling gap today: `run_batch.py humanize` globs
`books/**/DOCS.md`, so it only sees bundled units, not `README.md` files
scattered across the tree. Closing DOCREV-007 means either bundling the READMEs
or teaching the humanizer to target them directly.

Separately, when a bloated beside-code README is a real standalone guide, its
prose moves into `docs/markdown/` and becomes a bundle-able `DOCS.md` unit -
which picks up the normal voice pass with every other page as a side effect.

## What legitimately stays beside code

Not everything beside code is misplaced - the test is whether it is *method* (a
second copy) or *local instruction* (belongs to that directory):

- `CLAUDE.md` - agent guidance scoped to the subsystem. Stays.
- An area `PRD.md` - a requirements/spec artifact for that block. Stays (the
  repo `.gitignore` explicitly whitelists `PRD.md`). Keep its summary counts
  current or link them; do not let it become a second module catalogue.
- `known_issues/` - bug records for that area. Stays.
- A module docstring - what a reader of that one file needs, no more.

## When you find a violation

Move it, do not copy it. `git mv` so history follows. Repoint referrers - grep
for the old path across `*.md`, `*.py`, `*.sh` (code headers reference these:
`# Documentation: rtl/<area>/PRD.md` appears in ~50 generated files). Leave a
link where the reader will land. Then link-check the moved tree. This is the
same procedure the vault consolidation and the `RTLMath` split used.

Related: [[module-doc-template]] (the shape of a docs/markdown page),
[[doc-pipeline]] (how those pages build), [[kimi-review-rounds]] rule 8 (the
review pass that catches these), and the `tasks` convention for `vault/Tasks/`.
