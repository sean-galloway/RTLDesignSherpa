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

2. **No README or PRD anywhere under `rtl/` at all** (Sean, 2026-07-24, commit
   `f7ca848a`). This supersedes the older "a beside-code README is a link, not a
   standalone guide" rule, which the RTL tree no longer has any README to apply
   to. The history that got us here still matters: `rtl/common/README.md` was a
   14 KB quick-start that drifted (claimed 86 modules when 55 remained), so the
   guide moved to `docs/markdown/RTLCommon/quickstart.md` and the README shrank
   to a pointer -- and then the pointers went too. Outside `rtl/`, in project
   areas, a README is still allowed and still must be a link rather than a
   second copy; the template below is for those.

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

## Every book directory has an index and an overview

**Rule (Sean, 2026-07-25): every directory under `docs/markdown/` carries both
`index.md` and `overview.md`, and the overview links to the index.** No
exceptions among book directories. `assets/` is not a book -- it holds shared
header fragments and per-book image dirs -- so it is out of scope; anything that
holds reader-facing pages is in scope.

The two files are not redundant, and the split is what keeps them from rotting
into each other:

- **`index.md` is the catalogue.** Every module page, linked, grouped by
  category. Counts in it are derived (`ls rtl/<area>/*.sv | wc -l`), never typed
  -- see rule 3.
- **`overview.md` is the orientation.** What this area is for, how the pieces
  relate, which module to reach for. It links to `index.md` for the catalogue
  rather than restating it.

There is a tooling reason too, not just a tidiness one: `build_review_bundle.py`
builds a review unit per `_book_*_index.md` and pulls in `overview.md` plus the
pages that index links. A book with no `overview.md` silently reviews less than
you think, and `index.md`/`quickstart.md` are outside the bundle entirely --
which is exactly how `RTLCommon`'s meta docs drifted six modules and a phantom
`sync_2ff` past three review rounds. See [[kimi-review-rounds]] rule 8.

### The link back from the RTL tree

Each area's RTL should point at its book's `overview.md`. It **cannot** be a
`README.md` -- rule 2 forbids those under `rtl/` -- so it goes in one of the two
places that are allowed:

- **The module header line.** `// Documentation: docs/markdown/<Book>/...` is
  already the convention and already present in 225 of the 232 modules under
  `rtl/{common,cdc,math}`. Point it at the area's `overview.md` (or a specific
  page where one exists); today most point at `index.md`.
- **The area `CLAUDE.md`.** Legitimately beside-code, and the natural home for
  one "the reader-facing docs for this area live here" line. Only `rtl/amba` and
  `rtl/common` have one; `rtl/cdc`, `rtl/math` and `rtl/integ_amba` do not.

### Current state (2026-07-25)

| Book | index.md | overview.md |
|---|---|---|
| RTLAmba | yes | yes |
| RTLCommon | yes | yes |
| projects | yes | yes |
| RTLMath | yes | **missing** |
| Scripts | yes | **missing** |
| TestTutorial | yes | **missing** |
| RTLcdc | **missing** | **missing** (directory exists but is empty) |

`docs/markdown/RTLcdc/` is an empty directory with casing that disagrees with
the `RTLCdc` the CDC reorg task specifies -- settle the name when that book is
populated, and do not leave both. Tracked as DOCREV-010.

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
