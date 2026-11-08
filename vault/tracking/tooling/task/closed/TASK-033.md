# TASK-033: triage the guides still sitting beside their tools

**Priority:** P3
**Status:** CLOSED (2026-11-07)
**Owner:** tooling
**Filed:** 2026-11-07, when the tool-mechanics exception was retired

## Why

On 2026-11-07 the exception that let a tool's guide live beside the tool was
retired (CLAUDE.md, handbook `authoring/doc-placement.md` rule 1). Its three
named cases moved into the handbook: `doc-generation`, `signal-naming-audit`,
and the mechanics section of `signal-contracts-and-kmaps`. A guide beside its
tool is found only by an agent that already knows the tool exists, where it
lives and that a guide sits next to it.

Other Markdown under `bin/` was never named under the exception and was not
part of that move. Each needs a decision.

## Candidates (line counts 2026-11-07)

| File | Lines | First read |
|---|---|---|
| `bin/mux-level-schematics.md` | 679 | DONE 2026-11-07: deleted (Sean) |
| `bin/TBClasses/wavedrom_user/GAXI_WAVEDROM_GUIDE.md` | 563 | DONE 2026-11-07: it was only a symlink to `docs/markdown/TestTutorial/wavedrom_gaxi_example.md`, a chapter of the TestTutorial book linked from 6 pages; symlink deleted, DOCUMENTATION_INDEX and the dv INDEX point at the book chapter |
| `bin/rtl_generators/bf16/README.md` | 373 | generator guide |
| `bin/svsherpa/README.md` | 213 | tool guide |
| `bin/TBClasses/apb4_monitor/apb4_monitor_readme.md` | 148 | BFM usage |
| `bin/apps/ddr_drills/notes/pack-authoring.md` | 124 | app authoring notes |
| `bin/TBClasses/harness/README.md` | 81 | harness usage |
| `bin/HEADER_TOOL_USAGE.md` | 9 | likely already a pointer |
| `bin/review/README.md` | 7 | likely already a pointer |

Out of scope: `bin/review/*_BRIEF.md` are prompts the review tools send, not
guides, and `bin/apps/*/README.md` describe standalone apps to their users.
Confirm both readings during the triage rather than assuming them.

## Done when

Each candidate is either moved into the handbook (and indexed, with every
reference repointed) or reduced to a pointer file of the
`bin/md_to_docx_usage.md` shape, or recorded here as staying, with the reason.

## Resolution (2026-11-07)

Closed the same day, all candidates at once (Sean: they belong in the vault).

- Moved to the handbook, with `Source:` lines naming the tool directory and
  relative links rewritten: bf16 README -> `tools/bf16-generators`, svsherpa
  README -> `tools/svsherpa`, harness README -> `tools/uart-harness-transport`,
  apb4_monitor readme -> `dv/apb4-monitor-tests`, every `bin/apps/*/README.md`
  -> `tools/apps/<app>`, and the three ddr_drills notes ->
  `tools/apps/ddr-drills-{design,pack-authoring,timing-tables}`.
- New handbook area `tools/` with its own INDEX, linked from the handbook root.
- Deleted the two pointer files, `bin/HEADER_TOOL_USAGE.md` (`--help` carries
  it) and `bin/review/README.md` (the handbook note carries it).
- Repointed: seven cache-ip HAS/MAS pages (cache_sim), four ddr_drills JS
  comments, and the 2026-10-03 ddr-drills spec.
- `bin/review/*_BRIEF.md` stay: they are prompts the review tools send.
