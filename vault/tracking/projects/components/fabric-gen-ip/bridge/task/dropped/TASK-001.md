# TASK-001: trim the method out of bridge/CLAUDE.md, keep the area facts

**Priority:** P3
**Status:** dropped 2026-09-25 -- the file is already compliant. Every row of
the removal table below was falsified by reading the text it named.
**Owner:** --

Filed 2026-09-24 on the premise that `bridge/CLAUDE.md` (957 lines) restates
method that root `CLAUDE.md` says does not belong beside code. Then each row was
checked against the file. Four for four wrong, and the errors all have the same
shape: **duplication inferred from STRUCTURE -- section titles, line counts, the
presence of a "Rules" block -- instead of from the text.** Every time the text
was actually read, it turned out to be already-deferred or unique.

| filed claim | what the file says |
|---|---|
| Rules #0.1 / #1 / #3 / #4 are restated TB method, ~77 lines | Already pointers. #0.1: "the rule and the reasoning are in `vault/handbook/dv/tb-structure.md` and `/GLOBAL_REQUIREMENTS.md` 2.1", then what is bridge-specific (one TB shared by the per-config test, the `*_mon_monitor.py` stress test and external imports). #1: "the requirement is `/GLOBAL_REQUIREMENTS.md` 2.2 and 2.3", then `BridgeAXI4FlatTB`, `aclk`, `aresetn`. #3: defers to `bfm-usage.md`, keeps the `s0_axi4_` prefix example. Only #4 is mostly generic, and it still carries the in-order-response fact. |
| the directory tree is reconstructible with `ls`, ~45 lines | **Load-bearing.** Line 303: "The bridge layout that satisfies it is the tree under Rule #0.1 below." Line 321: "That layout is the tree above -- it is not repeated here." Two pointers were written against that tree; deleting it breaks both and puts the prose back. |
| Rule #0 restates root Rule #0, ~46 lines | Already defers: "The rule itself, why partial regeneration fails silently, and the symptom list are the root `/CLAUDE.md` Rule #0 and `generated-rtl-discipline.md`. What is bridge-specific:" -- then the generator list, the workflow, "Never regenerated: `rtl/bridge_cam.sv`", and the five per-generator header strings. |
| the 460-line TOML/CSV generator block duplicates `GENERATOR_ARCHITECTURE.md` | Measured: channel-specific masters appear 12 times here against 1 there and 0 in `bin/test_configs/README.md`; the RAPIDS example 28 against 0 and 0. This file is the ONLY home for both. |

Two further claims made while scoping, also false: that
`GENERATOR_ARCHITECTURE.md` is unmarked-stale (its debugging sections are
labelled `HISTORICAL (stale) ... do not act on it` at lines 7 and 817, and it
was refreshed 2026-09-13), and that its YAML section documents a dead format
(`bridge_generator.py` accepts `.yaml` at four sites and three config modules
handle it; 0 yaml against 42 toml is a preference, not a removal).

**There is no size rule.** `GLOBAL_REQUIREMENTS.md` states none and neither do
the authoring notes. "957 lines" was never the standard; the standard is
content, and this area genuinely holds that much area-specific content.

## The one residual, deliberately not filed as work

"Target Architecture: Intelligent Width-Aware Routing" (~100 lines) overlaps
`bridge/PRD.md`'s "Architecture Philosophy", which carries the same OLD/NEW
64b/512b conversion examples in condensed form. Both are current -- the PRD says
"**Delivered:** Intelligent width-aware routing" and this file's Implementation
Status records that the block "described the Phase-1 fixed-width crossbar as
current ... That rework has happened; the block outlived it." A move would put
requirements rationale in the requirements doc, but it is one section, both
copies are correct, and the correction note is worth keeping where an agent
reads it. Not worth a task; do it if you are editing the section anyway.

## What this cost, and the rule that would have saved it

Six verification passes to establish that the right answer was "do nothing".
The cheap check that would have collapsed it at the start: **read the first
paragraph of each section you intend to delete.** Three of the four rows above
announce their own deferral in their opening sentence. A section titled
"Rule #1: TBBase and the three mandatory methods" looks like restated method
from the outline and is a pointer in the body.

Related: [[doc-placement]] rule 1 gained the tool-mechanics clause on
2026-09-25, which is the rule this task should have been read against --
area-specific mechanics stay, restated general method goes.
