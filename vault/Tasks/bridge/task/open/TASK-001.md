# TASK-001: trim the method out of bridge/CLAUDE.md, keep the area facts

**Priority:** P3
**Status:** open
**Owner:** TBD

Root `CLAUDE.md` says a subsystem file holds AREA FACTS and references the vault
for method: "What does NOT [belong]: how to write a TB, how to run a regression,
naming conventions, doc standards, regeneration discipline." `bridge/CLAUDE.md`
is 957 lines and breaks that in three specific places. Measured 2026-09-24.

**There is no size rule.** `GLOBAL_REQUIREMENTS.md` states none, and neither do
the authoring notes. This is not "the file is too long" -- it is "these specific
passages are second copies". Do not turn it into a line-count exercise.

## What to remove, and why each is safe

| lines | what | why it is a copy |
|---|---|---|
| ~77 | Rules #0.1, #1, #3, #4 -- TB separation, TBBase's three methods, GAXI components, queue-based verification | restated verbatim in `GLOBAL_REQUIREMENTS.md` 2.1 / 2.2 / 2.4 / 2.5, and GR does **not** cite bridge as a source for any of them (it cites `projects/components/CLAUDE.md`, rapids, stream, amba). Replace with one pointer. |
| ~45 | "MANDATORY: Project Organization Pattern" directory tree | reconstructible with `ls`. Root `CLAUDE.md` v1.2 removed exactly this class from itself ("Removed the directory tree"). GR 2.1 carries the TB-location half. |
| ~46 | "CRITICAL RULE #0: RTL Regeneration Requirements" | root `CLAUDE.md` Rule #0 is canonical and names bridge explicitly (`make regen`). |
| ~100 | "Target Architecture: Intelligent Width-Aware Routing" | duplicated in `bridge/PRD.md` (its "NEW Approach (Target Architecture)" section carries the same 64b/512b conversion examples). The PRD is the right home for requirements rationale; the HAS/MAS do not cover it (0 book pages match "width-aware", "Intelligent" or "no fixed crossbar width"), so MOVE it to the PRD rather than deleting. |

## What must stay, and what nearly got deleted by mistake

Three claims I made while scoping this were wrong, and each would have destroyed
content if acted on. They are recorded because the next person will be tempted
the same way.

1. **"The 460-line TOML/CSV generator block duplicates `GENERATOR_ARCHITECTURE.md`."**
   False. Measured occurrences -- channel-specific masters (wr/rd/rw):
   `GENERATOR_ARCHITECTURE.md` 1, `bin/test_configs/README.md` 0,
   `CLAUDE.md` **12**. RAPIDS-style example: 0, 0, **28**. Generator output
   structure: 2, 0, 5. `CLAUDE.md` is the ONLY home for two of those topics.
   Only the invocation commands and the TOML basics are genuinely duplicated.
2. **"`GENERATOR_ARCHITECTURE.md` is stale and `CLAUDE.md` wrongly vouches for it."**
   False. Its "Current Broken State" and "Next Steps for Debugging" sections are
   already marked `HISTORICAL (stale) ... Kept for archaeology; do not act on it`
   at line 817 and again at line 7, and the file was refreshed 2026-09-13.
3. **"Its YAML Configuration Format section documents a format that no longer exists."**
   False. `bridge_generator.py` still accepts YAML --
   `ports_ext in ['.yaml', '.yml', '.toml']` at four sites, the error text reads
   "use .toml/.yaml", and `config_loader.py` / `config.py` /
   `config_validator.py` all handle it. There are 0 `.yaml` checked in against 42
   `.toml`, which is a preference, not a removal.

Also keep, because they are exactly what a subsystem file is for:

- the `slave_select_*` reverts-after-handshake pitfall with its WRONG/CORRECT
  patterns -- a trap particular to this directory;
- the Address Map facts (no default map, no 0x1000_0000 stride, and probing
  0x1000_0000 expecting slave 1 hits slave 0);
- the `bridge_id` in-order FIFO / IDs-pass-through / `bridge_cam.sv`-in-zero-
  bridges facts, and the "Deliberately NOT supported" list -- these correct
  claims that were false in this file for months;
- the TOOL-016 conftest `TEST_LEVEL` trap;
- "PDF Generation Location" -- a house convention shared with 9 peer files, so
  dropping it only here would break consistency.

## Before editing

`GLOBAL_REQUIREMENTS.md` cites area `CLAUDE.md` rules as its provenance
(`rtl/common` Rule #1 at GR:495 and Rule #3 at GR:175, `amba` Rule #0 at GR:210
and GR:306). GR restates each in full, so the area copies can defer to GR -- but
check the `**Source:**` lines still resolve after any renumbering. Nothing cites
a bridge rule, which is why bridge is the safe file to do first.

## The cross-area question -- not this task

`rtl/amba` (674), apbx-xbar (623) and `rtl/common` (567) have the same shape:
Q&A, integration patterns, anti-pattern catalogues, debugging workflows. Two
reasons not to sweep them here:

- a DOCREV round already went through `rtl/common/CLAUDE.md` and **corrected**
  its Integration Patterns against the RTL rather than removing them (four
  modules rewritten plus 9 stale occurrences swept, closed at `b398f8ae`), so
  removing that section would delete recently-verified work;
- whether method may live beside code at all is already parked for Sean as a
  doc-architecture call -- see the `bin/*.md` item in `tooling` closed notes
  ("Either the rule gains a 'tool mechanics may live beside the tool' clause, or
  those three move"). Settle that before applying a pattern to four files.

Do bridge as the worked example, then decide.
