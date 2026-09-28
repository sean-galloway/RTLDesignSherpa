# TASK-007: Migrate the remaining method docs out of bin/ into the handbook

> Migrated 2026-09-27 from `vault/Tasks/tooling/closed.md` as **TOOL-002** (tooling TOOL-001). The flat page did not record a lane; this item was placed by hand. Body preserved as written -- only the H1 and this line are new.
**Priority:** P2
**Status:** Closed 2026-09-23. Four of the seven reduced or retired; three kept
DELIBERATELY, which is the decision this entry asked for and did not make.

**Reduced to pointers** (the `bin/review/README.md` shape):
- `md_to_docx_install.md` 98 -> 12. Generic walkthrough -- install Python, make
  a venv, install Pandoc -- with nothing repo-specific in it.
- `md_to_docx_usage.md` 104 -> 13. **It was WRONG, not merely redundant.** It
  documented `-t/--template`, `-o/--output` and `--verbose`, none of which the
  tool has, and `md_to_docx.py input.md` with one positional when it takes two.
  Following it produced an argparse error. `--help` is now the pointer, because
  it is generated from the parser and cannot drift.
- `HEADER_TOOL_USAGE.md` 285 -> 9. 285 lines restating
  `add_file_headers.py --help`, which already carries the flags AND the
  dry-run / per-directory examples.

**Retired outright:** `markdown_to_word_instructions.md` (417 lines) documented
`markdown_to_word.py` -- a tool that has never existed in this repo. Not on
disk, not tracked, not in history, imported by nothing; its CLI (`--dir/--out`)
is not md_to_docx.py's. The entry says "do not delete outright", and that rule is
right for a doc whose tool exists; a redirect to a tool that was never here
points nowhere. It carried 24 broken links -- the single worst file in
DOCREV-011's tally -- because they pointed into that absent toolchain.

**KEPT as canonical mechanics, and this resolves the "known inconsistency":**
`DOC_GENERATION.md` (356), `SIGNAL_CONTRACTS_KMAPS.md` (118) and
`SIGNAL_NAMING_AUDIT.md` (451). The handbook deliberately points OUTWARD at the
first two -- `doc-pipeline.md:8` "Canonical how-to: bin/DOC_GENERATION.md. This
note carries the decisions and traps; the mechanics live there", and
`signal-contracts-and-kmaps.md:13` "Methodology (canonical):
bin/SIGNAL_CONTRACTS_KMAPS.md". That is a chosen split (rationale in the
handbook, mechanics beside the tool), not rot, and DOC_GENERATION.md carries 356
lines the handbook genuinely lacks: the 6-step stand-up, document-unit anatomy,
`<doc>_index.md` semantics, styles YAML, the generate script. Collapsing it would
change what `doc-pipeline.md` IS.

**What that leaves for Sean, deliberately not decided here:** CLAUDE.md's rule is
absolute ("no README beside a tool restating how to use it"), and the split above
is a documented exception to it. Either the rule gains a "tool mechanics may live
beside the tool, rationale in the handbook" clause, or those three move and the
two handbook notes stop deferring outward. Both are defensible; it is a
doc-architecture call, not a cleanup.

**RESOLVED 2026-09-25 (Sean): the rule gains the clause.** Tool mechanics may
live beside the tool, with the rationale in the handbook. The three files stay,
and `doc-pipeline.md` / `signal-contracts-and-kmaps.md` keep deferring outward
-- that split is now documented in root `CLAUDE.md` and [[doc-placement]] rule 1
rather than standing as a contradiction. The test that comes with it: mechanics
a reader of that directory needs may stay; method that applies everywhere goes
to the handbook. That same test now governs the subsystem `CLAUDE.md` files.
**Owner:** resolved.

The `- [ ]` checklist below is STALE and is kept only for history: the work it
lists was completed in this same entry above. `HEADER_TOOL_USAGE.md` is 9 lines,
`md_to_docx_install.md` 12 and `md_to_docx_usage.md` 13 -- all already reduced to
pointers; `markdown_to_word_instructions.md` was retired; and the remaining three
are the kept-by-exception cases. Nothing in it is outstanding.

`CLAUDE.md` now states the handbook is the single source of truth for skills and
methods, and that methodology does not live next to the code. Seven files in
`bin/` still do. They were deliberately left when the Kimi migration was scoped
to Kimi only — this is the follow-through, not new work.

- [ ] `bin/DOC_GENERATION.md` — the doc pipeline how-to
- [ ] `bin/HEADER_TOOL_USAGE.md`
- [ ] `bin/markdown_to_word_instructions.md`
- [ ] `bin/md_to_docx_install.md`
- [ ] `bin/md_to_docx_usage.md`
- [ ] `bin/SIGNAL_CONTRACTS_KMAPS.md`
- [ ] `bin/SIGNAL_NAMING_AUDIT.md`

Method content moves into the relevant handbook note (mostly
[[doc-pipeline]] and [[signal-contracts-and-kmaps]]); each file is reduced to a
short pointer, as `bin/review/README.md` already is. Do not delete outright —
someone landing in `bin/` should still be redirected.

**Known inconsistency to resolve as part of this:** `doc-pipeline.md` currently
calls `bin/DOC_GENERATION.md` the "canonical how-to", which contradicts the rule
one note away. Whichever way it resolves, the two must agree.

**Distinguish artifacts from documentation.** Files the code *reads* are not
documentation and stay put — `bin/review/REVIEWER_BRIEF.md` and
`docs/kimi_humanization_style_guide.md` are loaded verbatim as prompts. Check
before moving anything.

---

---
