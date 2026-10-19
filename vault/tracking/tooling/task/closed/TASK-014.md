# TASK-014: check_task_ids.py reconciles INDEX state counts against the directories

**Priority:** P2
**Status:** CLOSED 2026-09-28
**Owner:** TBD (tooling)
**Filed:** 2026-09-28

## What

`bin/check_task_ids.py` verifies filename == H1 and Next-ID monotonicity but
does NOT reconcile an INDEX's per-state count table against the directories.
The RLB session hit it 2026-09-28: its INDEX said `closed: 15` while the file
was still in `open/`, and the checker passed. Tooling TASK-004 edited counts in
nine lane indexes the same day and had to verify each with
`ls <state>/*.md | wc -l` by hand.

## Do

- For every lane INDEX, compare each `| [<state>/](<state>/) | N |` row with
  the number of `*.md` in that directory; mismatch fails.
- Also fail when a state directory has no row, or a row names a directory that
  does not exist.
- It runs in the pre-commit hook and CI already, so the gate is inherited;
  fix the mismatches it finds in the same commit (list them in the message).

## Done when

- [x] a deliberately wrong count fails the checker (mutation-tested)
- [x] tree-wide run passes with zero mismatches

## CLOSED 2026-09-28

`bin/check_task_ids.py` now reads every `| [<state>/](<state>/) | N |` row of a
lane INDEX and compares N with the `<ID>.md` files in that directory
(templates included, as the tables always counted them). A row that
disagrees, a missing row for a non-empty directory, and a row naming an
unknown state are ERRORS. Mutation-tested three ways on tooling/task before
committing: closed 13 -> 15 (FAIL, names both numbers), the open/ row deleted
(FAIL, "no count row for open/ but 2 item(s)"), and TASK-014 moved to active/
with no table edit (FAIL twice: open 2 vs 1, active 0 vs 1). Restored, the
tree-wide run passes on all 86 areas with zero mismatches, so no lane was
carrying a wrong count at the time this landed. The check inherits the
pre-commit hook and CI because both already run this script.
