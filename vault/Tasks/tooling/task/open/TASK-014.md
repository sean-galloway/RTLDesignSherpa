# TASK-014: check_task_ids.py reconciles INDEX state counts against the directories

**Priority:** P2
**Status:** open
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

- [ ] a deliberately wrong count fails the checker (mutation-tested)
- [ ] tree-wide run passes with zero mismatches
