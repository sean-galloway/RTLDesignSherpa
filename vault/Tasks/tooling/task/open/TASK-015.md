# TASK-015: check_task_ids.py runs only in pre-commit; CI never validates the tracker

**Priority:** P2
**Status:** open
**Owner:** TBD
**Filed:** 2026-09-28

`bin/check_task_ids.py` is invoked from `.git/hooks/pre-commit` and from
nowhere else. `grep -rn check_task_ids .github/workflows/` returns nothing,
and the filelist-checks workflow's fourteen steps (filelists, rdl-regen,
board-layer) contain no task-tracker step.

So the tracker's integrity has NO enforcement that survives a local
environment. A `--no-verify` commit, a checkout whose hooks were never
installed, or a hook file overwritten by another tool all land a lying tracker
with nothing downstream to catch it.

**That failure has already happened in the mirror direction, and is recorded
in this repo.** `.git/hooks/pre-commit`'s own header: a second tracked hook
appeared at `tools/hooks/pre-commit`, `make setup-hooks` COPIED it over the
symlink, and from 2026-08-28 to 2026-09-02 the filelist checks did not run
locally at all -- "Nobody noticed, because CI still ran them." For the task
checker there is no such backstop.

**Concretely at risk:** the count table (`open: N`), the INDEX item list, the
`Next ID` line, filename/H1 agreement, and the terminal-page status rule --
every invariant tooling TASK-014 added after an INDEX said `closed: 15` while
the file sat in `open/`.

**Done when:**

- [ ] a CI step runs `python3 bin/check_task_ids.py` over every area
- [ ] the step fails the build on a non-zero exit, not just prints
- [ ] a deliberately wrong count is shown to fail it (the gate must have teeth,
      not merely run -- see [[silent-fallbacks]])
