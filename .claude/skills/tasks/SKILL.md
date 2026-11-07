---
name: tasks
description: Where project tasks, bugs and issues live and how to track them - vault/tracking/<area>/ with task/bug/issue lanes, one file per item, state = directory, transitions by git mv, IDs from bin/check_task_ids.py --next. Use whenever you would record a TODO, file a bug, start/finish/park an item, or are tempted to create a TASKS.md or TODO.md next to code.
---

# tasks

READ FIRST: `vault/tracking/INDEX.md`. It is the authority for this convention;
this skill is a signpost and stops at the essentials.

**Never create a `TASKS.md`, `TODO.md` or `*_TODO.md` next to code.** That
scatter is what `vault/tracking/` replaces, and it is the rule agents break
most often here.

## The shape

```
vault/tracking/<area>/              area mirrors the repo path (rtl/amba, projects/components/...)
  INDEX.md                          rollup
  task/  bug/  issue/               three lanes, each with its own INDEX.md and Next ID
    open/ active/ closed/ dropped/  one file per item: <ID>.md
    deferred/                       created on first need
```

- **Pick the lane.** `task` = planned work (starts from intent). `bug` = a
  defect where you can state expected AND observed behaviour. `issue` =
  undiagnosed; it resolves into a bug, a task, or a recorded no-action.
- **Take the ID** from the lane INDEX's `Next ID:` line, or
  `bin/check_task_ids.py --next <lane path>` (e.g.
  `--next rtl/amba/bug`). Bump the line. Never recycle an ID; `-000` is the
  reserved template; real items start at `-001`.
- **One file per item.** Filename == ID == H1 (`# BUG-012: ...`). Add the item
  to the lane INDEX; the checker fails on a missing entry or a ghost.
- **State is the directory; a transition is `git mv`**
  (`git mv open/BUG-012.md active/BUG-012.md`). Keep the dated `**Status:**`
  line in step. `closed` = done, `dropped` = decided not to do it,
  `deferred` = parked on a NAMED external condition.
- **The area is the namespace.** File the item in the area of the code it is
  about, and cite it with the area: "pumice BUG-009", "amba TASK-073". Never
  invent compound prefixes (`PUMICE-BUG-001` does not parse).
- **Check before committing:** `bin/check_task_ids.py --area <path>`. It also
  runs from the pre-commit hook whenever a `vault/tracking/**` file is staged.

`known_issues/` beside the code is a different thing: a won't-fix ledger of
defects we accept. A vault item is something we intend to resolve.

Enforcement authority remains `/GLOBAL_REQUIREMENTS.md`. Design, DV and FPGA
method lives in the handbook (`vault/handbook/INDEX.md`); this tracks WORK.
