# TASK-000: TEMPLATE — copy this file, never file against it

**Priority:** P3
**Status:** open
**Owner:** TBD

ID 000 is a reserved dummy in every area and every lane. It exists so the lane
carries a recognised item from the day it is created -- an empty directory and
a directory the checker cannot parse look identical in a passing run, and this
repo has shipped that failure more than once. Real tasks start at TASK-001.

**What belongs in this lane:** planned work we have decided to do: a feature, a refactor, a migration, a cleanup. It starts from intent, not from a failure.

## How to file one

1. `bin/check_task_ids.py --next site-audit/task` gives you the ID.
2. `cp open/TASK-000.md open/<ID>.md`, then edit the H1 to `# <ID>: <title>`.
   The filename and the H1 must agree -- the checker enforces it.
3. Bump the `Next ID:` line in `INDEX.md` and add the item to its list.

## How to move one

State is the DIRECTORY, not a line of text:

    git mv open/<ID>.md active/<ID>.md

Keep the `**Status:**` line in step with the directory; the checker warns when
a file in `closed/` or `dropped/` still says it is open.
