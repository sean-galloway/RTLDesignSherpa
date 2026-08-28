<!-- Managed by the `tasks` convention: see /vault/Tasks/INDEX.md. Move a task between pages by cutting its block, do not copy. -->

# common — Open (accepted, ready to start)

## COMMON-024 — triage 11 tasks whose body status contradicts their page
**Status:** open 2026-08-28 — surfaced by `bin/check_task_ids.py`
**Priority:** P3 — bookkeeping, but it makes the rollup counts lie

`bin/check_task_ids.py` reports these as WARNINGS (it deliberately does not
auto-fix them):

    common:  COMMON-010, -014, -015, -016, -017, -018, -019, -021
    pumice:  PUMICE-010, PUMICE-011
    amba:    NEXYSA7-STREAM  (in closed.md, body says dropped)

Each lives in a terminal page (`closed.md` / `dropped.md`) while its body
still says `**Status:** open`. TWO different bugs are mixed in here and they
need OPPOSITE fixes, which is why it was not automated:

* **closed with a stale line** — the work is genuinely done and only the
  status text was never updated. Fix: update the line. (Session notes say
  COMMON-021 is this case: the covers were verified.)
* **still open and misfiled** — the work is NOT done and the task reached
  closed.md by mistake. Fix: move it back to `open.md`. (COMMON-010, "every
  module MUST have a filelist and a registry entry", reads like this one —
  and TASK-026 in amba is its shared gate, still open.)

Auto-flipping the text would launder the second kind into the closed pile,
which is worse than the inconsistency it fixes. Read each, decide, then the
warning count should reach zero.
