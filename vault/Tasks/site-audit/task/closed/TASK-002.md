# TASK-002: teach the checker to see BOTH directions (the 11-task triage is done)

> Migrated 2026-09-27 from `vault/Tasks/site-audit/open.md` as **AUDIT-002** (tooling TOOL-001). The flat page did not record a lane; this item was placed by hand. Body preserved as written -- only the H1 and this line are new.
**Status:** CLOSED 2026-10-04 — the checker gap was the only thing keeping
this open; the live-page direction now warns in `bin/check_task_ids.py`
(`LIVE_PAGES`/`TERMINAL_STATUS`, four teeth tests in
`bin/tests/test_check_task_ids.py`), and a full-tree run finds zero current
violations, so the rule enforces from day one.
**Priority:** P3 — bookkeeping, but it makes the rollup counts lie
**Area:** cross-cutting (common + pumice + amba) — filed here rather
than in `common/` because it is not common-area work; most of the
affected tasks happen to be COMMON-* and one amba. (The two pumice ones,
PUMICE-010/-011, were renumbered to PUMICE-019/-020 and re-statused closed on
2026-09-06 — no longer warnings.)

`bin/check_task_ids.py` reports these as WARNINGS (it deliberately does not
auto-fix them):

    common:  COMMON-010, -014, -015, -016, -017, -018, -019, -021
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

---

**Worked 2026-09-14 — warning count is now ZERO, and the caution above was
justified by the outcome.**

The COMMON-* and NEXYSA7-STREAM items named above are gone; someone cleared
them between 08-28 and now. A different set had taken their place, all in
amba, and it split exactly along the two-bug line this task predicted:

* **Genuinely done, stale line —** TASK-082. Its body already read "ALL FOUR
  FIXED ... safe to close" but never said CLOSED, so the checker kept flagging
  it. Status line updated; it stays in `closed.md`.
* **Still open and misfiled —** TASK-078, -083, -084, -085, -095. Every one
  says `open` or "NOT fixed" or "deliberately not fixed" in its own body, and
  four of them are real defects: monitor TIMEOUT saturation, SOFT_RESET not
  resetting the monitor subsystem, two deterministically seed-failing
  val/amba tests, and an arithmetic overflow in `axi_split_combi` found by
  formal. **Auto-flipping would have buried four defects.** Moved back to
  `open.md`.

The inverse problem was fixed in the same pass and is worth recording here
because the checker does NOT catch it: six entries sat in amba's `open.md`
with bodies reading CLOSED or DONE, including a duplicate
`AMBA-INTEG-EXAMPLES` heading that split one entry in half and made the task
count as both open and closed. `bin/check_task_ids.py` only warns on terminal
pages holding open bodies, not on `open.md` holding closed ones — so that
direction has to be looked for by hand, or the checker taught to see it.

Remaining: this task stays open only for that checker gap. The triage itself
is done.
