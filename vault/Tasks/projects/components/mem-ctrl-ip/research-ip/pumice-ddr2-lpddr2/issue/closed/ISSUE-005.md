# ISSUE-005: CAM->arbiter pick cone does not close timing: CLOSED (stale)

> **Migrated from `PUMICE-017`** on 2026-09-27, when this area's flat
> `closed.md` was split into one file per item to match the rest of the vault.
> The legacy ID is cited throughout the repo -- RTL comments, DV code, handbook
> notes, commit messages and session memory -- so it is NOT rewritten at those
> call sites; `vault/Tasks/MIGRATION_MAP.md` and this line are how an old
> `PUMICE-017` reference resolves. Body below is verbatim from the flat page.
>
> Lane chosen by reading this item's own Status line and opening, not its title:
> a keyword pass over the 35 items misclassified 14 of them.


**Status:** closed 2026-09-09 — the measured condition no longer exists

Filed 2026-08-31 against a post-route WNS of **-48.861 ns** with 8939 failing
endpoints, on the grounds that logic delay alone (17.825 ns) exceeded the 15 ns
period so no placement effort could recover it: "it is depth, and it needs
registers."

It got them. The three-stage pick split (STAGE-1a snapshot -> STAGE-1b arg_sel
-> pre-pick -> output), the CAM per-entry vector refactor, and finally the
pre-pick operand muxing of PUMICE-024 did exactly what the task asked for. The
current measurement on the same board and harness, at the HIGHER 75 MHz
target:

    WNS                 +0.009 ns   against 13.333 ns (75 MHz)
    Failing endpoints      0 / 72896
    ENHANCED tier       +0.005 ns, 0 failing

The task's secondary claim -- "TASK-001 was never synthesized" -- is also
stale: all three mode axes are in the board build, and the paging predictors
were restored to it on 2026-09-09.

Closed against evidence rather than assumption; the remaining pick-cone work
is performance (the auto-precharge head advance under strict ordering), not
closure, and it is recorded on PUMICE-021 in this file.
