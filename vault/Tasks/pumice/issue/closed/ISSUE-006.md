# ISSUE-006: paging_sched_cross in_order floor: MISCALIBRATED FLOOR, not an RTL stall

> **Migrated from `PUMICE-021`** on 2026-09-27, when this area's flat
> `closed.md` was split into one file per item to match the rest of the vault.
> The legacy ID is cited throughout the repo -- RTL comments, DV code, handbook
> notes, commit messages and session memory -- so it is NOT rewritten at those
> call sites; `vault/Tasks/MIGRATION_MAP.md` and this line are how an old
> `PUMICE-021` reference resolves. Body below is verbatim from the flat page.
>
> Lane chosen by reading this item's own Status line and opening, not its title:
> a keyword pass over the 35 items misclassified 14 of them.


**Status:** closed 2026-09-09 — diagnosed by measurement, floor re-cut by mechanism

The floor failure (`static_close x order_in_order` 37.87%, later joined by
`rbl_static` 37.87% and `rbl_dyn` 44.14%, against IN_ORDER_FLOOR=0.45 whose
comment expected ~56.3%) is the honest cost of the mode. It is NOT a stall
defect and there is nothing to fix in the RTL.

**Discriminator.** Across the eight paging modes under in_order, the split is
exact: every mode that actually drives AUTO-PRECHARGE sits at 37.87-44.14%
(static_close, rbl_static, rbl_dyn) and every mode that does not sits at
exactly 80.33% with stall=94 (build_default, static_open, fixed_open,
adapt_time, and adapt_access -- the last is AP-capable but never closes at the
default counter shape this sweep programs).

**Mechanism, measured** with a command-cadence probe on this exact window
(2026-09-09):

    static_open  x in_order  util 89.51%  ops {ACT:8, WR:64}   gaps 4x63, 8x8
    static_close x in_order  util 36.89%  ops {ACT:26, WRA:26} gaps 4x25, 8x34

Non-AP paging activates a row once and then streams columns at tCCD: ONE
command per access, every gap 4 cycles. AP paging makes every access a pair of
DEPENDENT commands, ACT then column-with-auto-precharge: ACT->col is tRCD
(gap 4) and col->next ACT is the head advancing through the arbiter's 3-stage
pick pipeline (gap 8). A 12-cycle period instead of 4, so about a third of the
utilization. Under FR-FCFS other banks' entries fill those gaps, which is why
the same windows read 100% there; strict ordering cannot fill them by
definition. The 0.45 floor and its 56.3% note predate the pipelined arbiter,
which is why every AP mode landed just under it.

**Resolution.** The test now carries floors split by mechanism -- 0.75 for the
non-AP paging modes, 0.30 for the AP ones -- with the probe numbers recorded
in the comment, plus an assertion that the AP modes are actually present so
the split cannot silently cover nothing. A regression in either class still
fails. Shortening the col->ACT head advance would lift the AP numbers and is
tracked as a performance item under PUMICE-024, not a correctness one.
