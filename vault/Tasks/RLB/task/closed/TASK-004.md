# TASK-004: Triage & fix the RTL bugs found by the MAS/RTL review

> Migrated 2026-09-27 from `vault/Tasks/RLB/closed.md` as **RLB-004** (tooling TOOL-001). The flat page did not record a lane; this item was placed by hand. Body preserved as written -- only the H1 and this line are new.
**Status:** closed 2026-09-14

The 9 `bug`-labeled issues from RLB-001, all fixed and all CLOSED on GitHub:
#44 gpio, #46 hpet, #48 ioapic, #50 pic_8259, #52 pit_8254, #54 pm_acpi,
#56 rtc, #58 smbus, #60 uart_16550, plus tracking #61.

This entry sat in `active` claiming "awaiting owner design decisions, not
started in RTL" for four days after the work had landed. It was STALE, not
paused: the fixes went in 2026-09-10/11 with commit references recorded in
[[RLB-008]], [[RLB-010]], [[RLB-011]], [[RLB-012]] and [[RLB-013]], and the
issues were closed at the same time. A tracker that claims active work which
is finished is worse than no tracker, because nobody re-reads it.

**Verified green today, not taken on trust.** A clean
`make clean-all && make run-all-full-parallel` across all nine blocks at
REG_LEVEL=FULL: **63 passed, 0 failed** in 343.60s.

pm_acpi was re-checked specifically, because a long-running agent reported it
"17/21 green with 4 genuine RED findings". That report was a stale snapshot of
a tree that moved under it (the agent ran ~119 hours; its files date 09-09 to
09-11). The GH#54 suite runs and passes 21/21 -- 21 distinct PASS strings, each
in 4 of the 6 cells, the gate-level cells not running it by design -- including
all four tests it named. The RTL it described as pending had already landed:
`pm_acpi_core.sv` edge-detects `cfg_sys_reset` (904/910/1268) because
`peakrdl_to_cmdrsp` holds `regblk_req` for the accept cycle plus one, so a
`singlepulse` field otherwise asserts for two cycles. Same mechanism and same
remedy as rapids' kick refactor -- worth knowing it bites in both components.

**What stays open is not a defect:** [[RLB-008]] (ioapic -- LowestPriority is
delegated by Sean's call, and its consumer-side arbiter now ships as a
companion module; multi-IOAPIC routing, boot-interrupt delivery and MSI remain
scoped out). [[RLB-010]] has since CLOSED 2026-09-14: the formal area was
created, and the clock mux -- named here as deliberately not fixed -- was
resolved by `rtc_clk_mux`, which supplies the device-specific cell the entry
itself said was the real answer. This paragraph's claim that RLB-010's missing
formal area was "the one genuine open work item anywhere in RLB" is kept for
history and is no longer true.

**Owner decision RESOLVED 2026-09-14: nothing was stranded.** This entry once
claimed several unpushed RLB-001/002 doc-fix commits sat on branch
`dmas-reorg-and-stream-perf`, and a later reader correctly noted the branch was
gone -- but read that as work possibly lost. It was not: the branch was MERGED
through six pull requests (#38 and #40 on 2026-07-18, then #62-#65 on
2026-07-22/23) and deleted afterwards, which is why no ref remains.

Verified rather than assumed: the RLB-001/002 doc-fix commits `243affb32`,
`a1b76d082` and `dc88e1a65` are all ancestors of both `HEAD` and `origin/main`,
and EVERY commit touching `vault/Tasks/RLB/` or the RLB docs is on main. There
is no unpushed RLB work anywhere.

(A stale copy of the old wording survives in the `pumice-ataglance-modes`
worktree's RLB pages. That checkout is ~677 commits behind main and carries no
RLB commits of its own, so it is a snapshot, not unmerged work; it corrects
itself when that branch takes main.)

---
