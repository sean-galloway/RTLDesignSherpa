# ISSUE-012: read alignment wastes 5 cycles of latency

> **Migrated from `PUMICE-040`** on 2026-09-27, when this area's flat
> `closed.md` was split into one file per item to match the rest of the vault.
> The legacy ID is cited throughout the repo -- RTL comments, DV code, handbook
> notes, commit messages and session memory -- so it is NOT rewritten at those
> call sites; `vault/Tasks/MIGRATION_MAP.md` and this line are how an old
> `PUMICE-040` reference resolves. Body below is verbatim from the flat page.
>
> Lane chosen by reading this item's own Status line and opening, not its title:
> a keyword pass over the 35 items misclassified 14 of them.


**Status:** CLOSED 2026-09-16 (6ba9dba62)  **Priority:** P2

A joint (t_rddata_en x rddata_delay) board sweep found EVERY clean pair on the
diagonal `rddata_delay = t_rddata_en + 1` -- the a7ddrphy's data-vs-valid offset
is a fixed 1 cycle, so any t_rddata_en works provided the delay tracks it.

The board runs rden=6/delay=7. rden=1/delay=2 is equally clean and **5 cycles
faster**, putting DFI read latency at ~7-8 -- matching LiteDRAM's
`read_latency = cl_sys_latency + 6 = 8` on the same board.

A single-axis sweep converges on working-but-slow and nothing flags it: the
a7ddrphy's DQ capture free-runs and rddata_en only gates WHEN VALID IS EMITTED,
so a late rddata_en does not corrupt reads, and rddata_delay silently absorbs
the cost. `TEST_T_RDDATA_EN` makes the faster point reachable.

LATENCY ONLY. It does NOT reduce tRTW -- proven on the board: at rden=1/delay=2
with tRTW=8, gaps 13/15 failed exactly as before the fix, while tRTW=18 was
clean at both alignments.

**Moved to this page 2026-09-16.** It was fixed and marked CLOSED in its own
status line, with the commit named, but stayed on the OPEN page -- so every
count and every "what is left" listing carried it as outstanding work.

---
