# TASK-007: Per-bank-group refresh accounting (PB-REF)
> Source: `/mnt/data/github/dfi-specs/ddr4/index.md` "Key Design Ideas" #6;
> ties to andesite TASK-001 (advanced-modes survey) and the Bhati 2016
> refresh-tradeoffs survey named there

**Priority:** P3
**Status:** closed 2026-10-04 — completed and owner-directed (pre-RTL creation pass)
**Owner:** TBD

The HAS/MAS refresh chapter (Ch 3.4 / `06_refresh_ctrl.md`) specifies FGR
1x/2x/4x on the inherited elastic/TCR/placement base but tracks one
device-wide tRFC. The research index notes JESD79-4 allows refresh staggered
across bank groups (per-bank refresh / PB-REF) with tRFC tracked per bank
group, saving bandwidth. Evaluate as a bounded MODIFIED-layer addition to
`refresh_ctrl` — the policy hook scoria's TASK-001 built is where it hangs.
Read Bhati 2016 (in the dfi-specs research set) before answering "helps vs
hurts" for the andesite design point. Closes when the evaluation lands as a
recorded decision in the HAS ch06 open-questions table (adopt / defer with
named condition).
