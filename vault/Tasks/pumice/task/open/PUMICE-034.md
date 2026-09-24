# PUMICE-034: the paging predictors are built unconditionally and the board never uses them

**Status:** open 2026-09-14  **Priority:** P2 — pure headroom, no correctness impact

`u_page_policy` (the mode 5 row predictor plus the mode 6/7 RBL table) is
**4,546 LUT / 3,341 FF**, a third of pumice's LUTs, instantiated with no build
gate. The board's default runs use `open_page` and never select modes 5/6/7, so
that area is carried and never exercised on a part where it is the difference
between comfortable and tight.

It is also where timing dies first when anything else grows: across the
2026-09-13 builds `u_row_pred` owned 340-920 of the failing endpoints every
time, more than any other block.

**The tension, which is why this is not simply a fix.** The modes were restored
specifically so that ONE bitstream characterizes every policy
([[project_pumice_advanced_sched_modes]]). Gating them trades that away for
area. Both positions are defensible and it is Sean's call, not a session's.

**Options, in increasing order of how much they give up:**
1. A `PAGE_PRED_MODES` parameter defaulting ON, with the board build turning it
   off. One bitstream per policy family instead of one for all.
2. Gate only the RBL table (248 LUT / 1,488 FF) and keep the row predictor.
3. Leave it and accept the area; revisit if a build stops closing.

**Context for the decision:** the four-generator build closes at **+0.016 ns**
with **87.1% slice occupancy**. There is not much room left for anything else to
grow, and this is the largest single block that is optional.

---
