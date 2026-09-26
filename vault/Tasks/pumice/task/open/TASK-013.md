# TASK-013: the adapt predictors (modes 4/5) are inert on everything measured — but untested on traffic built for them

**Status:** open 2026-09-26  **Priority:** P3 — research question; nothing
depends on it and the modes cost nothing to leave in

Sean, 2026-09-26: *"Leave adapt in; maybe they need more research."*

Raised when [[TASK-011]] retired RBL (modes 6/7) and the obvious next question
was whether `adapt_time` (mode 4) and `adapt_access` (mode 5) should follow.
They should NOT, yet, and the distinction is the point of this task.

## What is measured

Board, txn_scale=1000, peak 600 MB/s. Compared WITHIN each profile (comparing
a sequential number against a concurrent one is how a phantom 50% loss nearly
got reported here):

| profile | scenario | open_page | adapt_time | adapt_access |
|---|---|---|---|---|
| paging (sequential) | incremental_bl8 | 561.4 | 561.4 | 561.3 |
| paging (sequential) | col_major_bl8 | 195.2 | 195.2 | 195.2 |
| pairs_paging_mix (1w+1r) | incremental_bl8 | 276.1 | 276.2 | 276.0 |
| pairs_paging_mix | row_major_bl8 | 285.6 | 285.6 | 285.6 |
| pairs_paging_mix | col_major_bl8 | 88.2 | 88.2 | 88.2 |
| pairs_paging_mix | col_major_interleaved_bl8 | 110.6 | 110.6 | 110.6 |

**Identical to plain open page on all six, within +-0.2 MB/s** -- four
families, sequential and concurrent, no difference anywhere.

## Why that is NOT the same finding RBL got

RBL was retired on a **demonstrated cost**: mode 6 lost 26% of bandwidth on a
workload built specifically to suit it, and mode 7's hill-climb drove itself to
a no-op. The mechanism was exercised, proven to work (thrash% 100% -> 57.8%),
and still lost.

The adapt modes have only a demonstrated **absence of benefit**, and their
mechanisms may never have been exercised at all:

* `adapt_time` closes a row on an idle TIMEOUT. Every workload measured
  saturates the generators, so a bank may never sit idle long enough for the
  timer to expire. A mode whose trigger never fires cannot show a difference.
* `adapt_access` votes a row closed from 2-bit saturating counters that must
  LEARN. Short windows and one address pattern per run give the counters little
  to converge on.

So "inert on everything measured" is what the data supports. "Inert by nature"
is not, and removing them on this evidence would repeat the error [[TASK-010]]
diagnosed for RBL -- concluding from a workload that could not discriminate.

## What would settle it

The [[TASK-011]] method, applied to these modes:

1. **adapt_time** needs traffic with genuine idle gaps per bank -- bursts
   separated by more than the timeout, so the timer actually fires. The `gap`
   dial on the generators does this; `page_tr_init` sets the timeout.
2. **adapt_access** needs rows with STABLE, DIFFERING reuse -- some touched
   once, some many times, repeatedly, so the counters can converge to different
   verdicts per row. `hotcold_scenarios()` ([[TASK-010]]) already builds
   per-generator locality variation and is the obvious starting point.
3. Read it on **thrash% and ACT/txn**, not bandwidth -- that is what exposed
   RBL's mechanism working while it lost.

If either mode shows a win on traffic built for it, that is a real result. If
neither does, they are retired on the same evidence RBL was, and
`pumice_row_pred_table` goes with them.

**Do not remove them before running that.** They cost area, not correctness,
and the measurement is cheap compared to deleting a mechanism that was never
given its workload.

Related: [[TASK-011]] (RBL, the worked example), [[TASK-010]] (the
per-generator scenario machinery), [[TASK-005]] (predictor area).
