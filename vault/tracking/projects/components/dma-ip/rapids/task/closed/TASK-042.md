# TASK-042: reusable RAPIDS testbench classes

> Migrated 2026-11-07 from `projects/components/dma-ip/rapids/TASKS.md` as **TASK-003** ("Create Reusable Testbench Classes in CocoTBFramework").

**Priority:** P1
**Status:** CLOSED -- landed at a different path than the original named: TB classes live in the project area, `projects/components/dma-ip/rapids/dv/tbclasses/` (41 files), per GLOBAL_REQUIREMENTS 2.1. `bin/TBClasses/rapids/` correctly does not exist.
**Owner:** sean galloway

The original wanted the classes in the shared framework; the repo rule since is
that project TBs stay in the project. Scheduler, descriptor engine, scheduler
group(s), the source and sink data-path TBs and the top TBs are all there.

**Residual:** two test files still define a TB class inline -- filed as
[TASK-043](../open/TASK-043.md).
