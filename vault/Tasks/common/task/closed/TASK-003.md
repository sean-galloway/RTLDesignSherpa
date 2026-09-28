# TASK-003: Integration examples (became the technique index)

> Migrated 2026-09-27 from `vault/Tasks/common/closed.md` as **COMMON-003** (tooling TOOL-001). The flat page did not record a lane; this item was placed by hand. Body preserved as written -- only the H1 and this line are new.
**Status:** CLOSED 2026-08-09 (opened as "create integration examples",
migrated from rtl/common/TASKS.md; rescoped twice the day it closed)
**Priority:** P2

The task's shape changed twice under examination, each time by owner call:

1. Original (pre-migration): five standalone designs combining common
   modules — watchdog FSM, arbiter system, CRC+FIFO buffer, CDC transfer,
   PWM — each with test and docs, in rtl/integ_amba/examples/.
2. Rescope 1 (Sean): not "testing things together" — each example should
   demonstrate a design TECHNIQUE. PWM killed outright (rtl/common/pwm.sv
   already demonstrates it). Four technique showcases proposed, mapped to
   handbook notes, sited in rtl/integ_common.
3. Rescope 2 (Sean): "I've already basically done all four of those in the
   projects area" — and it is true: the stream engines ARE the
   streaming-no-fsm demo, the schedulers ARE the minimal-FSM demo, pumice
   and monbus ARE the arbitration demos, rtl/cdc + apb4_slave_cdc ARE the
   CDC demos. Toy copies of techniques that living, tested code already
   demonstrates are second implementations nobody maintains — the exact
   failure mode integ_amba's two untested examples (51 Verilator errors,
   AMBA-EXAMPLES) exhibit.

**Delivered instead: `docs/markdown/rtl-integ-common/technique-index.md`** —
a reader-facing map from each technique (streaming no-FSM, minimal FSM,
valid/ready discipline, CDC, arbitration/fairness, timeout/recovery,
in-line data integrity, field packing) to its best worked examples in real
code, each with "what to look at when you get there" and its handbook note
named. Every cited path verified to exist at authoring. Linked from the
book's index.md and overview.md, so the review bundle picks it up.

No new RTL, no new tests — deliberately. The area's two existing modules
(fifo_sync_multi{,_sigmap}) remain the standalone composition examples and
are fully tested.

---
