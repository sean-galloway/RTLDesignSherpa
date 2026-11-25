# TASK-004: hive-serv HIVE-C `CORE_FLAVOR=peregrine` swap (PRD §7 deliverable 6)

**Priority:** P3
**Status:** open (filed 2026-11-25)
**Owner:** TBD

## What

peregrine's system bring-up, as hive-serv PRD §10.3 plans it: HIVE-C's core
behind the `hive_c_loader` contract becomes selectable by `CORE_FLAVOR`
(`vexriscv` default, `peregrine`). Only the wrapper's core-facing glue
changes (VexRiscv ibus/dbus cmd/rsp vs peregrine's AXI4 master); the
loader, firmware and LDR testplan carry over, and the LDR plan becomes
peregrine's acceptance test. Filed here because hive-serv's tracker area
has no lane INDEX yet; the work is in compute-eng-ip/hive-serv.

## Done when

- The LDR testplan passes with `CORE_FLAVOR=peregrine` and still passes
  with `vexriscv`.
- The system-level deltas hive-serv §10.3 names are measured
  (interrupt-driven alert-to-action latency, scheduler worst case).
