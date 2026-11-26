# TASK-004: hive HIVE-C `CORE_FLAVOR=peregrine` swap (PRD §7 deliverable 6)

**Priority:** P3
**Status:** open (filed 2026-11-25)
**Owner:** TBD

## What

peregrine's system bring-up, as hive PRD §10.3 plans it: HIVE-C's core
behind the `hive_c_loader` contract becomes selectable by `CORE_FLAVOR`
(`vexriscv` default, `peregrine`). Only the wrapper's core-facing glue
changes (VexRiscv ibus/dbus cmd/rsp vs peregrine's AXI4 master); the
loader, firmware and LDR testplan carry over, and the LDR plan becomes
peregrine's acceptance test. Filed here because hive's tracker area
has no lane INDEX yet; the work is in compute-eng-ip/hive (renamed from
hive-serv 2026-11-25, when one gatling replaced its 16 SERV monitors; the
HIVE-C core strategy this task follows is unchanged by that).

**Clock (2026-11-25, resolved 2026-11-26):** HIVE targets 75 MHz in every
domain. peregrine closed at 54.1 MHz then; TASK-006 brought it to 75 MHz
(13.333 ns, PRD P14, owner floor), so HIVE-C runs peregrine on the 75 MHz
domain and no slower clock is needed.

## Done when

- The LDR testplan passes with `CORE_FLAVOR=peregrine` and still passes
  with `vexriscv`.
- The system-level deltas hive PRD §10.3 names are measured
  (interrupt-driven alert-to-action latency, scheduler worst case).
