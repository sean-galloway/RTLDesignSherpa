# TASK-001: HIVE-C on peregrine -- `CORE_FLAVOR=peregrine`, and VexRiscv retired

**Priority:** P3
**Status:** open (2026-11-27, moved from riscv-ip/peregrine-rv32im TASK-004; owner: "TASK-004 move this to a hive task")
**Owner:** TBD

## What

HIVE-C should run one of the repo's own RISC-V cores. `hive_c_loader`
(48a057cdf) is built for VexRiscv only: it sits behind a core seam, so
only the glue module changes per core (MAS ch02, hive_c_controller).

- Write `hive_c_core_peregrine.sv`, the glue for `peregrine_top`
  (`AXI_DW=32`). It needs an AXI4 slave on the banks (I$ fills to the
  fetch port, D$ write-backs to the data port), and a D$ clean before the
  core is reset when `run` falls.
- Settle the address-map conflict. peregrine's uncached window is
  0x1000_0000-0x1FFF_FFFF, so HIVE's 0x4000_0000 peripheral windows would
  be cached. riscv-ip/peregrine-rv32im TASK-005 makes the window a
  parameter; set it for HIVE-C here.
- LDR-01..05 pass with peregrine. LDR-04's contention witness will need
  fill-heavy traffic to bite, because peregrine's port-B traffic comes in
  bursts.
- Retire VexRiscv once peregrine passes, or keep it only as a recorded
  comparison point, as decided when this task starts. Update hive PRD
  §10.3, which still calls VexRiscv "the default today".

## Later (needs HIVE's firmware, fabric and engine monitors)

- The system-level deltas hive PRD §10.3 names: interrupt-driven
  alert-to-action latency, and the scheduler's worst case.

## Depends on

- riscv-ip/peregrine-rv32im TASK-005 (bus errors, uncached-window parameter).
