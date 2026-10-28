# TASK-001: implement jet per the 2026-10-28 design spec

**Priority:** P2
**Status:** open
**Owner:** TBD

Filed 2026-10-28, the day J1–J7 closed (Sean) and the design spec
`docs/superpowers/specs/2026-10-28-jet-mshr-design.md` was written. The PRD
(v0.2) and HAS (v0.3) record the rulings; the spec carries the module
decomposition and phasing.

## Scope

Phases per the spec:

1. `jet_pkg` + `jet_mshr` (full-assoc CAM, `MSHR_COUNT` 2–16 default 8) +
   unit TB.
2. `jet_wb_buffer` (`VICTIM_DEPTH` 1–4 default 2) + unit TB; drain-engine
   integration.
3. `jet_rsp_seq` + hit-under-miss in the lookup stage.
4. `jet_control` composition; amber oracle lockstep at FUNC.
5. Snoop-during-miss (per-entry bypass + WB-buffer service); formal
   liveness harness at the tiny 16-set/2-way geometry.
6. FULL soak grids (geometry × MSHR_COUNT × VICTIM_DEPTH); pair-rig DV.
7. Genesys2 pair-rig bring-up + the J7 measurement sweep.

## Depends on

- The shared core at `cache-ip/common-ip` (reused unchanged).
- Phase 7 waits on the amber rig upgrade (formal TASK-001) for the board
  measurement quality bar.

## Done when

The PRD success criteria hold: every amber proof and golden-model parity
result re-run green with MSHRs present; the J5/J6 deadlock corner proven;
the J7 delta measured with MonBus evidence.
