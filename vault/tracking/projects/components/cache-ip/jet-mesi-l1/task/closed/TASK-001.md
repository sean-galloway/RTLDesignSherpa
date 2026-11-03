# TASK-001: implement jet per the 2026-10-28 design spec

**Priority:** P2
**Status:** closed 2026-11-03 — all seven phases done; J7 measured on silicon (see phase-7 note). Open follow-ups live as ISSUE-001/002.
**Owner:** TBD

Filed 2026-10-28, the day J1–J7 closed (Sean) and the design spec
`docs/superpowers/specs/2026-10-28-jet-mshr-design.md` was written. The PRD
(v0.2) and HAS (v0.3) record the rulings; the spec carries the module
decomposition and phasing. Implementation plan:
`docs/superpowers/plans/2026-10-28-jet-mshr-implementation.md` (2026-10-28).

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
- ~~Phase 7 waits on the amber rig upgrade (formal TASK-001) for the board
  measurement quality bar.~~ **CLEARED 2026-11-02**: formal/amber TASK-001
  closed (all four items landed — tally clear/freeze CSR wiring, injector
  latency min/max/sum + log2 histogram + run cycles, 16-deep re-armable
  latch bank, latch readback RDL). The amber rig now meets the measurement
  bar; the J7 sweep can measure latency distributions, not just rates.

## Phase 7 progress (2026-11-02)

- **Step 1 (rig) DONE**: `projects/fpga-systems/Genesys2/cache-ip/jet/` —
  two `jet_top` + `jet_pair_fabric` + the post-upgrade injector/tally
  collateral, mirrored from the amber rig. DV green (AXIL + UART, func+gate;
  all five harness tests including latency/latch/clear-freeze), lint clean,
  `MSHR_COUNT` generic wired into the Vivado flow for the {2,4,8,16} grid.
- **Timing**: the cpu_req→snoop-accept combinational cone (31 levels) fails
  90 MHz (WNS −4.065) — jet ISSUE-001, expected T13-class finding, the v2
  pipelining fix is deliberately out of scope here. The rig runs at
  **60 MHz, WNS +0.220 ns, 0 failing endpoints**; J7 metrics are
  cycle-based so the amber↔jet comparison is unaffected.
- **Steps 2–4 DONE 2026-11-03** (board on the bench): amber rebuilt with the
  TASK-001 collateral (90 MHz, WNS +0.179, 0 failing) and swept clean; jet
  swept at MSHR_COUNT ∈ {2, 4, 8, 16} (bitstreams all timing-clean; the
  MSHR=16 build is tightest at WNS +0.054). J7 report filled with first
  silicon data: −16.6% run cycles on 64 KB thrash, −31.5% on the write
  storm, hit latency 3 vs 4 cycles, miss tail capped at 41 vs 60 cycles,
  fill bandwidth +18–37.5%. Grid is flat (injector is 1-outstanding, so
  MSHR=2 saturates the rig — documented in the report). Two findings filed
  as issues, both out of v1 scope: ISSUE-001 (90 MHz cone, jet v2) and
  ISSUE-002 (jet_monlite 2-event/cycle drop limit, measured and counted).

## Done when

The PRD success criteria hold: every amber proof and golden-model parity
result re-run green with MSHRs present; the J5/J6 deadlock corner proven;
the J7 delta measured with MonBus evidence.
