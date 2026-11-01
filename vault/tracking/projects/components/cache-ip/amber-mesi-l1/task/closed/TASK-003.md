# TASK-003: Genesys2 Vivado build of the post-restructure amber hierarchy

**Priority:** P3
**Status:** closed 2026-11-01
**Owner:** TBD

## Why

The cache-ip plane restructure (TASK-002) recomposed `amber_top` /
`amber_ace_top` onto `l1_cpu_plane` + `l1_coh_core` + `l1_axi4_plane` /
`l1_ace_plane`.  The external port lists were preserved, the targeted DV
suites pass, and the filelists are updated, but the Genesys2 board build
has not yet been run through Vivado.  This task tracks the board-level
elaboration/synthesis closure.

## What

Run the Genesys2 `amber_top` integration through Vivado at the next
available build opportunity.  Confirm that the post-restructure hierarchy
(`u_cpu` / `u_coh` / `u_fab`) elaborates and that the board harness still
meets timing / placement expectations.  The port list is unchanged, so the
risk is low, but the build is the final closure for the physical hierarchy.

## Done when

- Genesys2 amber build completes Vivado elaboration/synthesis without
  hierarchy-related errors.
- Any port-width or hierarchy-tap regressions specific to the board harness
  are fixed or filed as a follow-up bug.

## Notes

- Carried over from the open item in the deleted
  `docs/task-reports/2026-11-01-task-3-plane-restructure-amber-tops.md`
  (that report directory is not a sanctioned repo convention; the SDD
  workspace remains the home for session reports).

## Closure (2026-11-01)

Post-restructure Genesys2 build green: `make -C build-bringup bitstream`
(Vivado 2025.1) produced `fpga/bitstream/amber_bringup.bit` in ~24 min.
Timing closed: WNS +0.083 ns / WHS +0.054 ns, 0 failing endpoints of
404,557 (90 MHz target). Utilization: 47.5% LUT, 10.8% FF, 28.8% BRAM,
6 DSP — sane vs. pre-restructure. The 20 undriven-net warnings are
pre-existing harness padding (unused host_axi / s3-s5 slave ports in
amber_pair_harness.sv; prior builds carried 22). No hierarchy-related
errors — the plane hierarchy (u_cpu/u_coh/u_fab) synthesizes clean.
On-board run (program + host sweep) remains available on demand.
