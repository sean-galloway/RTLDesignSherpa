# TASK-002: restructure jet RTL into planes (mem-ctrl doctrine) with a swappable ACE fabric plane

**Priority:** P3
**Status:** open
**Owner:** TBD

Filed 2026-10-29 (Sean): structure the cache RTL in **planes** the way
`mem-ctrl-ip/common-ip` does — one parameterized source per plane,
protocol generation as a family boundary rather than a parameter — so a
future **CHI plane can be swapped in for the ACE plane** without touching
the coherence core.

## The doctrine to follow

`mem-ctrl-ip/common-ip/docs/common_has/ch03_dfi_generations/01_dfi_planes.md`:
each protocol generation is its own named block (`mc_dfi_2p1_plane` /
`3p1` / `4p0`); a product picks exactly one; what is revision-independent
is extracted once as shared FUBs underneath. Parameter-sustainability
doctrine: widths/depths are parameters; the protocol generation is not.

## What this means for jet

Same restructure as amber TASK-002, applied to jet's larger surface:
`jet_top` (plain AXI4) / `jet_ace_top` (+`jet_ace_issue`) already separate
the fabric-facing logic more cleanly than amber's, but the ACE concerns
(ARSNOOP stamping, AC/CD/CR snoop handling, RACK/WACK) should collapse
into one named fabric plane:

- **CPU plane** — GAXI front-end + `jet_rsp_seq`.
- **Coherence core plane** — `jet_control`, `jet_mshr`, `jet_wb_buffer`,
  arrays, replacement, fill/drain, MonBus. Protocol-agnostic MESI.
- **Fabric plane** — everything ACE-shaped. Swappable: a CHI plane
  presents the same core-facing contract (snoop request in,
  response+data out; coherent transactions out, fills/writebacks in).

## Done when

- jet RTL compiles as `<core planes>` + fabric plane, with `jet_top` /
  `jet_ace_top` reduced to thin plane selections.
- The core-facing fabric contract is written down (the seam a CHI plane
  would implement) — same document as amber's, designed once.
- Full jet DV (unit/core/pair-rig/monlite) + the formal harness re-run
  green with zero functional change; filelist registry clean.
- The seam's swap-ability is demonstrated at least by elaboration of a
  stub second plane (or documented why not).

## Notes

- Coordinate with amber TASK-002 — design the plane shapes once, apply to
  both, land what is shared in `cache-ip/common-ip`.
- Do not start while TASK-001 (implementation) is mid-flight on the same
  files.
