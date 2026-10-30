# TASK-002: restructure amber RTL into planes (mem-ctrl doctrine) with a swappable ACE fabric plane

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

## What this means for amber

Today's split is ad hoc: `amber_top` (plain AXI4) vs `amber_ace_top` (+`amber_ace_issue`) differ in the fabric-facing logic, but the ACE-specific concerns are spread across the tops, the issue block, and the snoop responder wrap. The plane restructure isolates:

- **CPU plane** — GAXI front-end (`l1_cpu_frontend`, rsp staging). Protocol-stable.
- **Coherence core plane** — control FSM, tag/data arrays, replacement, fill/drain engines, MonBus observation. Protocol-agnostic MESI.
- **Fabric plane** — everything ACE-shaped: the AC/CD/CR snoop responder (`l1_snoop_resp` wrap), the ACE issue block (`amber_ace_issue`), the ARSNOOP/AxDOMAIN stamping. Swappable: a CHI plane would present the same core-facing contract (snoop request in, response+data out; read/upgrade/writeback transactions out, fills/writebacks in) with CHI channels underneath.

## Done when

- amber RTL compiles as `<core planes>` + `l1_ace_plane` (name TBD at design time), with the pair-rig and onyx-rig tops becoming thin plane selections.
- The core-facing fabric contract is written down (the seam a CHI plane would implement).
- Full amber DV + formal re-run green with zero functional change; filelist registry clean.
- The seam's swap-ability is demonstrated at least by elaboration of a stub second plane (or documented why not).

## Notes

- Coordinate with jet TASK-002 (same restructure on jet) — the plane shapes should be designed once and applied to both, ideally into `cache-ip/common-ip`.
- Do not start while jet TASK-001 (implementation) is mid-flight on the same files.
