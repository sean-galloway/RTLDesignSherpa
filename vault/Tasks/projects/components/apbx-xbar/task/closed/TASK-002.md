# TASK-002: Formal coverage for the APB4/APB5 version gating

> Migrated 2026-09-27 from `vault/Tasks/projects/components/apbx-xbar/closed.md` as **APBX-002** (tooling TOOL-001). The flat page did not record a lane; this item was placed by hand. Body preserved as written -- only the H1 and this line are new.
**Status:** closed 2026-08-14 — `formal/apbx_xbar/apbx_xbar_thin_mixed/`,
prove and cover both PASS

A mixed build (m0=APB4, m1=APB5, s0=APB5, s1=APB4) with the sideband
buses as free inputs, proving the gate on both ends exhaustively rather
than by sampling:

- **A** — an APB4 slave is never driven with sideband.
- **B** — an APB4 master never receives completer sideband.
- **C** — an APB5 slave sees `'0` while no APB5 master has selected, so
  an APB4 master cannot contribute either.
- **cover** — the legal pairing (m1 → s0) really does carry nonzero
  sideband, reached in 4 steps. Without it, A–C could pass on a fabric
  that moved nothing.

**Property C is worth reading before writing a similar one.** The first
version stated it against `PSEL` and the solver refuted it in four
steps: grants persist from command acceptance through response
completion, so an APB5 master can still hold the grant — and still
legitimately drive sideband — in a cycle where it has dropped `PSEL`.
The refutation was correct; the property was wrong. Restating it
against `dut.arb_gnt_id` then hit two front-end limits (no dynamic
index into a parameter, no hierarchical reference resolution), so it
ended up as a sticky flag at the boundary, which needs no internal
names and is a stronger statement for it.

Like the sibling apbx_xbar proofs, this is not wired into
`formal/Makefile`'s targets; run it with `sby -f` in its directory.
