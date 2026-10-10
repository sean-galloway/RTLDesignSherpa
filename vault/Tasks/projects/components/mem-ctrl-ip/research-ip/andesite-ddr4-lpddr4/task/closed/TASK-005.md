# TASK-005: DFI 4.0 spec study and BFM gap analysis
> Docs tranche: `docs/superpowers/plans/2026-10-03-andesite-docs-tranche.md`
> Spec: `docs/superpowers/specs/2026-10-03-andesite-bootstrap-design.md`

**Priority:** P2
**Status:** closed 2026-10-04 — study executed and owner-reviewed; every
substantive DFI 4.0 clause citation in the HAS/MAS confirmed against the
on-disk spec, with five corrections recorded in-book and the BFM gap list
(G1-G5) filed as andesite TASK-010
**Owner:** TBD

**BFM reconciliation (amendment, 2026-10-04):** an in-house DFI BFM exists —
the DV repository's CocoTBFramework DFI component (`src/CocoTBFramework/
components/dfi/`), already carrying a CA-parity behavior and the LPDDR2/3
`lpddr_ca.py` encoder. What does not exist is a *DFI 4.0-complete* BFM: the
research notes name the LPDDR4 6-bit CA encoding (`lpddr4_ca.py`) as missing.
So this task's BFM half is **gap analysis and extension**, not green-field
acquisition.

Scope: (1) study the on-disk DFI 4.0 spec and confirm/correct every
`§TBC(TASK-005)` clause citation in the HAS ch04 and MAS ch03; (2) study the
in-house BFM's 4.0 coverage (present: CA parity; missing: LPDDR4 CA encoding
at minimum) and produce the gap list; (3) fold in the TASK-009 additions
(DRAMsim3 cross-check; CA round-trip tests). Closes when every suffix in both
books is a citation or a correction, the BFM gap list lands in HAS ch06, and
an integration note names the BFM path and version.
