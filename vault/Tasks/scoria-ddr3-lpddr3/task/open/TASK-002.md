# TASK-002: author the scoria DDR3/LPDDR3 HAS

Lock the architecture spec, so the PRD stub ("to be authored once HAS is
locked") and the RTL both have a fixed target.

**Priority:** P1 — this is the gating item for all scoria work.
**Status:** open 2026-09-29 (Sean: "HAS first, then RTL")
**Depends on:** nothing. Supersedes nothing.

## Where it starts from

`projects/components/mem-ctrl-ip/scoria-ddr3-lpddr3/docs/design-requirements.md`
— the delta analysis, written against JESD79-3F, JESD209-3C, DFI v3.1 and
DFI v2.1.1. It establishes:

- the DFI v2.1.1 -> v3.1 delta, and that multi-phase signalling carries over
  (v3.1 generalises `_p0..p3` to `_pN`; the 1:4 ratio is still defined), so
  pumice's `DFI_RATE = 4` datapath is unaffected;
- that v3.1's growth is mostly DDR4/LPDDR4 (ACT_n, bank groups, chip ID, CA
  parity, DBI, CA training) and out of scope, while the leveling rework is the
  one change scoria cannot avoid;
- the DDR3 device deltas: MR0..MR3, `ZQCL`/`ZQCS`/`RESET`/`PREA`, self-refresh
  entry/exit, and the write-leveling timings (`tWLMRD` 40 nCK minimum with a
  controller-defined maximum, `tWLDQSEN` 25 nCK, `tWLO`, `tWLOE`);
- that LPDDR3 keeps LPDDR2's 10-bit DDR CA bus, so that side is a timing and
  mode-register change rather than a protocol break.

## Done when

- The HAS covers every block as inherited / modified / new against pumice, with
  a spec clause behind each timing claim.
- The three open decisions in the delta analysis are settled and recorded:
  D1 (DFI v3.1 vs v2.1.1), D2 (write leveling firmware-driven vs hardware FSM),
  D3 (`scoria_pkg` vs a shared family package).
- The PRD stub is replaced, since its stated blocker is gone.

## Not in scope

RTL. Board bring-up — verification is against a DFI BFM in simulation and the
board decision is deferred (Sean, 2026-09-29). The advanced-modes survey is
[[TASK-001]] and stays P3.
