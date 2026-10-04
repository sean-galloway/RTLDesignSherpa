# TASK-003: Author the andesite MAS v0.1
> Docs tranche: `docs/superpowers/plans/2026-10-03-andesite-docs-tranche.md`
> Spec: `docs/superpowers/specs/2026-10-03-andesite-bootstrap-design.md`

**Priority:** P2
**Status:** closed 2026-10-04 — the MAS v0.1 is complete and owner-reviewed
(book assembly at fc61c80f)
**Owner:** TBD

Write the andesite Microarchitecture Specification v0.1
(`projects/components/mem-ctrl-ip/andesite-ddr4-lpddr4/docs/andesite_mas/`):
ch01 block inventory, ch02 per-block chapters for the changed/new blocks only
(cmd_formatter, init_sequencer, mode_register, addr_mapper, scheduler,
refresh_ctrl, zq_ctrl, odt_ctrl, training, dfi_datapath), ch03 DFI 4.0
pin-level, ch04 core signal contracts in bch style. Inherited-unchanged blocks
are referenced to scoria's books with where-and-why, not rewritten. Closes when
the MAS is owner-reviewed complete at v0.1.
