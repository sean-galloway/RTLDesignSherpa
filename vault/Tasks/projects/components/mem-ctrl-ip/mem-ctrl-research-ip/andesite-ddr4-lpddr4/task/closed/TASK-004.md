# TASK-004: Author the andesite command kmap book
> Docs tranche: `docs/superpowers/plans/2026-10-03-andesite-docs-tranche.md`
> Spec: `docs/superpowers/specs/2026-10-03-andesite-bootstrap-design.md`

**Priority:** P2
**Status:** closed 2026-10-04 — the kmap book is complete and owner-reviewed:
six generated tables, citation gate green, rerun-idempotent (sha256-verified
across a 2-second boundary), cited from the MAS ch04 anchor map and the HAS
ch03 pointer paragraph
**Owner:** TBD

Write the generated kmap book
(`projects/components/mem-ctrl-ip/mem-ctrl-research-ip/andesite-ddr4-lpddr4/docs/kmaps/`):
`gen_andesite_kmaps.py` on `bin/kmaps` producing `andesite_cmd_kmaps.xlsx`
plus `generated/*.md` — DDR4 command truth table (ACT_n x RAS_n x CAS_n x
WE_n, BG-aware), LPDDR4 CA-bus command table, address/bank-group decode maps,
MR0-MR6 per-field programming maps for both memtypes, ODT truth table
(RTT_NOM/WR/PARK x DRAM state), FGR refresh-mode select map. Citation-gated
(`verify_citations` against MAS ch02 anchors) and rerun-idempotent. Closes
when every table lands, the citation gate is green, and MAS ch04 / HAS ch03
cite the generated renderings.
