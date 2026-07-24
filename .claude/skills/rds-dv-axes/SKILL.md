---
name: rds-dv-axes
description: RDS-DV testbenches compose THREE ORTHOGONAL choices - BFM (who drives), sequence (what traffic), randomization (what timing). Pick each deliberately; using the right BFM says nothing about whether the test stresses anything. Points at the authoritative per-family RDS-DV docs. Use when starting or reviewing ANY testbench.
---

# rds-dv-axes

READ FIRST: vault/handbook/INDEX.md (the handbook is the repo's memory; this skill is the
signpost). Canonical: vault/handbook/dv/rds-dv-axes.md.

Three INDEPENDENT axes. Changing one does not imply changing another:

| Axis | Question | Skill / note |
|---|---|---|
| **BFM** | who drives + monitors the wires | `rds-dv-bfms` / [[bfm-usage]] |
| **Sequence** | what transactions are sent | see below |
| **Randomization** | when - the delay/timing shape | `rds-dv-randomization` / [[randomization]] |

**"I used the framework BFM" is not sufficient.** A correct BFM sending an
under-stressed sequence at a gappy delay profile is a weak test that looks
rigorous. A round-robin arbiter that starved half its clients passed its own
testbench exactly this way.

**Sequences:** `APBSequence`, `AXI4Sequence` (+`AXI4Burst`, run via
`run_axi4_sequence`), `FIFOSequence`, `GAXISequence`. They carry ready-made
generators - walking ones/zeros, incrementing data, dependency chains, corner
cases, capacity/stress patterns, and AXI4 memory-aware ones (row-hit burst,
row-miss pair, bank spray). Read the family's `_sequence.md` before hand-rolling
a transaction loop.

**THE DOCS ARE GOOD - READ THEM, DO NOT REVERSE-ENGINEER FROM SOURCE.**
Per-family, one file per axis, at `<RDS-DV>/docs/components/<family>/`:
`components_<family>_{overview,interfaces,sequence,randomization,packet,compliance}.md`
Published: https://sean-galloway.github.io/RTLDesignSherpa-DV/
Coverage is uneven - `axi4` is the most complete family and the best model when
a page is missing elsewhere; `shared/` holds the cross-protocol machinery.

The handbook root is vault/handbook/INDEX.md - design/, dv/, fpga/, authoring/ areas,
atomic notes, wikilinked. When you learn a durable lesson in this domain,
ADD IT TO THE HANDBOOK NOTE, not to this skill.
