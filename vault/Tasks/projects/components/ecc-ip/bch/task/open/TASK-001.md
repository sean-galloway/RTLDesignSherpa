# TASK-001: Stand up the BCH component

**Status:** open 2026-10-03
**Priority:** P3 — waits on a real consumer (the memory-controller project
named in RS PRD D10 / reed-solomon TASK-003), the same posture
reed-solomon TASK-001 had
**Owner:** TBD

Binary BCH was tracked alongside R/S under COMMON-009 and dropped with it;
RS PRD D7 (2026-09-29, Sean) made it its own component in `ecc-ip/`, sharing
the GF(2^m) primitives but nothing BCH-specific. History note: a docs-only
`projects/components/bch/` placeholder was deleted 2026-07-23 with "do not
recreate placeholder collateral" on record — this stand-up does not recreate
it. What lands today is working material: six stored reference documents
with sources and licences, and a PRD whose section 3 is a real decision
table. Each later phase lands real RTL/DV or it does not land.

## Scope (the umbrella, the way reed-solomon TASK-001 ran)

- **Stand-up (2026-10-03):** `projects/components/ecc-ip/bch/` with README,
  CLAUDE.md, draft PRD v0.1 (decision table D1-D12 with candidates drawn
  from the references), and `References/`: Massey 1969 + Massey 1965 (author
  archive, ETH Zürich), CCSDS 231.0-B-4 (the free standard whose channel
  coding is a BCH code), the Guruswami-Rudra-Sudan coding-theory draft
  (theory backbone), Cai/Mutlu 2017 + Nabipour & Javidan 2023 (the
  flash-consumer literature).
- **HAS:** mirror `docs/reed_solomon_has/` once the papers are read; the
  chapter skeleton tracks the RS HAS.
- **RTL + DV:** GF layer imported from reed-solomon (PRD D7), encoder first,
  then the decoder stages per the PRD D11 solver decision; golden model in
  `galois` with AFF3CT as cross-check; model-first order, the way
  reed-solomon TASK-002 ran.
- **Board harness:** only when a consumer or a Nexys A7 loop makes sense.

## Log

**2026-10-03 -- stand-up lands.** References gathered (six stored PDFs,
source + licence recorded for each), PRD v0.1 drafted, vault lane created.
Decisions open except D7 (share the reed-solomon GF layer), D9 direction
(valid/ready core plus wrapper adapters, per RS D9), and D10 (consumer
deferred to the memory-controller project). Next: read the references, then
the HAS.
