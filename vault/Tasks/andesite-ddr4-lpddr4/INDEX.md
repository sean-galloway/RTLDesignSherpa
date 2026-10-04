---
title: andesite-ddr4-lpddr4 tasks
summary: Task rollup for the ddr4-lpddr4 memory controller (projects/components/mem-ctrl-ip/andesite-ddr4-lpddr4).
---

# andesite-ddr4-lpddr4 — task rollup

**Next ID: TASK-011** — never recycle a number, even when its task closed.

**Every item is its own file**, `<ID>.md`, filed under the directory for its
state (`open/`, `active/`, `closed/`, `dropped/`). Moving an item between states
is `git mv`, so an item is in exactly one state by construction.

## Lanes

| Lane | For | Next ID |
|---|---|---|
| [task/](task/INDEX.md) | planned work we decided to do | `TASK-011` |

## Open shortlist

- **TASK-006..010** (open) — the post-tranche work list: parity recovery FSM,
  PB-REF evaluation, LPDDR4 reconciliation (two items), verification
  reference models, and BFM DFI 4.0 gap closure (G1-G5, DV-repo work).
- Details: [task/INDEX.md](task/INDEX.md).

## Closed

- **TASK-005** (closed 2026-10-04) — DFI 4.0 spec study; citations
  confirmed against the on-disk spec, BFM gaps filed as TASK-010.
- **TASK-001** (closed 2026-10-04) — the advanced scheduling / refresh modes
  survey; Bhati 2016-cited dispositions in the file.
- **TASK-004** (closed 2026-10-04) — the andesite kmap book; six generated
  tables, citation-gated, cited from MAS/HAS; docs tranche complete.
- **TASK-003** (closed 2026-10-04) — the andesite MAS v0.1; owner-reviewed.
- **TASK-002** (closed 2026-10-04) — the andesite HAS v0.1 and the family
  docs seed; owner-reviewed.