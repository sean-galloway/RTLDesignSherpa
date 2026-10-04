---
title: andesite-ddr4-lpddr4 tasks
summary: Task rollup for the ddr4-lpddr4 memory controller (projects/components/mem-ctrl-ip/andesite-ddr4-lpddr4).
---

# andesite-ddr4-lpddr4 — task rollup

**Next ID: TASK-006** — never recycle a number, even when its task closed.

**Every item is its own file**, `<ID>.md`, filed under the directory for its
state (`open/`, `active/`, `closed/`, `dropped/`). Moving an item between states
is `git mv`, so an item is in exactly one state by construction.

## Lanes

| Lane | For | Next ID |
|---|---|---|
| [task/](task/INDEX.md) | planned work we decided to do | `TASK-006` |

## Open shortlist

- **TASK-001** (open) — the advanced scheduling / refresh modes survey that
  predates the docs tranche (roadmap:
  `vault/Tasks/memory-controllers/ADVANCED_MODES_ROADMAP.md`).
- **TASK-003** (open) — author the andesite MAS v0.1; closes when
  owner-reviewed complete.
- **TASK-004** (open) — author the andesite kmap book; closes when the tables
  land, the citation gate is green, and MAS/HAS cite them.
- **TASK-005** (open) — DFI 4.0 spec acquisition + BFM study; un-blocks every
  `§TBC(TASK-005)` clause citation in the HAS/MAS.

## Closed

- **TASK-002** (closed 2026-10-04) — the andesite HAS v0.1 and the family
  docs seed; owner-reviewed, book complete at v0.1.

`bug/` and `issue/` lanes are created when this controller first needs one --
there is no RTL here yet, so an empty lane would carry nothing. Open counts
include the reserved `-000` template, which is never a real item.

IDs are scoped to THIS area AND its lane. Cite one from outside as
"andesite-ddr4-lpddr4 TASK-001".

## Grouping

`vault/Tasks/memory-controllers/` is a GROUPING directory and holds no items of
its own, the same shape as `vault/Tasks/projects/components/`. The three
controllers are leaf areas: this one, `ddr4-lpddr4`, and **pumice-ddr2-lpddr2,
which stays at `vault/Tasks/pumice-ddr2-lpddr2/`** -- it is the only one with live work and
was migrated long before this grouping existed (Sean, 2026-09-25: "group the
memory controllers").
