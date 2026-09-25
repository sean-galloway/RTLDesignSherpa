---
title: memory-controllers/ddr4-lpddr4 tasks
summary: Task rollup for the ddr4-lpddr4 memory controller (projects/components/memory-controllers/ddr4-lpddr4).
---

# memory-controllers/ddr4-lpddr4 — task rollup

**Every item is its own file**, `<ID>.md`, filed under the directory for its
state (`open/`, `active/`, `closed/`, `dropped/`). Moving an item between states
is `git mv`, so an item is in exactly one state by construction.

## Lanes

| Lane | For | Next ID |
|---|---|---|
| [task/](task/INDEX.md) | planned work we decided to do | `TASK-002` |

`bug/` and `issue/` lanes are created when this controller first needs one --
there is no RTL here yet, so an empty lane would carry nothing. Open counts
include the reserved `-000` template, which is never a real item.

IDs are scoped to THIS area AND its lane. Cite one from outside as
"memory-controllers/ddr4-lpddr4 TASK-001".

## Grouping

`vault/Tasks/memory-controllers/` is a GROUPING directory and holds no items of
its own, the same shape as `vault/Tasks/projects/components/`. The three
controllers are leaf areas: this one, `ddr4-lpddr4`, and **pumice-ddr2-lpddr2,
which stays at `vault/Tasks/pumice/`** -- it is the only one with live work and
was migrated long before this grouping existed (Sean, 2026-09-25: "group the
memory controllers").
