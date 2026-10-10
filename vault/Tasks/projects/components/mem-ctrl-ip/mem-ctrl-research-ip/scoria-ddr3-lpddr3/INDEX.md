---
title: scoria-ddr3-lpddr3 tasks
summary: Task rollup for the ddr3-lpddr3 memory controller (projects/components/mem-ctrl-ip/mem-ctrl-research-ip/scoria-ddr3-lpddr3).
---

# scoria-ddr3-lpddr3 — task rollup

**Every item is its own file**, `<ID>.md`, filed under the directory for its
state (`open/`, `active/`, `closed/`, `dropped/`). Moving an item between states
is `git mv`, so an item is in exactly one state by construction.

## Lanes

| Lane | For | Next ID |
|---|---|---|
| [task/](task/INDEX.md) | planned work we decided to do | `TASK-010` |
| [bug/](bug/INDEX.md) | a defect with a reproduction | `BUG-004` |

The `bug/` lane was created 2026-10-01, when the first COMPOSED test found the
first composition defect (BUG-001). Before that every scoria test was a FUB
test with mocked neighbours, and the lane would have carried nothing.

An `issue/` lane is created when this controller first needs one. Open counts
include the reserved `-000` template, which is never a real item.

IDs are scoped to THIS area AND its lane. Cite one from outside as
"scoria-ddr3-lpddr3 TASK-001".

## Grouping

`vault/Tasks/memory-controllers/` is a GROUPING directory and holds no items of
its own, the same shape as `vault/Tasks/projects/components/`. The three
controllers are leaf areas: this one, `ddr4-lpddr4`, and **pumice-ddr2-lpddr2,
which stays at `vault/Tasks/pumice-ddr2-lpddr2/`** -- it is the only one with live work and
was migrated long before this grouping existed (Sean, 2026-09-25: "group the
memory controllers").
