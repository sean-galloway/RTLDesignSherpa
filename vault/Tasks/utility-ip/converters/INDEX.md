---
title: utility-ip/converters tasks
summary: Task rollup for the AXI3 protocol converters (axi4_to_axi3 / axi3_to_axi4).
---

# utility-ip/converters — task rollup

**Every item is its own file**, `<ID>.md`, filed under the directory for its
state (`open/`, `active/`, `closed/`, `dropped/`). Moving an item between states
is `git mv`, so an item is in exactly one state by construction.

## Lanes

| Lane | For | Next ID |
|---|---|---|
| [task/](task/INDEX.md) | planned work we decided to do | `TASK-002` |
| [bug/](bug/INDEX.md) | a defect with a reproduction | `BUG-001` |
| [issue/](issue/INDEX.md) | an anomaly, risk or open question | `ISSUE-001` |

Open counts include the reserved `-000` template, which is never a real item.

## What lives here

AXI3 protocol converters (`axi4_to_axi3` / `axi3_to_axi4`) and their DV.

Cite an item from outside its own file as "utility-ip/converters TASK-001".
