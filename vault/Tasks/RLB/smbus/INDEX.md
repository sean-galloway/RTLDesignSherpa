---
title: RLB/smbus tasks
summary: Task rollup for the SMBus controller block (retro_legacy_blocks/rtl/smbus).
---

# RLB/smbus — task rollup

**Every item is its own file**, `<ID>.md`, filed under the directory for its
state (`open/`, `active/`, `closed/`, `dropped/`). Moving an item between states
is `git mv`, so an item is in exactly one state by construction.

Block: the SMBus controller. RTL under
`projects/components/retro_legacy_blocks/rtl/smbus/`; MAS spec under
`projects/components/retro_legacy_blocks/docs/smbus_mas/`.

## Lanes

| Lane | For | Next ID |
|---|---|---|
| [task/](task/INDEX.md) | planned work we decided to do | `TASK-001` |
| [bug/](bug/INDEX.md) | a defect with a reproduction | `BUG-001` |
| [issue/](issue/INDEX.md) | an anomaly, risk or open question | `ISSUE-001` |

Open counts include the reserved `-000` template, which is never a real item.
**This sub-area currently holds no real items** -- it was scaffolded so the
lane exists before the first item does.

## Why a sub-area (Sean, 2026-09-25)

**RLB is an area that also has sub-areas, one per block** -- pic_8259, hpet,
ioapic, pm_acpi, smbus, pit_8254, rtc, gpio, uart_16550. RLB's own lanes hold
cross-block work (the review arcs, the RDL relocation); a block's own defects
and features live under `RLB/<block>/`.

All nine blocks are SCAFFOLDED, on Sean's instruction (2026-09-25). The earlier
create-on-demand rule is superseded: an agent working a block should find its
lane already there rather than having to create one and get the convention right
from scratch. The `-000` template in every lane is what keeps a scaffolded empty
lane distinguishable from a lane the checker cannot parse.

IDs are scoped to THIS sub-area AND its lane: `RLB/smbus BUG-001` and
`RLB/hpet BUG-001` are different bugs. Cite one from outside as "RLB/smbus BUG-001".

The `RLB-0NN` sequence at the area level is the FROZEN legacy lane -- do not add
to it.
