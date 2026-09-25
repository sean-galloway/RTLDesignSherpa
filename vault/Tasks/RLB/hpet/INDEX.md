---
title: RLB/hpet tasks
summary: Task rollup for the HPET block (retro_legacy_blocks/rtl/hpet).
---

# RLB/hpet — task rollup

**Every item is its own file**, `<ID>.md`, filed under the directory for its
state (`open/`, `active/`, `closed/`, `dropped/`). Moving an item between states
is `git mv`, so an item is in exactly one state by construction.

## Lanes

| Lane | For | Next ID |
|---|---|---|
| [task/](task/INDEX.md) | planned work we decided to do | `TASK-006` |
| [bug/](bug/INDEX.md) | a defect with a reproduction | `BUG-002` |

`issue/` is created when this block first needs one. Open counts include the
reserved `-000` template, which is never a real item.

## Why a sub-area (Sean, 2026-09-25)

**RLB is an area that also has sub-areas, one per block** -- pic_8259, hpet,
ioapic, pm_acpi, smbus, pit_8254, rtc, gpio, uart_16550. RLB's own lanes hold
cross-block work (the review arcs, the RDL relocation); a block's own defects
and features live under `RLB/<block>/`.

Sub-areas are created ON DEMAND, not scaffolded. Nine blocks x three lanes x
four state directories would be ~100 files holding nothing, and this repo has
shipped the failure where an empty lane and a lane the checker cannot parse look
identical in a passing run. `hpet` is first because the pre-migration
`retro_legacy_blocks/TASKS.md` was entirely HPET.

IDs are scoped to THIS sub-area AND its lane: `RLB/hpet BUG-001` and a future
`RLB/ioapic BUG-001` are different bugs. Cite one from outside as
"RLB/hpet BUG-001".

The `RLB-0NN` sequence at the area level is the FROZEN legacy lane -- do not add
to it.
