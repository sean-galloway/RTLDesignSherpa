---
title: RLB/hpet tasks
summary: Task rollup for the HPET block (retro_legacy_blocks/rtl/hpet).
---

# RLB/hpet — task rollup

**Every item is its own file**, `<ID>.md`, filed under the directory for its
state (`open/`, `active/`, `closed/`, `dropped/`). Moving an item between states
is `git mv`, so an item is in exactly one state by construction.

## Lanes

| Lane | open | active | closed | dropped | deferred |
|---|---|---|---|---|---|
| [task/](task/INDEX.md) | 2 | 0 | 2 | 2 | 0 |
| [bug/](bug/INDEX.md) | 1 | 0 | 2 | 0 | 0 |
| [issue/](issue/INDEX.md) | 1 | 0 | 0 | 0 | 0 |

Open counts include the reserved `-000` template, which is never a real item.

## Why a sub-area (Sean, 2026-09-25)

**RLB is an area that also has sub-areas, one per block** -- pic_8259, hpet,
ioapic, pm_acpi, smbus, pit_8254, rtc, gpio, uart_16550. RLB's own lanes hold
cross-block work (the review arcs, the RDL relocation); a block's own defects
and features live under `RLB/<block>/`.

All nine blocks are SCAFFOLDED, on Sean's instruction (2026-09-25), superseding
the create-on-demand rule this page used to state. `hpet` was first and is the
only one that arrived with real items, because the pre-migration
`retro_legacy_blocks/TASKS.md` was entirely HPET. The `-000` template in every
lane is what keeps a scaffolded empty lane distinguishable from a lane the
checker cannot parse.

IDs are scoped to THIS sub-area AND its lane: `RLB/hpet BUG-001` and a future
`RLB/ioapic BUG-001` are different bugs. Cite one from outside as
"RLB/hpet BUG-001".

The `RLB-0NN` sequence at the area level is the FROZEN legacy lane -- do not add
to it.
