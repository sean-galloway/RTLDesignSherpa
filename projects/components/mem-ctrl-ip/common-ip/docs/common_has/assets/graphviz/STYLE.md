# Diagram house style: memory-controller specifics

**The binding, repo-wide rules live in the handbook:
`vault/handbook/authoring/block-diagrams.md`.** They cover the prime
directive, the nine rules, labels, palette, rendering, layout recipes and
render-then-read verification. This file keeps only what a reader of the
mem-ctrl-ip diagrams needs on top of that: how the flows map onto a DDR
memory controller, and the label vocabulary. The general rules started
here and moved to the handbook on 2026-10-12, so that there is one copy.

The reference the owner chose
(`design-a-ddr-memory-controller-i-top-level-diagram.webp`) is the classic
DDR-MC course diagram. `01_whole_unit.dot` in this directory implements it
and is the reference implementation for the whole repo.

## The three flows in a memory controller

A reader must be able to answer, from the drawing alone:

1. *Where does a command come from, and how does it reach the DRAM?*
2. *Where does write data enter, and by what route does it leave?*
3. *Where does read data come back, and how does it get home?*

| Flow | Direction | Geography |
|---|---|---|
| **Command** | strictly top-down | the center column: channels, then packetizers/intakes, pools, arbitration, the scheduler and the PHY. Commands never share an arrow with data. |
| **Write data** | top-down, own route | enters with the write channel and leaves by its own path to the PHY: down the left side, through the merge/forward buffers and the write data path. |
| **Read data** | **back up**, own route | returns from the PHY on a separate route: up the right side, through the read data path, merge logic and reorder buffer, home to the AXI read channel. |

Per-plane diagrams apply the same discipline at plane scale, with the plane
edge as the boundary bar.

## Rank geography

- The side buffers (merge, forward) sit one rank below the write pool, at
  the write flow's edge.
- The read return path climbs at the right edge, never through the center.
- Configuration registers sit with no edge; the label states "sideband
  config to all planes".

## Label vocabulary

| Where | Labels |
|---|---|
| Into the scheduler trapezium | `WR / RMW`, `RD`, `REF / ZQ`, `timer window` (the last a same-rank `xlabel`) |
| Scheduler output (narrow edge, `penwidth=1.8`) | `DDR Command` |
| PHY bar crossings | `Write to DDR`, `DDR Command`, `Read from DDR` |
| Sideband | `ticket at insert` (dashed) |

The scheduler is the family's trapezium (handbook rule 9). It is drawn only
for the command scheduler, `mc_scheduler_plane - mc_cmd_arbiter`.

## Rendering

`regenerate_all_graphviz.sh` in this directory renders every `.dot` to a
150 dpi PNG8. Copy it into any new `assets/graphviz/` directory.
