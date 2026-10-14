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
and is the reference implementation for the whole repo. It is drawn from
the RTL (`common-ip/rtl/macro/*_plane.sv` as `pumice_core` composes them) and
kept consistent with the per-plane figures in `common_mas/assets/graphviz/`.

## The three flows in a memory controller

A reader must be able to answer, from the drawing alone:

1. *Where does a command come from, and how does it reach the DRAM?*
2. *Where does write data enter, and by what route does it leave?*
3. *Where does read data come back, and how does it get home?*

| Flow | Direction | Geography |
|---|---|---|
| **Command** | strictly top-down | the center column: channels, then packetizers/intakes, the pools (whose entry views land straight on the scheduler; there is no separate arbitration stage), the scheduler, the command queue, the DFI plane and the PHY. Commands never share an arrow with data. |
| **Write data** | top-down, own route | enters with the write channel, waits in the write CAM (`mc_wr_data_cam`) and leaves by its own path: the commit stream down the left edge into the DFI plane's write side, then to the PHY. There is no merge or forward buffer. |
| **Read data** | **back up**, own route | returns from the PHY on a separate route: out of the DFI plane's read side, up the right edge into the reorder buffer (`mc_rd_return_ring`, filled in issue order), then drained in AR order through the read intake's R select home to the AXI read channel. The snarf (a read that hits a pending write) is a dashed host-side hop from the write CAM to the read intake; it never reaches the DFI plane. |

Per-plane diagrams apply the same discipline at plane scale, with the plane
edge as the boundary bar.

## Rank geography

- The pools sit directly above the scheduler's wide edge (a center spine and
  an alignment point keep them there); the maintenance requesters (init +
  refresh, the training plane) share the rank between the pools and the
  trapezium.
- The write data lane drops down the left edge on its own point scaffold and
  enters the DFI plane's left side; the read return leaves the DFI plane's
  right side and climbs the right edge on point scaffolds. The two lanes
  mirror each other.
- Timing control sits beside the trapezium (same-rank `xlabel`); page policy
  sits one rank below it, dashed up into it.
- Configuration registers sit with no edge; the label states "sideband
  config to all planes".

## Label vocabulary

| Where | Labels |
|---|---|
| Into the scheduler trapezium | `WR (commit slot back)`, `RD (issue slot back)`, `INIT / MRS / REF`, `ZQ / MRR (grant back)`, `timer window` (a same-rank `xlabel`), `PRE request` (dashed, from page policy) |
| Scheduler output (narrow edge, `penwidth=1.8`) | `DDR Command` (through the command queue) |
| Data lanes | `Write data (commit order)`, `Read data (issue order)`, `drain (AR order)` |
| PHY bar crossings | `Write to DDR`, `DDR Command`, `Read from DDR` |
| Sideband (dashed) | `ticket at insert / issue`, `snarf probe / hit + data` |

The scheduler is the family's trapezium (handbook rule 9). It is drawn only
for the command scheduler, `mc_scheduler_plane - mc_cmd_arbiter`.

## Rendering

`regenerate_all_graphviz.sh` in this directory renders every `.dot` to a
150 dpi PNG8. Copy it into any new `assets/graphviz/` directory.
