# DELTA-010: delta_mesh_cell advertises its cell's credits from a parameter

**Priority:** P2
**Status:** open
**Owner:** sean galloway
**Filed from:** owner direction 2026-10-18 on the tile end-to-end credit
scheme (TILE_SPEC 11.9-11.10; RAPIDS side is rapids TASK-027).

A cell should need no logic to advertise its input buffer to RAPIDS. Its
delta node does it.

## What to build

1. A `delta_mesh_cell` parameter giving its cell's input-buffer size in flits
   (name to settle; 0 = no cell attached).
2. As the node leaves reset, it sends a `credit` packet with `op` = set
   (TILE_SPEC 11.5, 11.10) to `level` 3, the tile I/O, carrying that size,
   with the cell's coordinate as the source. A value of 0 sends nothing, so
   RAPIDS marks the cell illegal when its advertisement window closes.
3. The advertisement rides the reset-default route toward RAPIDS (delta HAS
   ch07 §3) on the `credit` virtual channel; it needs no grant.
4. The node stays a conduit otherwise: no credit state for traffic passing
   through. The cell returns credits itself as it consumes.

Tetrad and root nodes advertise their own buffer for node-addressed packets
in the same way (TILE_SPEC 11.10, Boot step 1); whether that is the same
parameter mechanism is part of this task.

## Done when

- A cocotb test: a node with the parameter non-zero emits exactly one `set`
  packet after reset, with the right count and source coordinate; with 0 it
  emits none.
- delta HAS/MAS updated; the parameter is listed with the node's others.
