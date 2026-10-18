# DELTA-011: delta delivers result data to level 3, the tile I/O

**Priority:** P1
**Status:** open
**Owner:** sean galloway

Owner direction 2026-10-18 (TILE_SPEC 11.14): delta MUST be able to send
result data to `level` 3, RAPIDS. When gatling detects a flush-to-memory
condition it commands each cell's drain controller, which pushes the cell's
result memory out as write packets to `{ext 0, level 3}`.

Today delta routes on `{X, Y, Z}` only. A packet reaches the tile I/O only if
its sender writes the attach cell's coordinate (`TILE_IO_X/Y/Z`) into delta's
header; only the DELTA-010 credit advertisement does that, from inside the
node. A cell injecting at its local port has no way to say "level 3".

## What to build

1. Interim (flat mesh): a cell's local-port packet whose destination is the
   tile I/O is routed to `TILE_IO_X/Y/Z` without the cell knowing where
   RAPIDS attaches. The selection mechanism (a local-port sideband, or the
   node reading the tile header's `level`) is the design choice to make first.
2. Permanent: delta's head-flit header gains `level` and `ext` (TILE_SPEC
   11.3), routing on `{level, X, Y, Z}`; the interim parameters go away when
   the tetrad/root/tile I/O RTL lands.

## Done when

- A multi-beat result packet injected at any cell's local port, addressed to
  level 3, leaves the tile I/O's port intact (header beat + data, in order),
  for more than one attach cell, on AXIS and CXS.
- The flow-control rules hold: data class, not control class; a full tile I/O
  backs up into the routers without loss.
- Delta HAS/MAS updated; delta func regression clean-all.
