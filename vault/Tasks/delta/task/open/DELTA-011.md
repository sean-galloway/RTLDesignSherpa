# DELTA-011: delta delivers result data to level 3, the tile I/O

**Priority:** P1
**Status:** open
**Owner:** sean galloway

Owner direction 2026-10-18 (TILE_SPEC 11.14): delta MUST be able to send
result data to `level` 3, RAPIDS. When gatling detects a flush-to-memory
condition it commands each cell's drain controller, which pushes the cell's
result memory out as write packets to `{ext 0, level 3}`.

Today delta routes on `{X, Y, Z}` only. A packet reaches the tile I/O only if
its sender writes the attach cell's delta coordinate into delta's header. A
delta node never originates a packet (owner direction 2026-10-18; DELTA-012),
so every packet to level 3 comes from a cell or a control core.

## What to build

1. Interim (flat mesh): no delta change. Gatling tells the cell the
   destination (owner direction 2026-10-18), including the attach cell's
   delta coordinate, and the cell writes it into delta's header like any
   other local-port packet. The done-when test below still applies.
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
