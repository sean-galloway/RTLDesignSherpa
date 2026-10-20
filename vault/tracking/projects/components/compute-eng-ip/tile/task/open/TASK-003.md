# TASK-003: Milestone M2 — tile running in isolation (injectors) on the FPGA

**Priority:** P1
**Status:** open -- 2026-10-19
**Owner:** sean galloway

## Why

Owner direction 2026-10-19: milestone ladder rung 2 (TILE_SPEC 12). The full
16-cell tile — tetrads, root nodes, root mux, tile I/O, MonBus aggregation
at every level — exercised by injectors instead of rapids. Proves the tile
composition, the K4-at-both-scales fabric tables (modes 9/10), and the
observation tree.

## Done when

A 16-cell tile runs on the FPGA with injector-driven cfg/mem/credit
traffic and all four MonBus levels observable; no rapids in the loop.

## Notes

Depends on M1 (TASK-002) and the tile wrappers (no tile RTL yet —
tetrad/tile_top per TILE_SPEC 11.1).
