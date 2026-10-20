# TASK-006: Cell-to-cell credits/grants extension (TILE_SPEC 10 open item)

**Priority:** P2
**Status:** open -- 2026-10-19
**Owner:** sean galloway

## Why

TILE_SPEC 10 (open items, 2026-10-19): "Who reserves space for
cell-destined results, and how a cell advertises its input-buffer credits
to peer cells, is undefined." Cell PRD 7 keeps the DEST register reserved
for exactly this deferred path. Cell-to-cell streaming is what turns the
tile from a batch engine into a dataflow engine — worth doing, but only
after the rapids-bound loop is proven.

## What

Extend the end-to-end credit model (TILE_SPEC 11.9-11.10, straps-only-toward
-rapids today) so a cell can advertise input-buffer space to peer cells and
a sending cell can reserve/return credits cell-to-cell. Touches TILE_SPEC,
cell MAS ch04 (cell_credit: owed counters are already sender-generic — the
advertisement side is the new part), and the FLUSH_DEST/DEST precedence.

## Done when

TILE_SPEC 10 item closed with a recorded ruling; cell MAS/RTL carry the
extension; a cell-to-cell pipeline stage runs in tile simulation.

## Notes

Deferred until after M3 (rapids-bound loop proven) — owner sequencing.
