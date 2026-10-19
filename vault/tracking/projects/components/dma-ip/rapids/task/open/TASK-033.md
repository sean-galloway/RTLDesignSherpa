# TASK-033: Tagged, indexed tile intake (interleaving and out-of-order packets into RAPIDS)

**Priority:** P3
**Status:** open -- 2026-10-19; pencilled in and validated in a cycle model; RTL waits for a running tetrad
**Owner:** sean galloway

## Why

Owner 2026-10-19: delta may interleave and reorder packets. Today's sink
landing frames packets in arrival order, so a cell must wait for every
credit back before its next packet (RAPIDS MAS O4, the interim rule,
f57b79a23). Owner direction: RAPIDS keeps per-sender transfer state and
places flits by information each flit carries. Debug from cells, tetrads
and nodes is MonBus only, on its own per-level AXI4-Lite tree (TILE_SPEC 5,
owner 2026-10-19), never on the fabric; the MonBus class 2 pencilled in
earlier the same day is retired, and nodes never send into RAPIDS.

## Mechanism (RAPIDS MAS, Tile Packet Header, Interleaved and Out-of-Order Intake)

- Every flit carries `{sender[4:0], pos, head}` (sender = external slot) on delta's sideband (delta
  HAS, Interface Assumptions, pencilled in).
- Class 0 (cell data): the landing space becomes a ring written at `pos`,
  drained in ring order, flits returned as they drain (the header's too).
- Class 1 (core descriptors): one intake entry per `pos`, in order.
- Resync clears rings, entries and `pos` on both sides.

## Validation so far

`dv/models/tile_intake_model.py` + `dv/tests/models/test_tile_intake_model.py`
(pure Python, 32 cells): exact in-order delivery of both classes at
LAND 16 and 8 under three fabric latency profiles; today's landing fails as
the control; wait-all on today's landing passes; two mutations caught;
throughput table in the MAS.

## Remaining

1. delta: carry the tag on body flits (tuser / CXS user); owner sign-off.
2. TILE_SPEC 11: the tag (TILE_SPEC is peer-dirty; not edited here).
3. RTL: `rapids_tile_hdr_rx` keyed by sender, `rapids_tile_landing` as an
   indexed ring, the header's class-0 return moved from arrival to drain.
4. Harness (rapids TASK-032): cells and a tetrad model that tag flits; then a
   real tetrad hooked to RAPIDS.
