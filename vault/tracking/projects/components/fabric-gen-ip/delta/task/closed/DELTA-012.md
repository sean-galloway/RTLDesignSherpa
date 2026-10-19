# DELTA-012: remove the node-originated credit advertisement (revert DELTA-010)

**Priority:** P1
**Status:** CLOSED 2026-10-18 -- delta tree byte-identical to its pre-DELTA-010 state; mesh regen (CXS then AXIS) reproduces it
**Owner:** sean galloway

Owner direction 2026-10-18: delta transports on the data network but never
makes up data to send on it; anything a node generates goes on MonBus. The
DELTA-010 advertisement was the node originating a packet, so it is removed:
`CELL_CREDITS` and `TILE_IO_X/Y/Z` are gone from `bin/delta_mesh/cell.py`,
`fabric.py`, the regenerated cell, CXS wrapper and both fabrics, the 2x2
harness, `delta_mesh_tb.py`, `test_delta_mesh_credit_adv.py`, HAS ch07 and
MAS ch06. A cell or control core sends its own boot advertisement under its
external ID (TILE_SPEC 11.10, option (a)); RAPIDS treats delta nodes as legal
by topology.
