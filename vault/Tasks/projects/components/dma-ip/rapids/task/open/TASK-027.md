# TASK-027: End-to-end credits and straps toward RAPIDS for the tile header

**Priority:** P2
**Status:** open -- counters, window and legal mask built 2026-10-18 (`TILE_CREDITS`); straps toward RAPIDS remain
**Owner:** sean galloway

## Progress 2026-10-18

Items 1-3 are built behind `TILE_CREDITS` = 1 (needs `TILE_HDR`):
`rtl/fub/rapids_tile_credits.sv` in `rapids_src` (64 counters, each node's
internal and external ID, `rapids_pkg::tile_dest_index`), the `credit_*` path from
`rapids_tile_hdr_rx`, the per-packet charge in `src_data_path_axis`
(`tile_acq_*`), the scheduler's window hold and illegal-destination refusal,
and CSRs `SRC.TILE_ADV_WINDOW` / `TILE_LEGAL_DEST_LO` / `_HI` / `TILE_CREDIT_STATUS`.
Tests: `test_rapids_cxs_top.py::test_rapids_cxs_top_tile_credits[window,
no_oversend, shared_counter, node, illegal]` and the 16-channel
shared-counter cell, mutation-checked. The cell-side advertisement is delta
DELTA-010. Known limit: a channel reset does not refund charged credits.

Owner direction 2026-10-18: every node has an internal and an external ID
(the coordinate's `ext` bit, TILE_SPEC 11.3). delta nodes only transport and
never originate a packet on the data network (their own data goes on
MonBus): they never advertise or return credits and consume what is
addressed to them on arrival. So a node's internal ID is legal by topology
and never charged, and a read request to a node is refused (built
2026-10-18). Only the external IDs (cells, control cores) carry credits, and
each cell or core sends its own boot advertisement.

Owner direction 2026-10-18 (TILE_SPEC 11.14): delta must carry result data
to `level` 3. Toward RAPIDS the credits are **straps, not grants**: a cell
writes against a 16-flit strap, a control core (gatling, which creates the
descriptors) sends `desc` against strapped descriptor-queue entries.

## What to build

1. Done: 64 counters, advertisement window, legal mask, credit intake (above).
2. **Landing space**: 16 flits per cell, per sender, so a cell whose data
   targets a full sink channel holds only its own strap. A packet to RAPIDS
   is at most 16 flits.
3. **Credit returns from RAPIDS** on the source port: `credit`/`add` to the
   sender when its data leaves the landing space for its sink channel.
4. **Descriptor-queue entries per control core** (class 1), one returned
   when the scheduler takes the descriptor; how many per core, and whether
   each tetrad gets its own source channel, is open (TILE_SPEC 10).
5. **Resync** after root failover (TILE_SPEC 11.10): `set` to every cell and
   core restoring its strap.
6. **Deadlock:** credit packets must not wait behind data that waits for
   credits; on the source port they need priority or their own lane.

## Done when

- Tests: a cell model that advertises (`set`), returns credits after
  consuming, and sends only against its strap; RAPIDS never oversends a
  destination, cell or node; concurrent channels to one cell share its
  counter; a node is never charged and never advertises; a descriptor entry is consumed and returned; a spare index and a
  destination that never advertises end the window illegal, and a descriptor
  to either is refused.
- TILE_SPEC 11.12 updated; HAS/MAS chapters; byte regression clean-all FULL.
