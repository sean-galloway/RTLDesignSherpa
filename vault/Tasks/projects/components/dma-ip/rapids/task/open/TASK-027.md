# TASK-027: End-to-end credits and descriptor-slot grants for the tile header

**Priority:** P2
**Status:** open
**Owner:** sean galloway

RAPIDS sends tile packets (TILE_HDR = 1) without checking whether the
destination has room, and a cell can send a `desc` packet without a slot
grant. TILE_SPEC Sections 11.9 and 11.10 define the end-to-end credit scheme
that closes both; TILE_SPEC 11.12 records that it is not built. Split out of
rapids TASK-026 (2026-10-17), which delivered the header and the `desc` path.

## What to build

1. **Credit counters per destination** in the source half (22 per tile: 16
   cells, 4 tetrad nodes, 2 root nodes), starting at 0. A packet leaves only
   when its destination's counter covers every flit, header included.
2. **Credit packets in.** `rapids_tile_hdr_rx` already recognises `credit`
   packets and only counts them (`TILE_COUNTS.CREDIT_COUNT`). Route
   {source coordinate, op (add / set), count} over the sink-to-source path
   (the one `desc_inj_*` uses) into the counters.
3. **Grants out.** Per sink channel, free space less outstanding grants; a
   grant issuer that sends `credit` packets (class 0) out of the source port.
4. **Descriptor-slot grants** (class 1) for the per-channel injection slot in
   `descriptor_engine_shared`, returned when the scheduler takes the
   descriptor. A `desc` without a slot stays a counted drop
   (`TILE_DESC_DROPPED`).
5. **Deadlock:** credit packets must not wait behind data that waits for
   credits; on the source port they need priority or their own lane.

## Done when

- Tests: a cell model that advertises (`set`), returns credits after
  consuming, and sends only against grants; RAPIDS never oversends a
  destination; concurrent channels to one cell share its counter; a
  descriptor grant is consumed and returned.
- TILE_SPEC 11.12 updated; HAS/MAS chapters; byte regression clean-all FULL.
