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

1. **32 credit counters** in the source half, one per destination index
   (TILE_SPEC 11.9: 0-15 cells, 16-19 tetrad nodes, 20-21 root nodes, 22-31
   spare), starting at 0. A packet leaves only when its destination's counter
   covers every flit, header included. A node's counter covers only packets
   addressed to it: delta nodes are conduits for traffic passing through and
   hold no credit state for it, but advertise and return credits for what
   they consume (owner direction 2026-10-18, TILE_SPEC 11.9). A cell's
   advertisement comes from its delta node's parameter (delta DELTA-010).
2. **Advertisement window and legal-destination mask** (owner direction
   2026-10-18, TILE_SPEC 11.10). When the window after reset closes, every
   counter still at 0 is an illegal destination. Save the 32-bit mask, expose
   it as a CSR, and refuse a descriptor that targets an illegal destination as
   an invalid descriptor. A legal counter that later reaches 0 is waiting, not
   illegal; a failover resync keeps the saved mask.
3. **Credit packets in.** `rapids_tile_hdr_rx` already recognises `credit`
   packets and only counts them (`TILE_COUNTS.CREDIT_COUNT`). Route
   {source coordinate, op (add / set), count} over the sink-to-source path
   (the one `desc_inj_*` uses) into the counters.
4. **Grants out.** Per sink channel, free space less outstanding grants; a
   grant issuer that sends `credit` packets (class 0) out of the source port.
5. **Descriptor-slot grants** (class 1) for the per-channel injection slot in
   `descriptor_engine_shared`, returned when the scheduler takes the
   descriptor. A `desc` without a slot stays a counted drop
   (`TILE_DESC_DROPPED`).
6. **Deadlock:** credit packets must not wait behind data that waits for
   credits; on the source port they need priority or their own lane.

## Done when

- Tests: a cell model that advertises (`set`), returns credits after
  consuming, and sends only against grants; RAPIDS never oversends a
  destination, cell or node; concurrent channels to one cell share its
  counter; a node model advertises and returns credits for `cfg` writes
  addressed to it; a descriptor grant is consumed and returned; a spare index and a
  destination that never advertises end the window illegal, and a descriptor
  to either is refused.
- TILE_SPEC 11.12 updated; HAS/MAS chapters; byte regression clean-all FULL.
