# DELTA-013: multi-path route tables with failover, and the hazards they open

**Priority:** P2
**Status:** open -- hazards recorded 2026-10-18; solutions to be worked here
**Owner:** sean galloway

Owner direction 2026-10-18: resilience means a link failure changes the
topology. Each route-table entry holds a set of next hops (primary +
alternate), and failover is an in-band table write through the existing
config packets: no new wires. A flit can then take different paths with no
failure, just by table state ("one way there, another back"). This spans
delta, the tile and RAPIDS; the hazards are written where they bite:

- delta HAS ch07 `11_resilient_routing.md` (R1-R4, deadlock, ordering, fork)
- TILE_SPEC 11.15 and the 10 open item
- RAPIDS MAS ch03 `14_tile_header.md`, Ordering Across the Fabric (O1-O3)

## Decide first

- **Design fork:** fully adaptive on both legs, or pinned forward
  (requests follow the table's path, deterministic per table state) with an
  adaptive return. Leading option: pinned forward. It is much easier to
  verify, determinism on one leg keeps the escape-VC argument simple, and the
  failure survived is on the forward path while the return recomputes
  anyway. It still reorders at a failover flip and on the return leg.

## Work through

1. **Table format:** an entry carries primary + alternate, or a second
   table image; the selection rule (fixed per table state for pinned
   forward).
2. **R1 atomic flip:** install alternates everywhere, then switch every
   node at once through the broadcast mode-switch ack barrier, so no packet
   sees a mix of old and new tables.
3. **R2 escape channel after a failure:** re-derive VC0 on the surviving
   graph (up/down over the tetrad/root hierarchy) and re-run the load-time
   checker on it, including the mixed state if R1 is not atomic. Delta
   already budgets 2 VCs per link (Duato, VC1->VC0 only); keep it per class.
4. **R3 config route:** the reset-default route that carries config needs
   its own alternate (in the tile, through the other root).
5. **R4 misroute drops:** traffic carrying credits never misroutes, and
   every drop reports on MonBus, so "always return credits" (TILE_SPEC 11.9)
   holds.
6. **Ordering:** a transaction ID per request, echoed in its reply (the
   head flit's 4-bit packet ID is the hook; 16 outstanding per requester),
   and the requester reorders or keeps per-ID order. RAPIDS: O1 read
   replies sharing a sink-channel tag, O2 credit `set` vs an older `add`,
   O3 write then a dependent packet. Implicit fabric order is documented as
   gone.

## Done when

- The fork is decided and recorded in delta HAS ch07 and TILE_SPEC 11.15.
- Each hazard row has a ruling: a mechanism, or a reason it cannot occur.
- Follow-on build items are filed in delta, rapids and the tile lanes with
  their area named.
