---
title: What is a plane
summary: A repo-unifying architectural frame: purpose-sliced functional layers whose membership, edge contract and independent include/exclude decisions stay stable across areas.
---

# What is a plane

A **plane** is a purpose-sliced functional layer in the RTL: a set of blocks
with a defined membership, a data-flow contract at its edges, and the property
that the layer can be included or excluded without rerouting the others.

The owner uses "plane" as a **repo-unifying term**. RAPIDS already has network
planes; when anyone sees "plane" anywhere in the repo they should recognize the
same idea: a layer you decide about as a unit.

## What makes a plane

1. **Purpose slice.** Everything in the plane answers the same "what job?"
   question. The Ocelus protocol plane observes buses and emits protocol-event
   packets; the Ocelus output plane arbitrates, filters, compresses and drains
   those packets off-chip. The purpose is the layer's identity, not its
   protocol or clock domain.
2. **Membership.** A plane lists the modules that belong to it. Membership is
   an explicit decision, not an emergent grouping.
3. **Data-flow contract at the edges.** The plane consumes something well
   defined and produces something well defined. Other planes see only that
   contract, not the internal structure.
4. **Independently include/excludable.** You can drop a plane from a build and
   the remaining planes still connect the same way. No other plane is rerouted,
   renamed or repartitioned.
5. **Unit of inclusion/config decisions.** When you decide "this build needs
   performance samples" or "this build has no debug trace", you are deciding
   at plane granularity.

## Declared instances

| Area | Planes | Notes |
|---|---|---|
| Ocelus AMBA monitor | protocol, error, debug, perf, output | See [Ocelus plane map](../../../docs/markdown/rtl-amba/monitor/monitor_planes.md). The protocol plane observes the bus; error/debug/perf reporters consume its events independently; the output plane drains whatever is kept. |
| RAPIDS DMA | network planes: sink RX / source TX | See `projects/components/dma-ip/rapids/docs/rapids_planes.md`. The endpoint + monitor-lite slices live outside the core so one core can drive AXI-Stream or CXS by choosing the top module. |
| delta / cell | (expected to declare theirs) | Their plane assignments belong in their own docs; this note is the definition they should point back to. |

## Consequences

- **A plane is not a clock domain or a bus protocol.** A purpose slice may
  contain multiple protocols (the Ocelus output plane has AXI4, AXI4-Lite and
  Wishbone drains) and may cross clocks inside itself.
- **A plane is not a hierarchy level.** It is a membership list plus a
  contract, not a place in the instance tree.
- **A plane is the right place to document build personas.** "Bring-up",
  "silicon-perf" and "field-debug" are shorthand for which planes are kept and
  which options inside the output plane are enabled.

Related: [[new-monbus-protocol]], [[observers-do-not-drive]],
[Ocelus plane map](../../../docs/markdown/rtl-amba/monitor/monitor_planes.md).
