<!-- RTL Design Sherpa Documentation Header -->
<table>
<tr>
<td width="80">
  <a href="https://github.com/sean-galloway/RTLDesignSherpa">
    <img src="https://raw.githubusercontent.com/sean-galloway/RTLDesignSherpa/main/docs/logos/Logo_200px.png" alt="RTL Design Sherpa" width="70">
  </a>
</td>
<td>
  <strong>RTL Design Sherpa</strong> · <em>Learning Hardware Design Through Practice</em><br>
  <sub>
    <a href="https://github.com/sean-galloway/RTLDesignSherpa">GitHub</a> ·
    <a href="https://github.com/sean-galloway/RTLDesignSherpa/blob/main/docs/DOCUMENTATION_INDEX.md">Documentation Index</a> ·
    <a href="https://github.com/sean-galloway/RTLDesignSherpa/blob/main/LICENSE">MIT License</a>
  </sub>
</td>
</tr>
</table>

---

<!-- End Header -->

# Resilient Routing: Open Hazards

> **OPEN** — design hazards recorded 2026-10-18 for delta DELTA-013. Nothing
> here is built. The solutions are worked through in that task.

Resilience means a link or node failure changes the topology. Delta absorbs
it by rewriting route tables in band with the existing config packets
(Routing and Configuration, In-Band Configuration), with no new wires. To make failover a table write,
each table entry holds a set of next hops, a primary and an alternate. A
flit's path then depends on table state even with no failure, so a request
and its reply can take different paths. This section records what that
breaks, under correct configuration.

## Design Fork: Which Leg Adapts

Delta routes per packet: the head flit picks the output and the body follows
it (wormhole), so adaptivity is a per-packet choice at each node, never per
flit. "Forward" below is the request direction, from the requester; "return"
is the reply and the credit traffic it causes.

| Option | Forward leg | Return leg | Verification |
|---|---|---|---|
| Fully adaptive | Best next hop at every node | Best next hop at every node | Every path is a function of load; the escape-VC argument must cover both legs at once |
| **Pinned forward, adaptive return** | The table's chosen next hop, deterministic for a given table state | Best next hop at every node | One leg is deterministic, which keeps the escape-VC story simple |

: Adaptive-routing options

Pinned forward is the leading option: it is much easier to verify, and for a
resilience goal it is usually enough, because the failure being survived is
on the forward path (failover rewrites it) and the return recomputes anyway.
It does not restore ordering: packets before and after a failover flip take
different forward paths, and the return leg adapts, so the ordering rules
below apply under either option.

## Multi-Path Tables and Failover

Today an entry is one `(output port mask, VC)` per `(destination, QoS class)`
(Routing and Configuration, Routing Tables); path diversity comes only from routing classes
differently. Failover needs the alternate in the entry, or a second table
image, so the switch is a write and not a recompute.

| # | Hazard | Mechanism | Candidate direction |
|---|---|---|---|
| R1 | Mixed tables during an update | Unicast config writes land one cell at a time, so mid-update the fabric runs a mix of old and new entries. The load-time checker validates one table, not the mix; a mix can loop or black-hole a destination, and a VC0 mix can close a cycle | Install the alternates everywhere first, then flip every cell at once through the broadcast mode-switch ack barrier (Routing and Configuration), which already guarantees no packet straddles two modes |
| R2 | The escape channel loses connectivity | Duato's protocol needs VC0 to reach every destination. A failed link on the VC0 subrelation leaves VC1 traffic that drains into VC0 with nowhere to go | Failover recomputes VC0 on the surviving graph (connected and acyclic, e.g. up/down over the tile hierarchy), not only the VC1 alternates |
| R3 | The config path crosses the failure | Config rides QoS 0 on the reset-default route. If the failed link is on that route, the cells beyond it cannot be reached to fail them over | The bootstrap route carries its own alternate; in the tile, the path through the other root |
| R4 | A misroute drop loses state | A VC1 packet whose misroute budget reaches 0 is dropped and counted (Flow Control and Deadlock, Livelock). Alternates add non-minimal hops, so drops become reachable in normal traffic. A dropped data or `credit` packet breaks the tile rule that credits always return (TILE_SPEC §11.9): the sender's strap leaks until a resync | Tile traffic that carries credits never misroutes (minimal or VC0 only), and every drop is reported on MonBus |

: Failover hazards

Packets in flight on the failed link are lost. That is the existing root
failover assumption (TILE_SPEC §11.4): RAPIDS times the transfer out and
software re-issues it, and a resync `set` (TILE_SPEC §11.10) restores leaked
straps.

## Deadlock

Delta already has the standard fix: two VCs per class (Flow Control and Deadlock), VC0 the
deterministic escape channel, VC1 adaptive, VC1→VC0 permitted at any hop and
VC0→VC1 forbidden, with the dateline rule for torus wrap. The two-VC budget
is met and stays the rule for every QoS class, since each class has its own
VCs (Quality of Service).

What changes with failover is that the escape subrelation stops being a
design-time artefact. Today it is the reset default plus generator-checked
tables. After a failure it is whatever the surviving graph allows, so R2 is
the deadlock hazard: the escape rule must be re-derived and re-checked on
every failover, including the mixed state of R1.

## Ordering

| Guaranteed | Not guaranteed |
|---|---|
| The flits of one packet, in order (one packet, one path) | Order between packets, even from one source to one destination in one class, once tables hold alternates or a failover flips mid-stream |

: Ordering contract

Implicit ordering across the fabric is gone, and this is documented so
nothing is built on it. Order becomes a requester-side property: a
transaction ID on every request, echoed in its reply, with the requester
reordering, or delivering in order per ID as AXI IDs do. The head flit's
4-bit packet ID (Cell and Flit) is the existing hook; 16 outstanding IDs per
requester is its ceiling before aliasing. The tile and RAPIDS consequences
are in TILE_SPEC and the RAPIDS MAS (ch03 Tile Packet Header, Ordering
Across the Fabric).
