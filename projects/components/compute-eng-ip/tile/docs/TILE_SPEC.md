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
    <a href="https://github.com/sean-galloway/RTLDesignSherpa/blob/main/docs/LICENSE">MIT License</a>
  </sub>
</td>
</tr>
</table>

---

<!-- End Header -->

**[← Back to tile](../README.md)**

# Tile — Compute Engine Tile Subsystem Specification

**Version:** 1.5 (2026-10-18; §11.13 tetrad control core **deferred** pending
the cell — owner direction 2026-10-18, gatling-rv32itetrad the leading
candidate; cell→cell grant mediation added to §10 open items; §11.3 internal/external ID on every node, §11.9-11.10
credits — owner direction 2026-10-18: delta nodes are conduits for transit
and endpoints for what they consume, 32 RAPIDS credit counters, the
advertisement window's saved legal-destination mask, and a cell's
advertisement sent by its delta node from a parameter, then (same day) delta nodes only transport and never originate: a cell or core advertises for itself, nodes are legal by topology, and straps toward RAPIDS replace grants; §11.14 result flush to the tile I/O, delta must carry result data to `level` 3). Carries 1.4
(tetrad control core recorded 2026-10-17; §11 adopted
2026-10-16; cell integration decisions 2026-10-16; §11 proposal added
2026-10-16; re-homed to compute-eng-ip 2026-10-15; v1.0 owner-defined
2026-10-15)
**Status:** Canonical microarchitecture definition for the compute-engine
tile. **delta is the node** (`delta_mesh_cell`) — nodes collectively form
the network; this document defines the tile IP that instantiates 16 of
them. Where this document and `delta_has/ch07_mesh_network/01_hierarchy.md`
disagree, this document wins — the hierarchy chapter predates the
2026-10-15 owner decisions (tetrad/tile naming, real wrapper modules,
MonBus aggregation, this re-home). The working design record with full
citations is
[`docs/superpowers/specs/2026-10-13-delta-mesh-design.md`](../../../../../docs/superpowers/specs/2026-10-13-delta-mesh-design.md)
(§2 in particular); this spec is its distilled, decision-frozen form.

---

## 1. Scope

The **tile** is the delta mesh's subsystem unit: 16 cells arranged as
2×2×1 **tetrads** of 2×2×1 cells, fully connected at both scales, with
per-level MonBus observation aggregation and a single external attach
point for rapids. This document defines the tile's hierarchy, modules,
connectivity, observation architecture, interfaces, and mode set.

Out of scope: cell-internal microarchitecture (buffering, allocators,
VCs — design spec §3 and ch07 §§4–6), flit format (§4), the flat
crossbar modes of the delta generator's other configurations, and the
fabric-level Z stacking above one tile.

## 2. Hierarchy

| Level | Composition | RTL | Purpose |
|---|---|---|---|
| **Cell (node)** | 1 | `delta_mesh_cell` — owned by [`fabric-gen-ip/delta`](../../../fabric-gen-ip/delta) | the one module with datapath: routing tables, VCs, allocators |
| **Tetrad** | 2×2×1 cells (4) | `tetrad` (this IP) | datapath grouping (K4) + first MonBus aggregation |
| **Tile** | 2×2×1 tetrads = 4×4×1 cells (16) | `tile_top` (this IP) | the subsystem: full K4 at tetrad scale, tile-top MonBus, rapids attach |
| **Fabric** | 4×4×K tiles | generated top | planar recursion; Z lives between tile layers |

Owner-named 2026-10-15: "tetrad" (was "tile") and "tile" (was
"confluence").

**Adopted 2026-10-16:** §11 refines this hierarchy — the tetrad is a
routing node with datapath (not a passive wrapper), two root nodes sit
above the tetrads behind a root mux, and rapids attaches at the tile I/O
above the mux (§11.1, §8 below). The table's RTL column names predate
that decision; the wrapper-shaped `tetrad`/`tile_top` plan built on it
is superseded. The hierarchy's leaves are the cells, defined by the
cell PRD
([`compute-eng-ip/cell/docs/PRD.md`](../../cell/docs/PRD.md)) — each a
self-contained IP whose only tie to delta is one node instantiated
inside it.

**Owner direction 2026-10-17:** each tetrad additionally carries **one
RV32I control core** (kestrel-class, `CORE_FLAVOR`-swappable) at its
tetrad node's local port — the control agent for the tetrad's four
cells, defined with its duties and boundaries in
[alu-infer PRD §5](../../alu-infer/PRD.md). All data, config, and
programming for the tile blocks — the core's firmware included — arrive
in-band on delta; the core is a local reaction agent, not a config
originator. SERV is unchanged in its Ocelus observability role. See
§11.13.

## 3. Connectivity

Connectivity is the **same K4 clique at both scales** — the owner's
figure [`assets/3d-mesh-tile.drawio`](assets/3d-mesh-tile.drawio) draws
it: four fully meshed cells inside the tetrad, four fully meshed
tetrads inside the tile.

- **Cell ports**: 6 neighbors (±X, ±Y, ±Z) + 1 local (host/rapids-facing)
  + P_DIA + P_DIA2 + 1 MonBus observer out.
- **Intra-tetrad K4**: the 4 perimeter edges ride ordinary ±X/±Y links;
  both diagonals ride **P_DIA**, one link per cell to the diagonally
  opposite cell of its tetrad.
- **Intra-tile K4**: the 4 tetrads of a tile are themselves fully
  connected. Edge-adjacent tetrads share ±X/±Y boundaries; diagonal
  tetrad pairs ride **P_DIA2**, joining the diagonally adjacent corner
  cells (e.g. (1,1,0)↔(2,2,0), (1,2,0)↔(2,1,0) per tile). Out-of-grid
  mates tie P_DIA2 off — provably never selected.
- **One conceptual diagonal axis**: P_DIA and P_DIA2 are two instances
  of a single diagonal axis realized at tetrad and tile scale. A cell
  has 4 axes in-plane-plus-diagonal plus Z: 8 directional links + local
  = 9 ports.
- **Z**: entirely inter-tile; tetrads are planar (X/Y only).

## 4. Modules

- `delta_mesh_cell` — the node, owned and emitted by delta (the
  fabric-gen-ip component). The only datapath module: routing tables, VCs,
  allocators. The network is the collective of instantiated nodes; this
  IP is not it.
- `tetrad` (`rtl/tetrad.sv`, this IP) — instantiates 4 delta nodes; wires
  the K4 connectivity of §3; merges the 4 node MonBus streams into one
  tetrad MonBus (§5). No datapath function.
- `tile_top` (`rtl/tile_top.sv`, this IP — house `<ip>_top` naming) —
  instantiates 4 tetrads; merges the 4 tetrad MonBus streams into the
  single tile-top MonBus (§5); exposes boundary nodes' local ports for
  rapids attachment. No datapath function. (Working names during the
  delta-side design phase were `delta_mesh_tetrad` / `delta_mesh_tile`;
  retired with this re-home.)

**Adopted 2026-10-16 (§11.1):** the tetrad becomes a routing node with
datapath, so its module owns switching above its group of 4 cells; the
tile adds 2 root nodes, a root mux, and the single tile I/O. The
wrapper-only description above is kept for the decision trail; module
boundaries for the adopted shape are part of the tile RTL planning and
follow the cell PRD's block structure.

**Owner direction 2026-10-17:** the tetrad module also instantiates the
tetrad's **control core** — one kestrel-class RV32I core (this IP)
attached at the tetrad node's local port, per §11.13 and alu-infer PRD
§5.

## 5. Observation (MonBus aggregation)

Owner decision 2026-10-15. Every cell emits exactly **one** MonBus
stream; observation aggregates 4:1 per level:

```
cell  ┐
cell  ├─ tetrad (this IP) ────── 1 tetrad MonBus
cell  ┤
cell  ┘
tetrad ┐
tetrad ├─ tile_top (this IP) ─── 1 tile-top MonBus  ← host/board sees this
tetrad ┤
tetrad ┘
```

Aggregation uses the house AXIL MonBus group family
(`rtl/amba/ocelus/monbus_group_core` + `monbus_*_group` wrappers, AXIL
host-read flavor) — the same observation path as the amber tally
harness (merge → group → AXIL read-out), so standard host tooling
(`monbus_tally_axil`, regmaps) attaches at the tile top unchanged. Exact
leaf selection inside the wrappers is implementation detail; the
architectural contract is **one MonBus per level boundary, 4:1 merge per
level**.

This hierarchy is also the verification anchor: per-tetrad and per-tile
observability come for free, and the tile-top stream is the single
sim-vs-silicon equivalence point (the same role the UART-equivalence
cell plays for the amber harness).

## 6. Interfaces

- **Cell/tetrad/tile datapath ports**: AXI4-Stream
  (`TDATA/TVALID/TREADY/TLAST` + header sideband in `TUSER`), with the
  optional AMBA 5 TSTRB/TWAKEUP/TPARITY richness carrying over from
  flat mode unchanged.
- **CXS migration (owner plan, 2026-10-15)**: rapids gains a CXS
  interface variant — a separate model, `rapids_cxs`, replacing its AXIS
  interfaces — and delta's network ports move to CXS to match. Sequencing:
  rapids_cxs first (a working AXIS model exists to diff against), then
  delta. Header/sideband content is unchanged by the migration. Until
  both sides land, all delta ports stay AXI4-Stream.
- **MonBus ports**: per §5; cell-level streams are internal to the
  tetrad, tetrad-level streams internal to the tile.

## 7. Modes

The mode catalog (design spec §5.4) is unchanged by this spec; the
tile-relevant rows:

| Mode | Pattern | Tile relevance |
|---|---|---|
| 1 Mesh (default) | DOR over RAM tables | baseline; inter-tile dsts DOR |
| 9 Tetrad all-to-all (K4) | perimeter ±X/±Y + P_DIA diagonals | intra-tetrad 1 hop to any cell; inter-tetrad DOR |
| 10 Tile all-to-all (K4 of tetrads) | shared boundaries + P_DIA2 diagonals | any cell of any tetrad of the tile in 1–2 hops (diagonal-of-tetrad pairs 1 hop); inter-tile DOR |

Modes are table images, not new hardware — except that modes 9–10 make
P_DIA/P_DIA2 (emitted in every build) their enabling hardware.

## 8. Rapids attachment

Hive configuration (owner, 2026-10-15): one or more tiles — only one
for now — connect to a **single** rapids DMA at boundary cells' local
ports; any boundary cell can be the attachment. With the CXS migration
(§6), this link is the first CXS hop.

**Adopted 2026-10-16 (§11.1):** rapids attaches above the two root
nodes through the root mux, at the single tile I/O — not at a boundary
cell's local port. Its descriptors, buffers and channel state survive a
root failover (§11.4); the cell↔rapids protocols (packet header,
end-to-end credits, straps) are §§11.5–11.10.

**Status (owner, 2026-10-18):** rapids is the DMA running data in and
out of the tile; RTL **in progress** on a separate lane, alongside the
delta backbone (an agent is building that).

## 9. Clocking and reset

Single clock domain, active-low async `aresetn` (house `ALWAYS_FF_RST`)
throughout the tile — a deliberate simplification against the NoC
literature's GALS assumption; timing closure and generator
predictability win over clock flexibility (design spec §2 close).

## 10. Open items

Decided 2026-10-16 (was §11): the hierarchical tile of §11.1 (tetrad
routing nodes, two roots, root mux, tile I/O); the packet header and
payload types (§11.2, §11.5); the destination coordinate (§11.3);
end-to-end credits with boot advertisement, per-destination counters,
and straps gating cell→rapids traffic (§§11.9–11.10, owner direction
2026-10-18, replacing grants); credit-return
batching as a per-cell config with default N=1 (cell PRD §6).

Still open:

- What switches the root mux (§11.4): software, a watchdog, or the
  root-to-root link.
- How many descriptor-queue entries each control core is strapped, and
  whether each tetrad gets its own source channel (§11.9, §11.11).
- Cell input buffer sizes (the advertisement value) and result-memory
  sizing — cell PRD §12.
- Resync timing: how long RAPIDS waits for answers before declaring a
  destination dead (§11.10).
- Cell-issued descriptors (§11.11): whether a source channel is reserved for
  them or any channel may take them, and whether a cell is told when its
  pull completes.
- CXS leaf selection for both rapids_cxs and delta ports (§6).
- MonBus wrapper leaf selection inside tetrad/tile (§5).
- Config/address region naming per level — design spec §5, ch07 §3;
  §11.3's coordinate is the addressing answer, register naming follows
  the cell PRD.
- Cell→cell flow control (§11.9): credit *returns* are sender-generic
  already — a credit goes to the source coordinate of the packet whose
  flits it frees — but straps are defined only toward RAPIDS. Who
  reserves space for cell-destined results, and how a cell advertises
  its input-buffer credits to peer cells, is undefined. Needed for the
  cell PRD's `DEST` override (cell PRD v0.3 §6.3); v1 result traffic is
  rapids-bound.
- Result flush (§11.14): how gatling commands a cell's drain controller (an
  Xcell instruction or a `CTRL` flush-and-send write) and passes it the
  destination, how much the drain sends, and how the cell reports the drain
  complete.
- Tetrad control core (§11.13): the kick/wait custom-opcode encoding,
  its local memory map, and its program-load conventions — cell/tetrad
  MAS work, per alu-infer PRD §5. **Deferred** (owner direction
  2026-10-18): the engine is defined after the cell is fully defined and
  working; gatling-rv32itetrad is the leading candidate (§11.13).

Tile RTL (`tetrad` node, `tile_top` with roots + mux + I/O) is pending
the adopted-shape module split above; the node RTL (`delta_mesh_cell`,
modes 9–10 diagonal ports, Task 6c) has landed in
[`fabric-gen-ip/delta`](../../../fabric-gen-ip/delta).

## 11. Hierarchical tile, root nodes, addressing (ADOPTED 2026-10-16)

**Status: ADOPTED, owner decision 2026-10-16.** Where §§2–4 and §8
still carry the pre-adoption wrapper wording, this section is the
decision record and wins. Residual open sub-items are listed in §10.

### 11.1 Hierarchy

| Level | Count per tile | Role |
|---|---|---|
| Cell | 16, in 4 groups of 4 | Leaf node; the 4 cells of a group are fully meshed (K4) |
| Tetrad node | 4 | A routing node above its group of 4 cells; the 4 tetrad nodes are fully meshed (K4) |
| Root node | 2 (root 0, root 1) | A routing node above the tetrads; each root links to all 4 tetrad nodes; the two roots are linked to each other |
| Root mux | 1 | Selects the live root; not a node and not addressable |
| Tile I/O | 1 | The single connection out of the mux, to the one RAPIDS: its **source port** (RAPIDS to tile) and its **sink port** (tile to RAPIDS) |

Changes against §§2-4:
- The tetrad becomes a routing node with datapath, not a wrapper.
- RAPIDS attaches above the roots, through the mux, not at a boundary
  cell's local port.

### 11.2 Payload types

Every packet carries a payload type, chosen by the RAPIDS descriptor that
produced it:

| Code | Type | Target |
|---|---|---|
| 0 | `cfg` | Node or cell configuration (routing tables, mode, CSRs) |
| 1 | `prog` | Program load |
| 2 | `mem` | Node or cell memory |
| 3 | `credit` | End-to-end credit advertisement or return (§11.9); header only |
| 4 | `desc` | A cell-issued RAPIDS source descriptor (§11.11) |
| 5-7 | reserved | - |

Delta's existing QoS class 0 (config) would map from `cfg`, so the
fabric keeps one notion of config traffic.

### 11.3 Destination coordinate

| Field | Width | Meaning |
|---|---|---|
| `ext` | 1 | Which of the node's two IDs (owner direction 2026-10-18): 0 = internal, the node itself; 1 = external, what is attached at its local port |
| `level` | 2 | 0 = cell-level node, 1 = tetrad node, 2 = root node, 3 = tile I/O (RAPIDS) |
| X | `COORD_W` (4) | Cell: its X. Tetrad: its group's X (the cell X with the low bit dropped). Root: root 0 or 1. Tile I/O: reserved. |
| Y | `COORD_W` (4) | Cell: its Y. Tetrad: its group's Y. Root and tile I/O: reserved. |
| Z | `COORD_W` (4) | Tile layer, unchanged from delta |

: Proposed destination coordinate, `{ext, level, X, Y, Z}`, 15 bits at COORD_W = 4

- **Every node has an internal and an external ID** (owner direction
  2026-10-18). The internal ID (`ext` = 0) is the node itself: its routing
  tables, its configuration, the buffer for packets addressed to it. The
  external ID (`ext` = 1) is what is attached at its local port: at a
  cell-level node, the cell; at a tetrad node, its control core (§11.13).
- A cell is therefore the external ID of its cell-level node,
  `{1, 0, X, Y, Z}`. Tetrad nodes, roots and the tile I/O are addressed by
  their own level, never as a cell.
- Only a node with something attached has external credit (§11.9): an
  external ID with nothing behind it never advertises, so it is never a
  legal destination.
- Routing uses `{level, X, Y, Z}` only; `ext` is read at the last hop, to
  consume the packet in the node or deliver it out of the local port.
- The mux has no coordinate.
- A packet's source coordinate uses the same format. RAPIDS always sends
  as `level = 3`, the tile I/O (`ext` = 0), so replies reach it through
  whichever root is live.
- Delta's head-flit header carries `{X, Y, Z}` today (ch07 §2). Adding
  `level` and `ext` is a delta header change, still to be made. It is
  required: delta must deliver result data to `level` 3 (§11.14).

### 11.4 Root failover

- Root 1 takes over if root 0 fails. There is one RAPIDS, so its
  descriptors, buffers and channel state survive a root failure.
- Packets in flight inside the failed root are lost. RAPIDS sees those
  transfers stall and time out (its scheduler timeout), and software
  re-issues them.
- The mux switches only at a packet boundary. On the CXS link to RAPIDS,
  a switch is a link deactivation followed by a reactivation, which the
  CXS endpoints already handle (credits are returned before deactivation
  completes).
- Open: what drives the mux select (§10).

### 11.5 Packet header

Every packet starts with one header. It extends delta's head-flit header
(delta HAS ch07 §2: coordinates, QoS class, VC, multicast, misroute budget,
source-route pointer, packet ID) with the fields below.

| Field | Width | Meaning |
|---|---|---|
| Destination coordinate | 15 | `{ext, level, X, Y, Z}`, §11.3; adds `ext` and `level` to delta's `{X, Y, Z}` |
| Source coordinate | 15 | Same format; RAPIDS sends as `level` = 3, the tile I/O |
| `ptype` | 3 | Payload type, §11.2 |
| `op` | 1 | Data packets: 0 = write (payload follows), 1 = read (header only; the target replies). `credit` packets: 0 = add, 1 = set (§11.10) |
| Length | 32 | Write: payload bytes that follow. Read: bytes requested. Credit: flits (or descriptor entries) advertised or returned. `desc`: 32 (one descriptor). |
| Target address | 49 | Byte address inside the addressed node or cell. Credit packets: bits [1:0] are the credit class (0 = sink space, 1 = descriptor slots), the rest reserved. |
| Tag | 4 | The RAPIDS channel. Set by RAPIDS on a request; echoed by the target in its reply, so the reply reaches the right sink channel |

: Proposed tile packet header fields (beyond delta's existing ones)

Proposed packing, for a transport that carries the header as data:

| Bits | Field |
|---|---|
| `[14:0]` | Destination coordinate |
| `[29:15]` | Source coordinate |
| `[32:30]` | `ptype` |
| `[33]` | `op` |
| `[65:34]` | Length |
| `[114:66]` | Target address |
| `[118:115]` | Tag |
| above `[118]` | Delta's existing head-flit fields, then reserved |

: Proposed header packing

The header costs one flit per packet. For short `cfg` writes that is a
large share; a later revision could pack a small payload into the reserved
bits.

### 11.6 Transport

The header is the same whatever carries it:

| Transport | Where the header rides |
|---|---|
| AXI4-Stream (delta ports today) | `TUSER` of the head beat, as delta does now |
| CXS (RAPIDS CXS tops; delta ports after the migration in §6) | The data of the first flit of the packet. CXS has no address field, and `CXSSRCID` / `CXSTGTID` are at most 8 bits, too narrow for a coordinate. |

On CXS the link's own sidebands keep their link-level meaning: RAPIDS keeps
the channel in `CXSSRCID`, so per-stream framing is unchanged.

### 11.7 Where the fields come from

- **RAPIDS:** its descriptor supplies `ptype`, `op`, the destination
  coordinate and the target address (RAPIDS HAS, Descriptor Format); the
  tag is the channel that issued the descriptor. The source half builds the
  header and sends it out of the source port, ahead of any payload.
- **Nodes:** none. A delta node never originates a packet (§11.9), so it
  never answers a read; a cell or core answering one builds a reply header
  addressed to the request's source coordinate.
- **Open:** whether the RAPIDS sink half strips the header or delivers it
  to memory.

### 11.8 Operations

Only cells and control cores send into RAPIDS's sink port, and only against
their straps (§11.9); a delta node never does.

| Operation | Source port sends | Target does | Sink port receives |
|---|---|---|---|
| Write | Header (`op` = 0, length N, tag) + N bytes | Consumes the data, then returns credits (§11.9) | The credit packet |
| Read | Header only (`op` = 1, length N, tag = the sink channel that will take the data); never to a node | Sends N bytes back: a write-format packet to `level` 3 with the tag echoed | The data, into the tagged sink channel |
| Cell send | - | Sends a write-format packet to `level` 3 with the tag set, against its 16-flit strap | The data, via the cell's landing space, into the tagged sink channel |
| Credit return to a sender | Header only (`ptype` = `credit`, destination = the cell or core) for what RAPIDS consumed | Adds it to its strap counter | - |
| Credit return | - | - | Header only (`ptype` = `credit`) for flits the cell or core consumed; never stored in a channel |
| Core-issued descriptor | - | Sends a `desc` packet to `level` 3: header + one 256-bit source descriptor, tag = the source channel, against its strapped descriptor-queue entries | The descriptor, into that source channel's descriptor queue (§11.11) |

: Proposed operations between RAPIDS and the tile

A read carries its own reservation: RAPIDS issues it only when the tagged
sink channel has room for N bytes, and the reply needs no strap credit.

### 11.9 End-to-end credits

Link credits (CXS `CRDGNT` / `CRDRTN`) cover one hop and carry no address,
so they cannot say anything about a cell's buffer. End-to-end credits are
packets instead.

**delta nodes only transport** (owner direction 2026-10-18). A node carries
every packet on the data network, `credit` packets included, on that
packet's virtual channel, and holds no credit state for it: only the
hop-level flow control it already has. A node never originates a packet on
the data network; whatever it generates itself (debug, status) goes on
MonBus. It consumes what is addressed to its internal ID (§11.3) on arrival,
so it needs no end-to-end credit: it never advertises and never returns
credits, and it must never stall what is addressed to it. End-to-end credits
belong to what is attached at a node's local port, under the node's
external ID: a cell, or a tetrad's control core (gatling).

1. RAPIDS's source half keeps **64 credit counters** (owner direction
   2026-10-18), one per destination index `{ext, n}`: the internal and the
   external ID of every node. A tile uses at most 42 (22 internal: 16
   cell-level nodes, 4 tetrad nodes, 2 root nodes; 20 external: 16 cells, 4
   tetrad control cores). An external counter starts at 0 and is filled by
   its cell's or core's own advertisement (§11.10), so an external ID with
   nothing attached is never legal. An internal (node) index is legal by
   topology: a packet to a node is never held for credits and never charged.

   | Index | Destination |
   |---|---|
   | 0-15 | Cell-level node (internal), `{Y[1:0], X[1:0]}` |
   | 16-19 | Tetrad node (internal), `{Y[0], X[0]}` of its group |
   | 20-21 | Root node 0, 1 (internal) |
   | 22-31 | Spare |
   | 32-47 | Cell: the cell-level node's external ID, `32 + {Y[1:0], X[1:0]}` |
   | 48-51 | Tetrad control core: the tetrad node's external ID |
   | 52-53 | Root external: none (the root's local side is the tile I/O) |
   | 54-63 | Spare |

   : Proposed credit-counter index
2. Each flit sent to a destination, the header included, spends one credit.
   RAPIDS sends a packet only when the counter covers all of it.
3. The cell or core returns credits when it has **consumed** the flits
   (written them to memory, or applied the `cfg`), not when they arrive. It
   may batch them, for example one return per packet.
4. The return is a `credit` packet to `level` 3 with the count in the length
   field. The sink port recognises it, never stores it, and passes {source
   coordinate, count} to the source half, which adds the count to that
   destination's counter.

Counters are per destination, not per channel: two channels writing the
same cell share that cell's buffer. Traffic routed through a node never
touches a counter. A node never replies, so a read request to a node's
internal ID is refused as an invalid descriptor; node registers are read
over MonBus or AXIL.

**Where a credit goes:** a credit packet is routed like any packet, by its
destination coordinate. A credit return goes to the source coordinate of
the packet whose flits it frees, so a cell returning credits to RAPIDS always
addresses `level` 3, and a credit return from RAPIDS goes to the cell or
core whose packet it consumed.

**Credits toward RAPIDS: straps, not grants** (owner direction
2026-10-18). A cell or core must never send into the sink port without
guaranteed space: flits that cannot drain stall in the routers and block
everything behind them, credit packets included. The space is fixed by
construction instead of granted at run time:

| Sender | Sends to RAPIDS | Credit |
|---|---|---|
| Cell (a cell-level node's external ID) | Memory writes (results, §11.14) | A strap of 16 flits, header included |
| Control core (a tetrad node's external ID) | `desc` packets (§11.11) | Entries in a source channel's descriptor queue |
| delta node | Nothing | None |

: Credits toward RAPIDS

1. Each sender starts from its strap after reset and sends a packet only
   while its counter covers the whole packet.
2. RAPIDS reserves every strap: a landing space of 16 flits per cell, and the
   descriptor-queue entries per core. The sink cannot be overcommitted
   however many senders send.
3. RAPIDS returns credits as it consumes, with a `credit`/`add` packet to the
   sender: flits when the data moves out of the landing space into its sink
   channel, one entry when the scheduler takes a descriptor.

The landing space is per sender: a cell whose data targets a full sink
channel holds only its own 16 flits, never another sender's. A packet to
RAPIDS is therefore at most 16 flits.

With end-to-end credits in both directions, every packet in the fabric has
guaranteed space at its destination and always drains.

Requirements this places on the implementation:
- **Deadlock:** a credit packet must never wait behind data that is itself
  waiting for credits. Credit packets ride their own virtual channel, and
  the sink port accepts them unconditionally.
- **RAPIDS:** the sink-to-source credit path inside the core, the 64-entry
  counter table (filled by the advertisements), the advertisement window and
  the saved legal-destination mask (§11.10); and toward RAPIDS, the 16-flit
  landing space per cell, the descriptor-queue entries per core, and the
  credit returns on the source port.
- **Cells and control cores:** buffer sizing, their own boot advertisement,
  return batching, building credit packets, and a strap counter toward
  RAPIDS.
- **delta nodes:** none of it. No credit state, no advertisement, no
  returns; they consume what is addressed to them without stalling. A
  virtual channel for `credit` packets.

### 11.10 Credit advertisement

Each side advertises its own credits in-band. Nothing is loaded from CSRs, so
the counts cannot drift from the hardware.

| `op` in a `credit` packet | Meaning | Used by |
|---|---|---|
| 0 = add | Add N to the counter | Credit returns, both directions |
| 1 = set | Replace the counter with N | Advertisements at boot, resync |

: Credit packet operations

**Boot:**
1. After reset every cell and control core sends one `set` credit packet to
   `level` 3, under its external ID, carrying its full input-buffer size in
   flits (owner direction 2026-10-18: the cell or core originates it; a
   delta node never does). RAPIDS's external counters start at 0, so RAPIDS
   cannot send to a cell or core that has not advertised. delta nodes do not
   advertise: they are legal by topology.
2. The advertisements ride delta's hardwired reset-default route toward the
   RAPIDS boundary (delta HAS ch07 §3), so no routing table is needed first.
3. They need no strap credit: credit packets travel on their own virtual
   channel and the sink port always accepts them.
4. The advertisement doubles as the cell's or core's "alive": RAPIDS
   accepts strap traffic only from a sender that advertised in the window.
5. **Legal destinations** (owner direction 2026-10-18). RAPIDS opens an
   advertisement window when it leaves reset. When the window closes, every
   node's internal ID is legal, and every external counter still at 0 marks
   an **illegal** destination: nothing there advertised, whether an absent
   cell, an absent core or a spare index. RAPIDS
   saves the result as a 64-bit legal-destination mask, one bit per counter.
   - A descriptor whose destination is illegal is refused as an invalid
     descriptor, not sent and not left waiting for credits that will never
     come.
   - Only the window decides legality. A legal destination whose counter
     later reaches 0 because its credits are spent is waiting, not illegal.
   - The mask is readable by software (a CSR) and stays as saved until the
     next reset.

**RAPIDS's side: straps, not advertisements.** RAPIDS never advertises its
free sink space as a total. If it broadcast "channel 3 has 512 flits free",
every cell would believe it could send 512 flits, and the sink would be
overcommitted many times over. Its space toward each sender is a fixed
strap instead (§11.9), reserved by construction.

**Resync after root failover:** credit packets in flight in the failed
root are lost. Without a resync the lost credits leak until the counters
reach zero and traffic stops.
1. After the mux switches, RAPIDS sends every cell and core a `set` credit
   packet, as one multicast, restoring its strap counter to what RAPIDS can
   now accept from it.
2. Each cell and core answers with a `set` advertisement of its current free
   input-buffer space.
3. RAPIDS rebuilds its counters from the answers. The saved legal-destination
   mask stands: a resync does not reopen the window, so it never waits on a
   destination that was illegal at boot.

A destination that leaves reset on its own uses the same path: its fresh
advertisement replaces RAPIDS's view of it.

### 11.11 Cell-issued descriptors

A tetrad's control core (gatling) can make RAPIDS read memory and send the
data to a cell by handing RAPIDS a complete source descriptor (owner
direction 2026-10-18: gatling creates the descriptors). It is a pull: the
core asks, the RAPIDS source half does the read and the send.

1. The core sends a `desc` packet to `level` 3 through RAPIDS's sink port: the
   header (tag = the source channel to run it on, length = 32) followed by one
   256-bit RAPIDS source descriptor in the ordinary format. `src_addr` is the
   memory to read; `dst_addr` carries the destination coordinate and target
   address (RAPIDS HAS, Descriptor Format); `ptype`, `op`, `length` and the
   chaining fields mean what they always mean.
2. The sink port recognises `desc`, never stores it in a sink channel's SRAM,
   and passes the descriptor to the source half, which writes it straight into
   the tagged channel's descriptor queue, with no fetch.
3. An idle channel starts on it, as if kicked with the descriptor already
   fetched. A busy channel runs it after the descriptors already queued. A
   non-zero next pointer chains on into memory-resident descriptors as usual.
4. The source half reads `src_addr` and sends the data, with a header built
   from the descriptor, out of the source port to the destination it names.

Flow control: a source channel's descriptor queue is finite, so a core sends
a `desc` packet only against its strapped descriptor-queue entries (§11.9,
credit class 1, tag = that source channel). RAPIDS returns an entry when the
scheduler takes the descriptor.

RAPIDS hardware this needs: a second write port into each source channel's
descriptor queue (the queue is already per channel in the shared descriptor
engine), and the sink-to-source path the credit returns already use.

### 11.12 RAPIDS implementation status (2026-10-17)

Built in the byte-granular RAPIDS behind `TILE_HDR` = 1 (default 0; needs
`SHARED_ENGINES` = 1 and `DATA_WIDTH` >= 256). RAPIDS Beats does not have it.

| Item | State |
|---|---|
| Header packing (§11.5), payload types (§11.2) | Built: `rapids_pkg::tile_hdr_pack`. The header is the first beat of every packet on both ports, bits [127:0]; on an AXIS plane it is that first beat too, not `TUSER` |
| Source header from the descriptor (§11.7) | Built. Tag = the channel, source coordinate = the `TILE_SRC_COORD` parameter (level 3). A data packet's header leaves only when its first data beat is ready, so the two go back to back. A source descriptor with a `ptype` other than `cfg`/`prog`/`mem` is refused as an invalid descriptor |
| Read request (`op` = 1) | Built: a header-only packet, no memory read. As for a write, the descriptor completes when its packet is queued, not when the header has left; a zero-length request sends nothing |
| Sink header decode | Built (`rapids_tile_hdr_rx`): `cfg`/`prog`/`mem` writes are stripped and delivered by stream ID; `credit`, read requests into RAPIDS and reserved types are consumed, never stalled, and counted or flagged |
| Sink stream = tag | On RAPIDS's sink link the stream ID (`CXSSRCID`, the channel) must equal the header tag: the root sets it from the tag. RAPIDS delivers by stream ID and flags a mismatch (`sts_tile_tag_mismatch`) |
| Cell-issued descriptors (§11.11) | Built, with a one-descriptor slot per source channel instead of descriptor grants: a `desc` with no free slot, one arriving during a channel reset, or an EXT one is dropped and sets that channel's sticky `sts_tile_desc_dropped` bit. The channel and the work it holds carry on |
| End-to-end credits (§11.9, §11.10) | Built behind `TILE_CREDITS` = 1 (2026-10-18): 64 destination counters in the source half, the internal and external ID of every node (`rapids_tile_credits`; index map §11.9), external counters filled by class-0 `set` / `add` credit packets from cells and cores; a packet to a cell or core leaves only when its counter covers every flit, header included. Node internal IDs are legal by topology, never held or charged, and their credit packets are ignored; a read request to a node is refused. The advertisement window (`SRC.TILE_ADV_WINDOW`, cycles from reset) closes into the saved 64-bit legal-destination mask (`SRC.TILE_LEGAL_DEST_LO` / `_HI`); tile descriptors wait for it and one to an illegal destination is refused as invalid. A channel reset does not refund credits already charged |
| Straps toward RAPIDS (§11.9, §11.11) | Not built: no per-cell 16-flit landing space, no strapped descriptor-queue entries per core, no credit returns from RAPIDS; RAPIDS ignores class-1 credits (rapids TASK-027) |
| Status | CSRs: `SNK.TILE_STATUS` and `SRC.TILE_DESC_DROPPED` (W1C), `SNK.TILE_COUNTS`, and for credits `SRC.TILE_LEGAL_DEST_LO` / `_HI` / `SRC.TILE_CREDIT_STATUS`; the same values on the top-level `sts_tile_*` ports |

### 11.13 Tetrad control core (owner direction 2026-10-17; deferred 2026-10-18)

**Deferral (owner direction 2026-10-18):** the tetrad engine is defined
**after the cell is fully defined and working** — the cell is the lowest
module (cell PRD v0.3 §1). The owner-authored
[`gatling-rv32itetrad`](../../../riscv-ip/gatling-rv32itetrad/PRD.md) barrel-core
PRD (2026-10-17) is the leading candidate, with kestrel-class remaining a
candidate flavor via `CORE_FLAVOR`. The model below stays recorded — frozen
— for when the engine work resumes; the in-band-everything rulings are
unaffected.

Each tetrad carries **one RV32I control core** — kestrel-class,
`CORE_FLAVOR`-swappable, defined with its full duty list in
[alu-infer PRD §5](../../alu-infer/PRD.md). The model, frozen here so
the tile records it:

- **Attach.** The core sits at its tetrad node's **local port**, the same
  relationship the cell has with its own node. It is not a routing level,
  carries no coordinate of its own, and is reached as its tetrad: `prog`
  and `cfg` packets addressed `{level = 1, tetrad X/Y}` (§11.3) exit the
  tetrad node's local port into the core. Its firmware load rides the
  existing `prog` payload type (§11.2) — in-band like everything else.
- **In-band everything, no config origination.** All data, config, and
  programming for the tile blocks arrive with the delta traffic (owner
  ruling 2026-10-17). The core does not originate config traffic: the
  cells' programming (`FUNC_SEL`, `OP_LINES`, …) arrives in-band
  addressed to each cell (`level = 0`), carried by the stream. The core
  is a **local reaction agent**: it reads its four cells' status and IRQs
  over the local AXIL register plane, runs decision firmware
  (layer-boundary detection, flush policy), and exercises *operational*
  registers only (flush-and-send, soft reset, IRQ clear — the
  AXIL-for-registers plane, not fabric config).
- **Custom instructions stay minimal** (a custom-0 kick/wait pair for
  local coordination); encoding lands in the cell/tetrad MAS (§10).
- **Observability is unchanged.** SERV and the MonBus aggregation (§5)
  remain the tile's observability plane; the core reads registers and
  reacts — it takes no MonBus tap by default.
- **Why per-tetrad.** Four independent control points per tile (one per
  tetrad) allow layer pipelining across tetrads and one group-done per
  four cells, without sixteen instruction streams. A tetrad steps as
  4 cells × 2 bf16 lanes = 8 bf16 lanes.

### 11.14 Result flush to the tile I/O (owner direction 2026-10-18)

Delta **must** be able to carry a cell's result data to `level` 3, the tile
I/O, and so into RAPIDS. It is the path computed results leave the tile by:

1. **Detect.** Gatling, the tetrad engine (§11.13), detects a
   flush-to-memory condition. When to flush is program policy, not fixed
   hardware.
2. **Command.** Gatling sends a flush command to the result drain
   controller in each cell it applies to. **Gatling tells the cell the
   destination** (owner direction 2026-10-18): the cell does not choose it
   and does not need to know where RAPIDS attaches.
3. **Drain.** The controller pushes the cell's result memory out through
   the packetizer: write-format packets (`op` = 0) to `{ext 0, level 3}`,
   source = the cell's external ID `{1, 0, X, Y, Z}`, tag = the RAPIDS sink
   channel, each sent against the cell's 16-flit strap (§11.9).
4. **Carry and land.** Delta routes each packet to the tile I/O. RAPIDS's
   sink strips the header and delivers the data by tag into that sink
   channel, which writes it to memory.

| Link | State |
|---|---|
| Gatling detects and commands | Not defined: gatling PRD v0.1 has no flush instruction, and the engine is deferred until the cell works (§11.13) |
| Cell drain controller | Not built: the cell PRD has the packetizer and `CTRL` flush-and-send; no cell RTL beyond alu-infer |
| Delta to `level` 3 | Interim: delta has no `level` field, so the destination gatling hands the cell includes the attach cell's delta coordinate, and the cell writes it into delta's header; delta needs no change for that. Permanent: `level` and `ext` in delta's header (delta DELTA-011) |
| RAPIDS sink delivery by tag | Built (§11.12) |
| Straps toward RAPIDS | Not built (rapids TASK-027). Without the reserved landing space a drain into a full sink channel stalls in the routers |

## References

- [`docs/superpowers/specs/2026-10-13-delta-mesh-design.md`](../../../../../docs/superpowers/specs/2026-10-13-delta-mesh-design.md) — working design record (§2 architecture, §5.4 mode catalog).
- [`3d-mesh-tile.drawio`](assets/3d-mesh-tile.drawio) — owner's K4-at-both-scales figure.
- [`delta_has/ch07_mesh_network/`](../../../fabric-gen-ip/delta/docs/delta_has/ch07_mesh_network/) — the node/network chapters in delta's HAS (cell/flit, routing, flow control, QoS, multicast, modes, observability, verification).
- [`noc-ip/delta_spec`](../../../noc-ip/delta_spec) — the aspirational NoC draft this subsystem grew out of.

---

**Last Updated:** 2026-10-18
**Maintained By:** RTL Design Sherpa Project
