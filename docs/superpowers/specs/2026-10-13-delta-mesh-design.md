# Delta Mesh Mode — Design Spec

**Date:** 2026-10-13
**Status:** draft, pending owner review
**Component:** `projects/components/fabric-gen-ip/delta`
**Scope:** new mesh generation mode alongside the existing flat TDEST crossbar

## 1. Overview

Delta gains a `--topology mesh` mode that generates a 3-D, table-routed,
QoS-aware mesh network of identical cells. The existing flat
`delta_axis_flat_<M>x<N>` TDEST crossbar is untouched and remains the
default. Mesh mode targets the monitored manycore fabric: SERV + CGRA
compute cells interconnected by delta, observed by ocelus, fed by rapids
DMA at the boundary. Cell contents (SERV/CGRA/ocelus) are **out of
scope** — delta sees only streams at its local ports.

Feature sources: four-book survey of the calibre NoC library
(Duato *Interconnection Networks*; Dally & Towles *Principles and
Practices*; *Networks on Chip* edited volume; *Network Processor Design*).
Citations inline as (Book ch §).

## 2. Architecture

### 2.1 Hierarchy

- **Cell** — the one and only RTL design delta emits (`delta_mesh_cell`).
- **Tile** — 2×2×1 cells (4). Routing/config grouping, not separate RTL.
- **Confluence** — 2×2×1 tiles = 4×4×1 cells (16). Connects to rapids at
  boundary cells' local ports. (Owner-named 2026-10-13.)
- **Fabric** — 4×4×K confluences stacked in Z. The recursion is planar;
  the Z dimension lives entirely between confluence layers.

Rapids attaches at boundary cells' local ports; any boundary cell can be
a rapids attachment. Intra-tile and intra-confluence hops are hops like
any other — the hierarchy exists to bound table sizes and to name
address regions, not to add wrapper hardware.

### 2.2 Cell ports

- 6 neighbor ports: ±X, ±Y, ±Z. Wrap links are parameterizable per
  dimension (§7.1).
- 1 local port (host-facing; rapids at boundary cells).
- All ports AXI4-Stream: `TDATA/TVALID/TREADY/TLAST` + header sideband in
  `TUSER` (§4). Optional AMBA 5 check/TWAKEUP richness carries over from
  flat mode unchanged.

Single clock domain, active-low async `aresetn` (house `ALWAYS_FF_RST`).
Single clock is a deliberate simplification contrary to the GALS
assumption in the NoC literature (NoC-vol ch.10 §3.1) — documented
trade: timing closure and generator predictability over clock flexibility.

## 3. Cell microarchitecture

Per-port input buffers, one per VC (2 VCs/port, §6), partitioned
single-port readout per (NoC-vol ch.10 §4.3: per-VC reservation avoids
deadlock). Pipeline stages: **buffer write → route compute → VC
allocation → switch allocation → crossbar traversal**, with:

- **Route lookahead** (D&T ch.16 §16.5): next hop's output port computed
  one hop ahead; collapses steady-state per-hop latency toward 1 cycle.
- Optional speculative VA+SA (D&T ch.16 §16.5), enabled per build.
- Allocators use existing house arbiters: `arbiter_matrix` (D&T ch.17
  §17.5 — "favorite arbiter for small numbers of inputs") for per-output
  VC arbitration; round-robin/iSLIP-style for switch allocation (D&T
  ch.18 §19.3 — one-pass separable saturates ~66%, iSLIP reaches 100%).
- Multicast port-mask requests allocate incrementally over cycles (D&T
  ch.19): serve whichever masked outputs are free each cycle; release
  input when all served.

Credit-based flow control per VC. Credit counter depth sized to cover
round-trip latency: `F · Lf / tcrt ≥ b` (D&T ch.13 §13.3, ch.16 §16.3).

## 4. Flit format

Flit = one `DATA_WIDTH` beat. Packet = head flit + body flits + TLAST.
Header lives in a `TUSER` sideband on the head beat (payload streams
pass transparently — same principle as flat mode's TDEST handling):

| Field | Width | Notes |
|---|---|---|
| dest coord | 3×COORD_W | X,Y,Z; COORD_W sized by fabric dims |
| src coord | 3×COORD_W | for responses/counters |
| QoS class | 2 | 0=config, 1=latency, 2=bulk |
| VC | 1 | assigned at injection per §6 |
| multicast | 1 | with group/mask ref §5 |
| misroute budget | 3 | decremented on non-minimal hop; packet drops at 0 (§6.3) |
| source-route ptr | 4 | valid when SR mode set; indexes inline port list (§7.3) |

## 5. Routing

### 5.1 Tables

Per-cell RAM, keyed `(dest coord, QoS class)` → `{output port mask, VC}`.
Default content at reset: **dimension-ordered route toward the rapids
boundary** — hardwired, connected, and acyclic by construction; this is
the bootstrap path for in-band config (owner decision 2026-10-13).

Constraints (literature-mandated):

- VC1 table routes must be **minimal** or must not create indirect
  dependences on VC0 (Duato ch.4 §4.4; D&T ch.14 §14.3). Non-minimal
  entries are allowed only with a misroute budget (§4) and consume VC1.
- VC0 table entries must form a connected, acyclic subrelation
  (extended channel dependency graph) — a checked property at table-load
  time (verification suite), not just at reset.
- QoS path diversity: independent routes per class per destination
  (owner decision); realized simply as independent table regions.

### 5.2 In-band configuration

Config packets target a reserved address; the cell's ejection block
intercepts them instead of delivering to the local port. Format:
`{op (read/write), entry index, entry data}`; reads return response
packets to the source (load-verify). Config rides QoS class 0 over the
default route; a boundary cell or rapids injects. Per-cell unicast load
(owner decision): N cells × M entries writes at boot, plus runtime
re-route. Distribution of an identical table image by multicast is
possible but not required (deferred with logical addressing, §11).

### 5.3 Multicast

- Port-mask table entries, restricted to VC0.
- Multicast paths must conform to the base unicast routing (BRCP, Duato
  ch.5 §5.5.3) so multicast adds no new channel dependencies beyond the
  unicast proof.
- **Source-side replication** at the branching cell (NPU-book lesson,
  Toaster §11.3): enqueue one copy per masked output rather than
  broadcasting and filtering.
- **Multiple delivery VCs** at each cell for multicast reception
  (Duato ch.5 §5.5.3 — delivery-channel deadlock otherwise).
- **No responses on multicast connections** (Ethereal, NoC-vol ch.4
  §4.1.2). Many-to-one uses unicast narrowcast, not multicast.

## 6. Deadlock, livelock, QoS

### 6.1 Two VCs, escape-channel scheme (owner decision)

- VC0 = escape: reset-default and turn-model-conforming routes only;
  provably deadlock-free (Duato's Protocol, ch.4 §4.4; validated by
  both survey fronts).
- VC1 = full table freedom (QoS alternates, minimal-or-budgeted).
- VC1→VC0 transition permitted at any hop; VC0→VC1 forbidden
  (D&T ch.14 §14.3). Packets in VC1 can always drain into VC0, breaking
  cycles.

### 6.2 QoS classes (owner decision: 3, strict priority + aging)

- Class 0 config/control, class 1 latency, class 2 bulk.
- Strict priority at every output port with **programmable aging**
  (SPIDER/21364 style, Duato ch.7 §7.2.3).
- **Non-interference**: separate VCs *and* separate injection buffers
  per class (D&T ch.14/15 tree-saturation lesson). Config class gets its
  own VC0 slice so control traffic can never be bulk-blocked.
- **Bulk minimum reservation**: aging alone is insufficient (Duato ch.3
  intro): a guaranteed slot fraction per arbitration window for class 2.

### 6.3 Livelock

Non-minimal hops decrement the misroute budget (§4); at 0 the packet is
dropped and counted (observability). Minimal routing is the normal case;
budget exists to bound the VC1 alternates.

## 7. Systolic & common-pattern support (owner requirement)

First-class patterns: systolic chains/wavefronts, 3-D stencil halos,
nearest-neighbor streaming, broadcast/multicast, gather/scatter.

### 7.1 Torus wrap links (parameter `--torus=x,y,z` per dimension)

Periodic boundary conditions and uniform nearest-neighbor latency
(D&T ch.5 §5.1–5.3); halves diameter vs mesh. Folded implementation so
wire length doubles, not K. Deadlock note: a wrap channel creates a
cycle that plain DOR cannot break, so each wrapped dimension enforces a
**dateline** — one designated wrap channel per dimension participates in
VC0 only through the escape subrelation (D&T ch.14 §14.2 dateline
technique); wrap traffic otherwise uses VC1 with the misroute budget.

### 7.2 Route lookahead

§3 — the latency-critical piece for systolic repeat-cycle timing.

### 7.3 Source-route mode

Injection shim can carry an inline port list in the head-flit header
(source routing, D&T ch.11 §11.1): intermediate cells forward without a
table lookup — fixed-latency, table-free paths for static systolic
schedules. Node-table routing remains the default for dynamic traffic.

## 8. Observability (ocelus counter suite)

Per port, per VC, readable registers (NPU-book practice: IXP2400
performance monitors, Toaster per-queue stats):

- flit counts (sent/received), packet counts (TLAST)
- stall cycles per VC, arbitration win/loss per class
- queue occupancy (current/max watermark)
- injection-to-ejection latency min/avg/max + jitter, optional head-flit
  timestamps at boundary cells
- multicast replication count, misroute-drop count, credit starvation events

Counters freeze on `aresetn` clear; read via the config port (§5.2).

## 9. DFT test mode

Test mode configures each cell into three deterministic routing patterns
(NoC-vol ch.7 §5.3) so the mesh wiring behaves as a concatenated bus;
stuck-at and bridge faults testable with ~⌈log₂(n)⌉ patterns. Controlled
via the config port; a `test_active` output per cell.

## 10. Performance model (`bin/delta_mesh_perf.py`)

- Zero-load latency `T0 = H·tr + D/v + L/b`; per-hop queuing as M/D/1
  under deterministic flit service (D&T ch.3 §3.3, ch.23 §23.2).
- Saturation throughput from max channel load γ_max (bisection bound /
  multicommodity flow) (D&T ch.23 §23.1).
- Traffic patterns: uniform random, nearest-neighbor/stencil, tornado,
  bit-complement, transpose (D&T ch.3 §3.2 — adversarial set).
- Methodology: infinite source queues, warm-up/measurement/drain
  phases, latency measured from generation to departure (D&T ch.23 §23.1).

## 11. Deferred (recorded, not in this spec)

- **GT/TDM slot-table circuits** (Ethereal) — hard-real-time class,
  headerless flits. Phase 2 candidate.
- **Fault-tolerant routing** — block fault regions, software
  absorb/reinject, fault-status registers (Duato ch.6).
- **Barrier/superstep sync wave** (ECLIPSE) — lands with the CGRA work,
  not delta.
- **Express channels/cubes** — D&T ch.5 §5.4 warns of little use at our
  radix; skip.
- **Logical-to-physical address mapping** — with it, broadcast table
  images; revisit if remapping/fault-recovery demands it.
- **GALS/async links** — contrary to NoC-vol ch.1 assumption; single
  clock is deliberate (§2.2).
- **VOQ option** — possible compile-time area/throughput trade
  (NoC-vol ch.4 §4.2.2); add when a user needs it.

## 12. Generator interface

```
delta_generator.py --topology mesh \
  --cells-x 4 --cells-y 4 --cells-z K \
  [--torus=x,y,z] [--source-route] [--speculation] \
  [--data-width N] [--user-width N] [--amba5] [--no-counters] ...
```

Emits `delta_mesh_cell.sv` (one cell; hierarchy is placement + docs,
not wrappers) plus a fabric top that instantiates the 4×4×K grid,
parameterizes coordinates/wrap links, and exposes boundary local ports
(rapids attach points).

## 13. Verification plan

cocotb suites (each a generator-config + test file):

1. **Routing** — default DOR at reset; programmed-table routing; table
   load via config port + readback verify.
2. **QoS** — strict priority order; aging inversion under saturation;
   bulk minimum reservation; class isolation under tree-saturation
   attack.
3. **Multicast** — fanout correctness, no-response rule, delivery-VC
   deadlock soak.
4. **Deadlock soak** — random traffic under adversarial-but-valid random
   tables, plus VC1 stress with VC0 escape; soak to N×10⁶ flits.
5. **Systolic** — torus nearest-neighbor ring/wavefront with measured
   per-hop latency (lookahead target: 1 cycle steady-state); source-route
   fixed-latency path check; 3-D stencil halo exchange.
6. **Counters** — every §8 counter against golden model.
7. **DFT mode** — three patterns route correctly; pattern count check.
8. **Perf model calibration** — measured vs modeled latency/throughput
   on the §10 patterns; report deltas.

Formal assists: VC0-table acyclicity checker (offline, on table images);
one-hot grant assertions per output; TLAST-before-grant-release
assertion (packet atomicity, as flat mode does).

## 14. Decision log (owner decisions 2026-10-13)

| Decision | Choice |
|---|---|
| Hierarchy | 4 cells (2×2×1) = tile; 4 tiles = confluence; recursion, planar, Z between layers |
| Rapids attach | boundary cells' local ports |
| Cell RTL | one module; hierarchy is not RTL |
| Config | in-band, per-cell RAM tables, unicast load |
| Bootstrap | safe default route at reset |
| Tables enable | QoS path diversity + multicast |
| QoS | 3 classes, strict priority + aging (+ bulk reservation, from survey) |
| Deadlock | 2 VCs, escape-channel scheme |
| Multicast discipline | BRCP + source replication + delivery VCs + no-response (from survey) |
| Flat xbar | kept; mesh is a mode |
| Book pulls now | systolic package, perf model, ocelus counters, DFT mode |
| Book pulls deferred | §11 list |
