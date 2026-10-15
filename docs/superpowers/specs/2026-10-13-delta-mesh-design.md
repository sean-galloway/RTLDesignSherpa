# Delta Mesh Mode — Design Spec

**Date:** 2026-10-13
**Status:** draft, pending owner review
**Component:** `projects/components/fabric-gen-ip/delta`
**Scope:** new mesh generation mode alongside the existing flat TDEST crossbar

Citation keys: **[D*]** Duato et al., *Interconnection Networks*; **[P*]**
Dally & Towles, *Principles and Practices of Interconnection Networks*;
**[N*]** Jantsch & Tenhunen (eds.), *Networks on Chip*; **[Q*]**
Franklin et al. (eds.), *Network Processor Design: Issues and Practices*.
Full bibliography and library paths: §15. Decision→source traceability: §16.

## 1. Overview

Delta gains a `--topology mesh` mode that generates a 3-D, table-routed,
QoS-aware mesh network of identical cells. The existing flat
`delta_axis_flat_<M>x<N>` TDEST crossbar is untouched and remains the
default. Mesh mode targets the monitored manycore fabric: SERV + CGRA
compute cells interconnected by delta, observed by ocelus, fed by rapids
DMA at the boundary. Cell contents (SERV/CGRA/ocelus) are **out of
scope** — delta sees only streams at its local ports.

Feature sources: four-book survey of the calibre NoC library
(§15). Citations inline.

## 2. Architecture

### 2.1 Hierarchy

- **Cell** — the one and only RTL design delta emits (`delta_mesh_cell`).
- **Tetrad** — 2×2×1 cells (4). Owner-named 2026-10-15 (was "tile");
  every tetrad is fully connected K4 (§2.2). Routing/config grouping,
  not separate RTL.
- **Tile** — 2×2×1 tetrads = 4×4×1 cells (16). Owner-named 2026-10-15
  (was "confluence"); K4 at the tetrad level too — each tetrad connects
  to the other three tetrads of its tile (§2.2 P_DIA2). Connects to
  rapids at boundary cells' local ports.
- **Fabric** — 4×4×K tiles stacked in Z. The recursion is planar;
  the Z dimension lives entirely between tile layers.

Rapids attaches at tile boundary cells' local ports; any boundary cell
can be a rapids attachment. Hive configuration (owner, 2026-10-15): one
or more tiles — only one for now — connect to a single rapids DMA.
Intra-tetrad and intra-tile hops are hops like
any other — the hierarchy exists to bound table sizes and to name
address regions, not to add wrapper hardware. (The superswitch idea —
grouping 2×2 switches so a message reaches any switch in the local
group in one cycle — is the same recursion seen in ECLIPSE [N7]; we take
the grouping but not the single-cycle guarantee.)

### 2.2 Cell ports

- 6 neighbor ports: ±X, ±Y, ±Z. Wrap links are parameterizable per
  dimension (§7.1).
- 1 diagonal port: P_DIA, to the diagonally-opposite cell of the cell's
  2×2×1 tetrad (owner decision 2026-10-15: every tetrad is fully
  connected K4 — 4 perimeter edges over ±X/±Y plus both diagonals).
  One link per cell, always emitted; the fabric draws one diagonal wire
  pair per tetrad between (x,y,z) and (x^1,y^1,z). In 3-D, tetrads are
  planar (X/Y only); Z expansion stays axis-routed.
- 1 inter-tetrad diagonal port: P_DIA2 (owner decision 2026-10-15):
  the four tetrads of a tile are themselves fully connected K4. The
  link joins adjacent tetrad corner cells — (x,y,z) to the diagonally
  adjacent cell of the diagonally-neighboring tetrad, e.g. (1,1,0)↔
  (2,2,0) and (1,2,0)↔(2,1,0) per tile — direction set by the cell's
  position within its tetrad. Always emitted; edge cells whose mate
  tetrad is out of grid tie P_DIA2 off (provably never selected: the
  mate coordinate is out of grid, and mode images only name in-grid
  ports).
- 1 local port (host-facing; rapids at tile boundary cells).
- All ports AXI4-Stream: `TDATA/TVALID/TREADY/TLAST` + header sideband in
  `TUSER` (§4). Optional AMBA 5 check/TWAKEUP richness carries over from
  flat mode unchanged.

Single clock domain, active-low async `aresetn` (house `ALWAYS_FF_RST`).
Single clock is a deliberate simplification *contrary* to the GALS
assumption in the NoC literature [N1][N8: GALS §3.1] — documented
trade: timing closure and generator predictability over clock
flexibility.

## 3. Cell microarchitecture

Per-port input buffers, one per VC (2 VCs/port, §6), partitioned
single-port readout per input [P18: §17.1 — per-VC cell reservation is
required to avoid deadlock]. Pipeline stages: **buffer write → route
compute → VC allocation → switch allocation → crossbar traversal**, with:

- **Route lookahead** [P17]: next hop's output port computed one hop
  ahead; collapses steady-state per-hop latency toward 1 cycle.
- Optional speculative VA+SA [P17], enabled per build.
- Allocators use existing house arbiters: `arbiter_matrix` — D&T's
  "favorite arbiter for small numbers of inputs" [P19: §18.5] — for
  per-output VC arbitration; round-robin/iSLIP-style switch allocation
  (one-pass separable allocators saturate ~66%, iSLIP reaches 100%
  [P19: §19.3, §19.7]).
- Multicast port-mask requests allocate incrementally over cycles:
  serve whichever masked outputs are free each cycle, release the input
  once all are served [P18: §17.2][P19: §19 exercises].
- Conservative output-VC reallocation: wait for the downstream credit to
  return before reassigning the VC, so reallocation cannot introduce a
  dependency that breaks the deadlock analysis [P16].

Credit-based flow control per VC. Credit counter depth sized to cover
round-trip latency: `F · Lf / tcrt ≥ b`, else the channel duty factor
drops below one [P10][P15].

## 4. Flit format

Flit = one `DATA_WIDTH` beat. Packet = head flit + body flits + TLAST.
Header lives in a `TUSER` sideband on the head beat (payload streams
pass transparently — same principle as flat mode's TDEST handling).
Configurable header/payload split with explicit end-of-packet sideband,
Proteo-style [N8: §3.4]:

| Field | Width | Notes |
|---|---|---|
| dest coord | 3×COORD_W | X,Y,Z; COORD_W sized by fabric dims |
| src coord | 3×COORD_W | for responses/counters |
| QoS class | 2 | 0=config, 1=latency, 2=bulk |
| VC | 1 | assigned at injection per §6 |
| multicast | 1 | with group/mask ref §5.3 |
| misroute budget | 3 | decremented on non-minimal hop; packet dropped + counted at 0 (§6.3) [D4][P13] |
| source-route ptr | 4 | valid when SR mode set; indexes inline port list (§7.3) [P8] |
| packet ID | 4 | reorder tolerance at endpoints under multi-VC/adaptive routing [N8: §3.4][N3: §4.1.3] |

## 5. Routing

### 5.1 Tables

Per-cell RAM table lookup is the standard node-table implementation
[D5][P8]; its per-hop lookup penalty is the motivation for §7.3
source-routing [P8]. Keyed `(dest coord, QoS class)` → `{output port
mask, VC}`. Default content at reset: **dimension-ordered route toward
the rapids boundary** — hardwired, connected, and acyclic by
construction [D5][P11]; this is the bootstrap path for in-band config
(owner decision 2026-10-13).

Constraints (literature-mandated):

- VC1 table routes must be **minimal** or must not create indirect
  dependences on VC0 [D7][P12]. Non-minimal entries are allowed only
  with a misroute budget (§4) and ride VC1.
- VC0 table entries must form a connected, acyclic subrelation in the
  extended channel-dependency graph — Duato's sufficient condition for
  deadlock freedom [D2][D7] — checked at table-load time (verification
  suite), not just at reset.
- Routing function may depend on (input VC, dest) as well as dest —
  richer turn/escape policies [D3] — encoded by the table's VC field.
- QoS path diversity: independent routes per class per destination
  (owner decision); realized as independent table regions.

### 5.2 In-band configuration

Config packets target a reserved address; the cell's ejection block
intercepts them instead of delivering to the local port. Format:
`{op (read/write), entry index, entry data}`; reads return response
packets to the source (load-verify). Config rides QoS class 0 over the
default route; a boundary cell or rapids injects. Per-cell unicast load
(owner decision): N cells × M entries writes at boot, plus runtime
re-route. A **broadcast mode-switch** message for standard fabric modes
coexists with unicast loading (§5.4). (NPU precedent: control sequences
may be supplied *along with
the packet* — config flits carry their own program, not just an index
[Q6]; we implement the table-read/write form now and keep the
action-program form as a table-entry extension.)

### 5.3 Multicast

- Port-mask table entries, restricted to VC0.
- Multicast paths must conform to the base unicast routing (BRCP) so
  multicast adds no new channel dependencies beyond the unicast proof
  [D9].
- **Source-side replication** at the branching cell (Toaster/CellBus/Q-5
  precedent: enqueue one copy per destination [Q7]) rather than
  broadcasting everywhere and filtering.
- **Multiple delivery VCs** at each cell for multicast reception —
  delivery-channel deadlock otherwise, even under correct routing
  [D9: §5.5.3 deadlocks in delivery channels].
- **No responses on multicast connections** (Ethereal connection model:
  responses create volume/merge problems) [N3: §4.1.2]. Many-to-one uses
  unicast, not multicast.
- Tree-based multicast in wormhole networks deadlocks readily [D9:
  §5.5.2]; the BRCP + replication + delivery-VC combination above is the
  book-recommended discipline [D9: §5.5.3].

### 5.4 Standard fabric modes (owner decision 2026-10-13, amended)

Alongside per-cell unicast table loading, delta defines a **broadcast
mode-switch** config message: a broadcast packet carries a mode ID;
every cell holds generator-emitted images for the standard modes (ROM
or preloaded RAM) and switches atomically. Atomicity rule: the new mode
applies only after a fabric-wide ack barrier — each cell returns its
config read-response ack, and the injector treats the mode as active
when all acks are in. No packet straddles two modes. Custom mode (the
per-cell unicast tables of §5.2) coexists; mode 0 = custom, mode
switches among standard images, custom tables unaffected by broadcast
switches.

Standard mode catalog (modes 1-8 owner-confirmed 2026-10-13; modes 9-10 added 2026-10-15):

| Mode | Pattern | Routing/table content | Sources |
|---|---|---|---|
| 1 Mesh (default) | generic packet switching | RAM tables, reset DOR default | §5.1 |
| 2 Systolic-1D | linear nearest-neighbor chains, row/column selected, optional torus ring | fixed source-route paths, 1-cycle/hop steady state | [P8][P17][S1] |
| 3 Wavefront-2D | 2-D diagonal ripple, E/W + N/S skewed streams | per-diagonal static table/source routes | [S1][S2][N7] |
| 4 Stencil-3D | 3-D halo/ghost-zone exchange, periodic boundaries | nearest-neighbor tables + torus wrap all dims | [P3][P4][P5] |
| 5 Broadcast | one-to-all | multicast VC0, port masks to all | [D9][N3] |
| 6 Convergecast/reduce | all-to-one reduction tree | reverse-broadcast tables; ocelus counter reduction | [D9][Q7] |
| 7 All-to-all/transpose | permutations: transpose, shuffle/butterfly stages | per-stage table images | [P1] |
| 8 Pipeline + rapids-stream | boustrophedon serpentine chain; boundary↔rapids DMA streaming | fixed chain + boundary tables | [P8][Q9] |
| 9 Tetrad all-to-all (K4) | every 2×2×1 tetrad fully connected: perimeter via ±X/±Y, both diagonals via P_DIA | intra-tetrad table entries route edge-mates 1 hop and the diagonal mate via P_DIA (1 hop); inter-tetrad dsts DOR | owner, 2026-10-15 |
| 10 Tile all-to-all (K4 of tetrads) | the 4 tetrads of a tile fully connected: edge-adjacent tetrads via shared ±X/±Y boundaries, diagonal tetrad pairs via P_DIA2 | intra-tile table entries route to any cell of any tetrad of the tile 1..2 hops (diagonal-of-tetrad pairs via P_DIA2 single hop); inter-tile dsts DOR | owner, 2026-10-15 |

Mode images are data — the same table RAMs and mechanisms as §5.1;
adding a mode = adding an image + a verification suite, no new hardware
per mode. (Exception, modes 9-10: the P_DIA/P_DIA2 diagonal ports of
§2.2 are their enabling hardware, emitted in every build.)

## 6. Deadlock, livelock, QoS

### 6.1 Two VCs, escape-channel scheme (owner decision)

- VC0 = escape: reset-default and turn-model-conforming routes only.
- VC1 = full table freedom (QoS alternates, minimal-or-budgeted).
- This is Duato's Protocol — one adaptive channel set + one
  deterministic escape set, deadlock-free when the escape subrelation is
  connected and acyclic [D7][D2]; D&T restates the same theorem and its
  VC-transition rules [P12]. For 2-D meshes the canonical instance uses
  exactly 2 VCs; 3-D mesh is consistent (tori would need more [D7]) —
  our mesh + dateline-on-wrap rule (§7.1) stays in the 2-VC budget.
- VC1→VC0 transition permitted at any hop; VC0→VC1 forbidden
  [P12]. Packets in VC1 can always drain into VC0, breaking cycles.

### 6.2 QoS classes (owner decision: 3, strict priority + aging)

- Class 0 config/control, class 1 latency, class 2 bulk — the
  control/data-plane priority split of real NPU practice [Q4][Q5].
- Strict priority at every output port with **programmable aging**
  (SPIDER's programmable aging rate; 21364's explicit antistarvation
  bit) [D13].
- **Non-interference**: separate VCs *and* separate injection buffers
  per class — tree saturation blocks unrelated traffic through shared
  buffers even with priority bits [P14: §15.5]. Config class gets its
  own VC0 slice so control can never be bulk-blocked.
- **Bulk minimum reservation**: strict priority starves the lowest
  class unless bandwidth is reserved for it [D1]; ASPEN caps consecutive
  higher-priority cells then forces bulk service [Q5]. Aging alone is
  not sufficient [D1].
- Within-class fairness (per-flow queues, WRR/DRR) is a known
  enhancement [P14: §15.4][Q9: IXP WRR/DRR]; deferred until a user asks.

### 6.3 Livelock

Livelock only arises with non-minimal routing; the book remedies are
minimal routing or a bounded misroute count in the header [D4][P13].
Non-minimal hops decrement the misroute budget (§4); at 0 the packet is
dropped and counted (observability, §8). Minimal routing is the normal
case; the budget bounds the VC1 alternates.

## 7. Systolic & common-pattern support (owner requirement)

First-class patterns: systolic chains/wavefronts, 3-D stencil halos,
nearest-neighbor streaming, broadcast/multicast, gather/scatter.

### 7.1 Torus wrap links (parameter `--torus=x,y,z` per dimension)

Periodic boundary conditions, edge-symmetry restoration, and halved
diameter [P3][P4]; folded implementation so wire length doubles, not K
[P5]. Deadlock note: a wrap channel creates a cycle that plain DOR
cannot break, so each wrapped dimension enforces a **dateline** — one
designated wrap channel per dimension participates in VC0 only through
the escape subrelation [P11: dateline technique]; wrap traffic otherwise
uses VC1 with the misroute budget. (Express cubes were considered and
skipped — little use at our radix [P6].)

### 7.2 Route lookahead

§3 [P17] — the latency-critical piece for systolic repeat-cycle timing.

### 7.3 Source-route mode

Injection shim can carry an inline port list in the head-flit header:
intermediate cells forward without a table lookup — fixed-latency,
table-free paths for static systolic schedules [P8]. Node-table routing
remains the default for dynamic traffic. (ECLIPSE likewise programs
static routes for its PRAM/systolic workloads [N7].)

## 8. Observability (ocelus counter suite)

Per port, per VC, readable registers — NPU practice: IXP2400
programmable performance monitors [Q4], Toaster per-queue latency /
min/max / jitter statistics [Q2], RMON-style timestamp+sequence at line
rate [Q8: ASI]:

- flit counts (sent/received), packet counts (TLAST)
- stall cycles per VC, arbitration win/loss per class
- queue occupancy (current / max watermark)
- injection-to-ejection latency min/avg/max + jitter; optional head-flit
  timestamps at boundary cells [Q8]
- multicast replication count, misroute-drop count, credit starvation events

Counters clear on `aresetn`; read via the config port (§5.2). (The NoC
literature is thin on hardware observability — this suite is ahead of
the books, informed by NPU practice rather than NoC texts.)

## 9. DFT test mode

Test mode configures each cell into three deterministic routing patterns
so the mesh wiring behaves as a concatenated bus; stuck-at and bridge
faults testable with ~⌈log₂(n)⌉ patterns [N6]. Controlled via the config
port; a `test_active` output per cell.

## 10. Performance model (`bin/delta_mesh_perf.py`)

- Zero-load latency `T0 = H·tr + D/v + L/b`; per-hop queuing as M/D/1
  under deterministic flit service [P2][P20].
- Saturation throughput from max channel load γ_max (bisection bound /
  multicommodity flow); report minimum delivered flow, not average
  [P2][P20].
- Traffic patterns: uniform random, nearest-neighbor/stencil, tornado,
  bit-complement, transpose [P1].
- Methodology: infinite source queues, warm-up / measurement / drain
  phases, latency measured from generation to departure [P20];
  loaded-latency microbenchmarks per NPU benchmarking practice [Q1].
- (Network-calculus delay/backlog bounds for the fixed-priority classes
  [Q3] are a phase-2 analysis addition.)

## 11. Deferred (recorded, not in this spec)

- **GT/TDM slot-table circuits** — Ethereal/NoC slot tables, headerless
  GT flits, end-to-end credit flow control, optional VOQ [N2][N3][N4].
  Phase-2 candidate.
- **Fault-tolerant routing** — block fault regions, software
  absorb/reinject, fault-status registers [D10][D11][D12].
- **Barrier/superstep sync wave** — ECLIPSE synchronization wave [N7];
  lands with the CGRA work, not delta.
- **Express channels/cubes** — little use at our radix [P6]; skip.
- **Logical-to-physical address mapping** — with it, broadcast table
  images; revisit if remapping/fault-recovery demands it.
- **GALS/async links** — contrary to [N1][N8]; single clock is
  deliberate (§2.2).
- **VOQ option** — area/throughput trade [N2]; add when a user needs it.
- **Within-class per-flow fairness (WRR/DRR)** [P14: §15.4][Q9].
- **Flit-reservation flow control** — circuit-like streaming latency
  [P9: §13.4]; revisit if systolic latency targets aren't met by §7.2.
- **Reliable-mode resend/NACK** — Proteo re-send packets [N8: §3.3];
  only if a control-plane user needs lossless delivery beyond class-0
  VC isolation.

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
(rapids attach points). FIFO implementation (regs vs SRAM) is a
generator knob — buffer area dominated NoC node area in Proteo synthesis
(81% FIFO flops) [N8: §4.5].

## 13. Verification plan

cocotb suites (each a generator-config + test file):

1. **Routing** — default DOR at reset; programmed-table routing; table
   load via config port + readback verify.
2. **QoS** — strict priority order; aging inversion under saturation;
   bulk minimum reservation; class isolation under tree-saturation
   attack [P14: §15.5].
3. **Multicast** — fanout correctness, no-response rule, delivery-VC
   deadlock soak [D9].
4. **Deadlock soak** — random traffic under adversarial-but-valid random
   tables, plus VC1 stress with VC0 escape; soak to N×10⁶ flits.
5. **Systolic** — torus nearest-neighbor ring/wavefront with measured
   per-hop latency (lookahead target: 1 cycle steady-state); source-route
   fixed-latency path check; 3-D stencil halo exchange.
6. **Counters** — every §8 counter against golden model.
7. **DFT mode** — three patterns route correctly; pattern count check [N6].
8. **Perf model calibration** — measured vs modeled latency/throughput
   on the §10 patterns; report deltas [P20][Q1].

Formal assists: VC0-table acyclicity checker (offline, on table images)
[D2]; one-hot grant assertions per output; TLAST-before-grant-release
assertion (packet atomicity, as flat mode does).

## 14. Decision log (owner decisions 2026-10-13)

| Decision | Choice | Sources |
|---|---|---|
| Hierarchy | 4 cells (2×2×1) = tile; 4 tiles = confluence; recursion, planar, Z between layers | [N7] superswitch analogy |
| Rapids attach | boundary cells' local ports | [P7] concentrator concept |
| Cell RTL | one module; hierarchy is not RTL | — |
| Config | in-band, per-cell RAM tables, unicast load | [Q6] in-band program precedent |
| Bootstrap | safe default route at reset | [D5][P11] DOR acyclicity |
| Tables enable | QoS path diversity + multicast | — |
| QoS | 3 classes, strict priority + aging + bulk reservation | [D13][D1][Q5][P14] |
| Deadlock | 2 VCs, escape-channel scheme | [D2][D7][P12] |
| Multicast discipline | BRCP + source replication + delivery VCs + no-response | [D9][N3][Q7] |
| Flat xbar | kept; mesh is a mode | — |
| Book pulls now | systolic package, perf model, ocelus counters, DFT mode | §15 |
| Book pulls deferred | §11 | — |
| Standard modes | broadcast mode-switch w/ ack barrier; catalog §5.4 (modes 1-8 confirmed 2026-10-13; modes 9-10 added 2026-10-15: tetrad K4 via P_DIA, tile K4-of-tetrads via P_DIA2) | [P8][P17][D9][N3] |

## 15. References

Library root: `/mnt/data/github/calibre/books/`. Section paths below are
relative to each book's directory. Survey conducted 2026-10-13 by four
parallel readers, one per book.

### Duato, Yalamanchili, Ni — *Interconnection Networks: An Engineering Approach*, 2nd ed., Morgan Kaufmann, 2003
`interconnection-networks-the-morgan-kaufmann-ser/`

- **[D1]** Ch.3 intro — starvation; low-priority traffic needs reserved
  bandwidth under priority schemes. `ch03-chapter-3-deadlock-livelock-and-starvation/3.0-chapter-3-deadlock-livelock-and-starvation-intro.md`
- **[D2]** Ch.3 §3.1 — A Theory of Deadlock Avoidance (channel
  dependency, sufficient condition). `.../3.1-a-theory-of-deadlock-avoidance.md`
- **[D3]** Ch.3 §3.2 — Extending the routing-function domain
  (channel/VC-aware routing). `.../3.2-extensions.md`
- **[D4]** Ch.3 §3.7 — Livelock Avoidance (minimal routing / bounded
  misrouting). `.../3.7-livelock-avoidance.md`
- **[D5]** Ch.4 §4.2 — Deterministic Routing (dimension-order; table
  lookup as natural implementation). `ch04-chapter-4-routing-algorithms/4.2-deterministic-routing-algorithms.md`
- **[D6]** Ch.4 §4.3 — Partially Adaptive Algorithms (turn model:
  west-first, north-last, negative-first). `.../4.3-partially-adaptive-algorithms.md`
- **[D7]** Ch.4 §4.4 — Fully Adaptive Algorithms; Duato's Protocol
  (adaptive set + deterministic escape set; 2 VCs for 2-D mesh).
  `.../4.4-fully-adaptive-algorithms.md`
- **[D8]** Ch.4 §4.10 — Resource Allocation Policies (demand-slotted
  round-robin). `.../4.10-resource-allocation-policies.md`
- **[D9]** Ch.5 §5.5 — Hardware Multicast: tree-multicast deadlock,
  path-based multicast, BRCP, delivery-channel deadlock (2/4 delivery
  VCs). `ch05-chapter-5-collective-communication-support/5.5-hardware-implementations-of-multicast.md`
- **[D10]** Ch.6 §6.3 — Fault Models (block/rectangular regions).
  `ch06-chapter-6-fault-tolerant-routing/6.3-fault-models.md`
- **[D11]** Ch.6 §6.5 — Fault-Tolerant Routing (rectangular fault
  regions; software-based absorb/reinject). `.../6.5-fault-tolerant-routing-in-wormhole-switched-netw.md`
- **[D12]** Ch.6 §6.7 — Dynamic Fault Recovery (release/kill flits;
  fragment removal). `.../6.7-dynamic-fault-recovery.md`
- **[D13]** Ch.7 §7.2 — Router Architectures: SGI SPIDER (programmable
  aging, 255 priorities), Alpha 21364 (antistarvation bit), ServerNet
  (accumulator fairness). `ch07-chapter-7-network-architectures/7.2-router-architectures.md`

### Dally & Towles — *Principles and Practices of Interconnection Networks*, Morgan Kaufmann, 2004
`principles-and-practices-of-interconnection-netw/`

- **[P1]** Ch.3 §3.2 — Traffic Patterns (tornado, bit-complement,
  transpose, nearest-neighbor). `ch03-chapter-3-topology-basics/3.2-traffic-patterns.md`
- **[P2]** Ch.3 §3.3 — Performance (zero-load latency T0; max channel
  load γ_max; bisection bound). `.../3.3-performance.md`
- **[P3]** Ch.5 §5.1 — Torus structure (diameter, edge symmetry).
  `ch04-chapter-5-torus-networks/4.1-5-1-the-structure-of-torus-networks.md`
- **[P4]** Ch.5 §5.2 — Torus performance. `.../4.2-5-2-performance.md`
- **[P5]** Ch.5 §5.3 — Building Mesh and Torus Networks (folding).
  `.../4.3-5-3-building-mesh-and-torus-networks.md`
- **[P6]** Ch.5 §5.4 — Express Cubes (little use at low radix).
  `.../4.4-5-4-express-cubes.md`
- **[P7]** Ch.7 §7.1 — Concentrators and Distributors.
  `ch06-chapter-7-slicing-and-dicing/6.1-7-1-concentrators-and-distributors.md`
- **[P8]** Ch.11 §11.1 — Table-Based Routing (incl. source routing;
  per-hop lookup penalty). `ch10-chapter-11-routing-mechanics/10.1-11-1-table-based-routing.md`
- **[P9]** Ch.13 §13.2/13.3/13.4 — Virtual-Channel Flow Control; Buffer
  Management & Backpressure; Flit-Reservation Flow Control.
  `ch12-chapter-13-buffered-flow-control/12.2-13-2-flit-buffer-flow-control.md`,
  `.../12.3-13-3-buffer-management-and-backpressure.md`,
  `.../12.4-13-4-flit-reservation-flow-control.md`
- **[P10]** Ch.13 §13.3 — credit sizing to round-trip latency
  (F·Lf/tcrt ≥ b). (same file as P9's 12.3 entry)
- **[P11]** Ch.14 §14.2 — Deadlock Avoidance (DOR total order; turn
  model; dateline). `ch13-chapter-14-deadlock-and-livelock/13.2-14-2-deadlock-avoidance.md`
- **[P12]** Ch.14 §14.3 — Adaptive Routing (Duato's theorem restated;
  VC0→VC1 transition prohibition; indirect dependences).
  `.../13.3-14-3-adaptive-routing.md`
- **[P13]** Ch.14 §14.5 — Livelock. `.../13.5-14-5-livelock.md`
- **[P14]** Ch.15 §15.1/15.4/15.5 — QoS: service classes & contracts;
  best-effort implementation; Separation of Resources (tree
  saturation). `ch14-chapter-15-quality-of-service/14.1-15-1-service-classes-and-service-contracts.md`,
  `.../14.4-15-4-implementation-of-best-effort-services.md`,
  `.../14.5-15-5-separation-of-resources.md`
- **[P15]** Ch.16 §16.3 — Closing the Loop with Credits.
  `ch15-chapter-16-router-architecture/15.3-16-3-closing-the-loop-with-credits.md`
- **[P16]** Ch.16 §16.4 — Reallocating a Channel (conservative
  reallocation preserves deadlock freedom). `.../15.4-16-4-reallocating-a-channel.md`
- **[P17]** Ch.16 §16.5 — Speculation and Lookahead.
  `.../15.5-16-5-speculation-and-lookahead.md`
- **[P18]** Ch.17 §17.1/17.2 — Input Buffer Organization (per-VC
  reservation); Switches (incremental multicast allocation).
  `ch16-chapter-17-router-datapath-components/16.1-17-1-input-buffer-organization.md`,
  `.../16.2-17-2-switches.md`
- **[P19]** Ch.17–19 — Arbitration & Allocation: matrix arbiter
  (§18.5); variable-priority/aging arbiters (§18.4); queuing arbiter
  (§18.6); separable vs wavefront allocators, iSLIP (§19.3–19.4);
  allocator performance (§19.7); multicast incremental allocation
  (§19 exercises). `ch17-chapter-18-arbitration/17.5-18-5-matrix-arbiter.md`
  and `ch18-chapter-19-allocation/18.3-19-3-separable-allocators.md`,
  `.../18.4-19-4-wavefront-allocator.md`, `.../18.7-19-7-performance-of-allocators.md`,
  `.../18.9-19-10-exercises.md`
- **[P20]** Ch.23 — Performance Analysis (measures, methodology,
  M/D/1 queuing). `ch22-chapter-23-performance-analysis/22.1-23-1-measures-of-interconnection-network-perform.md`,
  `.../22.2-23-2-analysis.md`

### Jantsch & Tenhunen (eds.) — *Networks on Chip*, Kluwer, 2003
`networks-on-chip/`

- **[N1]** Ch.1 §2 — Trends and Challenges (single-global-clock
  unlikely at scale; GALS direction). `ch01-chapter-1/1.2-2-trends-and-challenges.md`
- **[N2]** Ch.4 §4.2 — Ethereal Architecture (GT TDM slot tables;
  headerless GT flits; end-to-end credit flow control; VOQ option).
  `ch04-chapter-4/4.11-4-2-ethereal-architecture.md`
- **[N3]** Ch.4 §4.1 — iEthereal Services (connection properties;
  multicast = no responses; narrowcast). `ch04-chapter-4/4.10-4-1-iethereal-services.md`
- **[N4]** Ch.5 §4.3 — Network on Silicon (routing-table slot
  reservation for GT pairs). `ch05-chapter-5/5.10-4-3-network-on-silicon-5.md`
- **[N5]** Ch.5 §3.4.2 — Resource Network Interface (resource-dependent
  vs independent sides). `ch05-chapter-5/5.8-3-4-2-resource-network-interface.md`
- **[N6]** Ch.7 §5.3 — Testing the Communication Infrastructure (3
  switch configurations; ⌈log₂n⌉ patterns). `ch07-chapter-7/7.15-5-3-testing-the-communication-infrastructure.md`
- **[N7]** Ch.9 §4.4 — ECLIPSE Interconnection Network (superswitches;
  acyclic greedy routing; address hashing; synchronization barrier
  wave). `ch09-chapter-9/9.12-4-4-interconnection-network.md`
- **[N8]** Ch.10 — Proteo: overview/GALS (`10.4-3-1-overview.md`),
  hardware elements (`10.5-3-2-hardware-elements.md`), protocols &
  resend (`10.6-3-3-protocols-and-transactions.md`), packet format & ID
  (`10.7-3-4-packet-format.md`), FIFO structure (`10.8-4-1-structure-of-fifos.md`),
  synthesis area 81% FIFO (`10.9-4-5-synthesis-of-basic-node.md`),
  network testing (`10.10-4-6-test-networks.md`). All under `ch10-chapter-10/`

### Franklin, Crowley, Hadimioglu, Onufryk (eds.) — *Network Processor Design: Issues and Practices, Vol. 1*, Morgan Kaufmann, 2002
`network-processor-design-issues-and-practices-th/`

- **[Q1]** Ch.2 — Hardware-Level Benchmarks (unloaded + loaded
  measurement). `ch04-2-benchmarking-network-processors/4.4-2-2-hardware-level-benchmarks.md`
- **[Q2]** Ch.3 — Toaster2 simulator: WRR serviceability/nonempty tags
  (`ch06-3-a-methodology-and-simulator-for-the-study-of-n/6.6-3-5-application-development.md`);
  per-queue latency/min/max/jitter stats (`.../6.7-3-6-organization-and-configuration.md`)
- **[Q3]** Ch.4 — Network Calculus for fixed-priority/GPS schedulers.
  `ch07-4-design-space-exploration-of-network-processor/7.3-4-2-analysis-using-a-scheduling-network.md`
- **[Q4]** Ch.12 — IBM PowerNP (control/data-plane split; calendar
  shaping) & Intel IXP2400 (XScale control plane; programmable
  performance-monitor unit).
  `ch12-patrick-crowley-jean-lout-baer/12.41-12-1-hardware-architecture.md`,
  `.../12.45-13-2-hardware-architecture.md`
- **[Q5]** Ch.12 — ASPEN CellBus scheduler: 4 priority levels with
  starvation prevention for lowest class (cap consecutive HP cells,
  then force LP service). `.../12.78-16-2-2-data-flow-and-control.md`
- **[Q6]** Ch.12 — ClassiPI: classification sequence supplied along
  with each packet (in-band programmability precedent).
  `.../12.71-15-7-classipi-control-and-sequencer-block.md`
- **[Q7]** Ch.12 — Multicast by source replication: Toaster multiple
  enqueue (`.../12.35-11-3-packet-flow-example-for-a-distributed-syste.md`),
  CellBus native multicast addressing (`.../12.76-16-1-applications.md`),
  Q-5 integrated multicast elaboration (`.../12.59-14-2-4-queue-management-unit-and-external-traffi.md`)
- **[Q8]** Ch.12 — Observability practice: IXP2400 PMU (`.../12.45-13-2-hardware-architecture.md`),
  Toaster μC wait-state monitor (`.../12.38-11-8-toaster-microcontroller.md`),
  Agere ASI RMON stats + timestamps + sequence check (`.../12.27-10-2-payloadplus-optimized-pipeline-based-hardwa.md`)
- **[Q9]** Ch.12 — Scheduling disciplines: IXP2400 ingress-WRR /
  egress-DRR DiffServ pipeline (`.../12.51-13-3-3-portability-framework.md`);
  RSP dynamic per-queue programs (`.../12.31-10-5-rsp-details.md`);
  elasticity buffers (`.../12.49-elasticity-buffers.md`); C-Port
  specialized buses (`.../12.61-14-2-7-internal-buses.md`); fabric
  processor in-band signaling headroom (`.../12.60-14-2-6-fabric-processor.md`)

### External references (not in the calibre library)

- **[S1]** H. T. Kung and C. E. Leiserson, "Systolic Arrays (for
  VLSI)," in *Sparse Matrix Proceedings 1978*, SIAM, 1979, pp. 256–282.
  The founding systolic-array paper — nearest-neighbor dataflow,
  rhythm/schedule skew, the systolic-1D and wavefront-2D mode patterns.
- **[S2]** H. T. Kung, "Why Systolic Architectures?," *IEEE Computer*,
  vol. 15, no. 1, pp. 37–46, Jan. 1982. Survey of systolic/wavefront
  design patterns and their bandwidth advantages.

## 16. Decision/feature → source traceability

| Spec claim or decision | Sources |
|---|---|
| 2-VC escape scheme is sound for a 3-D mesh | [D2][D7][P12] |
| VC0 must be a connected, acyclic subrelation (checked at load) | [D2][D7] |
| VC1 routes minimal-or-budgeted; no VC0→VC1 transitions | [P12][D7] |
| Dateline rule for torus wrap in VC0 | [P11] |
| Misroute budget in header (livelock) | [D4][P13] |
| Node-table routing default; source-route mode for static/systolic | [P8][D5] |
| Turn-model alternative for VC0 (future option) | [D6][P11] |
| 3 QoS classes strict-priority + programmable aging | [D13] |
| Aging insufficient without bulk reservation | [D1][Q5] |
| Class non-interference (VCs + injection buffers) | [P14: §15.5] |
| Matrix arbiters at outputs; iSLIP-style switch alloc | [P19] |
| Incremental multicast port-mask allocation | [P18][P19] |
| Conservative output-VC reallocation | [P16] |
| Credit sizing ≥ round-trip latency | [P10][P15] |
| Per-port input buffers with per-VC reservation | [P18] |
| BRCP multicast; path-based > tree-based in wormhole | [D9] |
| Delivery-VC multiplicity for multicast | [D9] |
| Source-side replication discipline | [Q7] |
| No responses on multicast | [N3] |
| In-band config (table read/write; program-per-packet precedent) | [Q6] |
| Header format: configurable header/payload, packet ID | [N8: §3.4][N3] |
| Torus wrap links + folding | [P3][P4][P5] |
| Route lookahead / speculation | [P17] |
| Perf model: T0, M/D/1, γ_max, adversarial patterns, methodology | [P1][P2][P20][Q1] |
| Counter suite contents | [Q4][Q2][Q8] |
| DFT 3-configuration test mode | [N6] |
| Buffer/FIFO area knob (regs vs SRAM) | [N8: §4.5] |
| Deferred: GT/TDM, faults, barrier, express, GALS, VOQ, WRR/DRR, flit-reservation, resend | [N2][N3][N4][D10–D12][N7][P6][N1][N8] |
| Standard modes: systolic/wavefront patterns | [S1][S2]; static-route precedent [P8][N7]; latency [P17] |
| Broadcast mode-switch + ack barrier | [D9][N3] multicast/config machinery; atomicity is a delta rule |
