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

# amber — Product Requirements (DRAFT)

**Version:** 0.2 (draft, 2026-10-04)
**Status:** decisions pending — this page records the questions and the
candidates, not answers. A decision becomes DECIDED when it records a name
and a date, the way the reed-solomon PRD does it. Until then every row below
is OPEN.
v0.2: D8 decided — `*_monlite` observation wrappers (never `_mon` on the
measured paths).

## 1. Purpose

A parameterised, blocking, snoopy MESI L1 data cache for the Sherpa
research/teaching flow: correct against a software golden model, provable
with SymbiYosys, observable through the MonBus monitor fabric, and
characterised for FPGA cost like every other component in this repo. It is
the first cache-ip IP and the deliberate baseline for
[jet](../jet-mesi-l1/PRD.md), the lockup-free follow-on.

## 2. Background

A blocking cache freezes on a miss: the pending request (and everything
behind it) waits for the fill to complete. That is poor for performance and
excellent for correctness work — one outstanding transaction means no MSHR
bookkeeping, no hit-under-miss hazards, no merge logic. MESI (Modified /
Exclusive / Shared / Invalid) is the coherence layer on top: each line
carries a state that says who may write it and who must be told when they
hold a stale copy. Snoopy coherence broadcasts probes on a shared bus;
every cache watches and answers.

Blocking and MESI are orthogonal, which is the design bet: amber nails the
coherence protocol with trivial miss handling; jet keeps the protocol and
upgrades the miss handling. The pair then answers the classic question with
measured, on-board data: what does lockup-freedom actually buy?

Repo anchors the design must respect: resets on the
`ALWAYS_FF_RST` macros, storage on the shared `sdpram_core` / gaxi FIFO
primitives (no bespoke SRAM, no reset on memories), `[DEPTH]` array syntax,
valid/ready streaming contracts, and the monitor/MonBus observation fabric
from `rtl/amba/`.

## 3. Decisions that pick the design

| # | Decision | Candidates | What it drives |
|---|---|---|---|
| D1 | Cache geometry | OPEN: total size (4–32 KiB), line size (32–64 B), associativity (2–8 ways) as elaboration parameters, vs a fixed 32 KiB / 64 B / 4-way profile with parameters deferred | tag/data array dimensions, the whole DV matrix |
| D2 | CPU-side interface | OPEN: plain valid/ready native port (reed-solomon D9 shape) vs AXI4 slave vs GAXI; must express single-beat reads, write-allocate fills, and (if write-through is chosen) store-without-allocate | front-end FSM, adapter surface, first consumer |
| D3 | Memory-side interface | OPEN: AXI4 read/write masters on the house `axi4_master_rd/wr` wrappers (stream/rapids pattern) vs GAXI vs a simple direct SRAM port for bring-up | fill/drain engines, burst behavior on misses |
| D4 | Snoop transport | OPEN: dedicated snoop bus (req/broadcast/response, custom but tiny) vs an AXI ACE-lite-shaped channel vs snooping on the AXI4 fabric directly; plus whether a snoop filter (directory-lite) is in scope for amber or deferred to a third IP | the coherence bus, formal surface, gate count |
| D5 | Write policy | OPEN: write-back + write-allocate (the research default — MESI's M state earns its keep) vs write-through + no-allocate (simpler, slower); dirty-eviction handling under it | M-state logic, memory traffic, formal targets |
| D6 | MESI variant | OPEN: plain MESI vs MOESI/MEOSI ownership (O state cuts dirty transfers between caches); default lean MESI, upgrade path noted | state machine count, snoop response matrix |
| D7 | Replacement policy | OPEN: true LRU vs tree-PLRU vs FIFO vs random, pluggable per elaboration parameter; must be the same policy set the [cache simulator](../../../../bin/apps/cache_sim/) models so sim-vs-RTL cross-check is exact | policy engine, cross-check fidelity |
| D8 | Observation | **DECIDED 2026-10-04 (Sean): `*_monlite` wrappers, not the heavyweight `_mon`.** MonBus taps for hits, misses (class split if the model supplies it), snoops, evictions, and state transitions, observed through the `axi4_monlite` / `axil4_monlite` family — same 128-bit MonBus packets, UNIT/AGENT ids, and host tooling as `_mon`, ~1/5 the monitor gates, and a drop-and-count policy that never stalls the port. Rationale for a research cache: the observer must not perturb what it measures — a `_mon` wrapper that gates the port when its tracking tables fill would corrupt the very miss-latency numbers amber and jet exist to produce. The events D8 lists are emitted as MonBus packets and tallied by the standard agents (`monbus_tally_axil`); heavyweight `_mon` stays available as a DV cross-check, never on the measured paths. | perf counters, board capture, DV scoreboards |
| D9 | Verification strategy | OPEN (direction: Pattern-B cocotb gate/func/full + SymbiYosys proofs of no-stale-served and protocol liveness + trace replay against the cache_sim golden model with matching policy) | DV structure, formal areas, CI time |
| D10 | First consumer | OPEN: standalone TB masters vs a pair of amber caches snooping each other (the coherence research rig) vs attachment to STREAM as a cached DMA path | integration scope, what "done" means |
| D11 | Data/tag arrays | OPEN (direction: shared primitives): `sdpram_core`-based tag/data stores + house FIFOs for pending/fill queues; FPGA attributes per [`../../../../GLOBAL_REQUIREMENTS.md`](../../../../GLOBAL_REQUIREMENTS.md) | area/timing headroom, the no-bespoke-SRAM rule |

## 4. Success criteria

1. **Golden-model parity.** Given the same trace + policy + geometry, amber's
   hit/miss/miss-class counts match
   [cache_sim](../../../../bin/apps/cache_sim/) exactly across a regression
   trace suite.
2. **Proofs.** SymbiYosys: no stale data is ever served after an external
   write; the coherence protocol cannot deadlock under fair arbitration.
3. **Observation.** Every event class above visible on MonBus in simulation,
   and captured on at least one FPGA board.
4. **Cost.** Synthesis/implementation numbers (LUT/FF/RAM, fmax) on Nexys A7
   and/or Genesys 2, recorded in `docs/` the way pumice characterised.

## 5. Non-goals

Non-blocking / lockup-free miss handling (jet), directory-based coherence,
L2/L3 or multi-level inclusion policies, ECC on cache arrays, virtual memory
and TLB interaction, multi-port CPU issue. Each is a future IP or a future
decision, not an amber requirement.

## 6. Where the block sits

Research cache on the AMBA fabric: CPU-side slave (D2), memory-side AXI4
masters (D3), snoop port to peer caches (D4), MonBus observation (D8).
Standalone-testable with TB masters before any consumer exists (D10).
