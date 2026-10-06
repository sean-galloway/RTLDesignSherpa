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

**Version:** 0.5 (draft, 2026-10-06)
**Status:** nine of the eleven decision rows record a name and a date; D3
(memory-side, now shaped by the two-top structure) and D11 (arrays, house
primitives by rule) remain OPEN. A decision becomes DECIDED when it records
a name and a date, the way the reed-solomon PRD does it.
v0.2: D8 decided — `*_monlite` observation wrappers (never `_mon` on the
measured paths).
v0.3: D4 decided — snoop transport is ACE-shaped (AC/CD/CR) per the
[onyx D7](../onyx-ace-ccu/PRD.md) port contract, family decision
2026-10-05. The snoop-filter (directory-lite) half of D4 stays deferred and
is reopened as [onyx D3](../onyx-ace-ccu/PRD.md).
v0.4: D2 decided (Sean, 2026-10-06) — CPU-side interface is a **GAXI
slave**. House BFM/monitor coverage and skid/FIFO plumbing already exist,
and STREAM can attach as first real consumer without an adapter.
v0.5 (Sean, 2026-10-06): D1, D5, D6, D7, D9, D10 decided in one working
session — geometry 32 KiB/64 B/4-way center + a tiny 16-set/2-way formal
config; write-back + write-allocate; plain MESI on a 3-bit state field;
replacement {LRU, tree-PLRU, FIFO, RANDOM} with LRU default (tree-PLRU the
timing fallback, no sim golden model — future sim extension recorded);
verification = Pattern-B grids + control-layer SymbiYosys at tiny geometry +
cache_sim parity on LRU/FIFO/RANDOM + FSM oracles derived from the gem5
Ruby MESI_Two_Level SLICC tables; first consumer = TB masters bring-up, pair
rig the gated deliverable, STREAM attach the documented future hook.

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
| D1 | Cache geometry | **DECIDED 2026-10-06 (Sean): 32 KiB / 64 B lines / 4 ways (128 sets) as the default center, fully elaboration-parameterised (4–32 KiB, 32–64 B, 2–8 ways), plus a reserved tiny config — 16 sets / 2 ways / 64 B — for SymbiYosys tractability.** Board BRAM does not bind (~9 of 135 36Kb RAMs on Nexys A7 at the default), so geometry serves the DV matrix and the proofs, not the board | tag/data array dimensions, the whole DV matrix |
| D2 | CPU-side interface | **DECIDED 2026-10-06 (Sean): GAXI slave.** Chosen over the plain valid/ready native port and the AXI4 slave: house BFM/monitor coverage and skid/FIFO plumbing already exist, and STREAM can attach as first real consumer without an adapter. Must express single-beat reads, write-allocate fills, and (if write-through is chosen) store-without-allocate | front-end FSM, adapter surface, first consumer |
| D3 | Memory-side interface | OPEN: AXI4 read/write masters on the house `axi4_master_rd/wr` wrappers (stream/rapids pattern) vs GAXI vs a simple direct SRAM port for bring-up | fill/drain engines, burst behavior on misses |
| D4 | Snoop transport | **DECIDED 2026-10-05 (Sean): ACE-shaped transport — amber implements the AC/CD/CR snoop channels exactly as [onyx D7](../onyx-ace-ccu/PRD.md) defines them (family decision: cache-ip is ACE-shaped), staying bus-agnostic internally behind a thin adapter.** Chosen over a custom dedicated snoop bus and over snooping on the AXI4 fabric directly; the ACE-lite-shaped candidate was set aside because a snoop responder must drive CR responses and CD data — ACE-Lite carries no snoop channels at all. The snoop-filter (directory-lite) sub-question stays deferred, reopened as [onyx D3](../onyx-ace-ccu/PRD.md). | the coherence bus, formal surface, gate count |
| D5 | Write policy | **DECIDED 2026-10-06 (Sean): write-back + write-allocate.** Write-through/no-allocate deletes the coherence traffic the research exists to measure — dirty snoop transfers (PassDirty), WriteBack drains, onyx's memory-read elision — and leaves MESI's M state with no job; it stays available as a bring-up mode only | M-state logic, memory traffic, formal targets |
| D6 | MESI variant | **DECIDED 2026-10-06 (Sean): plain MESI on a 3-bit state field.** MOESI's O-state is a later elaboration upgrade (encoding headroom reserved now, ~512 extra tag bits); its win — dirty→shared without a memory read — is a measurement for the pair rig, not a v1 requirement | state machine count, snoop response matrix |
| D7 | Replacement policy | **DECIDED 2026-10-06 (Sean): policy set {LRU, tree-PLRU, FIFO, RANDOM}, default LRU.** LRU/FIFO/RANDOM match the [cache simulator](../../../../bin/apps/cache_sim/) exactly (`POLICIES = ['LRU','FIFO','RANDOM']`), so golden-model parity covers every policy both sides implement; **tree-PLRU is carried as the timing-tight fallback — the one policy with no sim golden model**, cross-checked by RTL self-checks today and a future cache_sim extension (recorded, not silently assumed). Policy stays an elaboration parameter so the sim↔RTL cross-check holds per policy | policy engine, cross-check fidelity |
| D8 | Observation | **DECIDED 2026-10-04 (Sean): `*_monlite` wrappers, not the heavyweight `_mon`.** MonBus taps for hits, misses (class split if the model supplies it), snoops, evictions, and state transitions, observed through the `axi4_monlite` / `axil4_monlite` family — same 128-bit MonBus packets, UNIT/AGENT ids, and host tooling as `_mon`, ~1/5 the monitor gates, and a drop-and-count policy that never stalls the port. Rationale for a research cache: the observer must not perturb what it measures — a `_mon` wrapper that gates the port when its tracking tables fill would corrupt the very miss-latency numbers amber and jet exist to produce. The events D8 lists are emitted as MonBus packets and tallied by the standard agents (`monbus_tally_axil`); heavyweight `_mon` stays available as a DV cross-check, never on the measured paths. | perf counters, board capture, DV scoreboards |
| D9 | Verification strategy | **DECIDED 2026-10-06 (Sean): Pattern-B cocotb GATE/FUNC/FULL grids over the geometry × policy × rig matrix (ACE BFMs: cocotb-framework 1.2.0); SymbiYosys scoped to the control layer — `amber_control`, `amber_snoop_resp`, the pending-fill bypass, the victim-buffer handoff — proven at the tiny 16-set/2-way geometry; cache_sim trace-replay parity across LRU/FIFO/RANDOM. The Python reference model and the FSM oracles derive from the gem5 Ruby `MESI_Two_Level` SLICC tables in [`../References/gem5-ruby-protocols/`](../References/gem5-ruby-protocols/) — `L1cache.sm`'s enumerated transient states are the derivation source for the `amber_pkg` state encoding, and every stable and transient transition is cross-checked against an executable protocol spec, not prose** | DV structure, formal areas, CI time |
| D10 | First consumer | **DECIDED 2026-10-06 (Sean): standalone TB masters for bring-up; the gated deliverable is the pair rig — two ambers + shared memory, the coherence research rig.** STREAM attach is documented as the future integration hook (D2's GAXI choice is what makes it cheap later); the onyx rig is sequenced per onyx D10 — onyx waits behind the pair rig | integration scope, what "done" means |
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
masters (D3), snoop port toward onyx / peer caches (D4 — ACE-shaped
AC/CD/CR, decided 2026-10-05), MonBus observation (D8).
Standalone-testable with TB masters before any consumer exists (D10).
