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

# onyx — Product Requirements (DRAFT)

**Version:** 0.3 (draft, 2026-10-05)
**Status:** decisions pending — this page records the questions and the
candidates, not answers. A decision becomes DECIDED when it records a name
and a date, the way the reed-solomon PRD does it. Until then every row
below is OPEN.
v0.2: D7 decided 2026-10-05 (Sean) — onyx owns the ACE-shaped AC/CD/CR
snoop port; amber/jet adapt to it behind a thin adapter. Decided together
with [amber D4](../amber-mesi-l1/PRD.md), so the gate between the two is
resolved. The sequencing constraint that remains: onyx still waits behind
amber's pair rig (amber D10), its first consumer.
v0.3: D10 direction tightened 2026-10-05 — the ACE BFM extension of the
RDS-DV `axi4` family is now specified concretely (layering, four classes,
build order); the row stays OPEN. RDS-DV implementation filed as
[RTLDesignSherpa-DV issue #86](https://github.com/sean-galloway/RTLDesignSherpa-DV/issues/86).

## 1. Purpose

A snoop-based cache coherency unit (CCU) in the shape of Arm ACE: the
manager that sits between the repo's coherent caches and memory on the
house AXI4 fabric. An attached cache (amber instance, jet instance) is an
ACE *master*; it issues coherent transactions (ReadShared, ReadUnique,
CleanUnique, MakeUnique, WriteBack, Evict) instead of managing peers
directly. onyx receives those transactions, broadcasts a snoop (AC request)
to the other caches, gathers their CR responses (DataTransfer / IsShared /
PassDirty) and CD data, decides whether the transaction may be completed
from cache-supplied data alone or memory must be read, and serialises
same-address traffic. The research question is the manager side itself:
what do fanout, gather, adjudication, and ordering cost — in gates, in
latency, and in verification effort.

## 2. Background

ACE is AXI4 plus three snoop channels (AC, CR, CD) — and this repo already speaks AXI4
(skid buffers, GAXI FIFOs, `axi4_master_rd/wr` wrappers, Pattern-B BFMs).
The natural-protocol argument: every piece of onyx's data path reuses
existing, proven plumbing; the new logic is the coherence decision layer
and the serializer. The definition is Arm IHI 0022 (the ACE chapters);
the worked example is `pulp-platform/culsans` (ETH/PlanV), whose two halves
are exactly the reading list:

- **culsans' CVA6 coherent WB cache** — how a cache becomes a snoop
  responder: the AC/CD/CR channels, how snoop tag lookups arbitrate with
  the core's own tag port, and the MOESI-ish line states.
- **`ace_ccu_top`** — the manager: broadcast snoops on a coherent
  read/write, collect responses, decide whether memory is read, and
  serialise same-address transactions.

Treat culsans as a worked example, not a dependency (last push 2024, lightly
maintained). Note also what onyx is *not*: it is not a directory, not an L2,
and not a general NoC — amber's deferred "snoop filter / directory-lite"
question (amber D4) shows up here only as one candidate row (D3).

Repo anchors the design must respect: resets on the `ALWAYS_FF_RST` macros,
no bespoke SRAM (shared `sdpram_core` / house FIFO primitives), `[DEPTH]`
array syntax, valid/ready streaming contracts, MonBus observation through
`*_monlite` wrappers only (amber D8's decision — the observer must never
stall the measured paths), filelists registry, and GLOBAL_REQUIREMENTS.

## 3. Decisions that pick the design

| # | Decision | Candidates | What it drives |
|---|---|---|---|
| D1 | Functional scope | OPEN: CCU only — N ACE slave-side ports toward caches, one AXI4 master toward memory, one ACE-Lite IO port (the culsans shape; recommended starting scope) vs CCU + address striping / multiple memory ports (interconnect territory; non-goal today) | block boundary, what "onyx done" means |
| D2 | ACE transaction subset | OPEN: research subset — ReadShared / ReadUnique / CleanUnique / MakeUnique / WriteBack / Evict (recommended) vs subset + barrier support vs full ACE incl. DVM | front-end decoder, BFM scope, conformance matrix |
| D3 | Snoop fanout | OPEN: broadcast to all attached caches (culsans shape, simplest, recommended for v1) vs directory-lite snoop filter as an elaboration parameter (amber D4's deferred question, reopened here) vs snoop filter mandatory | fanout logic, gate count, the coherence-traffic measurements |
| D4 | Response gather | OPEN: fixed response window (all caches respond within N beats, presumed-miss after timeout — simple, needs a proven bound) vs tagged outstanding snoop IDs with per-transaction completion (exact, more bookkeeping) | gather buffer, formal surface, ACE conformance |
| D5 | Same-address serialization | OPEN: per-address scoreboard allowing interleaving of different addresses (recommended; the interesting manager) vs full in-order single outstanding (simplest, strangles concurrency; fine as a bring-up mode) | the serializer, the deadlock/liveness proof, jet J4 interactions |
| D6 | Memory-read elision | OPEN: full adjudication — read memory only when no cache supplied data and no PassDirty (correct ACE semantics; recommended) vs always-read simplification for bring-up | memory traffic, the measurable win onyx exists to quantify |
| D7 | Cache-side interface ownership | **DECIDED 2026-10-05 (Sean): onyx defines and owns an AC/CD/CR-shaped snoop port; amber/jet stay bus-agnostic internally and add a thin adapter to it.** Chosen over caches natively growing ACE ports — the cache cores stay unpinned from ACE except at the adapter, so onyx (or a real ACE interconnect, e.g. culsans' `ace_ccu_top`) can supersede the custom bus without touching cache RTL. | the amber D4 ↔ onyx contract, who changes when ACE supersedes the custom bus |
| D8 | Domain / barrier rules | OPEN: single shareability domain, barriers ignored (recommended non-goal, recorded here so it is a decision and not an accident) vs minimal barrier ordering vs full DVM | scope honesty, later upgrade path |
| D9 | Observation | OPEN (direction: amber D8 pattern): `*_monlite` taps for coherent-txn start, snoop fanout per transaction, response gather completion, memory-read elision hit/miss, serialization stalls, and WB/Evict drains; tallied by `monbus_tally_axil` | perf counters, board capture, DV scoreboard |
| D10 | Verification strategy | OPEN (direction: Pattern-B cocotb gate/func/full. **ACE BFM — an extension of the `axi4` BFM family in RDS-DV, layered the way that family is built** (analysis from inspecting `CocoTBFramework/components/axi4/`): (1) field configs — an `AXI4ACEFieldConfigHelper` adds `ARSNOOP[3:0]` / `AWSNOOP[2:0]` to the AR/AW field configs; (2) signal-map patterns — new `axi4ace_*` protocol patterns (decide there: framework-shipped vs. user-loadable, the signal_mapping_helper question); (3) transaction/packet layer — the six D2 transaction types as an enum, CRRESP as a bitfield (DataTransfer/Error/PassDirty/IsShared/WasUnique); (4) four BFM classes — `AXI4ACEMasterRead` / `AXI4ACEMasterWrite` as subclasses (snoop type on commands; the BFM **drives RACK/WACK** when playing master against an onyx-port DUT, since the RTL auto-pulse in `axi4ace_master_rd/wr` only covers DUT-as-master), `AXI4ACESnoopSlave` (new, no base: receives AC, drives CR/CD in **issue order** — snoops carry no ID — with programmable cache-state behavior producing the correct CRRESP; this is the golden-model hook that replays gem5 traces through amber), `AXI4ACESnoopMaster` (new: drives AC, gathers CR/CD in order — drives onyx's fanout in DV); (5) compliance checker — in-order CR/CD, no snoop to the requesting master, CD-before-CDLAST, CRRESP validity per snoop type; (6) main-repo TB classes under `bin/TBClasses/axi4ace/` per consumer. **Build order:** snoop-slave BFM first (amber's pair rig needs it), snoop-master BFM lands with onyx; ships as an RDS-DV framework release the way the irq BFM did. Python golden model derived from the gem5 Ruby `MESI_Two_Level` spec in `../References/gem5-ruby-protocols/`; the ACE subset contract is the in-repo [definition doc](../References/AMBA_ACE_Interface_Definition.md); SymbiYosys proofs of same-address serialisation and no-deadlock under fair arbitration; culsans behaviours as informal cross-checks, not oracles) | DV structure, formal areas, CI time |
| D11 | Master count & profile | OPEN: N coherent cache masters 2–4 as an elaboration parameter (culsans uses 2–4 CVA6) vs fixed 2 for the research rig; line size / profile locked to amber's geometry vs independently parameterised | array dimensions, DV matrix, the measured system's realism |

## 4. Success criteria

1. **Three-block coherence.** Two amber instances (or amber + jet) plus
   onyx form a coherent system that passes the golden-model parity suite
   amber D9 defines — the pair rig grown by one block, same traces, same
   policy space.
2. **IHI 0022 conformance on the D2 subset.** A scoreboard checks the
   AC/CR/CD behaviour per transaction type: the CR bits (DataTransfer,
   IsShared, PassDirty) of every gather are correct for the transaction
   and the caches' states.
3. **The serializer, proven.** Formal: no two same-address coherent
   transactions proceed incompatibly; no deadlock under fair arbitration
   at N ∈ {2, 3, 4} masters; the D4 response-gather mechanism cannot
   livelock (a presumed-miss bound exists and is proven).
4. **Observation.** Every D9 event class visible on MonBus in simulation
   and captured on at least one FPGA board.
5. **Cost.** Synthesis/implementation numbers (LUT/FF/RAM, fmax) on
   Nexys A7 and/or Genesys 2, recorded in `docs/` the way pumice
   characterised.

## 5. Non-goals

Cache storage in onyx (it is a manager, not an L2 — tempting because a
CCU's gather point is the natural place to cache; explicitly out),
directory-based coherence (the D3 snoop-filter candidate is the closest
this IP comes), ACE DVM and full barrier semantics (D8), cache
stash/dealloc features, multi-CCU / multi-domain systems, and any CPU-side
or upstream-master port beyond ACE-Lite IO. Each is a future IP or a
future decision, not an onyx requirement.

## 6. Where the block sits

The fabric's coherence point, on three kinds of port: **cache-side**, N
ACE-facing ports accepting coherent transactions from amber/jet instances
acting as ACE masters (D7, decided 2026-10-05: onyx owns this port's ACE
shape; caches adapt); **memory-side**,
one AXI4 master toward the house memory path (D6 fixes when it is read);
**inter-cache**, the snoop fanout — AC requests driven into each peer
cache, CD snoop data and CR snoop responses returned. No CPU port, no
register block beyond what observation needs (D9 tallies live in
`monbus_tally_axil` like every other component). Standalone-testable with
BFM caches long before amber exists: culsans' `ace_ccu_top` demonstrates
exactly that decoupling.
