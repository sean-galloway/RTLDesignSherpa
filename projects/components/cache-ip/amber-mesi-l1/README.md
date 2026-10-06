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

# amber — Blocking MESI Snoopy L1 Cache

First IP of the [`cache-ip/`](../) gemstone family: a
blocking, snoopy, MESI L1 data cache. The research baseline — the
coherence protocol, snoop transport, storage arrays, and observation fabric
are all here; only the miss handling is deliberately simple (a miss blocks
the cache until the line arrives). The non-blocking upgrade is
[`../jet-mesi-l1/`](../jet-mesi-l1/), whose performance delta over amber is
the second research artifact.

## Status

**Scaffolded 2026-10-04; architecture decided 2026-10-06.** The [PRD](PRD.md)
(v0.5) carries nine of eleven decision rows closed with name and date — D1
geometry (32 KiB/64 B/4-way center + a tiny formal config), D2 GAXI CPU-side,
D4 ACE snoop transport, D5 write-back + write-allocate, D6 plain MESI on a
3-bit state field, D7 replacement {LRU, tree-PLRU, FIFO, RANDOM} default LRU,
D8 `*_monlite` observation, D9 verification (control-layer SymbiYosys +
cache_sim parity + FSM oracles derived from the gem5 Ruby MESI_Two_Level
SLICC tables), D10 first consumer (TB masters bring-up, pair rig the gated
deliverable); D3 and D11 remain OPEN. The full **[Hardware Architecture
Specification](docs/amber_has/amber_has_index.md)** (chapter book, v1.0)
ratifies the [Pre-HAS](docs/amber_has/amber_prehas.md) sketch — two tops,
`amber` (pair rig) and `amber_ace` (onyx rig), on a shared `amber_core`. The
**[Micro-Architecture Specification](docs/amber_mas/amber_mas_index.md)** and
pre-RTL **[signal-contract / K-map workbook](docs/gen_amber_contracts_kmaps.py)**
now close the implementation decisions the HAS deferred (pipeline staging,
array banking, FSM state encoding, replacement datapaths, interface timing).
`rtl/`, `dv/` are still placeholders; no RTL, no testbench, no register model.

## What it teaches / why it exists

- **Coherence as a verifiable protocol.** MESI gives four states and two
  agents (local CPU port + snoop port) — small enough to prove things about.
  The formal targets: a snooped line is never served stale, and the protocol
  cannot deadlock or livelock under fair arbitration.
- **The sim ↔ RTL ↔ board methodology.** The trace-driven
  [cache simulator](../../../../bin/apps/cache_sim/) models the same
  sets/ways/policy space; amber's DV replays the same traces and must match
  the model's hit-rate numbers cycle-for-policy. On board, MonBus capture
  turns the same counters into measured truth (the pumice-vs-LiteDRAM
  yardstick pattern from the memory-controller campaign).
- **Blocking first, on purpose.** Removing MSHRs from the first design keeps
  the correctness surface small and makes jet a clean second paper.

## Goals (summary — the binding list is [PRD.md](PRD.md) §"Success criteria")

1. Parameterised L1 data cache (sets/ways/line size as elaboration
   parameters) with pluggable replacement policy.
2. Snoopy MESI coherence over an ACE-shaped snoop port (PRD D4), correct
   against a Python golden model and SymbiYosys proofs.
3. MonBus-instrumented: hit/miss/snoop/eviction events observable in sim and
   on FPGA.
4. FPGA-cost characterisation (Nexys A7 and/or Genesys 2) the way the rest of
   the repo measures.

## Explicit non-goals (for amber)

Non-blocking / lockup-free operation, directory coherence, multi-level
caching, ECC integration, virtual memory / TLB handling. See
[PRD.md](PRD.md) §"Non-goals".

## Layout

`rtl/`, `dv/`, `docs/` exist as placeholders. When RTL lands, this directory
follows the per-component layout of
[`../dma-ip/stream/`](../../dma-ip/stream/README.md) (fub/macro/top split,
filelists registry, Pattern-B cocotb tests) and the mandatory rules in
[`../../CLAUDE.md`](../../CLAUDE.md) (reset macros, shared `sdpram_core` /
FIFO primitives, array syntax).
