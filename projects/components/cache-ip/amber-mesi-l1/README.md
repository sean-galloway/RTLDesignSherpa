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

**Scaffolded 2026-10-04** — README + PRD only. `rtl/`, `dv/`, `docs/` are
placeholders; no RTL, no testbench, no register model. Decisions are OPEN in
[PRD.md](PRD.md) until they record a name and a date; so far **D8 observation
(`*_monlite`) is decided (2026-10-04), D4 snoop transport is ACE-shaped
AC/CD/CR per the onyx D7 contract (2026-10-05), and D2 CPU-side interface is
a GAXI slave (2026-10-06)**. An architecture sketch for the open decisions —
the [Pre-HAS](docs/amber_has/amber_prehas.md) — landed 2026-10-06 and took
owner direction the same day (pending-fill bypass for probe-during-fill; the
two rigs as two tops, `amber` and `amber_ace`, on a shared core); it records
proposed working defaults only, no decisions.

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
