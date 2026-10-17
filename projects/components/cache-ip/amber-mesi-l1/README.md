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

**RTL complete and board-verified (2026-10-15).** All eleven PRD decision
rows are closed (D3/D11 fell in v0.6, 2026-10-07). The
**[Hardware Architecture Specification](docs/amber_has/amber_has_index.md)**
is at v0.9 and the
**[Micro-Architecture Specification](docs/amber_mas/amber_mas_index.md)** at
v0.7; the pre-RTL
**[signal-contract / K-map workbook](docs/gen_amber_contracts_kmaps.py)**
closes the implementation decisions the HAS deferred.

- **RTL:** `rtl/top/amber_top.sv` (pair rig, AXI4), `rtl/top/amber_ace_top.sv`
  (onyx rig, ACE), `rtl/top/amber_pair_fabric.sv`, and
  `rtl/fub/amber_ace_issue.sv` live here; the shared MESI L1 core (`l1_core`
  + twelve `l1_*` FUBs, `l1_pkg`) lives in
  [`../common-ip/`](../common-ip/) per the sharing contract.
- **DV:** 19 test roots in the flat `dv/tests/` directory, on the repo-wide
  `make/tests.mk` rails — `make clean-all && make run-all-full-parallel` is
  the sign-off run (350/350 green at 2026-10-15). The D9 SymbiYosys targets
  (control layer, tiny geometry) are defined under [`../../formal/`](../../../../formal/).
- **Board:** the Genesys 2 pair-rig bring-up is verified end to end — both
  cycle injectors 20000/20000 with clean error flags and live read data in
  the smoke sequence. See the
  [FPGA system book](../../../fpga-systems/Genesys2/cache-ip/amber/README.md).
- **Conformance and robustness since v0.6:** ACE issue #106
  (`2594d73bb` — `ReadNotSharedDirty` read misses, `PassDirty` honoured with
  M install, `CleanUnique`/`MakeUnique` on AR with spec encodings);
  `PF_GUARD` pending-fill snoop guard (`ab308d108`, amber BUG-002);
  boundary reset-sync per the
  [BKM](../docs/BKM_boundary_reset_sync.md) (`003773645`). The bug board
  (BUG-001/002/003) is fully closed as of 2026-10-15 — see
  `vault/Tasks/amber/bug/`.

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

`rtl/`, `dv/`, `docs/` follow the per-component layout of
[`../dma-ip/stream/`](../../dma-ip/stream/README.md) (fub/macro/top split,
filelists registry, Pattern-B cocotb tests) and the mandatory rules in
[`../../CLAUDE.md`](../../CLAUDE.md) (reset macros, shared `sdpram_core` /
FIFO primitives, array syntax).

RTL layout as landed (Sean, 2026-10-06 conventions; core moved to
`../common-ip/` 2026-10-11 so jet can inherit it, renamed `amber_*` →
`l1_*` 2026-10-12 — see [`../common-ip/README.md`](../common-ip/README.md)):

- `rtl/includes/`, `rtl/fub/` (12 leaf blocks), `rtl/top/l1_core.sv` —
  now live in `../common-ip/rtl/`. The MESI L1 core — package, arrays,
  replacement, snoop responder, control/fill/drain/frontend/monlite/victim —
  is shared IP; amber and jet both instantiate `l1_core` from there.
- `rtl/fub/amber_ace_issue.sv` — the coherent-transaction issuer stays
  here: per the jet inheritance contract it is top-wrapping amber owns
  (the Table 2.8.1 event-to-transaction map, post-#106 on AR for upgrades).
- `rtl/top/` — the integration tops, named `<ip>_top.sv`. amber has two
  rigs sharing `l1_core`: `amber_top.sv` (pair rig, plain AXI4) and
  `amber_ace_top.sv` (onyx rig, ACE).
- `rtl/filelists/` — amber's integration lists (`amber_top.f`,
  `amber_ace_top.f`, `amber_pair_fabric.f`, `amber_ace_issue.f`) plus
  `amber_all.f`, the whole-closure list. The core/fub lists moved with
  the RTL to `../common-ip/rtl/filelists/` and resolve there through
  `$CACHE_COMMON_ROOT`.
- `dv/tests/` (flat, 19 roots), `dv/tbclasses/` — Pattern-B grids on the
  repo-wide make/tests.mk rails.
