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

# Purpose and Scope

## Purpose

amber is a parameterized, blocking, snoopy MESI L1 data cache for the Sherpa research and teaching flow. It is deliberately the simplest correct cache: one outstanding transaction, no MSHRs, no hit-under-miss, no merge logic. That deletion makes it a clean baseline for the follow-on `jet` lockup-free cache and a tractable target for SymbiYosys proofs and cache-simulator parity.

This document specifies amber's hardware architecture. It is written after the PRD decisions that fix geometry, write policy, MESI variant, replacement policy, CPU-side interface, snoop transport, observation, verification strategy, and first consumer, but while D3 (memory-side shape) and D11 (array construction) remain open. The open rows are recorded honestly with their current direction and consequences; nothing here is presented as decided that is not.

## Scope

In scope:

- The two top-level wrappers, `amber` (pair rig) and `amber_ace` (onyx rig), and the shared `amber_core`.
- CPU-side GAXI slave interface (`amber_cpu_frontend`).
- Fabric-side plain AXI4 masters under `amber` and ACE masters plus coherent-issue logic under `amber_ace`.
- ACE-shaped snoop responder port (`amber_snoop_resp`) toward a peer cache or onyx.
- Blocking control FSM, pending-fill bypass, victim buffer, fill/drain engines, tag/data arrays, replacement policy engine, and observation wrapper.
- Parameterization, clocking/reset, verification strategy, characterization plan, and future hooks.

Out of scope (named as decisions, not omissions): lockup-free miss handling (jet), directory-based or L2/L3 coherence, ECC on arrays, virtual memory and TLB interaction, multi-port CPU issue, ACE DVM and full barrier semantics, speculative prefetching, and adaptive replacement.

## Why a blocking cache matters

Blocking simplifies coherence because there is only one transaction in flight. A probe against a pending fill can be answered from a single bypass register (F9); there is no MSHR hazard matrix, no merge CAM, no response reorder buffer. The research value is the measured delta to `jet`: with arrays, policy, observation, and the MESI protocol held constant, the difference between the two IPs is strictly the miss-handling concurrency. amber makes that delta isolable.
