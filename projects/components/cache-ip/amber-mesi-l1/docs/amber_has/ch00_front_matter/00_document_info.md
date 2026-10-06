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

# Document Information

| Field | Value |
|-------|-------|
| Title | amber — Blocking MESI Snoopy L1 Cache — Hardware Architecture Specification |
| Version | 1.0 |
| Date | 2026-10-06 |
| Status | HAS ratifies the Pre-HAS sketch; PRD decisions D1, D2, D4, D5, D6, D7, D8, D9, D10 are DECIDED. D3 (memory-side shape) and D11 (array construction) remain OPEN and are recorded in the chapters they shape. |
| Scope | `amber` and `amber_ace` tops, the shared `amber_core`, interfaces, parameters, and integration rules for the pair rig and the onyx rig. |
| Not in scope | Lockup-free miss handling (jet), directory-based coherence, L2/L3, ECC, TLBs, multi-port CPU issue, ACE DVM and barrier semantics. |

: Table 0.1: Document information

## Related documents

| Document | Where | Relationship |
|---|---|---|
| amber PRD | [../../../PRD.md](../../../PRD.md) | **binding requirements** — all decisions and success criteria originate here |
| amber Pre-HAS | [../amber_prehas.md](../amber_prehas.md) | architecture sketch ratified by this book |
| jet PRD | [../../../../jet-mesi-l1/PRD.md](../../../../jet-mesi-l1/PRD.md) | lockup-free follow-on; amber must not pre-decide its open rows |
| onyx PRD | [../../../../onyx-ace-ccu/PRD.md](../../../../onyx-ace-ccu/PRD.md) | defines the ACE-shaped snoop port (D7) and the coherent-transaction subset (D2) |
| AMBA ACE Interface Definition | [../../../../References/AMBA_ACE_Interface_Definition.md](../../../../References/AMBA_ACE_Interface_Definition.md) | in-repo ACE contract, verified against IHI 0022H |
| gem5 Ruby protocols | [../../../../References/gem5-ruby-protocols/README.md](../../../../References/gem5-ruby-protocols/README.md) | source for the Python reference model and FSM oracles |
| cache simulator | [../../../../../../../bin/apps/cache_sim/README.md](../../../../../../../bin/apps/cache_sim/README.md) | golden parity model for LRU/FIFO/RANDOM |
| Global Requirements | [../../../../../../../GLOBAL_REQUIREMENTS.md](../../../../../../../GLOBAL_REQUIREMENTS.md) | reset macros, array syntax, no bespoke SRAM, filelist registry |

: Table 0.2: Related documents

## Terminology

**Pair rig.** Two `amber` instances plus shared memory; snoops travel peer-to-peer on the ACE-shaped port and misses are plain AXI4 to memory (amber D10).

**Onyx rig.** An `amber_ace` instance attached to the `onyx` coherency manager; misses become the onyx D2 coherent-transaction subset and snoops arrive from onyx.

**Rig.** The top-level instantiation you choose: `amber` or `amber_ace`. There is no `RIG` elaboration parameter; the rig is the top (Pre-HAS Q1, resolved 2026-10-06).

**F-item.** Feature sketch from the Pre-HAS (F1–F18); this HAS ratifies each decided sketch and records where it remains open.

## Revision history

| Version | Date | Change |
|---------|------|--------|
| 1.0 | 2026-10-06 | Full HAS. Ratifies Pre-HAS F1–F18 against PRD v0.5 decisions, fixes the two-top structure, the module set, the interface pin contracts, the parameter sketch, the verification strategy, and the open D3/D11 questions. |

: Table 0.3: Revision history

## How to read this book

Chapter 1 states purpose and vocabulary. Chapter 2 is the system shape: use cases, features, context, and one block diagram. Chapter 3 is the architecture — the shared core, data flow, the blocking control FSM, the coherence FSM, and arbitration. Chapter 4 is the pin-level interface inventory. Chapter 5 is the parameter package. Chapter 6 is integration: clock/reset, verification, characterization, and future hooks.
