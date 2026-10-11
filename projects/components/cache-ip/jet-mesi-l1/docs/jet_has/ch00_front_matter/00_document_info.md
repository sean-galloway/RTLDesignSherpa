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
| Title | jet — Lockup-Free MESI Snoopy L1 Cache — Hardware Architecture Specification |
| Version | 0.2 |
| Date | 2026-10-11 |
| Status | 0.2: owner rulings inherited from amber/onyx recorded — RACK/WACK omitted from the contract; CD-before-CR confirmed as the family convention. Otherwise the same skeleton: purpose, context, and the decision landscape are real content; chapters shaped by open J-rows are stubs. |
| Scope | `jet` and `jet_ace` tops, the inherited `amber_core`, the MSHR delta, interfaces, parameters, and integration rules for the pair rig and the onyx rig. |
| Not in scope | Speculative prefetching, adaptive replacement, QoS policies, multi-banked parallelism beyond MSHRs, directory-based coherence, L2/L3, ECC, TLBs, multi-port CPU issue, ACE DVM and barrier semantics. |

: Table 0.1: Document information

## Related documents

| Document | Where | Relationship |
|---|---|---|
| jet PRD | [jet PRD](../../../PRD.md) | **binding requirements** — all J-rows and success criteria originate here |
| amber HAS | [amber HAS](../../../../amber-mesi-l1/docs/amber_has/amber_has_index.md) | inherited architecture, interfaces, parameters, and integration rules |
| onyx PRD | [onyx PRD](../../../../onyx-ace-ccu/PRD.md) | onyx D7 defines the ACE-shaped snoop port; onyx D2 defines the coherent-transaction subset |
| AMBA ACE Interface Definition | [AMBA ACE Interface Definition](../../../../References/AMBA_ACE_Interface_Definition.md) | in-repo ACE contract, verified against IHI 0022H |
| cache simulator | [cache simulator](../../../../../../../bin/apps/cache_sim/README.md) | golden parity model; jet extends it to predict concurrency numbers |
| Global Requirements | [Global Requirements](../../../../../../../GLOBAL_REQUIREMENTS.md) | reset macros, array syntax, no bespoke SRAM, filelist registry |
| Chinnakonda, *Designing a Multiprocessor Cache Subsystem* | [Chinnakonda, *Designing a Multiprocessor Cache Subsystem*](../../../../../../../../calibre/books/designing-a-multiprocessor-cache-subsystem/index.md) | background for open decisions: §7.8 forward-progress guarantees, §8.2 deadlocks, §8.3 starvation, §10.8 snoop snarfing, §10.10 outstanding sizing, §13.4 prefetch training |

: Table 0.2: Related documents

## Terminology

**MSHR (miss-status handling register).** A table entry that records an outstanding cache miss: address, expected fill state, and enough context to replay or merge dependent accesses. jet's J1 row decides the organization; until then, the term refers to the function, not a structure.

**Lockup-free.** A cache that continues to service hits and accept new misses while one or more fills are outstanding. For jet, lockup-freedom is bounded by MSHR capacity and the J6 congestion policy.

**Hit-under-miss.** A hit to a resident line is serviced while a different line's fill is in flight. J2 decides the scope: all resident lines, non-conflicting lines only, or read hits only.

**Miss merging.** Two or more CPU misses to the same cache line are satisfied from a single external fetch. J3 decides the merge policy: exact-line alias, line plus offset range, or none.

**Pair rig.** Two `jet` instances plus shared memory; snoops travel peer-to-peer on the ACE-shaped port and misses are plain AXI4 to memory (inherited from amber D10).

**Onyx rig.** A `jet_ace` instance attached to the `onyx` coherency manager; misses become the onyx D2 coherent-transaction subset and snoops arrive from onyx (inherited from amber).

**Rig.** The top-level instantiation you choose: `jet` or `jet_ace`. There is no `RIG` elaboration parameter; the rig is the top (inherited from amber).

## Revision history

| Version | Date | Change |
|---------|------|--------|
| 0.1 | 2026-10-11 | Skeleton HAS. States purpose, context, and the open decision landscape for J1–J7. Records amber inheritance for interfaces, parameters, clock/reset, and observation. |
| 0.2 | 2026-10-11 | Owner rulings inherited from amber/onyx recorded: RACK/WACK omitted from the contract; CD-before-CR confirmed as the family convention. |

: Table 0.3: Revision history

## How to read this book

Chapter 1 states purpose and scope. Chapter 2 is the system shape: use cases, features, context, and a prose block diagram. Chapter 3 is the architecture delta over amber; at 0.1 it is a set of stubs that record the J1–J5 decision landscape and cite the background material that will inform each decision. Chapter 4 is the pin-level interface inventory; the contracts themselves are inherited from amber HAS ch04, with jet-specific stress noted. Chapter 5 is the parameter package; at 0.1 it lists inherited geometry and the pending jet additions. Chapter 6 is integration: clock/reset, verification, characterization, and future hooks.
