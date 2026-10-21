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
|---|---|
| Title | onyx — Snoop-Based ACE Coherency Unit — Hardware Architecture Specification |
| Version | 0.2 |
| Date | 2026-10-11 |
| Status | 0.2: owner rulings recorded — RACK/WACK omitted from the contract (N1 decided); CD-before-CR confirmed as the family convention (invariant 6 decided). Otherwise the same skeleton: decided contracts and invariant landscape are real; chapters shaped by remaining open D/N rows are stubs. |
| Scope | `onyx` as the coherence manager between the family's ACE-shaped caches and the house AXI4 memory path; N cache-side ACE slave ports, one memory-side AXI4 master, one inter-cache snoop fanout, MonBus observation. |
| Not in scope | Cache storage inside onyx, directory-based coherence except as the D3 snoop-filter candidate, DVM and full barrier semantics, multi-CCU/multi-domain systems, stash/dealloc, CPU or upstream-master port beyond ACE-Lite IO. |

: Table 0.1: Document information

## Related documents

| Document | Where | Relationship |
|---|---|---|
| onyx PRD | [../../../PRD.md](../../../PRD.md) | **binding requirements** — all D/N rows and success criteria originate here |
| cache-ip README | [../../../../README.md](../../../../README.md) | family context and the ACE-shaped interface decision |
| AMBA ACE Interface Definition | [../../../../References/AMBA_ACE_Interface_Definition.md](../../../../References/AMBA_ACE_Interface_Definition.md) | in-repo ACE contract, verified against IHI 0022H; normative for the ACE-shaped ports |
| amber HAS | [../../../../amber-mesi-l1/docs/amber_has/amber_has_index.md](../../../../amber-mesi-l1/docs/amber_has/amber_has_index.md) | the cache that onyx manages; D7 decided the onyx↔amber adapter boundary together with amber D4 |
| jet HAS | [../../../../jet-mesi-l1/docs/jet_has/jet_has_index.md](../../../../jet-mesi-l1/docs/jet_has/jet_has_index.md) | future onyx-rig consumer |
| amber PRD | [../../../../amber-mesi-l1/PRD.md](../../../../amber-mesi-l1/PRD.md) | amber D10 is onyx's first consumer |
| jet PRD | [../../../../jet-mesi-l1/PRD.md](../../../../jet-mesi-l1/PRD.md) | future onyx-rig consumer; onyx must not pre-decide jet's J-rows |
| culsans | `pulp-platform/culsans` — `rtl/src/ace_ccu_top.sv` | worked example of a snoop-based ACE CCU |
| gem5 Ruby protocols | [../../../../References/gem5-ruby-protocols/README.md](../../../../References/gem5-ruby-protocols/README.md) | golden-model source for the Python reference model |
| cache simulator | [../../../../../../../bin/apps/cache_sim/README.md](../../../../../../../bin/apps/cache_sim/README.md) | golden parity model for hit-rate cross-checks |
| Global Requirements | [../../../../../../../GLOBAL_REQUIREMENTS.md](../../../../../../../GLOBAL_REQUIREMENTS.md) | reset macros, array syntax, no bespoke SRAM, filelist registry |
| Chinnakonda, *Designing a Multiprocessor Cache Subsystem* | local Calibre conversion, outside the repo: `/mnt/data/github/calibre/books/designing-a-multiprocessor-cache-subsystem/index.md` | background and candidate invariants |

: Table 0.2: Related documents

## Terminology

**CCU.** Cache coherency unit. In this family, onyx: the manager that receives coherent transactions from attached caches, fans out snoops, gathers responses, decides whether memory must be read, and serializes same-address traffic.

**AC/CD/CR.** The three ACE snoop channels: AC (snoop address from manager to cache), CD (snoop data from cache to manager), CR (snoop response from cache to manager).

**CRRESP bits.** The snoop-response bitfield consumed by onyx's adjudication. The four bits this book names are: `DataTransfer` (bit 0 — "I will drive the line's data on CD"), `PassDirty` (bit 2 — dirty responsibility moves with the data), `IsShared` (bit 3 — another copy may exist), and `Error` (bit 1). `WasUnique` (bit 4) exists per IHI 0022 but is not part of the D2 subset's adjudication path.

**PoS.** Point of Serialization. The structure where same-address transactions are ordered before they are allowed to proceed incompatibly.

**Fanout.** The action of driving an AC snoop request to every peer cache attached to onyx.

**Gather.** The action of collecting the per-cache CR responses (and any CD data) for one coherent transaction and forming the adjudication result.

**Memory-read elision.** Completing a coherent read from cache-supplied data without issuing an AXI4 read to memory. The safe condition is decided by D6; the naive rule "any DataTransfer elides memory" is not correct because Shared copies may still require the DRAM read.

**Pair rig.** Two `amber` or two `jet` instances plus shared memory, with snoops peer-to-peer. onyx is not in this rig.

**Onyx rig.** An `amber_ace` or `jet_ace` instance attached to `onyx`, with memory on the far side of `onyx`.

## Revision history

| Version | Date | Change |
|---|---|---|
| 0.1 | 2026-10-11 | Skeleton: purpose, system context, decided D7 interface contract, invariant landscape, and stubs for every chapter shaped by an open D/N row. |
| 0.2 | 2026-10-11 | Owner rulings recorded: RACK/WACK omitted from the contract (N1 decided); CD-before-CR confirmed as the family convention. |

: Table 0.3: Revision history

## How to read this book

Chapter 1 states purpose and vocabulary. Chapter 2 is the system shape: use cases, features, context, and a prose block diagram. Chapter 3 is the manager architecture; at 0.1 every section is a stub that records the decision landscape and the relevant book citations. Chapter 4 is the pin-level interface inventory; the cache-side ACE port, the memory-side AXI4 master, and the snoop fanout contract are real content at 0.1 because D7 is decided, while the MonBus observation section is a stub pending D9. Chapter 5 is the parameter sketch; all entries are pending. Chapter 6 is integration: verification is real content at 0.1 because the success criteria fix the proof obligations; characterization is a stub; future hooks mix real candidate material with open rows.
