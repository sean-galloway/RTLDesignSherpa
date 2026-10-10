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

# amber MESI L1 Cache — Design-Decisions Alignment Memo

**Version:** 0.1
**Date:** 2026-10-10
**Status:** Research memo — cited authority for amber v1.0 documentation
**Scope:** `projects/components/cache-ip/amber-mesi-l1/`, decisions D1–D11 from
PRD.md §3, plus the fabric/ACE-issue design choices in
`rtl/top/amber_ace_top.sv` and `rtl/fub/amber_ace_issue.sv`.

---

## 1. How to cite this memo

Amber's education-site text cites the five target books by print chapter and
section number (e.g. "COD §5.3" or "Handy §4.3.1"). This memo is the
**mapping layer** that makes those citations safe: every amber decision is
mapped to a specific section in one or more of the five books, with the local
converted-source path, and a verdict — **aligned**, **aligned-with-divergence**
(the educational rationale is stated; the divergence is never softened), or
**no-guidance** (the books do not cover the topic). Where a book does not cover
something, that absence is stated explicitly and is itself a citable fact.

Rule for amber docs: cite a book section as authority only for rows marked
**aligned** or **aligned-with-divergence**, and reproduce the divergence note
when citing an aligned-with-divergence row.

## 2. Decision alignment table (D1–D11)

Book anchors give print section numbers and the local converted-source path
(`<book>/` prefixes per the bibliography). Verdicts follow the rule above.

| Decision | amber decision (PRD wording) | Book anchor | Verdict |
|---|---|---|---|
| **D1** | **Cache geometry: 32 KiB / 64 B lines / 4-way (128 sets) as default center, fully parameterised (4–32 KiB, 32–64 B, 2–8 ways), plus a tiny 16-set / 2-way / 64 B config for SymbiYosys tractability.** | **Przybylski §4.1**: "the optimum total cache size is typically in the 32KB to 128KB range" and "this range is relatively insensitive to variations in the workload and memory system" (`cache-and-memory-hierarchy-design-a-performance/ch05-4-performance-directed-cache-design/5.1-4-1-speed-size-tradeoffs-46.md`); **Przybylski §4.2**: direct-mapped to two-way set-associative drops the miss ratio by about 20% for caches up to ~256 KiB total, "associativities greater than two are unwarranted except when mandated by other factors", and the tag-compare-before-data-gating hit-time cost is the main temporal penalty (`5.2-4-2-speed-set-size-tradeoffs-57.md`); **COD §5.4/§5.8**: set-associative placement; "the largest gains are obtained in going from direct mapped to two-way set associative, which yields between a 20% and 30% reduction in the miss rate" (`computer-organization-and-design-risc-v-edition/ch05-5-large-and-fast-exploiting-memory-hierarchy/5.5-5-4-measuring-and-improving-cache-performance.md` and `5.9-5-8-a-common-framework-for-memory-hierarchy.md`); **Harris & Harris §8.3**: cache characterised by capacity, number of sets, block size, and degree of associativity (`digital-design-and-computer-architecture-risc-v/ch08-8-memory-systems/8.3-caches.md`) | **aligned** — 32 KiB/4-way sits inside the books' optimum/typical region; parameterisation is education-first |
| **D2** | **CPU-side interface: GAXI slave.** Chosen over plain valid/ready native port and AXI4 slave; house BFM/monitor coverage and skid/FIFO plumbing already exist, and STREAM can attach as first real consumer without an adapter. | No book covers a house GAXI streaming fabric. COD §5.9's example cache uses a generic 1-bit Read/Write + Valid + Ready + 32-bit address/data processor port (`computer-organization-and-design-risc-v-edition/ch05-5-large-and-fast-exploiting-memory-hierarchy/5.10-5-9-using-a-finite-state-machine-to-control-a-si.md`). | **aligned-with-divergence** — the abstract CPU/cache port is book-canonical; replacing it with the repo's GAXI slave is an education-first divergence (real fabric attach, reuse of house BFM/monitors). Must be flagged as divergence in amber docs |
| **D3** | **Memory-side interface: AXI4 read/write masters on the house `axi4_master_rd`/`axi4_master_wr` wrappers (stream/rapids pattern), `*_monlite` observation per D8.** Chosen over GAXI (D2 already spent that on CPU side) and over simple SRAM bring-up port; matches D8's monitored-paths requirement and the pair-rig shared-memory hook. | COD §5.9's memory interface is "not a fixed number of cycles" and uses 128-bit data with a Ready handshake (`5.10-5-9-using-a-finite-state-machine-to-control-a-si.md`); no SoC fabric or AXI4 appears in COD ch5. | **aligned-with-divergence** — the handshake abstraction is book-canonical; AXI4 bursts + house wrappers are industry/repo constructs the books abstract away. Divergence defended: real bus protocol as a learning objective |
| **D4** | **Snoop transport: ACE-shaped transport — amber implements the AC/CD/CR snoop channels exactly as onyx D7 defines them (family decision: cache-ip is ACE-shaped), staying bus-agnostic internally behind a thin adapter.** | **COD §5.10**: snooping — "every cache ... monitor or snoop on the medium", "this broadcasting to all caches makes snooping protocols simple to implement but also limits their scalability" (`5.11-5-10-parallelism-and-memory-hierarchy-cache-cohe.md`); **COD §5.13**: write-invalidate protocol over a broadcast medium, shared-state bit, owner concept (`5.13-advanced-material-implementing-cache-controllers.md`); **Handy §4.2/§4.3.1**: full coherence-protocol taxonomy including write-once, ownership, MESI, and Futurebus+ (`cache-memory-book-the-second-edition-the-morgan/ch06-maintaining-coherency-in-cached-systems/6.3-4-2-multiple-processor-systems.md`) | **aligned-with-divergence** — the *protocol family* (snoopy write-invalidate MESI) is book-canonical; the **ACE channel names and AC/CD/CR payload encoding** are ARM-specific and beyond all five books (Handy's Futurebus+ §4.3.2 is the closest documented bus-level realization). Cite COD/Handy for the protocol; flag ACE as the transport choice |
| **D5** | **Write policy: write-back + write-allocate.** Write-through/no-allocate deletes the coherence traffic the research exists to measure; it stays available as a bring-up mode only. | **COD §5.3**: write-back defined as "the modified block is written to the lower level of the hierarchy when it is replaced"; write-allocate vs no-write-allocate elaboration (`computer-organization-and-design-risc-v-edition/ch05-5-large-and-fast-exploiting-memory-hierarchy/5.4-5-3-the-basics-of-caches.md`); **Handy §2.2.4**: copy-back + Dirty bit + eviction/victim terminology, and "more than three states can be encoded by the two bits normally used for the Valid and Dirty bits" (`cache-memory-book-the-second-edition-the-morgan/ch04-how-are-caches-designed/4.2-2-2-choosing-cache-policies.md`); **Przybylski Appendix B**: the studied machine class is "write-back, with write buffering ... a write into a cache is assumed to take twice as long as a read, since the tags must be checked before the data array is written" (`cache-and-memory-hierarchy-design-a-performance/ch11-appendix-b-modelling-write-strategy-effects/11.1-appendix-b-modelling-write-strategy-effects.md`) | **aligned** — and the PRD's research rationale (write-through deletes the dirty-snoop traffic the pair rig exists to measure) is the Handy §4.2.4 bus-traffic argument turned into an experiment |
| **D6** | **MESI variant: plain MESI on a 3-bit state field.** MOESI's O-state is a later elaboration upgrade (encoding headroom reserved now); its win — dirty→shared without a memory read — is a measurement for the pair rig, not a v1 requirement. | **COD §5.13**: "The most common extension of this basic protocol is the addition of an exclusive state ... The popular MESI protocol ... uses this structure" (`computer-organization-and-design-risc-v-edition/ch05-5-large-and-fast-exploiting-memory-hierarchy/5.13-advanced-material-implementing-cache-controllers.md`); **Handy §4.3.1**: MESI state semantics; "Exclusive must be entered before going to Modified. No cache line is allowed to go directly from either of the other states to the Modified state"; original Multibus MESI had no write allocation, Intel added write allocation (`cache-memory-book-the-second-edition-the-morgan/ch06-maintaining-coherency-in-cached-systems/6.3-4-2-multiple-processor-systems.md`) | **aligned-with-divergence** — amber pairs MESI with write-allocate, i.e. the Intel/Futurebus+ evolution Handy documents, not the original Multibus form; the 3-bit field with reserved headroom is the Handy §2.2.4 state-encoding point. One line in amber's docs citing both closes this |
| **D7** | **Replacement policy: policy set {LRU, tree-PLRU, FIFO, RANDOM}, default LRU.** LRU/FIFO/RANDOM match the cache_sim exactly; **tree-PLRU is carried as the timing-tight fallback — the one policy with no sim golden model**. | **COD §5.4/§5.8**: LRU "most commonly used"; random replacement simple in hardware; pseudo-LRU approximations for >4-way (`computer-organization-and-design-risc-v-edition/ch05-5-large-and-fast-exploiting-memory-hierarchy/5.5-5-4-measuring-and-improving-cache-performance.md` and `5.9-5-8-a-common-framework-for-memory-hierarchy.md`); **Handy §2.2.2**: true-LRU bit cost (4-way needs 5 bits/line, 8-way 16 bits/line) and Intel pseudo-LRU tree (3 bits/line, "implemented as write-only", "essentially double the speed ... over a true LRU algorithm") (`cache-memory-book-the-second-edition-the-morgan/ch04-how-are-caches-designed/4.2-2-2-choosing-cache-policies.md`) | **aligned-with-divergence** — the "LRU default, tree-PLRU timing fallback" split is exactly Handy's argument; the FIFO/RANDOM additions exist for cache_sim golden-model parity, an education-first extension the books don't require but don't contradict. The tree-PLRU no-golden caveat is a documented amber limitation |
| **D8** | **Observation: `*_monlite` wrappers, not the heavyweight `_mon`.** MonBus taps for hits, misses, snoops, evictions, and state transitions; `*_monlite` ~1/5 the monitor gates, drop-and-count policy never stalls the port. | No book describes a non-intrusive observation fabric or MonBus. COD §5.4 measures caches with counters/models, not hardware observation fabrics (`computer-organization-and-design-risc-v-edition/ch05-5-large-and-fast-exploiting-memory-hierarchy/5.5-5-4-measuring-and-improving-cache-performance.md`). | **aligned-with-divergence (education-first)** — "the observer must not perturb what it measures" is amber's own principle; the books simply don't have instrumentation chapters. Defend as a teaching instrument: amber/jet exist to *produce* the miss-latency numbers COD §5.4 assumes |
| **D9** | **Verification strategy: Pattern-B cocotb grids; SymbiYosys scoped to the control layer at tiny geometry; cache_sim trace-replay parity across LRU/FIFO/RANDOM; FSM oracles derived from gem5 Ruby `MESI_Two_Level` SLICC tables.** | COD §5.9/§5.11 specify the FSM but no verification methodology; Handy/Przybylski predate executable protocol oracles. | **aligned-with-divergence (modern practice)** — flag honestly: the protocol's *content* is book-derived (COD Fig 5.38's skeleton, Handy Table 4.1's MESI matrix, gem5's SLICC as the executable oracle), the *method* is the repo's rds-dv culture |
| **D10** | **First consumer: standalone TB masters for bring-up; gated deliverable is the pair rig — two ambers + shared memory, the coherence research rig.** STREAM attach is documented future hook. | Not covered by any book — no text proposes a coherence research rig as a teaching deliverable. | **aligned-with-divergence (education-first)** — defended: the pair rig is the instrument that answers "what does lockup-freedom actually buy" with measured data, the quantitative question COD §5.4 and Przybylski ch4 both pose |
| **D11** | **Data/tag arrays: `sdpram_core`-based tag/data stores + `gaxi_fifo_sync` house FIFOs for the pending/fill queues.** House no-bespoke-SRAM rule applies. | **Przybylski §4.2**: implementation/technology constraints shape organization — integrated vs discrete RAM cost arguments, tag-compare timing (`cache-and-memory-hierarchy-design-a-performance/ch05-4-performance-directed-cache-design/5.2-4-2-speed-set-size-tradeoffs-57.md`); **COD §5.3**: separate large data RAM and smaller tag RAM (Fig 5.12 caption, `computer-organization-and-design-risc-v-edition/ch05-5-large-and-fast-exploiting-memory-hierarchy/5.4-5-3-the-basics-of-caches.md`) | **aligned-with-divergence** — the books' implementation-constraint reasoning supports the *pattern*; the house primitives themselves are repo constructs |
| **D12** | **No D12 decision is recorded in PRD.md §3.** The decisions table in PRD v0.6 (2026-10-07) ends at D11. The user directive presumes D1–D12, but no twelfth design decision is documented in the cited PRD section. | — | **not applicable** — placeholder row; when a D12 is added to PRD §3, map it here |

## 3. Fabric / ACE-issue choices

These choices live in `rtl/top/amber_ace_top.sv` and `rtl/fub/amber_ace_issue.sv`
and are documented in `docs/amber_mas/ch02_blocks/08_amber_ace_issue.md` and
`docs/amber_has/ch04_interfaces/03_fabric_ace.md`.

### 3.1 What amber decided

`amber_ace_issue` maps cache-side coherence events to the ACE transaction
subset used by the onyx-rig CCU:

| Cache event | ACE transaction | Snoop field (RTL localparam) |
|---|---|---|
| Read miss, shared intent | `ReadShared`  | `ARSNOOP_READ_SHARED  = 4'h1` |
| Read miss, exclusive intent | `ReadUnique`  | `ARSNOOP_READ_UNIQUE  = 4'h7` |
| Write to Shared line | `CleanUnique` | `AWSNOOP_CLEAN_UNIQUE = 3'h6` |
| Write to Invalid line (whole line) | `MakeUnique`  | `AWSNOOP_MAKE_UNIQUE  = 3'h4` |
| Dirty eviction | `WriteBack`   | `AWSNOOP_WRITE_BACK   = 3'h3` |
| Clean eviction | `Evict`       | `AWSNOOP_EVICT        = 3'h5` |

The values are the framework `ACETransactionType` encodings where they fit
the wire width. **CleanUnique's framework value (0xB) collides with
WriteBack (0x3) under 3-bit truncation**, so the family AWSNOOP assigns the
next free code 0x6. This ruling is recorded in
`.superpowers/sdd/2026-10-07-amber-rtl-completion/task-12-report.md`
("Encodings: CleanUnique = 3'h6 chosen because the framework 0xB collides
with WriteBack at 3 bits") and in the RTL header of
`rtl/fub/amber_ace_issue.sv` lines 64–68.

### 3.2 Book alignment

| Topic | Book guidance | Verdict |
|---|---|---|
| Snoopy coherence / write-invalidate / MESI states | COD §5.10/§5.13 and Handy §4.2/§4.3.1 cover the protocol family (see D4/D6 rows). | **aligned** at the protocol level |
| ACE channel names, ARSNOOP/AWSNOOP encodings, CleanUnique/MakeUnique/Evict transactions | None of the five books discusses the ARM AXI/ACE coherence transport or its snoop-field encodings. Handy's closest material is Futurebus+ §4.3.2, which is a different open bus. | **no-guidance** — the CleanUnique=0x6 ruling is repo-local and is disclosed for onyx reconciliation; cite the generic snooping literature for the protocol semantics, not for ACE wire values |
| Combinational event→transaction map, AW-only transactions swallowed on B | No book discusses this micro-architectural mapping; COD §5.13 treats bus transactions as atomic and abstracts the issue stage. | **no-guidance** — amber's `ace_issue` is a repo-specific adapter needed because the core's engines generate plain AXI4 AR/AW and the ACE rig needs snoop fields |
| Auto-pulsed `RACK`/`WACK` inside the house ACE wrappers | Not covered by any book; ACE-specific. | **no-guidance** |

### 3.3 CleanUnique ruling — divergence note

The CleanUnique=0x6 assignment is **not** an alignment with any book; it is a
repo-local encoding decision forced by a width collision. It must be cited as
such in amber docs: "CleanUnique is encoded as 3'h6 in the family AWSNOOP
because the framework enum value 0xB truncates to the same 3-bit code as
WriteBack (0x3); this is an amber/onyx family convention, not an ARM ACE
specification value."

## 4. Gaps in our plans the books expose

Numbered for tracking; "Action" is a concrete spec/doc edit for amber v1.0.

- **G1 — No AMAT/performance model in amber docs.** COD §5.4 gives the
  machinery (CPU time = exec cycles + memory-stall cycles; AMAT = hit time +
  miss rate × miss penalty) and a worked example. Przybylski ch4 gives the
  speed/size/associativity tradeoff contours. The amber PRD carries no such
  model, so MonBus counters have no predicted values to deviate from.
  *Action:* one subsection in amber's docs carrying a worked COD-style example
  with the actual geometry (32 KiB/64 B/4-way) and an assumed DRAM latency.

- **G2 — Physical-cache rationale is unstated.** Handy §2.2.1 (logical vs
  physical caches; aliasing) and COD §5.7 cover virtual memory. Amber is
  physically indexed by construction (no MMU — an explicit non-goal), but no
  doc says so or says why it dodges the aliasing problem.
  *Action:* one paragraph in amber's PRD/HAS citing Handy §2.2.1.

- **G3 — Split-cache and write-policy rationale is one line.** COD §5.3's
  split-vs-combined tradeoff and write-back/write-allocate elaboration, plus
  Handy §2.2.4, are the missing justification for D5.
  *Action:* cite both in amber's docs.

- **G4 — Memory-consistency model never stated.** COD §5.10 elaboration
  separates coherence from consistency. The pair rig documents its ordering
  assumptions against COD §5.10's elaboration.
  *Action:* add a one-paragraph doctrine note to the pair-rig docs.

- **G5 — Replacement-policy discussion omits the pseudo-LRU cost argument.**
  Handy §2.2.2 is the canonical cost/speed justification for tree-PLRU; amber
  D7 currently records the decision but not the book reasoning.
  *Action:* cite Handy §2.2.2 in the replacement-policy doc.

- **G6 — H&P memory-hierarchy chapter is unavailable in the local conversion.**
  The calibre tree for H&P ends inside book chapter 4 (ILP); book chapter 5
  (the canonical quantitative MSHR/nonblocking-cache/multilevel treatment) is
  not converted. Amber blocking decisions do not need it, but any future jet
  MSHR citations cannot come from this tree.
  *Action:* extend the conversion or cite Kroft's MSHR paper and H&P ch5 by
  print section only, flagged as outside the local conversion.

## 5. Deliberately-divergent repo constructs (defense summary)

Marked here once so amber docs can inherit the verdict:

- **GAXI CPU-side slave** (D2), **AXI4 house fabric** (D3), **ACE-shaped
  snoop transport** (D4), **MonBus/monlite observation** (D8), **pair rig as
  gated deliverable** (D10), and **house-primitive SRAM/FIFO rule** (D11) are
  **education-first divergences**: none appears in the five books; each exists
  to teach something the books leave abstract (real SoC fabric; bus-level
  coherence transports; observation without perturbation; controlled
  experiment design; disciplined implementation reuse).

- **MESI + write-allocate** (D6) is a **deliberate divergence from the
  original Multibus MESI form** documented by Handy; amber adopts the
  Intel/Futurebus+ evolution because the pair rig exists to measure the
  coherence traffic that write-allocate generates.

- **CleanUnique = 3'h6** is a **repo-local encoding divergence** from the
  framework enum, forced by 3-bit width collision with WriteBack. It is not a
  book recommendation and must be disclosed as such.

The memo's rule stands: these are cited as divergences with rationale — never
as book-aligned.

## 6. Bibliography

Full citations with the local converted-source paths used for this memo. Cite
by print chapter/section in amber docs; the paths are for maintainers auditing
a claim.

1. **Patterson, David A., and John L. Hennessy.** *Computer Organization and
   Design: The Hardware/Software Interface, RISC-V Edition.* Morgan Kaufmann,
   2018 (1st ed.). Local conversion:
   `/mnt/data/github/calibre/books/computer-organization-and-design-risc-v-edition/`
   — chapters as `chNN-<slug>/`, sections as numbered `.md` files. Chapters
   cited here: 5 (§5.3, §5.4, §5.8, §5.9, §5.10, §5.13 advanced material).

2. **Hennessy, John L., and David A. Patterson.** *Computer Architecture: A
   Quantitative Approach,* 6th ed. Morgan Kaufmann, 2017. Local conversion:
   `/mnt/data/github/calibre/books/computer-architecture-a-quantitative-approach-th/`
   — **note: the local conversion covers front matter and book chapters 1–4
   only** (ILP and earlier). Book chapter 5, the canonical memory-hierarchy
   treatment, is **not present** in this conversion. No amber cache decision
   is cited from H&P because the relevant chapter is missing; this absence is
   itself recorded in G6.

3. **Handy, Jim.** *The Cache Memory Book,* 2nd ed. Morgan Kaufmann, 1998.
   Local conversion:
   `/mnt/data/github/calibre/books/cache-memory-book-the-second-edition-the-morgan/`
   — ch4 §2.2 (cache policies: §2.2.1 logical/physical, §2.2.2 associativity +
   replacement incl. pseudo-LRU, §2.2.4 write-through vs copy-back), ch6
   §4.2/§4.3 (coherency: multiprocessor systems, MESI, Futurebus+, MOESI).

4. **Przybylski, Steven A.** *Cache and Memory Hierarchy Design: A
   Performance-Directed Approach.* Morgan Kaufmann, 1990. Local conversion:
   `/mnt/data/github/calibre/books/cache-and-memory-hierarchy-design-a-performance/`
   — ch3 (background), ch4 (design problem: §4.1 speed–size, §4.2 speed–set
   size), ch11 Appendix B (modelling write-strategy effects).

5. **Harris, Sarah L., and David Harris.** *Digital Design and Computer
   Architecture, RISC-V Edition.* Morgan Kaufmann, 2022. Local conversion:
   `/mnt/data/github/calibre/books/digital-design-and-computer-architecture-risc-v/`
   — ch8 §8.3 (caches: capacity, sets, block size, associativity, replacement,
   write policy).

---

**Last Updated:** 2026-10-10
**Maintainer note:** re-run this memo's mapping if PRD §3 gains a D12 or if
Hennessy & Patterson's book chapter 5 is added to the local conversion
(unblocks G6).

## Navigation

- **← amber PRD:** [PRD.md](../PRD.md)
- **Precedent memo:** [cod-riscv-uarch-alignment.md](../../../riscv-ip/docs/cod-riscv-uarch-alignment.md)
- **Cache-IP line:** [cache-ip README](../../README.md)
