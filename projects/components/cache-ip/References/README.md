# Cache References

Curated 2026-10-05 for the stand-up of the [`cache-ip`](../) family —
[amber](../amber-mesi-l1/PRD.md) (blocking MESI snoopy L1, the baseline),
[jet](../jet-mesi-l1/PRD.md) (same protocol, lockup-free with MSHRs), and
[onyx](../onyx-ace-ccu/PRD.md) (the snoop-based ACE coherency unit). The
family's shared reference library lives here, one level above the IPs,
mirroring the `References/` convention of the ecc-ip components. Everything
except the jet-specific lockup-free material informs all three IPs; the
gem5 protocol extract and the Primer inform amber/jet's coherence core,
while the ACE definition is the onyx/amber-D4 contract document.

## The definition document (read this first)

| File | What it is | Informs |
|---|---|---|
| [`AMBA_ACE_Interface_Definition.md`](AMBA_ACE_Interface_Definition.md) | The in-repo working definition of the ACE-shaped port contract: AC/CR/CD channels, the six transaction types of the onyx D2 subset (ReadShared / ReadUnique / CleanUnique / MakeUnique / WriteBack / Evict), the CRRESP decision bits (DataTransfer / Error / PassDirty / IsShared), ACE-Lite, and what "ACE-shaped" means in this family vs. full IHI 0022 conformance. Distilled 2026-10-05 and verified clause-by-clause against IHI 0022H the same day (verification notes inside); the normative spec (Arm IHI 0022, available from Arm without charge, direct PDF linked inside) wins on any disagreement. | **amber D4 and onyx D7 (both DECIDED 2026-10-05), onyx D2/D4/D5/D6** — the adapter contract, the front-end decoder, the response-gather window, the adjudication logic |

## Research sources (stored PDFs)

All PDFs are freely hosted copies pulled from author/lab/institutional pages
(Cornell CS, UW–Madison, HP Labs WRL mirror, MIT CSG, Dagstuhl, author
sites) on 2026-10-05. Where only a paywalled version of the canonical paper
exists, the entry says so and records the DOI.

| File | Source | Informs |
|---|---|---|
| `Sorin_Hill_Wood_2020_Primer_Memory_Consistency_Cache_Coherence_2ed.pdf` | Sorin, Hill, Wood, *A Primer on Memory Consistency and Cache Coherence*, 2nd ed. (2020) — full book, author-hosted ([UW–Madison copy](https://pages.cs.wisc.edu/~markhill/papers/primer2020_2nd_edition.pdf)) | **The foundation.** Ch. 2–3 (coherence invariants, snoopy MESI/MOESI state machines, transition tables) drive amber D5/D6 and jet's protocol reuse. The snoopy-vs-directory comparison and the transient-state treatment are the two chapters to read before designing anything — most coherence bugs live in transient states, which the simple MESI diagrams omit. Read first. |
| `gem5-ruby-protocols/` | gem5 Ruby SLICC specs: `MESI_Two_Level` and `MOESI_CMP_directory`, verbatim from gem5 master @ `f5c5a6e` (BSD-3, per-file headers; see its README) | Executable, state-table-style protocol specifications with every transient state enumerated (`IS`/`IM`/`SM`/`M^I`/...) — the raw material for deriving amber's state encoding and for building the Python reference model the DV scoreboard replays against (amber D9, jet J7; onyx D10's golden model). `MESI_Two_Level-L1cache.sm` ≈ amber; `MOESI_CMP_directory` is the directory contrast set. |
| `Papamarcos_Patel_1984_ISCA_Snoopy_Coherence.pdf` | Papamarcos & Patel, *A Low-Overhead Coherence Solution for Multiprocessors with Private Cache Memories*, ISCA 1984 — [Cornell course copy](https://www.csl.cornell.edu/courses/ece5750/papamarcos.isca84.pdf) | The original snoopy-cache paper: valid bits per block, state tags, bus-watching. Amber D4 (snoop transport heritage), amber D6 (state minimality). |
| `Jouppi_1991_WRL-91-12_Cache_Write_Policies.pdf` | Jouppi, *Cache Write Policies and Performance*, WRL Research Report 91/12 (1991, full 48p report) — [HP Labs WRL mirror](https://shiftleft.com/mirrors/www.hpl.hp.com/techreports/Compaq-DEC/WRL-91-12.pdf) | Amber D5: write-back+write-allocate vs write-through+no-allocate, subblock placement, write buffering. Quantifies what the M state buys. |
| `Farkas_Jouppi_1994_WRL-94-3_Non-Blocking_Loads.pdf` | Farkas & Jouppi, *Complexity/Performance Tradeoffs with Non-Blocking Loads*, WRL Research Report 94/3 (1994, full 37p report) — [HP Labs WRL mirror](https://shiftleft.com/mirrors/www.hpl.hp.com/techreports/Compaq-DEC/WRL-94-3.pdf) | **Jet's core.** J1 (MSHR organization, associativity vs size), J3 (merging), J6 (full-MSHR policy: strict vs drop-and-retry). The standard citation for the lockup-free design space. |
| `Jouppi_1990_WRL-TN-13_Victim_Cache_Prefetch_Buffers.pdf` | Jouppi, *Improving Direct-Mapped Cache Performance by the Addition of a Small Fully-Associative Cache and Prefetch Buffers*, WRL Technical Note TN-13 (1990) — [HP Labs WRL mirror](https://shiftleft.com/mirrors/www.hpl.hp.com/techreports/Compaq-DEC/WRL-TN-13.pdf) | Not an amber/jet requirement — the victim-cache reference for the future opal follow-on named in the cache-ip README. Included because the eviction datapath decision (amber D11 / jet J5) is cheaper to make victim-cache-ready now. |
| `Jaleel_2023_ISCA50_RRIP_Retrospective.pdf` | Jaleel, Theobald, Steely, Emer — authors' own ISCA@50 **retrospective** (2023), [Cornell-hosted](https://bpb-us-w2.wpmucdn.com/sites.coecis.cornell.edu/dist/7/587/files/2023/06/jaleel_2010_high.pdf). The 12-page original (ISCA 2010, DOI 10.1145/1815961.1815971) is paywalled. | Amber D7: replacement policy space — RRIP/SRRIP/DRRIP insertion-prediction framing, the modern lens on "LRU vs FIFO vs random." The cache_sim golden model should implement the policy in these terms so the sim-vs-RTL cross-check stays exact. |
| `Berg_2006_WCET_PLRU_Domino_Effects.pdf` | Berg, *PLRU Cache Domino Effects*, WCET 2006, OASIcs vol. 4 (open access, [Dagstuhl](https://drops.dagstuhl.de/entities/document/10.4230/OASIcs.WCET.2006.672)) | Amber D7's tree-PLRU candidate: the shortest precise description of binary-tree PLRU update/evict behavior, plus its pathological case (relevant to jet J6 fairness reasoning). |
| `Stoy_Shen_Arvind_2001_FME_Cache_Coherence_Proofs.pdf` | Stoy, Shen, Arvind, *Proofs of Correctness of Cache-Coherence Protocols*, Formal Methods Europe 2001; MIT CSG Memo 432 (March 2001) — [MIT CSG open archive](https://csg.csail.mit.edu/pubs/memos/Memo-432/memo-432.pdf) | Amber D9's SymbiYosys surface: how to state and prove the two target properties (no stale data served; protocol cannot deadlock) as protocol-level invariants rather than ad-hoc assertions. |
| `Balkind_2019_CACM_OpenPiton.pdf` | Balkind et al., *OpenPiton: An Open Source Hardware Platform For Your Research*, CACM 2019 (author copy) — [jbalkind.github.io](https://jbalkind.github.io/docs/balkind-op-cacmrh.pdf) | The engineering reality check for a multi-cache fabric: a production open-source snoopy system — L1/L1.5 split, distributed directory, NoC transport, real RTL + FPGA bring-up. The reference for "what does a shippable coherence fabric look like" when onyx's fanout and serialization get sized (onyx D3/D5). |

## Sought but not freely redistributable (citation only)

- Arm, *AMBA AXI and ACE Protocol Specification*, IHI 0022 — the normative
  ACE definition; available from Arm without charge (direct PDF:
  <https://developer.arm.com/-/media/Arm%20Developer%20Community/PDF/IHI0022H_amba_axi_protocol_spec.pdf>),
  Arm copyright, deliberately not mirrored here. The working subset
  definition lives in-tree as
  [`AMBA_ACE_Interface_Definition.md`](AMBA_ACE_Interface_Definition.md),
  verified against issue H.
- Kroft, *Lockup-Free Instruction Fetch/Prefetch Cache Organization*, ISCA 1981 — the original MSHR paper; no open PDF found (paywalled; retrospectively summarized in Farkas & Jouppi above). DOI 10.1145/285930.285981.
- Al-Zoubi, Milenkovic & Milenkovic, *Performance Evaluation of Cache Replacement Policies for the SPEC CPU2000 Benchmark Suite*, ACMSE 2004 — LRU/FIFO/LFU/random measured comparison, useful when amber D7 picks the default; no open PDF found. DOI 10.1145/986537.986601.
- Pong & Dubois, *Verification Techniques for Cache Coherence Protocols*, ACM Computing Surveys 29(1), 1997 — the exhaustive verification survey behind amber D9's method choice; no open PDF found. DOI 10.1145/248621.248624.

## Open-source implementations (read for structure; licences vary)

| What | Where | Licence | Use |
|---|---|---|---|
| culsans (`ace_ccu_top` + CVA6 coherent WB cache) | https://github.com/pulp-platform/culsans | Solderpad-2.0 | the worked ACE example the definition document and onyx PRD reference; RTL read for structure — never copied into this MIT-licensed repo |
| gem5 Ruby | https://github.com/gem5/gem5 (`src/mem/ruby/protocol/`) | BSD-3 | the SLICC specs above; also runnable as a simulator for protocol-level experiments |
| `bin/apps/cache_sim/` (in-repo) | `../../../../bin/apps/cache_sim/` | MIT (this repo) | the trace-driven policy simulator amber/jet DV cross-checks against |
