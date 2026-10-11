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

# Caches

Research-oriented cache IP. Each IP carries a sedimentary-gemstone codename —
the thematic counterweight to the igneous-rock memory-controller family in
[`../mem-ctrl-ip/`](../mem-ctrl-ip/), whose volcanic names (pumice, scoria,
andesite) track JEDEC-era density the way gemstone names here track cache
behavior: **amber** preserves and stores (the blocking cache — correct,
quiescent, holding its line), **jet** is fossilized wood and jet-fast (the
lockup-free cache — everything still moving while a miss is in flight),
**onyx** is the banded stone — parallel bands, stern and orderly; the
serializer that holds same-address traffic in strict order.

The codename is the RTL identifier prefix and the module/package prefix
(`amber_*`, `jet_*`); the DIRECTORY is the compound `<codename>-<scope>` form,
mirroring the memory-controller convention — `amber-mesi-l1/`, not `amber`.
The bare codename is how an IP is referred to in prose; the compound form is
canonical anywhere a directory names one.

## Members

| Directory | Codename | Scope | RTL prefix | Start here |
|---|---|---|---|---|
| [`amber-mesi-l1/`](amber-mesi-l1/) | **amber** | Blocking MESI snoopy L1 cache — the research baseline | `amber_*` | [README](amber-mesi-l1/README.md) · [HAS](amber-mesi-l1/docs/amber_has/amber_has_index.md) |
| [`jet-mesi-l1/`](jet-mesi-l1/) | **jet** | Lockup-free (MSHR) MESI snoopy L1 — the non-blocking follow-on to amber | `jet_*` | [README](jet-mesi-l1/README.md) · [HAS](jet-mesi-l1/docs/jet_has/jet_has_index.md) |
| [`onyx-ace-ccu/`](onyx-ace-ccu/) | **onyx** | Snoop-based ACE coherency unit — the coherence manager over the house AXI4 fabric | `onyx_*` | [README](onyx-ace-ccu/README.md) · [HAS](onyx-ace-ccu/docs/onyx_has/onyx_has_index.md) |

The design intent: **amber** establishes the coherence protocol, snoop
transport, storage arrays, and observation fabric with the simplest possible
miss handling (a miss blocks); **jet** keeps all of that and adds miss-status
holding registers, hit-under-miss, and miss merging — so the performance
delta between the two is itself the research artifact. **onyx** is the
manager that makes the caches a system on real AMBA plumbing: an Arm-ACE
coherency unit on the house AXI4 fabric (the `pulp-platform/culsans` shape)
that broadcasts snoops, gathers CR responses, decides when memory must be
read, and serialises same-address traffic — the third side of the research
(caches both sides of a snoop, then the fabric between them). Opal stays
unclaimed as a future codename until a concrete follow-on (for example, a
victim cache) earns it.

Family interface decision, 2026-10-05: **cache-ip is ACE-shaped.** onyx owns
and defines the AC/CD/CR snoop-port contract; amber and jet stay
bus-agnostic internally and speak it through a thin adapter (amber D4, onyx
D7 — decided together). Any future cache-ip member adopts the same port
shape by inheritance, so a real ACE interconnect can replace onyx (or the
custom bus around it) without touching cache RTL.

Both IPs are built to be watched: MonBus checkers and perf counters observe
hits, misses, snoops, and evictions in simulation and on board, and the
trace-driven [cache simulator](../../../bin/apps/cache_sim/) app models the
same policy space for sim-vs-RTL hit-rate cross-checks.

Per-IP state, requirements, and architecture live in each directory's
`README.md`, `PRD.md`, and `HAS/` book. This README stays at the family
level: vision first, structure next, then the reference shelf below.

## References

The cache-ip family's unified uarch-design shelf. Items marked `(in-repo)`
live in [`References/`](References/); the full curated inventory is in
[`References/README.md`](References/README.md).

### In-repo reference library

- [`References/AMBA_ACE_Interface_Definition.md`](References/AMBA_ACE_Interface_Definition.md) — the ACE-shaped port contract (AC/CR/CD channels, the six transaction types of the onyx D2 subset, CRRESP decision bits, ACE-Lite), distilled 2026-10-05 and verified clause-by-clause against Arm IHI 0022H. What the family took from it: the normative pin-level contract between amber/jet and onyx.
- [`References/gem5-ruby-protocols/`](References/gem5-ruby-protocols/) — gem5 Ruby SLICC specs (`MESI_Two_Level` and `MOESI_CMP_directory`). What the family took from it: executable transient-state tables used as golden-model source for the Python reference model and FSM oracles.
- `References/Sorin_Hill_Wood_2020_Primer_Memory_Consistency_Cache_Coherence_2ed.pdf` — Sorin, Hill, and Wood, *A Primer on Memory Consistency and Cache Coherence*, 2nd ed. (2020). What the family took from it: coherence invariants, snoopy MESI/MOESI state machines, and the transient-state treatment that the transaction types instantiate.
- `References/Papamarcos_Patel_1984_ISCA_Snoopy_Coherence.pdf` — Papamarcos and Patel, "A Low-Overhead Coherence Solution for Multiprocessors with Private Cache Memories," ISCA 1984. What the family took from it: the original snoopy-cache vocabulary — valid bits per block, state tags, bus-watching — behind amber D4 and D6.
- `References/Jouppi_1991_WRL-91-12_Cache_Write_Policies.pdf` — Jouppi, *Cache Write Policies and Performance*, WRL Research Report 91/12 (1991). What the family took from it: write-back/write-allocate vs write-through/no-allocate analysis and the quantitative case behind amber D5.
- `References/Farkas_Jouppi_1994_WRL-94-3_Non-Blocking_Loads.pdf` — Farkas and Jouppi, *Complexity/Performance Tradeoffs with Non-Blocking Loads*, WRL Research Report 94/3 (1994). What the family took from it: the lockup-free design space — MSHR organization, associativity vs size, miss merging, and full-MSHR policy — that drives jet J1/J3/J6.
- `References/Jouppi_1990_WRL-TN-13_Victim_Cache_Prefetch_Buffers.pdf` — Jouppi, *Improving Direct-Mapped Cache Performance by the Addition of a Small Fully-Associative Cache and Prefetch Buffers*, WRL Technical Note TN-13 (1990). What the family took from it: victim-cache background; kept in the library so the eviction datapath decision (amber D11 / jet J5) stays victim-cache-ready for a future opal follow-on.
- `References/Jaleel_2023_ISCA50_RRIP_Retrospective.pdf` — Jaleel, Theobald, Steely, and Emer, ISCA@50 retrospective on RRIP (2023). What the family took from it: the insertion-prediction framing for the replacement-policy space (amber D7 / cache_sim golden model).
- `References/Berg_2006_WCET_PLRU_Domino_Effects.pdf` — Berg, "PLRU Cache Domino Effects," WCET 2006. What the family took from it: the precise binary-tree PLRU update/evict behavior used as amber D7's timing-tight fallback.
- `References/Stoy_Shen_Arvind_2001_FME_Cache_Coherence_Proofs.pdf` — Stoy, Shen, and Arvind, "Proofs of Correctness of Cache-Coherence Protocols," FME 2001. What the family took from it: how to state and prove no-stale-data and no-deadlock properties as protocol-level invariants (amber D9).
- `References/Balkind_2019_CACM_OpenPiton.pdf` — Balkind et al., "OpenPiton: An Open Source Hardware Platform For Your Research," CACM 2019. What the family took from it: the engineering reality check for a multi-cache fabric — L1/L1.5 split, distributed directory, NoC transport, real RTL/FPGA bring-up — used to size onyx fanout and serialization (onyx D3/D5).

### External books and canonical papers

- Murali Chinnakonda, *Designing a Multiprocessor Cache Subsystem* (Arm Education Media). What the family took from it: the practitioner view of ACE coherency, forward-progress guarantees, deadlock/starvation avoidance, snoop snarfing, and serializer sizing — mined 2026-10-11 for onyx PRD candidate rows N1–N7, the proposed design invariants, and the amber/jet improvement plan (`docs/amber-jet-improvement-plan.md`).
- John L. Hennessy and David A. Patterson, *Computer Architecture: A Quantitative Approach*, 6th ed., Morgan Kaufmann, 2017, ch. 2 Memory Hierarchy Design. What the family took from it: the nonblocking/lockup-free cache theory behind jet, including the MSHR taxonomy of §2.3 (Kroft's taxonomy as the book presents it).
- Steven A. Przybylski, *Cache and Memory Hierarchy Design: A Performance-Directed Approach*, Morgan Kaufmann, 1990. What the family took from it: the write-policy and cache-geometry reasoning behind amber's decisions (see `amber-cache-decisions-alignment.md` D1/D5/D11).
- D. Kroft, "Lockup-Free Instruction Fetch/Prefetch Cache Organization," ISCA 1981. What the family took from it: the original MSHR organization — the jet anchor for lockup-free operation.
- Arm, *AMBA AXI and ACE Protocol Specification*, IHI 0022 (ACE chapters). What the family took from it: the normative ACE protocol definition; the in-repo working definition was verified against issue H. Arm makes the PDF available without charge; see the Sources section of `References/AMBA_ACE_Interface_Definition.md` for the direct link.

### Worked examples and design memos

- `pulp-platform/culsans` (`ace_ccu_top` + CVA6 coherent WB cache), https://github.com/pulp-platform/culsans. What the family took from it: a worked ACE CCU example — read after the in-repo ACE definition, not before.
- [`amber-mesi-l1/docs/amber-cache-decisions-alignment.md`](amber-mesi-l1/docs/amber-cache-decisions-alignment.md) — book-alignment verdicts for amber decisions D1–D11.
- [`docs/amber-jet-improvement-plan.md`](docs/amber-jet-improvement-plan.md) — Chinnakonda-informed improvement proposals for amber (A1–A8) and jet (JI1–JI7).
- The per-component architecture books — current `amber HAS`, `jet HAS`, and `onyx HAS` — linked from the Start here column above.
