<!-- RTL Design Sherpa Documentation Header -->
<table>
<tr>
<td width="80">
  <a href="https://github.com/seang-galloway/RTLDesignSherpa">
    <img src="https://raw.githubusercontent.com/seang-galloway/RTLDesignSherpa/main/docs/logos/Logo_200px.png" alt="RTL Design Sherpa" width="70">
  </a>
</td>
<td>
  <strong>RTL Design Sherpa</strong> · <em>Learning Hardware Design Through Practice</em><br>
  <sub>
    <a href="https://github.com/seang-galloway/RTLDesignSherpa">GitHub</a> ·
    <a href="https://github.com/seang-galloway/RTLDesignSherpa/blob/main/docs/DOCUMENTATION_INDEX.md">Documentation Index</a> ·
    <a href="https://github.com/seang-galloway/RTLDesignSherpa/blob/main/LICENSE">MIT License</a>
  </sub>
</td>
</tr>
</table>

---

<!-- End Header -->

# basalt — Pencil PRD (v0.1 DRAFT)

**Version:** 0.1 (pencil, 2026-10-11)
**Status:** direction penciled at owner request — every row below is OPEN
until it records a name and a date. **No RTL is gated until onyx v1
exists**; this document exists so the unit breakdown and the open questions
stop living only in conversation. When scoped for real work, this PRD is
rewritten properly (v1.0 draft) and the README gains its full text.

## 1. Purpose

The family's capstone: a **shared, banked L2** that inserts into onyx's
memory side — onyx master → basalt front; basalt back-side → the house
memory-controller line. The research question is the family's usual one,
one layer down: *what does a shared last-level cache buy on a small fabric —
hit rate, DRAM-traffic reduction, latency adder, area — measured against the
same trace suite as amber/jet/onyx?*

Position in the stack (recorded 2026-10-11, see onyx HAS future hooks):
basalt sits **below the coherency point**. From the coherence protocol's
perspective it is memory; from onyx's perspective its single AXI4 master
now terminates at basalt instead of raw DRAM. Nothing snoops basalt, so it
has no AC/CD/CR port and the D2 subset / CRRESP adjudication / D7 snoop
contract are untouched.

## 2. Units (penciled, names provisional)

House conventions apply: `basalt_` module prefix, fub/macro/top split,
shared primitives only, MonBus observation per the D8 pattern, filelists
registry. `git mv`-grade renames are cheap now and painful later — names
below are chosen to survive scoping.

| Unit | Provisional name | Job |
|---|---|---|
| Front-end | `basalt_front` | AXI4 slave-facing request path from onyx: accept AR/AW, hash the address to a bank, attribute the source master from ARID/AWID (observability + optional sharer vector), per-bank request queues on house FIFOs. Wraps the house `axi4_slave_rd/wr`. |
| Arrays | `basalt_tag_array`, `basalt_data_array` | Per-way arrays in the `sdpram_core` idiom (amber D11 precedent); lookup port plus fill/drain port. |
| Bank | `basalt_bank` (×B, elaboration) | Distributed bank with its own arbiter and fill/victim buffers — the book's §10.2 distributed model; bank count ≥ attached master count (§10.1). |
| Line FSM | `basalt_line_fsm` | Per-line state machine: V/D plus transients (ALLOCATE / FILL / VICTIM). Scope is an OPEN row (D2): topology A needs only V/D; MOESI cluster tracking belongs to the topology-B variant. |
| Miss file | `basalt_mshr` | Miss-status holding registers, depth an elaboration parameter (bring-up 1, target 2–16); jet's J1–J7 machinery directly reused, sized by the book's §10.8 outstanding-access math. |
| Back-end | `basalt_mem` | AXI4 master toward the mem-ctrl line: burst fill/drain sequencing, outstanding-transaction budget per §10.8, AWID policy per the onyx D5 book note. |
| Victim | `basalt_victim` | Dirty-victim buffering and drain-to-DRAM; clean victims dropped. |
| Replacement | `basalt_repl` | LRU baseline with a policy parameter; RRIP the recorded candidate (book §10.12 — L2 does not see L1 hits, so plain LRU is partially blind). |
| Observation | `basalt_monlite` | MonBus taps: front rd/wr, hit/miss per bank, victim drains, DRAM stalls, MSHR occupancy. |
| Directory (optional) | `basalt_dir` | L1ID sharer vector in the tag (book §10.4) — **elaboration parameter, default off**; useful only if the topology question (D1) ever moves it beside the snoop path. |
| Top | `basalt_top` | Standalone-testable top with BFM masters (culsans-style decoupling) long before onyx exists. |

## Tiering note: why these are fubs, and what would graduate

Everything in the table above is a **sub-block (fub) of the one basalt IP**,
not a standalone IP — that is a deliberate choice, not an accident of
penciling. The repo has three tiers, and basalt follows the amber precedent
(fill/drain/victim/replacement are amber's own fubs, not IPs):

1. **House IP** (`rtl/amba/`, `rtl/common/` — `axi4_master_rd/wr`,
   `gaxi_fifo_sync`, `sdpram_core`): owned by no component, instantiated by
   everyone. Graduation rule: two or more *unrelated* components must need
   it. Nothing in the basalt list graduates — the generic movers it reuses
   already exist at this tier.
2. **Component IP** (amber, jet, onyx): a full product with its own
   PRD/HAS/RTL/DV and a research question. A *function* graduates to this
   tier only when it becomes a research artifact itself. The recorded case:
   the **nonblocking follow-on** (the "jet of L2s" — MSHRs, hit-under-miss,
   decoupled victims at L2 scale) earns its own codename at scoping time;
   that is the "another whole IP for a major function" the family plans for,
   and it is a rung, not a function.
3. **Fubs inside an IP**: the units above. The family's measured-delta
   philosophy depends on functions staying inside the product whose context
   defines them — an MSHR-as-shared-IP between jet and basalt would blur
   exactly the diffs the family exists to measure.

**The one candidate that could stand alone.** `basalt_dir` (the L1ID
sharer-vector directory) is the only penciled unit with a second customer:
onyx's deferred D3 directory-lite question. A standalone snoop-filter IP
could serve onyx without any L2. It is deliberately *not* penciled as an IP
now — it would re-open onyx's scope before onyx v1 exists, and there is
nothing to measure a filter against until onyx's broadcast baseline is real.
If a directory IP ever makes sense, it makes sense after that baseline.

## 3. Decision rows (all OPEN)

| # | Decision | Candidates | What it drives |
|---|---|---|---|
| D1 | Topology position | memory-side, below the coherency point (**recorded default** — consistent with the committed onyx contract) vs book-style cluster-L2 beside the snoop path (would re-open the onyx boundary) | everything: ports, state scope, whether `basalt_dir` means anything |
| D2 | Line-state scope | V/D + transients (topology A) vs MOESI cluster tracking (topology B, book §10.5) | `basalt_line_fsm`, and whether the directory infix in the component name survives scoping (else rename `basalt-wb-l2`) |
| D3 | Inclusivity | non-inclusive / exclusive (LLC norm for topology A) vs inclusive (book §10.3 — argued for *its* topology where the L2 snoop-filters) | tag contents, eviction side effects |
| D4 | Bank count | 2–8 as elaboration, default ≥ attached master count (§10.1) | array duplication, hash, throughput |
| D5 | MSHR depth | 1 (blocking bring-up) → 2–16, §10.8 sizing math | `basalt_mshr`, formal surface |
| D6 | Write policy | write-back, write-allocate baseline (near-certain default) vs write-through | `basalt_victim`, DRAM traffic |
| D7 | Directory elaboration | off (default) / on — depends on D1 | `basalt_dir` |
| D8 | Observation | monlite event classes per unit table, tallied by `monbus_tally_axil` | perf counters, the measured claim |
| D9 | Verification | standalone BFM rig first; onyx-rig integration (amber ×2 + onyx + basalt + mem-ctrl) passing the pair-rig suite unchanged; golden model per family precedent (gem5 Ruby `MESI_Two_Level` lower level or a cache_sim extension) | DV structure, CI time |
| D10 | Back-end profile | which house memory path (pumice/scoria/andesite) terminates `basalt_mem` | interface widths, burst behavior |

## 4. Success criteria (pencil)

1. **Standalone first:** BFM-master rigs prove hit/miss/fill/victim/drain
   behavior before any consumer exists.
2. **Transparency:** the amber pair-rig + onyx suite passes unchanged with
   basalt inserted on the memory path.
3. **The measured claim:** hit rate, DRAM-traffic reduction vs the no-L2
   baseline, and latency adder — all from MonBus capture, same trace suite
   as the family.

## 5. Non-goals (v1 pencil)

AC/CD/CR snoop port (nothing snoops memory); coherence state *against
masters* (basalt is below the coherency point); L3; cache-maintenance
broadcast handling (the onyx D2 subset carries none); QoS; multi-basalt
striping (that is the onyx D1 rejected candidate's territory, one layer
down).

## 6. References (the stocked shelf)

Chinnakonda ch10 is the design manual (banking §10.1–10.2, inclusivity
§10.3–10.4, MOESI-at-L2 §10.5, snoop-response progress §10.6, PoS §10.7,
outstanding sizing §10.8, completion §10.11, replacement §10.12); H&P 6e ch2
and Kroft ISCA'81 back the MSHR file; gem5 Ruby `MESI_Two_Level` is the
golden-model candidate. Family precedents: amber (arrays, fill/drain,
victim, monlite), jet (MSHRs, fairness), onyx D5/D3 (AWID policy, directory
question). See the cache-ip README References section.
