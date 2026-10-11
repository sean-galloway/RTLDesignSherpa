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

# amber / jet — Improvement Plan (Chinnakonda-informed)

**Version:** 0.1 (2026-10-11)
**Status:** Proposal plan informed by Murali Chinnakonda, *Designing a Multiprocessor Cache Subsystem*. Nothing here is decided; a decision is DECIDED only when it records a name and a date.

---

## 1. Method

This plan mines the local Calibre conversion of Chinnakonda's book (`/mnt/data/github/calibre/books/designing-a-multiprocessor-cache-subsystem/index.md`) for topics that touch the amber/jet boundary, then validates each candidate against the current repo state.

Chapters read in full for citations used here:

- ch06 Arm memory instruction set: §6.3 (exclusive loads/stores), §6.4–6.5 (consistency/barriers/multi-copy atomicity), §6.8–6.9 (memory types/device vs normal)
- ch07 Multi-processing: §7.4 (WriteBack/Evict), §7.7 (forward-progress guarantees), §7.9–7.10 (store-exclusive livelock), §7.20 (RACK/WACK)
- ch08 Livelocks/deadlocks/starvation: §8.1 (livelocks), §8.2 (deadlocks), §8.3 (starvation)
- ch09 Load-store section: §9.12–9.14 (hit predictor/tag-less cache)
- ch10 Level-2 cache: §10.5 (implementing inclusivity), §10.6 (forward progress / snarfing), §10.7 (POS / device accesses)
- ch11 Mem-copy: §11.1–11.3 (stream detection / L1 behavior)
- ch13 Hardware prefetching: §13.3–13.4 (training discipline / start-maintenance-end)
- ch14 ACE Q&A: §14.18 (channel dependencies / in-order snoop responses), §14.33 (multi-copy atomicity), §14.39 (RACK/WACK)

Each item below states the book anchor, the current repo state (with a relative doc link), the proposed improvement, an effort estimate, a priority, and the repo row or chapter it feeds. Items that are already handled or are out of scope for an L1 cache are listed in §4 with a one-line reason.

---

## 2. Amber improvement items

### A1 — Exclusive loads/stores and the internal exclusive monitor

| Field | Value |
|---|---|
| **Area** | CPU/cache interface for LDREX/STREX semantics |
| **Book citation** | Chinnakonda §6.3, §7.9–7.10, §8.1 |
| **Current repo state** | The [amber PRD](../amber-mesi-l1/PRD.md) §3 decisions D1–D11 and the [HAS CPU-interface chapter](../amber-mesi-l1/docs/amber_has/ch04_interfaces/01_cpu_gaxi.md) define a GAXI slave for ordinary loads and stores. There is no mention of LDREX/STREX, exclusive monitor state, or how a snoop invalidates a monitor. The [coherence FSM chapter](../amber-mesi-l1/docs/amber_has/ch03_architecture/04_coherence_fsm.md) maps only the six IHI0022 snoop encodings (ReadShared, ReadOnce, ReadUnique, CleanShared, CleanInvalid, MakeInvalid); it does not discuss monitor-clear semantics on snoops. |
| **Proposal** | Document amber's position explicitly: the internal exclusive monitor is a load-store-unit (core-side) construct, not an L1-cache state. amber sees only ordinary read/write requests; a future CPU core that issues LDREX/STREX owns the monitor and must clear it on any snoop to the monitored address. If a future core interface ever carries an exclusive flag, amber must respond to STREX with pass/fail derived from whether the line is still exclusive when the store arrives. Until then, no RTL change in amber. |
| **Effort** | S (documentation) |
| **Priority** | P3 |
| **Feeds** | [amber PRD](../amber-mesi-l1/PRD.md) non-goals; [HAS ch04 CPU interface](../amber-mesi-l1/docs/amber_has/ch04_interfaces/01_cpu_gaxi.md) |

### A2 — Snoop-response sourcing rule for pending fills

| Field | Value |
|---|---|
| **Area** | Snoop responder / pending-fill bypass |
| **Book citation** | Chinnakonda §7.7 (forward-progress guarantees), §10.6 (forward progress of snoop responses) |
| **Current repo state** | The [coherence FSM chapter](../amber-mesi-l1/docs/amber_has/ch03_architecture/04_coherence_fsm.md) shows a pending-fill bypass: a snoop that matches a pending fill reads "post-fill state" from a bypass register. It does not explicitly state the rule that the snoop must respond immediately with "not present" when the fill data has not yet arrived, nor does it forbid stalling the snoop on unrelated resources such as a full victim buffer or a blocked write-back. |
| **Proposal** | Harden the pending-fill bypass into a documented and formally proven rule. If a snoop hits a pending fill and the fill data has arrived, source the response from the fill buffer; if the fill data has not arrived, respond DataTransfer=0/PassDirty=0/IsShared=0 immediately. The snoop must never wait for an unrelated victim buffer, write buffer, or MSHR entry. Add this rule to the SymbiYosys no-deadlock proof set in [PRD D9](../amber-mesi-l1/PRD.md). |
| **Effort** | M |
| **Priority** | P1 |
| **Feeds** | [PRD D9](../amber-mesi-l1/PRD.md); [HAS ch03 coherence FSM](../amber-mesi-l1/docs/amber_has/ch03_architecture/04_coherence_fsm.md); [HAS ch03 arbitration](../amber-mesi-l1/docs/amber_has/ch03_architecture/05_arbitration_bypass.md) |

### A3 — Clean-victim `Evict` messaging for snoop-filter accuracy

| Field | Value |
|---|---|
| **Area** | Memory-side ACE transaction issue |
| **Book citation** | Chinnakonda §7.4, §10.5 |
| **Current repo state** | The [fabric ACE chapter](../amber-mesi-l1/docs/amber_has/ch04_interfaces/03_fabric_ace.md) already maps "clean eviction → `Evict`" in Table 4.2. The [alignment memo](../amber-mesi-l1/docs/amber-cache-decisions-alignment.md) records this mapping. However, the [PRD D5](../amber-mesi-l1/PRD.md) rationale focuses on dirty WriteBack traffic; it does not explicitly require that every clean victim emit an `Evict` rather than being dropped silently. |
| **Proposal** | Verify in RTL and testbench that `amber_ace_issue` emits an `Evict` transaction for every clean victim (not merely that the encoding exists). Add a MonBus event for clean evictions per [PRD D8](../amber-mesi-l1/PRD.md) so that a future [onyx D3](../onyx-ace-ccu/PRD.md) snoop filter can stay accurate. Document that `Evict` is the L1's way of telling the system interconnect the line is no longer resident. |
| **Effort** | S–M |
| **Priority** | P2 |
| **Feeds** | [PRD D5](../amber-mesi-l1/PRD.md), [D8](../amber-mesi-l1/PRD.md); [HAS ch04/03](../amber-mesi-l1/docs/amber_has/ch04_interfaces/03_fabric_ace.md); [onyx D3](../onyx-ace-ccu/PRD.md) |

### A4 — Temporary snoop-stall rule for a non-speculative store holding ownership

| Field | Value |
|---|---|
| **Area** | Coherence FSM livelock avoidance |
| **Book citation** | Chinnakonda §8.1 (livelock case 4 and the "temporary" qualifier), §7.9–7.10 (competing CleanUnique/store-exclusive livelock) |
| **Current repo state** | amber is blocking and single-outstanding; the [coherence FSM chapter](../amber-mesi-l1/docs/amber_has/ch03_architecture/04_coherence_fsm.md) issues `CleanUnique`/`MakeUnique` for writes but does not describe a temporary snoop-stall window after ownership is granted. Because amber blocks, the window is small, but the rule is not written down. |
| **Proposal** | Define a coherence-FSM hook: when a non-speculative store has received ownership (the line is Exclusive/Modified-bound) but has not yet updated the line, incoming snoops to that line may be stalled for a bounded number of cycles so the store can complete. The stall must be temporary and must never depend on an event that may not happen (e.g., waiting for a fill). Document this as a future-proofing rule; it becomes essential for jet, where multiple misses can be in flight. |
| **Effort** | M |
| **Priority** | P2 |
| **Feeds** | [HAS ch03 coherence FSM](../amber-mesi-l1/docs/amber_has/ch03_architecture/04_coherence_fsm.md); jet [PRD J6](../jet-mesi-l1/PRD.md) |

### A5 — `RACK`/`WACK` handling in the amber ACE adapter

| Field | Value |
|---|---|
| **Area** | ACE master acknowledge signals |
| **Book citation** | Chinnakonda §7.20, §14.39 |
| **Current repo state** | The [fabric ACE chapter](../amber-mesi-l1/docs/amber_has/ch04_interfaces/03_fabric_ace.md) states that `m_axi_rack`/`m_axi_wack` are "auto-pulsed inside the adapters one cycle after the last R beat / the B handshake" and that `amber_ace_issue` never drives them because the [onyx D2](../onyx-ace-ccu/PRD.md) subset has no ordering semantics that need master-controlled acknowledges. |
| **Proposal** | Evaluate making `RACK`/`WACK` optional via an elaboration parameter. The book argues they can be omitted if data return and snoops take the same ordered path to the coherency point. Because amber's snoop adapter already enforces CD-before-CR and processes snoops one at a time, the onyx-rig may be able to omit the auto-pulse and reduce snoop latency. Default should remain auto-pulse until a compliance test proves omission is safe. Document the condition explicitly. |
| **Effort** | S |
| **Priority** | P2 |
| **Feeds** | [HAS ch04/03](../amber-mesi-l1/docs/amber_has/ch04_interfaces/03_fabric_ace.md); [onyx D7](../onyx-ace-ccu/PRD.md) contract |

### A6 — CD/CR in-order, no-ID snoop response obligations

| Field | Value |
|---|---|
| **Area** | ACE snoop response ordering |
| **Book citation** | Chinnakonda §7.1, §14.18 (ACE snoops carry no ID; responses must be in order) |
| **Current repo state** | The [snoop adapter chapter](../amber-mesi-l1/docs/amber_has/ch04_interfaces/04_snoop_accdcr.md) says "responses are returned in the order of the AC addresses" and that amber strengthens this by completing CD beats before asserting CR. The [onyx D4](../onyx-ace-ccu/PRD.md) row still calls the response-gather mechanism OPEN. |
| **Proposal** | Move the no-ID in-order obligation from an adapter implementation detail into the onyx-facing port contract. Add a compliance assertion that CR responses are strictly in AC order and that CDLAST for transaction N is asserted before CR for transaction N. This protects both amber and jet, because jet's MSHRs make out-of-order internal snoop handling tempting. |
| **Effort** | S |
| **Priority** | P1 |
| **Feeds** | [amber D4](../amber-mesi-l1/PRD.md); [onyx D4](../onyx-ace-ccu/PRD.md), [D7](../onyx-ace-ccu/PRD.md); [HAS ch04/04](../amber-mesi-l1/docs/amber_has/ch04_interfaces/04_snoop_accdcr.md) |

### A7 — Multi-copy-atomic store invariant as a documented assumption

| Field | Value |
|---|---|
| **Area** | Memory consistency model for the pair rig |
| **Book citation** | Chinnakonda §6.4–6.5, §14.33 |
| **Current repo state** | The [alignment memo](../amber-mesi-l1/docs/amber-cache-decisions-alignment.md) §4 G4 notes that "Memory-consistency model never stated." The [PRD](../amber-mesi-l1/PRD.md) non-goals do not list consistency. |
| **Proposal** | Document that the amber/onyx pair rig assumes multi-copy-atomic stores: a store is not considered complete until its ownership invalidations have reached all observers. This is the book's recommended simplification and matches the KISS argument in §6.5. State that non-multi-copy-atomic behavior is out of scope. This is a documentation-only proposal. |
| **Effort** | S |
| **Priority** | P2 |
| **Feeds** | [PRD non-goals](../amber-mesi-l1/PRD.md); [alignment memo G4](../amber-mesi-l1/docs/amber-cache-decisions-alignment.md); pair-rig documentation |

### A8 — Device vs normal memory ordering at the cache boundary

| Field | Value |
|---|---|
| **Area** | CPU-side memory-type semantics |
| **Book citation** | Chinnakonda §6.8–6.9 (memory types), §10.7 (device accesses in L2/POS) |
| **Current repo state** | The [PRD D2](../amber-mesi-l1/PRD.md) CPU-side interface is a GAXI slave; the [HAS CPU-interface chapter](../amber-mesi-l1/docs/amber_has/ch04_interfaces/01_cpu_gaxi.md) does not carry memory-type or cacheability attributes. There is no mention of device memory, non-cacheable memory, or shareability domains. |
| **Proposal** | Document that amber v1.0 treats all CPU-side requests as normal write-back cacheable memory. Device-memory ordering, non-cacheable bypass, and shareability-domain interpretation are deferred to the attached CPU core / load-store unit. If the GAXI interface is later extended with memory-type signals, define that device requests bypass the cache (or are treated as non-cacheable) and that the core is responsible for program-order enforcement. |
| **Effort** | S |
| **Priority** | P3 |
| **Feeds** | [PRD D2](../amber-mesi-l1/PRD.md); [HAS ch04/01](../amber-mesi-l1/docs/amber_has/ch04_interfaces/01_cpu_gaxi.md); [future hooks](../amber-mesi-l1/docs/amber_has/ch06_integration/04_future_hooks.md) |

---

## 3. Jet improvement items

IDs use `JI` to avoid colliding with the jet PRD rows J1–J7.

### JI1 — Snoop visibility into MSHRs

| Field | Value |
|---|---|
| **Area** | Lockup-free snoop-against-pending-miss handling |
| **Book citation** | Chinnakonda §7.7, §8.2, §10.6 |
| **Current repo state** | The [jet PRD J4](../jet-mesi-l1/PRD.md) says a probe against a pending line "must see the post-fill state or stall cleanly." The [amber HAS](../amber-mesi-l1/docs/amber_has/ch03_architecture/04_coherence_fsm.md) has a single pending-fill bypass; jet has no detailed architecture yet. |
| **Proposal** | Define the MSHR-visible snoop rule: every MSHR exposes its target address and a `fill_arrived` flag. A matching snoop with arrived data sources the response from the fill buffer (or merged data) and updates MSHR state if the snoop invalidates the line; a matching snoop without arrived data responds "not present" immediately. The response must not stall waiting for MSHR allocation, victim-buffer space, or write-buffer drainage. Document the interaction with [onyx D4](../onyx-ace-ccu/PRD.md) response gather and [onyx D5](../onyx-ace-ccu/PRD.md) same-address serialization. |
| **Effort** | M–L |
| **Priority** | P1 |
| **Feeds** | [jet PRD J1](../jet-mesi-l1/PRD.md), [J2](../jet-mesi-l1/PRD.md), [J4](../jet-mesi-l1/PRD.md); [amber HAS ch03/04](../amber-mesi-l1/docs/amber_has/ch03_architecture/04_coherence_fsm.md) |

### JI2 — Victim-buffer snarfing

| Field | Value |
|---|---|
| **Area** | Dirty-victim handling under outstanding fills |
| **Book citation** | Chinnakonda §10.6 mechanism 1 (snarfing data from write/victim buffers) |
| **Current repo state** | The [jet PRD J5](../jet-mesi-l1/PRD.md) says a dirty victim behind an outstanding fill must write back without deadlocking and proposes victim-buffer depth 0–4. It does not mention forwarding snoop data from the victim buffer or killing the pending WriteBack. |
| **Proposal** | Extend J5 with victim-buffer snarfing: when a snoop arrives for a line that is sitting in the victim buffer awaiting WriteBack, the snoop response sources the data directly from the victim buffer and the pending WriteBack entry is killed or marked complete. This breaks the classic deadlock where the WriteBack cannot drain because downstream buffers are full waiting for the very snoop response that the victim buffer could have supplied. |
| **Effort** | M |
| **Priority** | P1 |
| **Feeds** | [jet PRD J5](../jet-mesi-l1/PRD.md), [J6](../jet-mesi-l1/PRD.md) |

### JI3 — Buffer-reservation deadlock rule

| Field | Value |
|---|---|
| **Area** | Speculative-buffer allocation and deadlock avoidance |
| **Book citation** | Chinnakonda §8.2 deadlock case 4 |
| **Current repo state** | The [jet PRD J6](../jet-mesi-l1/PRD.md) discusses policy when MSHRs are full (stall / drop-and-retry / throttle) and snoop-vs-fill arbitration priority, but it does not require reservation of entries for the oldest non-speculative access. |
| **Proposal** | Add a reservation rule to J6: every buffer that can accept speculative entries (MSHR, store buffer, fill buffer, victim buffer) must reserve at least one entry for the oldest non-speculative access. Without this reservation, a buffer can fill with younger speculative entries and deadlock because the oldest entry that would allow them to retire cannot allocate. Prove this with the SymbiYosys deadlock target in [jet success criterion 3](../jet-mesi-l1/PRD.md). |
| **Effort** | M |
| **Priority** | P1 |
| **Feeds** | [jet PRD J6](../jet-mesi-l1/PRD.md); [jet success criterion 3](../jet-mesi-l1/PRD.md) |

### JI4 — Fairness via timeout counters instead of fixed priorities

| Field | Value |
|---|---|
| **Area** | Arbitration fairness / starvation avoidance |
| **Book citation** | Chinnakonda §8.3 |
| **Current repo state** | The [amber HAS ch03/05](../amber-mesi-l1/docs/amber_has/ch03_architecture/05_arbitration_bypass.md) uses "snoop-priority round-robin." The [jet PRD J6](../jet-mesi-l1/PRD.md) mentions "snoop-vs-fill arbitration priority" without specifying fixed vs timeout-based. |
| **Proposal** | Replace or augment fixed snoop/CPU/fill priorities with timeout counters: after N consecutive wins by one requestor, the arbiter grants to another eligible requestor. Emit a MonBus event when a timeout flip occurs so starvation can be measured. Add a SymbiYosys no-starvation proof for the MSHR-full and victim-buffer-full corner cases. |
| **Effort** | S–M |
| **Priority** | P2 |
| **Feeds** | [jet PRD J6](../jet-mesi-l1/PRD.md); [amber HAS ch03/05](../amber-mesi-l1/docs/amber_has/ch03_architecture/05_arbitration_bypass.md) |

### JI5 — Prefetch discipline for a future hook

| Field | Value |
|---|---|
| **Area** | Hardware prefetching constraints |
| **Book citation** | Chinnakonda §13.3 (train on misses, loads only, no store prefetches that invalidate), §13.4 (start/maintenance/end) |
| **Current repo state** | The [jet PRD](../jet-mesi-l1/PRD.md) lists "Speculative prefetching" as a non-goal. There is no prefetch architecture. |
| **Proposal** | If prefetch is ever added as a future hook, constrain it up front: train only on cache misses (not hits), issue only for load streams, never issue store-ownership prefetches that would invalidate peer lines, mark prefetched lines so their utility can be measured, and stop a stream when demand hits against it disappear. Keep this as documentation only for jet v1.0. |
| **Effort** | S (documentation) / M (if implemented) |
| **Priority** | P3 |
| **Feeds** | [jet PRD non-goals](../jet-mesi-l1/PRD.md); [future hooks](../amber-mesi-l1/docs/amber_has/ch06_integration/04_future_hooks.md) |

### JI6 — Hit predictor / tag-less cache as recorded future hooks only

| Field | Value |
|---|---|
| **Area** | Micro-architectural timing/power ideas |
| **Book citation** | Chinnakonda §9.12–9.14 |
| **Current repo state** | The [jet PRD](../jet-mesi-l1/PRD.md) non-goals include "adaptive replacement" but do not mention hit predictors or tag-less caches. The [amber HAS future-hooks](../amber-mesi-l1/docs/amber_has/ch06_integration/04_future_hooks.md) table does not list them. |
| **Proposal** | Record hit predictor and tag-less cache as future hooks only; do not implement in jet v1.0. Tag-less cache requires TLB integration, which is an amber non-goal. Hit predictor requires an extra array, power accounting, and aliasing analysis. Add one paragraph to the jet future-hooks section describing why each is deferred. |
| **Effort** | S |
| **Priority** | P3 |
| **Feeds** | [jet PRD non-goals](../jet-mesi-l1/PRD.md); [amber future hooks](../amber-mesi-l1/docs/amber_has/ch06_integration/04_future_hooks.md) |

### JI7 — Mem-copy stream detection interplay as a future hook

| Field | Value |
|---|---|
| **Area** | Mem-copy read/write stream handling |
| **Book citation** | Chinnakonda §11.1–11.3 |
| **Current repo state** | Neither the [amber PRD](../amber-mesi-l1/PRD.md) nor the [jet PRD](../jet-mesi-l1/PRD.md) mentions mem-copy streams. [Amber D5](../amber-mesi-l1/PRD.md) decided write-back + write-allocate for all stores. |
| **Proposal** | Record mem-copy stream detection as a future hook: when a read stream paired with a write stream is detected, switch store misses to no-write-allocate and restrict read allocation to dedicated ways to avoid strip-mining useful data. This is explicitly beyond jet v1.0 and depends on a CPU core that can signal stream hints or on heuristics in the cache itself. |
| **Effort** | S |
| **Priority** | P3 |
| **Feeds** | [jet PRD non-goals](../jet-mesi-l1/PRD.md); [amber D5](../amber-mesi-l1/PRD.md) |

---

## 4. Explicitly rejected / not-applicable list

These book topics were evaluated and deliberately excluded from the amber/jet improvement list.

| Book topic | Section | Reason for exclusion |
|---|---|---|
| L2 inclusivity / directory construction | §10.3–10.4 | This is [onyx D3](../onyx-ace-ccu/PRD.md) material (snoop filter / directory-lite), not an L1 cache responsibility. |
| LSU pipeline internals | ch09 | Core-side load/store scheduler and pipeline design; outside the cache boundary. |
| TLB and walk unit | ch12 | Out of scope per [amber PRD non-goals](../amber-mesi-l1/PRD.md) (virtual memory / TLB interaction). |
| DRAM buffer sizing for mem-copy | §11.6–11.7 | Memory-controller domain; the cache does not size DRAM buffers. |
| Banking beyond what MSHRs imply | §9.15 | Listed as a jet non-goal (multi-banked parallelism beyond MSHRs). |
| Software prefetch instructions | §6.11 | Opcode decode / CPU-core feature; the cache only sees the resulting demand requests. |
| DVM / barrier propagation | §6.6–6.7, §7.18 | Out of scope per [onyx D8](../onyx-ace-ccu/PRD.md). |
| Non-temporal / mem-copy allocation heuristics | §11.1 detail | Beyond v1.0; only stream detection is recorded as a future hook. |

---

## 5. Sequencing proposal

This sequencing assumes amber's "Task 14" verification freeze is the point at which the pair-rig RTL and formal targets are frozen before rig-integration DV begins.

### Before amber verification freeze

These items change the formal surface, the onyx-facing contract, or the consistency assumptions and should land before the freeze:

- **A2** — pending-fill snoop sourcing rule (adds a SymbiYosys deadlock target).
- **A5** — optional `RACK`/`WACK` omission evaluation (may change adapter timing).
- **A6** — CD/CR in-order contract made explicit (affects onyx D4 gather logic).
- **A7** — multi-copy-atomic invariant documented (pair-rig assumption).

These documentation-only items can land at the same time without RTL risk:

- **A1** — exclusive monitor is core-side.
- **A8** — device memory ordering deferred to core.

### Post-rig / future-hook material

These items are either lower priority or belong to jet/non-goal future work:

- **A3** — clean-victim `Evict` event (important for a future onyx D3 snoop filter, but not needed for the first pair rig).
- **A4** — temporary snoop-stall for non-speculative stores (more urgent for jet; document in amber as a forward-compatibility hook).
- **JI1** — MSHR snoop visibility (jet architecture).
- **JI2** — victim-buffer snarfing (jet J5).
- **JI3** — buffer-reservation rule (jet J6).
- **JI4** — timeout-counter fairness (jet J6).
- **JI5** — prefetch discipline (future hook).
- **JI6** — hit predictor / tag-less cache (future hook).
- **JI7** — mem-copy stream detection (future hook).

---

## 6. Surprises / repo-state notes

1. **README stale on RTL status.** The [cache-ip README](../README.md) says all three IPs are "Scaffolded — README + PRD only, no RTL," but the [amber HAS](../amber-mesi-l1/docs/amber_has/amber_has_index.md) references RTL modules (`amber_ace_issue`, `amber_snoop_resp`, `amber_control`) and the alignment memo cites RTL line numbers. An `rtl/` directory exists under `amber-mesi-l1/`. The README needs an update; this plan does not attempt it.

2. **Clean `Evict` is already encoded but not proven.** The [fabric ACE chapter](../amber-mesi-l1/docs/amber_has/ch04_interfaces/03_fabric_ace.md) maps clean evictions to `Evict`, so A3 is a verification/documentation tightening rather than a new transaction type.

3. **Pending-fill bypass exists, rule is implicit.** The [coherence FSM chapter](../amber-mesi-l1/docs/amber_has/ch03_architecture/04_coherence_fsm.md) shows the bypass hardware; A2 is about making the deadlock-avoidance rule explicit and proving it.

4. **Consistency model is unclaimed territory.** The [alignment memo](../amber-mesi-l1/docs/amber-cache-decisions-alignment.md) flags this as G4; A7 is the proposal to close that gap with the book's recommended multi-copy-atomic simplification.

---

## 7. Navigation

- **amber PRD:** [../amber-mesi-l1/PRD.md](../amber-mesi-l1/PRD.md)
- **jet PRD:** [../jet-mesi-l1/PRD.md](../jet-mesi-l1/PRD.md)
- **onyx PRD:** [../onyx-ace-ccu/PRD.md](../onyx-ace-ccu/PRD.md)
- **amber HAS index:** [../amber-mesi-l1/docs/amber_has/amber_has_index.md](../amber-mesi-l1/docs/amber_has/amber_has_index.md)
- **amber alignment memo:** [../amber-mesi-l1/docs/amber-cache-decisions-alignment.md](../amber-mesi-l1/docs/amber-cache-decisions-alignment.md)
- **cache-ip README:** [../README.md](../README.md)
- **Book source index:** [../../../../../calibre/books/designing-a-multiprocessor-cache-subsystem/index.md](../../../../../calibre/books/designing-a-multiprocessor-cache-subsystem/index.md)

---

**Last Updated:** 2026-10-11
**Maintainer note:** Revisit this plan when amber PRD/HAS are updated, when jet architecture is drafted, or when onyx D3/D4/D5/D7 decisions close.
