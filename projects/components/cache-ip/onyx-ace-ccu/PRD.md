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

# onyx — Product Requirements (DRAFT)

**Version:** 0.8 (draft, 2026-11-21)
**Status:** the D rows are decided (v0.7, 2026-11-20); the N rows other
than N1 and the invariants other than 6 remain OPEN/PROPOSED. A decision
becomes DECIDED when it records a name and a date, the way the reed-solomon
PRD does it. **v0.5 recorded two owner rulings (N1 and invariant 6); v0.7
records the D1-D6 and D8-D11 rulings, each on the candidate the row had
recommended.**
v0.2: D7 decided 2026-10-05 (Sean) — onyx owns the ACE-shaped AC/CD/CR
snoop port; amber/jet adapt to it behind a thin adapter. Decided together
with [amber D4](../amber-mesi-l1/PRD.md), so the gate between the two is
resolved. The sequencing constraint that remains: onyx still waits behind
amber's pair rig (amber D10), its first consumer.
v0.3: D10 direction tightened 2026-10-05 — the ACE BFM extension of the
RDS-DV `axi4` family is now specified concretely (layering, four classes,
build order); the row stays OPEN. RDS-DV implementation filed as
[RTLDesignSherpa-DV issue #86](https://github.com/sean-galloway/RTLDesignSherpa-DV/issues/86).
v0.4: Chinnakonda book analysis folded in 2026-10-11 — Ch. 6/7/8/10/11/13/14
mined for candidate invariants, liveness scenarios, and scope-growth options.
Book is cited in References; all new material is candidate/recommended/PROPOSED.
v0.5: Ruling 2026-10-11 (Sean) — N1 decided (RACK/WACK omitted from the
onyx↔cache contract) and invariant 6 decided (CD-before-CR is the binding
family convention). See also the updated
[AMBA ACE Interface Definition](../References/AMBA_ACE_Interface_Definition.md).
v0.6 (Sean, 2026-10-30): client-context note — with jet's J8–J10 ruled
(AMO cache-side ALU; LR/SC snoop-touch sideband), the gyrfalcon-A coherent
rig is now concrete on both sides of the snoop interface: N2's PoS monitor
is onyx's half, jet's J9 sideband is the L1's half. Rig figure:
[gyrfalcon_coherent_rig](../../riscv-ip/docs/assets/graphviz/gyrfalcon_coherent_rig.png).
N2 itself stays OPEN until that rig is designed.
v0.7 (Sean, 2026-11-20, "follow the D recommendations"): D1-D6 and D8-D11
decided on the recommended candidates, with the reasons recorded in each
row; D2 names the transactions the house caches issue (ReadNotSharedDirty,
not ReadShared: a MESI cache has no Owned state); D4/D5/D6 record that
jet-prime's pipelined pair fabric (`jet_prime_pair_fabric`, TASK-001 steps
3-5: a transaction table serializing per line, the memory read issued
alongside the snoop, completion at the requester's retire, a 27-property
formal safety argument that found two memory-AR defects) is the two-port
prototype of onyx's core, so onyx's first measurement is replacing it on
the reference rig. The sequencing constraint ("onyx waits behind amber's
pair rig") is retired: the jet and jet-prime pair rigs exist and are
measured. Success criterion 6 added (equal cycles to the pair fabric). The
N rows and invariants 1-5 and 7 are untouched by this ruling. Same day,
the owner's pointer: the ACE BFM and the `rtl/amba/ace` transport already
exist (2026-10-05) and are green; jet-prime's snoop port is already
AC/CR/CD-shaped while its front side carries the request class on the
`coh_req` sideband, which onyx v1 takes natively (onyx TASK-001).

v0.8 (2026-11-21, onyx TASK-001 steps 1, 2, 4, 6): the RTL exists --
`rtl/top/onyx_ccu.sv`, the pair fabric generalized to N ports under the D
rulings -- and the success criteria carry their measured status below.
Criterion 6 is met exactly (SEL 4 reproduces the pair fabric's bin 7 cycle
for cycle on 110 cells); criteria 1 and 2 are met on the pair rig through
jet-prime's own testbench; criterion 3 is met for safety at N = 2 (the
fabric's 27 properties, mutations) and open for liveness bounds and N = 3,
4; criterion 4 (observation) is built, held to the pair-rig model in sim
(exact counters, an honest MonBus observer) and captured on the board,
where the counters give the D6 trade its numbers (parallel mode wastes one
read per supplied line, 30 percent of the reads on the shared resident set
and 1 to 3 percent in thrash; deferred mode wastes none and issues exactly
that many fewer) and the MonBus tally bins are lower bounds (onyx
ISSUE-001); criterion 5 is measured out of context and on the board. The D1
ACE-Lite IO port is built (TASK-001 step 7, 2026-11-23): requester `N_PORTS`
of the table, ReadOnce / ReadNoSnoop and WriteUnique / WriteLineUnique /
WriteNoSnoop, verified in the pair rig against the lockstep model with the
RDS-DV ACE master BFMs, argued formally beside the two caches, and exercised
on the reference rig through a CSR doorbell; the remaining core items are
the N = 3 formal harness, a core-alone BFM-cache rig and the MAS.

## 1. Purpose

A snoop-based cache coherency unit (CCU) in the shape of Arm ACE: the
manager that sits between the repo's coherent caches and memory on the
house AXI4 fabric. An attached cache (amber instance, jet instance) is an
ACE *master*; it issues coherent transactions (ReadNotSharedDirty,
ReadUnique, CleanUnique, WriteBack, Evict -- the D2 subset, what amber and
jet actually issue) instead of managing peers directly. onyx receives those transactions, broadcasts a snoop (AC request)
to the other caches, gathers their CR responses (DataTransfer / IsShared /
PassDirty) and CD data, decides whether the transaction may be completed
from cache-supplied data alone or memory must be read, and serialises
same-address traffic. The research question is the manager side itself:
what do fanout, gather, adjudication, and ordering cost — in gates, in
latency, and in verification effort.

## 2. Background

ACE is AXI4 plus three snoop channels (AC, CR, CD) — and this repo already speaks AXI4
(skid buffers, GAXI FIFOs, `axi4_master_rd/wr` wrappers, Pattern-B BFMs).
The natural-protocol argument: every piece of onyx's data path reuses
existing, proven plumbing; the new logic is the coherence decision layer
and the serializer. The definition is Arm IHI 0022 (the ACE chapters);
the worked example is `pulp-platform/culsans` (ETH/PlanV), whose two halves
are exactly the reading list:

- **culsans' CVA6 coherent WB cache** — how a cache becomes a snoop
  responder: the AC/CD/CR channels, how snoop tag lookups arbitrate with
  the core's own tag port, and the MOESI-ish line states.
- **`ace_ccu_top`** — the manager: broadcast snoops on a coherent
  read/write, collect responses, decide whether memory is read, and
  serialise same-address transactions.

Treat culsans as a worked example, not a dependency (last push 2024, lightly
maintained). Note also what onyx is *not*: it is not a directory, not an L2,
and not a general NoC — amber's deferred "snoop filter / directory-lite"
question (amber D4) shows up here only as one candidate row (D3).

Repo anchors the design must respect: resets on the `ALWAYS_FF_RST` macros,
no bespoke SRAM (shared `sdpram_core` / house FIFO primitives), `[DEPTH]`
array syntax, valid/ready streaming contracts, MonBus observation through
`*_monlite` wrappers only (amber D8's decision — the observer must never
stall the measured paths), filelists registry, and GLOBAL_REQUIREMENTS.

## 3. Decisions that pick the design

| # | Decision | Candidates | What it drives |
|---|---|---|---|
| D1 | Functional scope | **DECIDED 2026-11-20 (Sean): CCU only -- N ACE slave-side ports toward caches, one AXI4 master toward memory, one ACE-Lite IO port (the culsans shape).** Chosen over CCU + address striping / multiple memory ports: that is interconnect territory and would blur what "onyx done" means; it stays a non-goal. **Built 2026-11-23 (TASK-001 step 7):** the IO port is requester `N_PORTS` of the table -- ReadOnce / ReadNoSnoop, WriteUnique / WriteLineUnique / WriteNoSnoop by `AxDOMAIN` and `AxSNOOP`, every cache a peer (ReadOnce; CleanInvalid for the writes, so a Modified holder's line is absorbed before the IO's bytes land), one read and one write in flight; HAS Chapter 4.5.<br><br>**Book input:** §10.1 (banks ≥ master count), §10.2–10.3 (centralized vs. distributed manager; BIU as mapper), §10.7 (coherency logic can live in L2 or BIU). Confirms onyx as the BIU/manager block rather than an L2; keeps CCU-only the recommended v1 scope. | block boundary, what "onyx done" means |
| D2 | ACE transaction subset | **DECIDED 2026-11-20 (Sean): the transactions the house caches issue -- ReadNotSharedDirty, ReadUnique, CleanUnique, WriteBack, Evict.** The row had said ReadShared, but a MESI cache has no Owned state and issues ReadNotSharedDirty (jet's fill classes are RNSD / RU / CU); MakeUnique is deferred until a cache issues it. Chosen over barrier support and full ACE/DVM (D8, N6); WLU/WU/WC/WE stay the N5 scope-growth option.<br><br>**Book input:** §7.2–7.4 give the full ARSNOOP/AWSNOOP taxonomy; WLU/WU are entire/partial-line writes used for non-temporal/all-bytes-updated stores and coherent mem-copy (§11.1); WC/WE are clean-victim/LLC-victim writes. The recommended research subset stays RS/RU/CU/MU/WB/Ev; WLU/WU/WC/WE are recorded as scope-growth option N5. | front-end decoder, BFM scope, conformance matrix |
| D3 | Snoop fanout | **DECIDED 2026-11-20 (Sean): broadcast to all attached caches; the directory-lite snoop filter stays a future elaboration parameter.** At N = 2-4 a filter saves little snoop traffic and costs a sharer vector per line; the sharer vector's home is basalt (the family README already puts it there).<br><br>**Book input:** §10.3–10.5 describe inclusive-directory options: copy-of-L1-tags, L1ID sharer vector in tag, or separate snoop filter sized ≈1.5× combined L1. §10.6.2 notes the false-positive-snoop corner (multiple shared responders → pick one; many systems read DRAM for shared copies). Broadcast remains recommended v1; directory-lite is a future elaboration parameter. | fanout logic, gate count, the coherence-traffic measurements |
| D4 | Response gather | **DECIDED 2026-11-20 (Sean): tagged outstanding transactions with per-transaction completion -- the pair fabric's transaction table, not a fixed response window.** Fills complete out of order since jet-prime step 2 (one read ID per MSHR entry), so a fixed window would either stall the fast case or presume a miss wrongly; `jet_prime_pair_fabric` already proves the per-slot bookkeeping (27 safety properties) and its argument transfers.<br><br>**Book input:** §7.1 and §7.7 state snoops have no IDs and must be responded to in issue order; §14.18 confirms the three snoop channels are independent except for the same-address WB/Ev/WC/WE dependency. §7.7 gives the response bound: a snoop may be delayed only until the last data beat of a matching fill has arrived, otherwise it must respond not-present; holding it beyond that deadlocks. | gather buffer, formal surface, ACE conformance |
| D5 | Same-address serialization | **DECIDED 2026-11-20 (Sean): per-address scoreboard; different addresses interleave, same-address traffic keeps grant-after-completion.** Exactly the pair fabric's per-line rule (jet-prime JP4), proven at 16 lines / four slots. Full in-order single outstanding is a bring-up mode only.<br><br>**Book input:** §7.5, §10.7, §10.8 describe same-AxID ordering and the banked PoS with per-address linked lists (older completes first, different addresses any order); §10.9.1 notes device accesses routed to a dedicated bank for program order; §10.8 gives outstanding-access sizing math (≈40 read + 40 write transactions for 200-cycle DRAM latency on a 1 GHz 16-byte bus). Informs the scoreboard/serializer design but does not decide it. | the serializer, the deadlock/liveness proof, jet J4 interactions |
| D6 | Memory-read elision | **DECIDED 2026-11-20 (Sean): full adjudication -- data accepted only from a PassDirty (dirty) responder or a single designated forwarder, memory read otherwise; the memory read is issued alongside the snoop as the pair fabric does, with a mode that defers it until the CR.** Elision trades memory bandwidth for latency, and two modes make the trade measurable, which is the win onyx exists to quantify. "Any DataTransfer elides memory" is not the safe rule with several shared responders.<br><br>**Book input:** §10.5–10.6.2 refine adjudication: when multiple DataTransfer responders exist, the manager must pick one; many real systems read DRAM for Shared copies and accept data only from an O-state holder; MOESIF Forward state is one way to designate a single forwarder. Therefore "any DataTransfer elides memory" is NOT the safe rule — elision requires a dirty (PassDirty or O-state) responder, or a single designated forwarder. | memory traffic, the measurable win onyx exists to quantify |
| D7 | Cache-side interface ownership | **DECIDED 2026-10-05 (Sean): onyx defines and owns an AC/CD/CR-shaped snoop port; amber/jet stay bus-agnostic internally and add a thin adapter to it.** Chosen over caches natively growing ACE ports — the cache cores stay unpinned from ACE except at the adapter, so onyx (or a real ACE interconnect, e.g. culsans' `ace_ccu_top`) can supersede the custom bus without touching cache RTL. | the amber D4 ↔ onyx contract, who changes when ACE supersedes the custom bus |
| D8 | Domain / barrier rules | **DECIDED 2026-11-20 (Sean): single shareability domain, barriers ignored -- a recorded non-goal.** The book terminates barriers in the processor (multi-copy-atomic stores, invariant 5); nothing in the repo issues one. Minimal barrier ordering and DVM stay out (N6 is the upgrade path, not promoted).<br><br>**Book input:** §6.4–6.5 and §14.33 recommend making stores always multi-copy atomic even though Arm does not require it; this is the book's justification for terminating barriers in the processor and ignoring them at the manager. Single shareability domain / barriers ignored remains recommended. | scope honesty, later upgrade path |
| D9 | Observation | **DECIDED 2026-11-20 (Sean): `*_monlite` taps for coherent-txn start, snoop fanout per transaction, response-gather completion, memory-read elision hit/miss, serialization stalls and WB/Evict drains, tallied by `monbus_tally_axil`, all behind USE_MONITOR.** The 2026-11-19 area rows showed the observers are about a third of every house cache's LUTs; the parameter keeps onyx's area row readable both ways.<br><br>**Book input:** §8.2/§8.3/§10.6 treat independent snoop paths and fairness as first-class observables; §10.8 gives outstanding-access sizing math that shapes the counters listed above. | perf counters, board capture, DV scoreboard |
| D10 | Verification strategy | **DECIDED 2026-11-20 (Sean): Pattern-B cocotb at gate/func/full; the ACE BFM as the extension of the RDS-DV `axi4` family specified below, built before the RTL; plus a fabric-style formal safety argument on the serializer and gather.** The BFM exists (RDS-DV `components/ace`, 2026-10-05; 135 unit tests; the transport movers in `rtl/amba/ace` 24/24 func cells from clean on 2026-11-20) but has never faced a manager -- onyx is its first real application, so step 1 of onyx TASK-001 is verifying it on onyx's gather shapes, and RDS-DV #86 (still open) closes against that; the pair fabric's harness found two memory-AR defects before the board did. Direction as recorded (2026-10-05): Pattern-B cocotb gate/func/full. **ACE BFM — an extension of the `axi4` BFM family in RDS-DV, layered the way that family is built** (analysis from inspecting `CocoTBFramework/components/axi4/`): (1) field configs — an `AXI4ACEFieldConfigHelper` adds `ARSNOOP[3:0]` / `AWSNOOP[2:0]` to the AR/AW field configs; (2) signal-map patterns — new `axi4ace_*` protocol patterns (decide there: framework-shipped vs. user-loadable, the signal_mapping_helper question); (3) transaction/packet layer — the D2 transaction types as an enum, CRRESP as a bitfield (DataTransfer/Error/PassDirty/IsShared/WasUnique); (4) four BFM classes — `AXI4ACEMasterRead` / `AXI4ACEMasterWrite` as subclasses (snoop type on commands; onyx-port BFMs do not model RACK/WACK because the contract omits them), `AXI4ACESnoopSlave` (new, no base: receives AC, drives CR/CD in **issue order** — snoops carry no ID — with programmable cache-state behavior producing the correct CRRESP; this is the golden-model hook that replays gem5 traces through amber), `AXI4ACESnoopMaster` (new: drives AC, gathers CR/CD in order — drives onyx's fanout in DV); (5) compliance checker — in-order CR/CD, no snoop to the requesting master, CD-before-CDLAST, CRRESP validity per snoop type; (6) main-repo TB classes under `bin/TBClasses/axi4ace/` per consumer. **Build order:** snoop-slave BFM first (amber's pair rig needs it), snoop-master BFM lands with onyx; ships as an RDS-DV framework release the way the irq BFM did. Python golden model derived from the gem5 Ruby `MESI_Two_Level` spec in `../References/gem5-ruby-protocols/`; the ACE subset contract is the in-repo [definition doc](../References/AMBA_ACE_Interface_Definition.md); SymbiYosys proofs of same-address serialisation and no-deadlock under fair arbitration; culsans behaviours as informal cross-checks, not oracles<br><br>**Book input:** §7.6–7.10, §8.1–8.3, §10.9 give concrete liveness scenarios: WLU-vs-WB valid/ready deadlock when SI buffers are full (§7.6.1/§7.7.1); CU livelock on RU-then-downgrade (§7.8, §10.9); store-exclusive semaphore livelock and POS-monitor recipe (§7.9–7.10); starvation from fixed priority → timeout fairness (§8.3). These become the named proof obligations under Success criterion 3. | DV structure, formal areas, CI time |
| D11 | Master count & profile | **DECIDED 2026-11-20 (Sean): N coherent cache masters 2-4 as an elaboration parameter; the research rig at N = 2 (two jet-primes on the cache-ip reference rig, replacing `jet_prime_pair_fabric`); line size and profile locked to amber's geometry.** The pair's cycles per transaction (bin 7) are already on disk, so the first onyx measurement has its baseline.<br><br>**Book input:** §10.1 states banks should be ≥ master count (4 CPUs → at least 4 banks). Supports keeping N=2–4 as an elaboration parameter and sizing internal resources accordingly. | array dimensions, DV matrix, the measured system's realism |
| N1 | RACK/WACK omission-by-contract | **DECIDED 2026-10-11 (Sean): follow the book — RACK/WACK are omitted from the onyx↔cache contract.** The binding condition is that data-return and snoop paths are ordered to the coherency point, which the D7 port contract guarantees. The house `axi4ace_master_rd/wr` wrappers still auto-pulse RACK/WACK; that behavior is deprecated for family contract use, and its removal is tracked as amber RTL follow-up A5. | adapter logic, snoop/data ordering assumptions |
| N2 | AxLock / PoS monitor for cross-master exclusives | OPEN: arm a POS monitor on AxLock for exclusive transactions: one master receives EXOKAY, competing CUs receive OKAY (fail), and invalidation snoops are withheld from the winning master until its store completes. Book §7.9–7.10 and §14.36 describe this as the livelock-reduction recipe for store exclusives. Out of the initial D2 subset; recorded as a candidate upgrade. Planned future consumer: gyrfalcon-A (falcon suite design spec amended 2026-10-11) on a coherent onyx rig; the row stays OPEN until that rig is designed. | exclusive-transaction handling, POS monitor logic |
| N3 | Snoop-response sourcing from in-flight fills | OPEN: a snoop matching an in-flight fill must respond not-present if no data beat has arrived, and may forward from the fill buffer only after the last data beat has arrived; the response must never depend on an unrelated event. Book §7.7, §8.2, §10.6. Elevates the D4 book input to a proposed invariant. | snoop responder, fill-buffer comparators, formal progress proof |
| N4 | CD-path independence | OPEN: never share the snoop-data return path (CD) with WDATA; reserve credit/capacity for the WB/Ev/WC/WE family so snoop responses cannot be blocked by ordinary writes. Book §10.6 and §14.11–14.13 emphasize an independent snoop path as the deadlock-avoidance bedrock. (ACE permits CDDATA to be combined with WDATA; the book argues against it.) | snoop data channel, write-buffer allocation, credit logic |
| N5 | WLU/WU + WC/WE scope-growth option | OPEN: add WriteLineUnique / WriteUnique for coherent DMA/mem-copy, plus WriteClean / WriteEvict for clean-victim handling. Book §7.3–7.4 and §11.1–11.3 tie WLU/WU to mem-copy traffic (read stream → RS+Evict, write stream → WLU/WU); WC/WE handle clean victims and LLC victim caching. Not in the recommended D2 subset; recorded as a scope-growth candidate tied to a future coherent DMA/mem-copy use-case. | front-end decoder, fanout/adjudication, conformance matrix |
| N6 | DVM upgrade path | OPEN: if DVM is ever promoted, follow the book's recipe: DVM Messages are two-beat read transactions sent back-to-back with no intervening transaction; one DVM Sync per cluster is serialized at the SI; DVM Complete uses a unique ARID and is sent only after all translated-address buffers have drained. Book §7.16 (TLB maintenance / DVM). Revisits the D8/DVM non-goal but does not promote it. | DVM message handling, serialization, drain logic |
| N7 | Prefetch-traffic handling constraint | OPEN: the CCU must never see speculative store-ownership requests; prefetch traffic, if it reaches onyx at all, is speculative read-shared/read-clean only. Book §13.3: processors do not prefetch for stores because prefetches are speculative and must not make speculative state changes or set Dirty bits. | prefetch filtering, BFM scenario matrix, coherency checker |

## 4. Design invariants (proposed)

The following bedrock liveness rules are mined from Chinnakonda Ch. 7/8/10/14.
Each is **PROPOSED** pending an owner ruling except where marked **DECIDED**.

1. **Snoop forward progress (PROPOSED).** A snoop may wait only on (a) a
   same-address outstanding WB/Ev/WC/WE, or (b) a guaranteed-to-complete
   temporary block (e.g. a retired store completing after it has received
   ownership). It must never wait on an unrelated transaction or an
   unpredictable buffer-drain event.
2. **Snoops ignore WLU/WU entirely (PROPOSED).** §7.13: a snoop to the same
   address as a WLU/WU is always allowed to make progress; the WLU/WU does
   not block it.
3. **Snoop responses never depend on WU/WLU completion (PROPOSED).**
   Otherwise SI buffers full of interdependent WU/WLU traffic can deadlock.
4. **CD never blocks on WDATA (PROPOSED).** The snoop-data return path must
   have independent forward progress; if it shares resources with ordinary
   writes, those resources must be credit-reserved for the WB/Ev/WC/WE
   family.
5. **Multi-copy-atomic stores (PROPOSED).** A store is considered complete
   only after all ownership invalidations have been performed everywhere;
   this is the book's recommended simplification that makes barriers-ignored
   at the manager defensible.
6. **CD before CR, CD-before-CDLAST, in-order CR/CD (DECIDED 2026-10-11
   (Sean)).** A snoop transaction's CD beats complete before its CR is
   asserted; CR responses are returned in AC order; CD data is returned in
   AC order; CDLAST marks the final beat. This is the family contract,
   stricter than the spec's per-channel ordering rule.
7. **No snoop to the requesting master (PROPOSED).** Already a D10 compliance
   checker rule; restated here as a design invariant.

## 5. Success criteria

1. **Three-block coherence.** Two jet-prime instances (D11; amber or jet
   behind the D7 adapter are the same contract) plus onyx form a coherent
   system that passes the golden-model parity suite amber D9 defines —
   the pair rig with onyx in the fabric's place, same traces, same policy
   space. **Met 2026-11-21 (TASK-001 step 2):** jet-prime's pair-rig
   testbench and grid unchanged against `onyx_pair_rig_tb`, 36 of 36
   cells at gate/func/full from clean including the MSHR x VICTIM x
   policy sweep, 0 mismatches; the gate reports equal the fabric's line
   for line.
2. **IHI 0022 conformance on the D2 subset.** A scoreboard checks the
   AC/CR/CD behaviour per transaction type: the CR bits (DataTransfer,
   IsShared, PassDirty) of every gather are correct for the transaction
   and the caches' states. **Met on what exists (2026-11-21):** the
   pair-rig testbench's ACE compliance scoring on every snoop of every
   cell, and the snoop-gather rig's CRRESP matrix check (the caches'
   `amber_snoop_crresp` cell by cell at 2 to 4 ports, 0 violations).
3. **The serializer, proven.** Formal: no two same-address coherent
   transactions proceed incompatibly; no deadlock under fair arbitration
   at N ∈ {2, 3, 4} masters; the D4 response-gather mechanism cannot
   livelock (a presumed-miss bound exists and is proven). The Chinnakonda
   book supplies the named proof obligations: absence of CU livelock at
   the PoS, no WLU/WB-style deadlock in the fanout/gather path, and
   fairness (no fixed-priority starvation) under N ∈ {2, 3, 4}.
   **Safety met at N = 2 (2026-11-21, TASK-001 step 4):**
   `formal/onyx/onyx_ccu`, the pair fabric's 27 properties restated for
   onyx -- `prove` depth 24 PASS 20:30, `prove_book` depth 16 PASS 14:41,
   19 of 19 covers, three mutations failing as written. With the tagged
   gather (D4) there is no presumed-miss bound to prove: completion is
   counted, not timed out. **Open:** liveness bounds (the control's
   derived-bound style) and the N = 3, 4 harness.
4. **Observation.** Every D9 event class visible on MonBus in simulation
   and captured on at least one FPGA board. **Not built** (a later
   TASK-001 step); the pair fabric's debug taps are in place.
5. **Cost.** Synthesis/implementation numbers (LUT/FF/RAM, fmax) on
   Nexys A7 and/or Genesys 2, recorded in `docs/` the way pumice
   characterised, with and without the observers (D9). **Measured
   2026-11-21** (HAS Chapter 6.2): manager alone out of context 4,628 LUT
   / 1,664 FF / 1,296 LUTRAM at +2.885 ns against the fabric's 4,300 /
   1,660 / 1,296 at +2.757; the Genesys2 rig at 100 MHz with onyx WNS
   +0.006 ns (SEL 4) and +0.000 ns (SEL 5), the worst path jet-prime's.
   Without-observers is moot until the taps exist.
6. **No slower than the fabric it replaces.** On the cache-ip reference
   rig's pair sweeps, onyx in parallel-issue mode (D6) at cycles per
   transaction equal to `jet_prime_pair_fabric`'s (bin 7, both injectors)
   within measurement noise at every depth; the deferred-read mode's
   memory-read elision rate and its latency cost measured on the same
   sweeps. Added 2026-11-20 with the D rulings. **Met exactly 2026-11-21
   (TASK-001 step 6):** SEL 4 reproduces bin 7's cycle count on all 55
   single and all 55 dual cells, both injectors, every CRC equal. The
   deferred mode's latency cost measured: +8 to +12 % at depth 1 on the
   thrash rows, under +2 % at depth 16, resident rows equal; its elision
   rate awaits a memory-side AR counter (D9).

## 6. Non-goals

Cache storage in onyx (it is a manager, not an L2 — tempting because a
CCU's gather point is the natural place to cache; explicitly out),
directory-based coherence (the D3 snoop-filter candidate is the closest
this IP comes), ACE DVM and full barrier semantics (D8; revisited by
candidate N6 as a future upgrade path, not promoted out of non-goals),
cache stash/dealloc features, multi-CCU / multi-domain systems, and any CPU-side
or upstream-master port beyond ACE-Lite IO. Each is a future IP or a
future decision, not an onyx requirement.

## 7. Where the block sits

The fabric's coherence point, on three kinds of port: **cache-side**, N
ACE-facing ports accepting coherent transactions from amber/jet instances
acting as ACE masters (D7, decided 2026-10-05: onyx owns this port's ACE
shape; caches adapt); **memory-side**,
one AXI4 master toward the house memory path (D6 fixes when it is read);
**inter-cache**, the snoop fanout — AC requests driven into each peer
cache, CD snoop data and CR snoop responses returned. No CPU port, no
register block beyond what observation needs (D9 tallies live in
`monbus_tally_axil` like every other component). Standalone-testable with
BFM caches long before amber exists: culsans' `ace_ccu_top` demonstrates
exactly that decoupling.

## 8. References

1. Arm, *AMBA AXI and ACE Protocol Specification*, IHI 0022 (ACE chapters) —
   the normative definition. The in-repo working subset is recorded in
   [`../References/AMBA_ACE_Interface_Definition.md`](../References/AMBA_ACE_Interface_Definition.md).
2. Murali Chinnakonda, *Designing a Multiprocessor Cache Subsystem* —
   Arm-ACE-centric multiprocessor cache subsystem design; ch. 7/8/10/14
   mined 2026-10-11. (Source markdown in the owner's calibre library;
   not mirrored in-tree.)
3. `pulp-platform/culsans` — `rtl/src/ace_ccu_top.sv` and the CVA6
   coherent cache: a working ACE CCU and a working snoop-responder cache.
   Worked example, not a dependency. https://github.com/pulp-platform/culsans
4. *A Primer on Memory Consistency and Cache Coherence* (Sorin, Hill, Wood,
   2nd ed., stored alongside the ACE definition doc) — coherence-theory
   background the transaction types instantiate.
5. gem5 Ruby SLICC specs (`gem5-ruby-protocols/`, stored alongside the ACE
   definition doc) — executable transient-state tables for the same
   protocol family; the golden-model source material, phrased in messages
   rather than ACE signals.
6. amber/jet improvement plan memo — future family-level planning document
   at [`../docs/amber-jet-improvement-plan.md`](../docs/amber-jet-improvement-plan.md);
   linked for cross-reference even though it does not yet exist.
