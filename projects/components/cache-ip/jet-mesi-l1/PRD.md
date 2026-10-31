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

# jet — Product Requirements

**Version:** 0.3 (2026-10-30)
**Status:** decisions CLOSED — J1–J7 ruled 2026-10-28 (Sean), recorded in
the table below; inherits every DECIDED row of
[amber's PRD](../amber-mesi-l1/PRD.md). Earlier inherited rows: D8
observation (`*_monlite`, 2026-10-04) and D4 snoop transport (ACE-shaped
AC/CD/CR per the onyx D7 contract, 2026-10-05).
v0.3 (Sean, 2026-10-30): target clients named — **gyrfalcon (RV32IM,
baseline and A_EXT=1 flavor) and garuda (RV32IMAF)** — and the RV32A rows
J8–J10 ruled (AMO cache-side ALU; LR/SC snoop-touch sideband; aq/rl no
cache hardware). Rig figure:
[gyrfalcon_coherent_rig](../../riscv-ip/docs/assets/graphviz/gyrfalcon_coherent_rig.png).

## 1. Purpose

The lockup-free (non-blocking) MESI snoopy L1 cache: amber with MSHRs. The
research question is measurement — with coherence, arrays, and observation
held constant, what do outstanding misses, hit-under-miss, and miss merging
actually buy in latency and bandwidth, in simulation and on board?

Target clients (v0.3, Sean): **gyrfalcon** — the OoO capstone, whose store
buffer drains to the D$ in program order, so jet still sees an in-order
single request stream while its MSHRs absorb miss latency the core can
actually exploit — and **garuda**, whose F extension adds no cache-visible
operations (FLW/FSW are 32-bit; no D). The gyrfalcon-A flavor
(`A_EXT=1`, Zalrsc + Zaamo) drives the J8–J10 rows below.

## 2. Decisions jet adds to amber's

| # | Decision | Candidates | What it drives |
|---|---|---|---|
| J1 | MSHR organization | **DECIDED 2026-10-28 (Sean): fully associative CAM keyed by line address, capacity an elaboration parameter 2–16, default 8** (default amended from 4 later the same day per the Chinnakonda §9.10.4 sizing: occupancy ÷ line-return time + 2 margin centers on 8–16 at the pair rig's latency)**.** Merge and hazard checks are exact-address comparators over N entries (the same shape as amber's tag hit-compare); smallest formal surface. Liveness rule: a fill once started always retires; MSHR-full stalls new misses; deadlock-free because no speculative/prefetch entries exist | the miss queue, merge logic, formal surface |
| J2 | Hit-under-miss scope | **DECIDED 2026-10-28 (Sean): reads AND writes to any resident line proceed during fills.** A pending-fill line cannot "hit" (its tag installs at commit — that is the J3 merge case); a doomed victim stays hittable until the fill's commit tag-write lands (array copy intact, state still valid). The single W port arbitrates fill beats over write hits — fills must retire for J5/J6 liveness, write hits can wait a cycle | hazard logic between fill port and hit port |
| J3 | Miss merging policy | **DECIDED 2026-10-28 (Sean): exact-line aliases merge; no in-flight class escalation.** Same class joins (read+read share the fill; write+write merge data at commit per amber's D-4 semantics). Cross-class waits: a write miss behind an outstanding read fill stalls until commit, then issues its own upgrade; a read behind a write fill waits and hits the committed M line. No RNSD→RU mutation of an outstanding entry | memory traffic, MSHR occupancy, fairness |
| J4 | Ordering guarantees | **DECIDED 2026-10-28 (Sean): out-of-order fill completion, in-issue-order CPU responses.** The GAXI slave (amber D2) has no ID field, so responses release in issue order through a response-sequence queue while fills/MSHRs complete out of order internally. Snoop-on-pending-line keeps amber's answer-at-post-fill-state pending-fill bypass, generalized per MSHR entry (PF_GUARD included) | response path complexity, protocol proofs, consumer expectations |
| J5 | Eviction under misses | **DECIDED 2026-10-28 (Sean): dirty victim captured to a global writeback buffer at miss start (victim_load); the fill proceeds immediately; the drain engine writes back oldest-first, independently.** Buffer depth an elaboration parameter 1–4, default 2. Snoop-on-buffer keeps amber's SINK_WB_ACK semantics. Buffer full stalls only new dirty-victim misses; drains always complete, so no deadlock | write-back path, the classic lockup-free deadlock corner |
| J6 | Congestion/fairness | **DECIDED 2026-10-28 (Sean): strict stall — MSHR full stalls new CPU misses, writeback-buffer full stalls only dirty-victim misses; snoops arbitrate ahead of new CPU accepts** (a snoop never waits behind a fill that waits behind a snoop — the pair-rig deadlock class). No drop-and-retry (GAXI has no retry); no watermark (no consumer for a spare entry — snoops do not allocate MSHRs). Formal liveness targets: oldest MSHR entry always retires; drains always complete; snoop service never blocked by CPU congestion | starvation/liveness proofs |
| J7 | The measured claim | **DECIDED 2026-10-28 (Sean): the experiment is frozen now — amber's cache_sim trace suite and the Genesys2 pair rig, identical traces on both caches.** Four metrics from MonBus tally capture: hit-latency distribution under a background miss stream, MSHR occupancy histogram, sustained fill bandwidth, drain/writeback overlap. MSHR count swept 2/4/8/16 so the occupancy→bandwidth curve is itself a result. cache_sim gains a concurrency model, or the gap is documented as a finding | what "jet is faster by X" must mean, reproducibly |
| J8 | AMO execution site (RV32A) | **DECIDED 2026-10-30 (Sean): cache-side ALU.** The CPU-plane request gains an op field (LD / ST / the nine word AMOs: swap, add, xor, and, or, min, max, minu, maxu); the RMW executes inside the cache against a line held in M, so atomicity is structural — a snoop can never observe a half-done AMO, and the J5/J6 deadlock proofs are untouched. Chosen over core-side RMW under a cache line-lock, which would reopen the snoop-deferral deadlock corner and stretch atomic latency. Implementation is a future task (gyrfalcon-A integration); the plane restructure (TASK-002) reserves the op field in the CPU-plane seam contract | CPU-plane request format, a small RMW ALU, DV surface for gyrfalcon-A |
| J9 | LR/SC support (RV32A) | **DECIDED 2026-10-30 (Sean): reservation register lives in the core** (falcon-suite ruling); the cache's part is a one-line sideband out of the CPU plane — "snoop service invalidated or demoted line at address X" — which the core wires to its reservation-clear. No cache state is added. In the coherent rig this fires when onyx's snoop (the N2 monitor activation) touches the reserved line | CPU-plane sideband, core↔cache contract |
| J10 | aq/rl ordering bits (RV32A) | **DECIDED 2026-10-30 (Sean): no cache hardware.** Acquire/release order the core's pipeline and store buffer (enforced at execute/commit per the falcon-suite ruling); a write-back MESI cache behind an in-order request stream is already correctly ordered. Recorded so the question is not re-litigated at integration time | nothing — a closed door |

## 3. Success criteria (additions to amber's)

1. **Correctness inheritance.** Every amber proof and golden-model parity
   result still passes with MSHRs present (proofs are re-run, not assumed).
2. **The delta, measured.** On the amber trace suite and at least one board:
   reported latency/bandwidth improvement with MonBus evidence, and the
   cache_sim cross-check extended so the model predicts jet's concurrency
   numbers too (or the model gap is documented as a finding).
3. **The deadlock corner, proven.** J5/J6 formal targets: no deadlock when
   MSHRs are full and dirty victims wait behind fills.

## 4. Non-goals (for jet, beyond amber's)

Speculative prefetching, adaptive replacement, quality-of-service policies,
multi-banked parallelism beyond what MSHRs imply. Each is a future IP or a
later decision.
