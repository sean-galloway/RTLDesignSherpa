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

# jet — Product Requirements (DRAFT)

**Version:** 0.1 (draft, 2026-10-04)
**Status:** scaffold only — inherits every DECIDED row of
[amber's PRD](../amber-mesi-l1/PRD.md). Decided inherited rows so far: D8
observation (`*_monlite`, 2026-10-04) and D4 snoop transport (ACE-shaped
AC/CD/CR per the onyx D7 contract, 2026-10-05). The rows below are the
deltas jet must decide for itself; all are OPEN until they record a name
and a date.

## 1. Purpose

The lockup-free (non-blocking) MESI snoopy L1 cache: amber with MSHRs. The
research question is measurement — with coherence, arrays, and observation
held constant, what do outstanding misses, hit-under-miss, and miss merging
actually buy in latency and bandwidth, in simulation and on board?

## 2. Decisions jet adds to amber's

| # | Decision | Candidates | What it drives |
|---|---|---|---|
| J1 | MSHR organization | OPEN: full associativity keyed by address vs direct-mapped by line index vs CAM of pending lines; capacity 2–16 entries as an elaboration parameter | the miss queue, merge logic, formal surface |
| J2 | Hit-under-miss scope | OPEN: hits to any resident line (default) vs hits only to lines not conflicting with a pending fill vs reads-only (writes still block) | hazard logic between fill port and hit port |
| J3 | Miss merging policy | OPEN: merge only exact-line aliases (default) vs merge line + offset range vs no merging (issue duplicate fetches, dedupe on return) | memory traffic, MSHR occupancy, fairness |
| J4 | Ordering guarantees | OPEN: CPU-side responses in-issue-order vs out-of-order with ID tags; snoop-during-miss handling (a probe against a pending line must see the post-fill state or stall cleanly) | response path complexity, protocol proofs, consumer expectations |
| J5 | Eviction under misses | OPEN: a dirty victim behind an outstanding fill must write back without deadlocking against the fill; victim buffer depth (0 = block like amber, 1–4 = decouple) | write-back path, the classic lockup-free deadlock corner |
| J6 | Congestion/fairness | OPEN: policy when MSHRs are full — stall new misses (strict) vs drop-and-retry vs throttle CPU-side accepts; plus snoop-vs-fill arbitration priority | starvation/liveness proofs |
| J7 | The measured claim | OPEN: define the experiment now — same trace suite + same board as amber, report hit latency distribution, miss concurrency, bandwidth, and MSHR occupancy from MonBus capture | what "jet is faster by X" must mean, reproducibly |

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
