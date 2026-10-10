# ISSUE-019: tFAW/tRRD are checked two registers before the command fires

**Priority:** P2 — if reachable it is a JEDEC violation on real silicon, and the
symptom is a marginal DRAM rather than a failing test. Not raised higher because
reachability is NOT established; see "What is not known" below.
**Status:** CLOSED 2026-09-28 (resolution below)
**Owner:** TBD
**Found by:** analysing whether the arbiter's compensating guards were made
redundant by [[ISSUE-018]]. They were not -- and the analysis turned up the
opposite problem.
**Related:** [[ISSUE-018]] (the readiness flop's own one-cycle lag, fixed; this
is a DIFFERENT and larger gap), [[TASK-034]] (the N+1 convention)

## The gap

`pumice_cmd_arbiter` drives the timer event strobes at FIRE and makes its
decisions three to four registered stages earlier. Its own header says so:

> this arbiter drives the set_* strobes at FIRE (`evt_act_o = w_fire_out &&
> r_do_act`) while it SELECTS three to four registered stages earlier. So up to
> four commands are in flight that the timers have never seen, and `safe_*`
> reports safe because it has not seen them.

For PER-BANK constraints that gap is covered, deliberately and at length, by the
in-flight shadow matrix (`w_guarded`, `w_preact_bank_guard`, `w_col_inflight_bank`,
`w_tccd_fwd_ok`, the `!(w_fire_out && r_do_rd)` turnaround terms). For the two
RANK-GLOBAL activate constraints it appears not to be:

| Checkpoint | Covers tFAW / tRRD? |
|---|---|
| classify masks (`rd_act_m` / `wr_act_m`) | no -- `w_act_classify_gate` is 1'b1 except in one paging mode, deliberately (ISSUE-002: gating the mask drained the pick pipeline and cost 30% of the command bus) |
| STAGE-1b pre-pick (`w_act_gate_live`) | **yes** -- `!w_rfc_busy && tfaw_ok_i[RK0] && trrd_ok_i[RK0]` |
| final stage (`w_out_safe`, line ~315) | **no** -- `r_do_act` re-validates against `bank_act_ready_i[RK0][r_bank]` only, which is `bank_timer`'s PER-BANK gate |
| `pumice_cmd_history_checker` | **no** -- "audit ... against JEDEC **same-bank** sequencing"; tRRD and tFAW are cross-bank by definition |

`w_act_gate_live` is used exactly once, at the STAGE-1b `always_comb` that
produces `w_sel_rd_act_f` / `w_sel_wr_act_f`. Those feed the registered pre-pick,
which feeds the main pick, which feeds the output register. So **two registers
separate the tFAW/tRRD check from the fire**, and in that window another ACT can
fire without the check being redone.

`bank_timer` cannot close this: its windows are per-bank, and tRRD/tFAW exist
precisely for the cross-bank case. Two ACTs to DIFFERENT banks are what is at
issue.

## Two RTL comments claim otherwise

Both ACT masks carry a comment asserting the check happens at the fire stage:

> They are re-checked live at the fire stage (`w_act_gate_live`), which is
> authoritative.

> ... and `w_act_gate_live` re-checks both live at the fire stage (4a/4b) where
> it is authoritative.

Measured against the code, `w_act_gate_live` is at the pre-pick, not the output.
Either the comments predate a pipeline change or "fire stage" is being used
loosely for "later than classify". **Whichever it is, the comment is the reason
this went unexamined** -- it is the same failure mode as ISSUE-018, where a
contract asserted in prose was not what the logic implemented.

## What is not known, and must not be asserted

**Whether two ACTs to different banks can actually fire one cycle apart.** That
needs the pick pipeline in the reasoning, and it may well be unreachable for an
unrelated structural reason (class priority at the output, the pre-pick holding
under backpressure, `r_ap_closing`, or simply that two ACT candidates rarely
co-exist at CLOSE page). Nothing here establishes reachability, and the board has
run clean for a long time, which is weak evidence against it.

It is filed as an issue rather than a bug for exactly that reason: there is a
demonstrated hole in the checking, not a demonstrated violation.

## How to settle it

In rough order of cost:

1. **Cheapest and probably decisive:** extend `pumice_cmd_history_checker` to
   record a rank-global ACT history alongside its per-bank one, and check tRRD and
   the 4-in-tFAW window on it. It already has the shift-register machinery and is
   already instantiated in the sim environment -- this is a positional lookup on a
   second array. Then run the existing scheduler matrix and the char sim. If the
   hazard is reachable, the existing regression will find it immediately.
2. Formal, with `pumice_cmd_arbiter` in the cone -- 1601 lines plus the CAMs, so
   a large proof, but the property is small: no two `evt_act_o` pulses closer than
   `t_rrd_i`, and no five inside `t_faw_i`.
3. If reachable: move the tFAW/tRRD check to `w_out_safe` alongside the per-bank
   term, or add a rank-global in-flight ACT guard to the shadow matrix. Note
   ISSUE-002's warning before gating anything earlier -- gating the MASK on these
   two cost 30% of the command bus and is why the check sits late in the first
   place.

Option 1 also has standalone value: a cross-bank command-history check is missing
from the environment regardless of the outcome here.

---

## Closed 2026-09-28 -- the checking gap is filled; the hazard was not observed

The defect this issue actually named was a GAP IN CHECKING, not a demonstrated
violation, and that gap is now closed permanently.

### What was added

`pumice_cmd_history_checker` already carried rank-global windows -- `T_WTR` and
`T_RTW`, added earlier for "the flopped-ac staleness bug ... the per-bank history
above cannot see". The machinery was therefore already right; tRRD and tFAW were
simply missing from it. Added:

* `T_RRD` and `T_FAW` parameters (0 = check off, so the release build is
  bit-identical).
* A per-rank global ACT history `r_gact[NUM_RANKS][DEPTH]`, separate from the
  per-bank `r_hist` -- because recording per bank and scanning one bank's window
  is exactly what misses a cross-bank constraint.
* Check (8) GLOBAL tRRD: an ACT must be >= `T_RRD` cycles after ANY ACT to the
  same rank.
* Check (9) GLOBAL tFAW: at most four ACTs per rank inside any `T_FAW` window.

Threaded through `pumice_mem_cmd_scheduler` as `HIST_T_RRD` / `HIST_T_FAW` and
armed in both macro suites from the live operating point, so the windows track
the config being programmed rather than being pinned (the mistake a comment in
those tests already warns about: a scoreboard auditing windows no config uses
"still reports success", which is worse than not auditing).

### The result, and the arming proof that makes it mean something

**171 passed, rc 0**, across all 14 named DRAM operating points including
`board_ddr2_300`, at the real `tRRD = 2`. No violation.

That number is worth nothing on its own -- a check that never armed passes too.
So the check was proved live by inflating the window to `HIST_T_RRD = 30` and
re-running, which fires:

    %Fatal: pumice_cmd_history_checker.sv:284: GLOBAL tRRD violation --
    rank0 bank1 ACT only 10 cyc after another ACT (need 30)
    -- cross-bank activate rate limit

The check reports a real measured spacing, so it is reading the stream correctly.
Incidentally that also answers the reachability question quantitatively: the
tightest ACT-to-ACT spacing the suite produces is **10 cycles**, five times the
tRRD it has to clear. The two-ACTs-one-cycle-apart case is nowhere near being
approached, which is consistent with the pick pipeline not being able to present
it.

### What this does and does not establish

**Does:** nothing checked cross-bank ACT spacing at the issuing cycle before
this, and something does now, permanently, in the suite that runs on every
change. If the hazard ever becomes reachable, a test fails.

**Does not:** prove it is unreachable. "Not observed across 171 tests with the
check armed" is strong evidence, not a proof. Upgrading it is
[[TASK-035]] tier 1 -- `pumice_cmd_arbiter` in a formal cone, where the property
is small even though the block is 1613 lines: no two `evt_act_o` closer than
`t_rrd_i`, none five inside `t_faw_i`.

### Also fixed: the comments that hid it

Both ACT masks claimed tFAW/tRRD were "re-checked live at the fire stage
(`w_act_gate_live`), which is authoritative". Measured against the code,
`w_act_gate_live` is used once, at the STAGE-1b pre-pick, two registers ahead of
the output. The comments now say where the check actually is, and that
`w_out_safe` covers only the per-bank gate. That comment was the reason this went
unexamined -- the same failure mode as [[ISSUE-018]], a contract asserted in prose
that the logic did not implement.

### Not done, deliberately

The DFI-wire instance of the checker (`pumice_dfi_cmd_path`) leaves `T_RRD` /
`T_FAW` at 0. Wiring it would need the two parameters threaded through
`pumice_dfi_layer`, `pumice_core`, `pumice_top` and `pumice_top_geared` as well,
and it would add little: the DFI path "adds a constant register delay, which
shifts every command equally and cannot hide a violation" (its own comment), and
the scheduler instance is where the arbiter's decision actually lands, which is
what this issue is about.
