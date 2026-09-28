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

# Page-Policy Engine (`pumice_page_policy`)

## Overview

`pumice_page_policy` is the runtime Axis-2 (paging) engine. It replaced the
HAPPY address-hash predictor (`page_predictor.sv`, retired 2026-08-25: it was
never wired into the rearchitected core — `PAGE_POLICY_HAPPY_HYBRID` degraded
to OPEN in the arbiter). The engine watches the arbiter's ISSUED command
stream — the same `valid && ready` tap the command-history checker audits —
together with the registered per-bank row state, and owns two decisions plus
the page telemetry.

All behaviour is selected at runtime by `PAGE_POLICY_CFG.policy_mode`;
encoding 0 is the build default (bit-identical to the pre-engine controller,
where `REFRESH_TUNING.page_policy_or` alone selects OPEN/CLOSE).

**The reset value is 0.** Mode 3 (`fixed_open`) with
`PAGE_TIMEOUT_CFG.tr_init = 2` is the measured best default and is RECOMMENDED,
but the reset change was made and reverted on 2026-09-26 and is **blocked on
BUG-003** (a short timeout precharges under an in-flight read; the read-return
ring loses a ticket at `rd_gap >= 8`). The measurement below stands. Measured on the board at txn_scale=1000 it is
strictly dominant over open page across every scenario in the suite --
+41.2% on `col_major_interleaved_bl4`, +8.6..11.6% on `col_major`, and exactly
flat on `incremental`/`row_major` -- with no scenario regressing and zero
integrity failures. Two notes for anyone changing it:

* `tr_init = 0` **disables the timeout entirely** (`f_tr`/`r_idle` below). It is
  not a "build default" sentinel on this field, which is why the reset had to
  move to 2 and not stay at 0.
* TR=2 is a measured optimum, not a guess: TR=1 is identical on every scenario
  and TR=4 already falls back to open-page numbers on plain `col_major`, so the
  cliff sits between 2 and 4.

See `vault/Tasks/pumice/task/open/TASK-013.md` for the full campaign.

## Modes

| `policy_mode` | Name         | Behaviour |
|---|---|---|
| 0 | build default | Engine inert; legacy flat auto-precharge from `page_policy_or`. |
| 1 | `static_open`  | Per-bank ap mask forced 0 — rows stay open. |
| 2 | `static_close` | Per-bank ap mask forced 1 — every column op auto-precharges. |
| 3 | `fixed_open`   | **THE SHIPPING DEFAULT** -- `policy_mode` resets to 3 and `tr_init` to 2 as of 2026-09-27. ap=0; per-bank idle countdown from `PAGE_TIMEOUT_CFG.tr_init`. On expiry the engine REQUESTS a close; the arbiter issues the PRE as its strictly lowest-priority pick. This background-precharge path is where the measured win comes from -- see "Mechanism" below. |
| 4..7 | *retired* | **Fall through to the build default** — engine inert, no auto-precharge. 4 (`adapt_time`) and 5 (`adapt_access`) RETIRED 2026-09-27 (TASK-014); 6 (`rbl_static`) and 7 (`rbl_dyn`) RETIRED 2026-09-26 (TASK-011). `policy_mode` is a 3-bit field, so software can still write these; the fallthrough is a contract, regressed by `test_page_predictor` and the scheduler matrix. |

## Decision interfaces to the arbiter

1. **Auto-precharge override** — `ap_mode_en` + a per-bank `ap_close` mask.
   When enabled, the arbiter's column picks take `ap_close[bank]` instead of
   the legacy flat `w_ap`.
2. **Timeout close** — `timeout_pre_req` + bank. A new arbiter branch below
   the conflict-precharge path issues the PRE, gated identically (registered
   `row_active` + `pre_ready` + the 2-cycle re-issue guard), so demand,
   refresh and JEDEC timing always outrank a housekeeping close.

## The retired adaptive modes (4 and 5)

Both were implemented 2026-08-25 and removed 2026-09-27 (TASK-014).

**`adapt_time` was measured to BE `fixed_open(tr_min)`.** It carried a mistake
taxonomy — premature close (MC++) when an ACT re-opened the row a timeout PRE
had just closed, held-too-long (MC−−) when a conflict PRE closed a bank whose
timer had not expired — and walked TR by `tr_step` within `[tr_min, tr_max]`
every `check_interval`. In practice MC is dominated by the held-too-long case,
so TR decayed monotonically to the floor and stayed: moving only `tr_min` moved
the result onto the matching fixed point every time (2 → 436.8 MB/s, 8 → 338.5,
16 → 327.7). `MC` was also a single GLOBAL counter driving all eight `r_tr[b]`,
so `policy_scope`'s "per-bank TR" could not diverge from global. Mode 3 is
already its close path, so retiring it cost nothing functional.

**`adapt_access` was removed as a decision, not a measurement.** A per-row
2-bit saturating counter (tagless, {bank, XOR-folded row}) voted at ACT time
and drove `ap_close_o` — auto-precharge. That mechanism measures 4.9x the
activations of a background precharge on identical traffic (160,006 vs 32,400
ACT) and double the read latency, and it commits at the column op, before it is
known whether more requests to that row are coming. On a controller whose value
is FR-FCFS reordering to batch same-row columns, AP fights the reordering that
justifies the design, so even a perfect predictor is bounded by a losing
mechanism. It was unproven and mis-plumbed rather than disproven; re-plumbing
it onto the background precharge was the alternative not taken.

<!-- retired adapt_time adjustment rule, kept for the record:
Every `check_interval` cycles: `MC > mc_high_thr` → TR += step;
`MC < mc_low_thr` → TR −= step; clamp to `[tr_min, tr_max]`; MC re-arms to
`mc_init`. `policy_scope` selects per-bank TR (0) or a single global TR (1).
-->

## Telemetry

Always on, mode-independent, feeding the read-only `*_STATS` CSRs:

| Counter | Event |
|---|---|
| `PAGE_STATS_HIT`   | Column op issued (columns only issue on row hits in this arbiter). |
| `PAGE_STATS_MISS`  | ACT to a bank whose previous close was a conflict PRE. |
| `PAGE_STATS_EMPTY` | ACT to a simply-closed bank (timeout / refresh closes count here). |
| `SCHED_STATS_ACT` / `SCHED_STATS_PRE` / `REF_STATS_REF` | Command-class counts. |

## Verification

`test_pumice_core_dfi.py::test_pumice_core_fixed_open` — self-checking in
both directions: mode-0 arms assert zero idle precharges before and after the
mode arms (inertness and disarm) and the fixed_open arm asserts the idle-timeout
close and a clean golden-data reopen. The close request was mutation-checked
(engine forced off → the test fails at "row never closed").

`test_page_predictor.py` asserts the RETIREMENT contract: mode 0 and every
retired encoding (4..7) leave `ap_mode_en_o` low and `ap_close_o` at zero,
while mode 2 (`static_close`) does auto-precharge — so the test still
distinguishes "no AP" from a block that has stopped driving `ap_close_o` at
all. `test_pumice_sched_matrix.py` sweeps the retired encodings as
fallthrough arms across all 12 operating points.

## Related

- `ch02/07` scheduler — the arbiter pick order this engine feeds.
- `docs/design-requirements.md` "Advanced modes", Axis 2 — the mode catalog
  and the serial landing order.

> Modes 6/7 (`rbl_static`/`rbl_dyn`) were **RETIRED 2026-09-26**: measured on silicon at txn_scale=1000 on a workload built specifically to suit them (TASK-011), mode 6 lost 26% of bandwidth (195.2 -> 144.2 MB/s) by paying +22,827 ACTs to save precharges that never materialised, and mode 7's hill-climb drove its threshold to "never close early", landing bit-identical to plain open page. A write of 6 or 7 now falls through to the build default.

## Mechanism: why the close path matters more than the policy

One live mode closes a row with **auto-precharge** (`ap_close_o`, fused into
the column command) and one with a **background precharge**
(`timeout_pre_req_o`, a separate command the arbiter issues at lowest
priority). This distinction is why the adaptive modes were retired rather than
tuned — it dominates the policy that selects it:

| mode | close mechanism |
|---|---|
| 2 `static_close` | auto-precharge |
| 3 `fixed_open` | background precharge |

Measured on the board, same stimulus and the same close-on-sight policy,
differing only in mechanism (txn_scale=1000, peak 600 MB/s):

| mechanism | rd MB/s | ACT | PRE | thrash | rd latency |
|---|---|---|---|---|---|
| auto-precharge | 144.1 | **160,006** | 8 | 0.0% | 192.0 |
| background precharge (TR=1) | **436.8** | **32,400** | 40,400 | 24.7% | 96.0 |

**Auto-precharge costs 4.9x the activations for identical traffic and doubles
read latency.** Confirmed independently on both AP paths -- the legacy `w_ap`
route (160,018 ACT) and `ap_close_o` (160,002 ACT) land on the same number, so
this is a property of auto-precharge and not of one implementation.

The reason is that **auto-precharge is uncancellable.** It commits to closing at
the column op, before it is known whether more requests to that row are coming.
A background precharge fires only once the bank goes IDLE, and if more same-row
requests are pending the bank is not idle -- so the row survives and serves
them. That idle gate is an implicit cancellation. On a controller whose value is
FR-FCFS reordering to batch same-row columns, auto-precharge destroys the row
before the batching can happen: it fights the reordering that justifies the
design.

Corollary for the adaptive modes: `fixed_open` at TR=1 and TR=2 are identical,
so the grace period contributes nothing measurable. The idle gate alone does the
work.

## Standing of the adaptive modes (measured 2026-09-26)

**Mode 4 `adapt_time` is subsumed by mode 3.** Its adaptation earns nothing
measurable. `r_mc` is dominated by the held-too-long case (a conflict PRE on a
bank whose timer had not expired), so TR decays monotonically to `tr_min` and
stays there. Proven by moving only the floor:

| config | `tr_min` | rd MB/s | equals |
|---|---|---|---|
| `adapt_time` | 2 | 436.8 | `fixed_open` TR=2 -> 436.8 |
| `adapt_time` | 8 | 338.5 | `fixed_open` TR=8 -> 338.5 |
| `adapt_time` | 16 | 327.7 | `fixed_open` TR=16 -> 327.7 |

Exact equality at three different floors: mode 4 is `fixed_open(tr_min)`. Note
also that `r_mc` is a single GLOBAL counter driving every `r_tr[b]` from one
decision, and all eight start at `tr_init` -- so `policy_scope = 0`'s "per-bank
TR" cannot diverge and is a fiction. Retiring mode 4 costs nothing functional,
because mode 3 *is* its close path.

**Mode 5 `adapt_access` is unproven and mis-plumbed, not disproven.**
`close_pred_o` does not assert on hardware: `PRE ~= ACT` and thrash falls only
100% -> 97% at best, against 60% of activations converted in the DFI-loopback
sim on identical stimulus. The divergence is not run length (board engagement is
0% at txn_scale 1 and 10, saturating at 3% from 100) and not refresh rate (it is
non-monotonic -- zero at both refresh extremes). The `ap_close_o` port itself is
proven good: mode 2 driving it returns ACT=160,002 / PRE=2.

Even with that bug fixed, mode 5 would drive auto-precharge -- the mechanism
above, costing 4.9x the activations. **The change worth making is routing the
per-row verdict to `timeout_pre_req_o` instead of `ap_close_o`**, keeping the
idle-gate cancellation that makes mode 3 fast while adding per-row selectivity.
That is the only version of mode 5 that could beat `fixed_open`.
