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

## Modes

| `policy_mode` | Name         | Behaviour |
|---|---|---|
| 0 | build default | Engine inert; legacy flat auto-precharge from `page_policy_or`. |
| 1 | `static_open`  | Per-bank ap mask forced 0 — rows stay open. |
| 2 | `static_close` | Per-bank ap mask forced 1 — every column op auto-precharges. |
| 3 | `fixed_open`   | ap=0; per-bank idle countdown from `PAGE_TIMEOUT_CFG.tr_init`. On expiry the engine REQUESTS a close; the arbiter issues the PRE as its strictly lowest-priority pick. |
| 4 | `adapt_time`   | `fixed_open` with an adapting timeout register TR (Ghasempour 2015 adaptive-timeout): a mistake counter walks TR by `tr_step` within `[tr_min, tr_max]` every `check_interval` cycles. |
| 5 | `adapt_access` | Per-row 2-bit close predictor (Ghasempour "Hybrid", `pumice_row_pred_table`): a tagless direct-mapped table of saturating counters indexed by {bank, XOR-folded row}. An explicit PRE close teaches from the accesses-per-activation count (<=1 access -> toward close, >=2 -> toward open); an auto-precharge close is judged by its reopen (same-row reopen = premature -> toward open). Verdict latched per bank at ACT time drives the ap mask. `ctr_open_max` / `ctr_init` in `PAGE_POLICY_CFG` shape the threshold and init (0 = defaults 2 and weak-open 1). |
| 6 | `rbl_static` | RBLA miss-counter table (Yoon 2012, `pumice_rbl_table`): per-set-associative row **miss** counters (tag = row, true-LRU, `PAGE_RBL_CFG` shapes ways/sets/threshold/epoch). A row whose miss count exceeds the threshold at ACT time is low-locality: its columns auto-precharge. |
| 7 | `rbl_dyn` | `rbl_static` + a per-epoch divider-free hill-climb of the miss threshold on the measured page-hit fraction (direction memory, clamp [1,255]). Needs a nonzero `PAGE_RBL_CFG.reset_interval`. |

## Decision interfaces to the arbiter

1. **Auto-precharge override** — `ap_mode_en` + a per-bank `ap_close` mask.
   When enabled, the arbiter's column picks take `ap_close[bank]` instead of
   the legacy flat `w_ap`.
2. **Timeout close** — `timeout_pre_req` + bank. A new arbiter branch below
   the conflict-precharge path issues the PRE, gated identically (registered
   `row_active` + `pre_ready` + the 2-cycle re-issue guard), so demand,
   refresh and JEDEC timing always outrank a housekeeping close.

## adapt_time mistake taxonomy

At the command stream, per the paper:

- **Premature close** (MC++): an ACT re-opens the same row a timeout PRE just
  closed on that bank. The closed row is captured from the registered
  open-row image at PRE time (a PRE carries no row field).
- **Held too long** (MC−−): a conflict (wrong-row) PRE closes a bank whose
  timer had not expired.

Every `check_interval` cycles: `MC > mc_high_thr` → TR += step;
`MC < mc_low_thr` → TR −= step; clamp to `[tr_min, tr_max]`; MC re-arms to
`mc_init`. `policy_scope` selects per-bank TR (0) or a single global TR (1).

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
mode arms (inertness and disarm), the fixed_open arm asserts the idle-timeout
close and a clean golden-data reopen, and the adapt_time arm smoke-tests the
adaptive path. The close request was mutation-checked (engine forced off →
the test fails at "row never closed").

## Related

- `ch02/07` scheduler — the arbiter pick order this engine feeds.
- `docs/design-requirements.md` "Advanced modes", Axis 2 — the mode catalog
  and the serial landing order.
