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

# Global Timers (`global_timers`)

**Module:** `global_timers.sv`
**Location:** `rtl/fub/`
**Category:** FUB
**Parent macro:** `pumice_mem_cmd_scheduler`
**Status:** implemented (v2 H)

## Purpose

Controller-wide constraint trackers that span banks. Where
`pumice_bank_timers` holds per-(rank, bank) JEDEC "safe" countdowns,
`global_timers` holds the **windows that apply across banks** — some
per-rank (device-local limits), some truly global (shared DQ bus):

| Constraint | Meaning                                              | Tracked as                                            |
|------------|------------------------------------------------------|-------------------------------------------------------|
| **tFAW**   | At most 4 ACT commands within `t_faw_i` cycles       | Per-rank: a 4-deep sliding window of countdown timers |
| **tRRD**   | Minimum cycles between any two ACT commands          | Per-rank: single countdown, reloaded on each ACT      |
| **tWTR**   | Cycles after a WR before any RD                      | Global: single countdown, reloaded on each WR         |
| **tRTW**   | Cycles after a RD before any WR                      | Global: single countdown, reloaded on each RD         |
| **tCCD**   | Cycles between back-to-back column (RD/WR) commands  | Global: single countdown, reloaded on each RD *and* WR |

tFAW and tRRD are **per-rank** because they enforce device-local
thermal/power limits — each rank has its own 4-deep tFAW slot array and its
own tRRD countdown, so multi-rank silicon meters each device
independently. tWTR, tRTW, and tCCD are **global** because they gate the
shared DQ bus, which every rank contends for.

The FUB exposes `_window_ok` flags to the scheduler:

```
tfaw_window_ok_o [NUM_RANKS]   // per-rank: 1 = at least one tFAW slot is at 0
trrd_window_ok_o [NUM_RANKS]   // per-rank: 1 = tRRD has elapsed
twtr_global_ok_o               // global : 1 = tWTR has elapsed
trtw_window_ok_o               // global : 1 = tRTW has elapsed
tccd_window_ok_o               // global : 1 = tCCD has elapsed
```

All five `_window_ok` outputs are strict-flop registered. Default after
reset is `'1` / `1'b1` (all windows open), which is correct given no
ACTs/WRs/RDs have been issued.

## Timer mechanics

All timers are 8-bit down-counters that saturate at 0 (they decrement each
`mc_clk` while non-zero). Reload values come in on the `t_*_i` ports:

- **`evt_act_i`** (with `evt_act_rank_i`): installs `t_faw_i` into the
  targeted rank's tFAW slot with the smallest remaining count (the freed
  slot), and reloads that rank's tRRD with `t_rrd_i`.
- **`evt_wr_i`**: reloads the global tWTR (`t_wtr_global_i`) *and* tCCD
  (`t_ccd_i`).
- **`evt_rd_i`**: reloads the global tRTW (`t_rtw_i`) *and* tCCD
  (`t_ccd_i`).

`tfaw_window_ok_o[r]` is high when rank `r` has at least one tFAW slot at 0
(i.e. fewer than 4 ACTs are still inside the window).

## Observability

Combinational `obs_*` "non-zero" flags mirror each counter for CSR/debug
observation:

```
obs_faw_nz_o  [NUM_RANKS]   obs_trrd_nz_o [NUM_RANKS]
obs_twtr_nz_o               obs_trtw_nz_o               obs_tccd_nz_o
```

## Parameters

| Parameter   | Default | Purpose                        |
|-------------|---------|--------------------------------|
| `NUM_RANKS` | 1       | Per-rank tFAW/tRRD array depth |
| `NUM_BANKS` | 8       | (`BKW` derivation)             |

## Scope

- **Per-rank tFAW / tRRD** are implemented (v2 H). Multi-rank silicon may
  still need the per-rank windows tightened against rank-level scheduler
  coordination.
- **tCCD is tracked here** now (it was previously baked into burst-length
  pacing in the scheduler).

## Tests

Verified by `dv/tests/fub/test_global_timers.py`: `smoke`, `tfaw_4_acts`,
`trrd_spacing`, `twtr_after_wr`, `trtw_after_rd` (plus tCCD coverage as the
suite is extended for the v2 H additions).
