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
**Parent macro:** `command_scheduler_macro`
**Status:** v1 implemented

## Purpose

Controller-wide constraint trackers that span banks. Where `xbank_timers`
holds per-(rank, bank) JEDEC counters, `global_timers` holds **windows
that apply across all banks**:

| Constraint | Meaning                                              | Tracked as                                            |
|------------|------------------------------------------------------|-------------------------------------------------------|
| **tFAW**   | At most 4 ACT commands within `t_faw_i` cycles       | 4-deep sliding window of countdown timers per rank    |
| **tRRD**   | Minimum cycles between any two ACT commands          | Single countdown per rank, reloaded on each ACT       |
| **tWTR**   | Cycles after a WR before any RD                      | Single countdown per rank, reloaded on each WR        |
| **tRTW**   | Cycles after a RD before any WR                      | Single countdown per rank, reloaded on each RD        |

The FUB exposes per-rank `_window_ok` flags to the scheduler:

```
tfaw_window_ok_o   [NUM_RANKS]   // 1 = at least one tFAW slot is at 0
trrd_window_ok_o   [NUM_RANKS]   // 1 = tRRD has elapsed
twtr_global_ok_o   [NUM_RANKS]   // 1 = tWTR has elapsed
trtw_window_ok_o   [NUM_RANKS]   // 1 = tRTW has elapsed
```

All outputs are strict-flop registered. Default after reset is `'1` (all
windows open), which is correct given no ACTs/WRs/RDs have been issued.

## Scope

This is the v1 implementation; see TODOs in the RTL header for known
limitations:

- **Per-rank tFAW** is implemented; multi-rank silicon may need per-rank
  windows tightened against rank-level coordination.
- **tCCD** (CAS-to-CAS delay) is currently baked into burst-length timing
  in the scheduler rather than tracked here.

## Tests

Verified by `dv/tests/fub/test_global_timers.py` (5 scenarios):
`smoke`, `tfaw_4_acts`, `trrd_spacing`, `twtr_after_wr`, `trtw_after_rd`.
