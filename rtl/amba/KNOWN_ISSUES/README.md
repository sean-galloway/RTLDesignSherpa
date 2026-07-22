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

# AXI Monitor Known Issues

This directory tracks known bugs and issues in the AXI monitor subsystem.

---

## Active Issues

### 🔴 OPEN

#### Issue: 8-channel STREAM engine wedge (non-monitor)
**Status:** 🟠 OPEN
**Severity:** MEDIUM — hang under 8-channel stress

**Summary:** After the monitor saturation fixes (`cb29e226`, `95c9490a`),
a residual hang remains in the 8-channel stream-engine stress family
(params 7/9/11 of the multi-channel sweep). The mechanism is on the DMA
engine side, not the monitor path — the monitor's `block_ready` contract
is proven recoverable by formal and the 100-seed undersized-table sweep.
Tracked in the STREAM project area
(`projects/components/dmas/stream/`).

#### Issue: axil4 monitor TB drain-window race (framework, non-RTL)
**Status:** 🟠 OPEN (workaround in place)
**Severity:** LOW — test flakiness only, no RTL impact

**Summary:** The 8 axil4 monitor suites shared a drain-window race with
the trans_mgr suite (the TB sampled results before the monitor's drain
window settled). Seeds are pinned as an interim workaround (`95c9490a`).
The proper settle-poll fix belongs in the RDS-DV (CocoTBFramework)
repository, not in this repo's RTL or tests.

---

## Resolved Issues

### ✅ ROOT-CAUSED AND FIXED (2026-07-21)

#### Issue: cluster state-accumulation wedge (long-session DMA hang)
**File:** `axi_monitor_blockready_hang_partial_channels.md`
**Status:** ✅ FIXED — commits `cb29e226` + `95c9490a`
**Severity:** MEDIUM — hang (not corruption); needed a long session; reprogram cleared it

**Summary:** The long-session board wedge was the monitor transaction
table saturating through two permanent slot-leak mechanisms — stray
non-last-beat poison (fixed by the saturation-recovery contract in
`cb29e226`: command-entry cap + strict `block_ready` reopen margin from
`monitor_common_pkg::cmd_entry_reserve`) and runtime-disabled packet
classes never marking entries reported (fixed by continuous auto-retire
in `95c9490a`). `block_ready` then latched low forever because the old
flat `MAX-3` margin placed the reopen threshold exactly at the
saturation point. Verified by in-RTL formal properties
(mutation-checked) and a 100-seed deliberately-undersized stream sweep.

#### Issue: `active_count` accumulator underflow
**File:** `axi_monitor_active_count_underflow.md`
**Status:** ✅ FIXED (2026-07-18)
**Severity:** MEDIUM-HIGH

**Summary:** The alloc-minus-cleanup accumulator could desync and
underflow to 0xFF under legal AXI, sticking `busy` high and
`block_ready` low. Found by the SymbiYosys proof; fixed by deriving
`active_count` as a registered pop-count of CAM occupancy (structurally
bounded to [0, N]).

### ✅ FIXED (2025-10-03)

#### Issue #1: Orphan Error Packet Flood
**File:** `axi_monitor_orphan_error_flood.md`
**Status:** ✅ FIXED (2025-10-03)
**Severity:** HIGH - Blocks monitor operation

**Summary:** Monitor generated continuous duplicate error packets after detecting orphan data, flooding the monitor bus and blocking legitimate completion packets.

**Impact (Before Fix):**
- 4/11 tests failing (all ID_WIDTH=8 configurations)
- Monitor bus saturation
- Unable to track transaction completions during stress tests

**Fix Applied:**
- **File:** `rtl/amba/monitor/axi_monitor_reporter.sv`
- **Change:** Added `TRANS_ORPHANED` state to `w_events_to_mark` logic
- **Result:** All 11/11 tests now passing

**Quick Reference:**
- **Affected module:** `axi_monitor_reporter.sv`
- **Root cause:** Orphan error flag not cleared after packet generation (TRANS_ORPHANED state excluded from event marking logic)
- **Fix:** Include TRANS_ORPHANED in event_reported flag update logic

---

### ✅ RESOLVED (2025-09-30)

#### Issue #0: Event Reported Feedback Bug
**File:** `axi_monitor_reporter.md`
**Status:** ✅ FIXED (2025-09-30)
**Severity:** MEDIUM

**Summary:** Transaction table entries weren't cleared after error events were reported, causing table exhaustion.

**Fix:** Added `event_reported_flags` feedback from reporter to trans_mgr to properly clear table entries after event reporting.

---

## Test Status Summary

**Overall (as of `95c9490a`):** val/amba regression fully green — 679
passed / 0 failed. Monitor formal: 10/10 proof directories PASS (in-RTL
properties, mutation-checked).

Directed suites added with the 2026-07 fixes:
- `test_axi_monitor_trans_mgr.py` — same-ID slots, oldest-first
  attribution, `phase_saturation_recovers`
- `test_axi_monitor_runtime_disable.py` — auto-retire of runtime-disabled
  classes (failed on pre-`95c9490a` RTL)
- `test_axi_monitor_wr_same_cycle.py` — same-cycle AW+W first-beat capture
- `test_axi4_master_rd_mon_cfg.py` — wrapper cfg API
  (`cfg_monitor_enable`, `cfg_timeout_cycles`, counters)
- `test_axi_monitor_pktgen.py` — reporter packet generation (rewritten:
  it previously encoded the runtime-disable leak as expected behavior)

---

## Bug Reporting

When reporting new issues, please include:

1. **Configuration** - Parameter values (ID_WIDTH, ADDR_WIDTH, MAX_TRANSACTIONS, etc.)
2. **Test case** - Reproducible test sequence
3. **Expected vs Actual** - What should happen vs what actually happens
4. **Log files** - Relevant excerpts from simulation logs
5. **Time window** - Simulation time or line numbers where issue occurs
6. **Waveform** - If available, point to specific signals/times

---

## Investigation Tools

### Finding Issues in Logs
```bash
# Find test failures
grep "FAIL" val/amba/logs/*.log

# Find duplicate packets
grep "UNKNOWN_EVENT_2" val/amba/logs/*.log | uniq -c

# Check packet counts
grep -c "PktType" val/amba/logs/*.log
```

### Searching RTL
```bash
# Find orphan detection
grep -rn "orphan" rtl/amba/monitor/

# Find error generation
grep -rn "UNKNOWN_EVENT" rtl/amba/monitor/

# Check event feedback
grep -rn "event_reported" rtl/amba/monitor/
```

---

## Version History

| Date       | Event |
|------------|-------|
| 2026-07-21 | Saturation wedge + runtime-disable leak FIXED (`cb29e226`, `95c9490a`); blockready hang root-caused; two open items recorded (STREAM 8ch engine wedge, axil4 TB drain race) |
| 2026-07-18 | active_count underflow found by formal and FIXED (pop-count derivation) |
| 2025-10-03 | Issue #1 FIXED - Orphan error flood resolved, all 11/11 tests passing |
| 2025-10-02 | Issue #1 discovered and documented (orphan error flood) |
| 2025-09-30 | Issue #0 fixed (event reported feedback) |

---

**Maintained by:** RTL Design Sherpa Project
**Last Updated:** 2026-07-21
