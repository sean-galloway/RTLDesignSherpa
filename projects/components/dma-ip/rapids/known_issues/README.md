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

# RAPIDS Known Issues - Tracking and Resolution

**Last Updated:** 2025-10-14

## Directory Structure

This directory tracks all known RTL issues in the RAPIDS subsystem, organized by resolution status:

```
known_issues/
├── README.md           ← This file
├── scheduler_group_signal_naming_conflicts.md
├── active/             ← Unresolved issues and pending enhancements (empty)
└── resolved/           ← Fixed; kept permanently for reference
    ├── desc_arsize_exceeds_bus_width.md
    ├── drain_size_gt1_source_beat_drop.md
    ├── sink_sram_control.md
    ├── char_harness_sink_selfcheck_no_beats.md
    ├── sink_data_path.md
    └── snk_scheduler_write_commit_stall.md
```

> **Status (2026-09-14):** `resolved/` exists again. The 2026-07-22 note said it
> had been retired with the pre-beats RTL its write-ups described, and invited
> whoever next resolved an issue to recreate it — but the next resolution
> (`snk_scheduler_write_commit_stall`, fixed 2026-07-16) was simply left sitting
> in `active/` with a body reading "RESOLVED". It stayed there for two months and
> made the active list read one issue longer than it was. Moved 2026-09-14.
>
> If you resolve an issue, MOVE THE FILE. A status line inside a file in
> `active/` is invisible to anyone counting the directory, which is how everyone
> counts it.

---

## Current Status

### Resolved Issues (6)

| File (`resolved/`) | What it was | Closed |
|---|---|---|
| `snk_scheduler_write_commit_stall.md` | Sink scheduler stalled on write commit | 2026-07-16 |
| `sink_data_path.md` | Sink data path AXI timeout detection (moved to the monitor by design) | 2026-09-14 |
| `char_harness_sink_selfcheck_no_beats.md` | Genesys2 char harness sink self-check saw no beats | 2026-09-22 |
| `drain_size_gt1_source_beat_drop.md` | Source path dropped beats at DRAIN_SIZE > 1 | 2026-09-27 (`29c696c30`) |
| `desc_arsize_exceeds_bus_width.md` | Descriptor engine issued ARSIZE wider than the bus | fixed in `e236d102e`, tracker moved 2026-09-27 |
| `sink_sram_control.md` | Single-read limit of the old `sink_sram_control` unit | module deleted in `bdf4e0dff` (STREAM `sram_controller` now), tracker retired 2026-09-27 |

### Active Issues (0)

`active/` is empty. The last two entries had been fixed days before their
trackers moved (see the 2026-09-14 note above for the same failure); the
directory count is what people read, so the file moves when the fix lands.

Open work that is not a defect is tracked in `vault/Tasks/projects/components/dma-ip/rapids/`,
not here.

---

## Issue Lifecycle

### When to Add an Issue

Create a new markdown file in `active/` when:
1. Bug discovered in RTL
2. Test failure indicates potential RTL issue
3. Missing functionality identified
4. Architectural limitation documented

### Issue File Format

```markdown
# Component Name - Known RTL Issues

## Issue Title

**Severity**: High/Medium/Low
**Impact**: Description of functional impact
**Status**: Active/Investigation/Fixed/No Bug Found
**Discovery Date**: YYYY-MM-DD

### Description
Clear description of the issue...

### Location
**File**: `projects/components/dma-ip/rapids/rtl/path/to/file.sv`
**Lines**: Line numbers

### Current Code (Problematic/Incomplete)
```systemverilog
// Code snippet showing the issue
```

### Impact on Functionality
1. List of impacts
2. ...

### Root Cause
Explanation of why the issue exists...

### Fix Required / Fix Applied
Description of the fix or proposed solution...

### Fix Priority
Justification for priority level...
```

### When to Move to Resolved

Move issue file from `active/` → `resolved/` when:
1. Bug fixed in RTL
2. All tests passing (100% success rate required)
3. Fix verified in production testing
4. Investigation complete (even if "no bug found")

**Update the file before moving:**
- Change **Status** to "FIXED" or "NO BUG FOUND" or "RESOLVED"
- Add **Fix Date** and **Verification** sections
- Include test results showing 100% pass rate
- Mark as production-ready

### When to Delete Issues

**NEVER delete issue files!** They serve as historical documentation:
- Track what bugs existed and how they were fixed
- Prevent regression of similar issues
- Document design decisions and investigations
- Provide examples for future debugging

Even resolved issues remain in `resolved/` permanently for reference.

---

## Quick Reference

### Check Current Status

```bash
# List all active issues
ls projects/components/dma-ip/rapids/known_issues/active/

# View specific issue
cat projects/components/dma-ip/rapids/known_issues/resolved/sink_data_path.md
```

### Search Issues

```bash
# Search for specific component
grep -r "Scheduler" projects/components/dma-ip/rapids/known_issues/

# Search for specific bug type
grep -r "timeout" projects/components/dma-ip/rapids/known_issues/

# Find all high-severity issues
grep -r "Severity.*High" projects/components/dma-ip/rapids/known_issues/active/
```

---

## Production Readiness Status

### PRODUCTION READY

**Scheduler Group FUBs (All 3 components):**
- **Scheduler** - Credit-based flow control fully functional
- **Program Engine** - All FSM state machine bugs fixed
- **Descriptor Engine** - All descriptor paths working correctly

**Test Coverage:**
- Scheduler: 43/43 tests (100%)
- Program Engine: 8/8 tests (100%)
- Descriptor Engine: 14/14 tests (100%)

**Date:** 2025-10-14

### PENDING ENHANCEMENTS

**Sink Data Path:**
- Missing: AXI timeout detection (medium priority)
- Status: Functionally correct, enhancement planned

**Sink SRAM Control:**
- Limitation: Single read operation at a time (low priority)
- Status: Functionally correct, architectural simplification

---

## Validation Philosophy

**RAPIDS follows a strict 100% success requirement for all tests:**

- Partial success (e.g., 70%) is **NOT acceptable** - indicates bugs or timing issues
- All tests must achieve **100% success rate** for production readiness
- RTL is deterministic - 100% success is always achievable
- Lower thresholds mask real problems and allow regressions

**Example Results:**
- Before fixes: 5/12 descriptors (42%) - UNACCEPTABLE
- After fixes: 14/14 tests (100%) - REQUIRED STANDARD

---

## References

**RAPIDS Documentation:**
- `projects/components/dma-ip/rapids/docs/rapids_beats_has/` + `docs/rapids_beats_mas/` - Complete RAPIDS specification
- `projects/components/dma-ip/rapids/PRD.md` - Product requirements document
- `projects/components/dma-ip/rapids/CLAUDE.md` - AI assistant guide
- `projects/components/dma-ip/rapids/TASKS.md` - Work items (largely pre-beats history)

**Test Infrastructure:**
- `projects/components/dma-ip/rapids/dv/tests/fub_beats/` (+ `fub/`) - Individual FUB tests
- `projects/components/dma-ip/rapids/dv/tests/macro_beats/` (+ `top_beats/`) - Multi-block/system tests
- `projects/components/dma-ip/rapids/dv/tbclasses/` - Reusable testbench classes

---

**Maintained By:** RTL Design Sherpa Project
**Version:** 1.0
**Last Review:** 2025-10-14
