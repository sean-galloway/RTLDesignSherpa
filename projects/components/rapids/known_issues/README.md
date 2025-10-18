# RAPIDS Known Issues - Tracking and Resolution

**Last Updated:** 2025-10-14

## Directory Structure

This directory tracks all known RTL issues in the RAPIDS subsystem, organized by resolution status:

```
known_issues/
├── README.md           ← This file
├── resolved/           ← Fixed bugs and completed investigations
│   ├── scheduler.md
│   ├── program_engine_bugs_found.md
│   └── descriptor_engine_apb_rda_sequential.md
└── active/             ← Unresolved issues and pending enhancements
    ├── sink_data_path.md
    └── sink_sram_control.md
```

---

## Current Status

### ✅ Resolved Issues (3)

All three FUBs (Functional Unit Blocks) in the scheduler group are now **production-ready** with all known bugs fixed:

| Issue | Component | Status | Date Fixed | Verification |
|-------|-----------|--------|------------|--------------|
| Credit counter initialization | Scheduler | ✅ FIXED | 2025-10-14 | 43/43 tests passing |
| FSM state transitions (3 bugs) | Program Engine | ✅ FIXED | 2025-10-14 | 8/8 tests passing |
| APB→RDA sequential pattern | Descriptor Engine | ✅ NO BUG FOUND | 2025-10-14 | All scenarios working |

**Test Results:**
- **Scheduler:** 43/43 tests passing (100%) - Credit-based flow control fully functional
- **Program Engine:** 8/8 tests passing (100%) - All FSM bugs fixed and verified
- **Descriptor Engine:** 14/14 tests passing (100%) - Sequential patterns work correctly

### ⚠️ Active Issues (2)

| Issue | Component | Severity | Priority | Impact |
|-------|-----------|----------|----------|--------|
| AXI timeout detection missing | Sink Data Path | Medium | Medium | Error detection incomplete |
| Single read operation limit | Sink SRAM Control | Low | Low | Architectural simplification |

**Note:** Active issues are **not bugs** but missing features or architectural limitations:
- **Sink Data Path:** Timeout detection is a planned enhancement, not a critical bug
- **Sink SRAM Control:** Single-read limitation is a design simplification, functionally correct

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
**File**: `projects/components/rapids/rtl/path/to/file.sv`
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
1. ✅ Bug fixed in RTL
2. ✅ All tests passing (100% success rate required)
3. ✅ Fix verified in production testing
4. ✅ Investigation complete (even if "no bug found")

**Update the file before moving:**
- Change **Status** to "✅ FIXED" or "✅ NO BUG FOUND" or "✅ RESOLVED"
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
ls projects/components/rapids/known_issues/active/

# List all resolved issues
ls projects/components/rapids/known_issues/resolved/

# View specific issue
cat projects/components/rapids/known_issues/active/sink_data_path.md
cat projects/components/rapids/known_issues/resolved/scheduler.md
```

### Search Issues

```bash
# Search for specific component
grep -r "Scheduler" projects/components/rapids/known_issues/

# Search for specific bug type
grep -r "timeout" projects/components/rapids/known_issues/

# Find all high-severity issues
grep -r "Severity.*High" projects/components/rapids/known_issues/active/
```

---

## Production Readiness Status

### ✅ PRODUCTION READY

**Scheduler Group FUBs (All 3 components):**
- ✅ **Scheduler** - Credit-based flow control fully functional
- ✅ **Program Engine** - All FSM state machine bugs fixed
- ✅ **Descriptor Engine** - All descriptor paths working correctly

**Test Coverage:**
- Scheduler: 43/43 tests (100%)
- Program Engine: 8/8 tests (100%)
- Descriptor Engine: 14/14 tests (100%)

**Date:** 2025-10-14

### ⚠️ PENDING ENHANCEMENTS

**Sink Data Path:**
- Missing: AXI timeout detection (medium priority)
- Status: Functionally correct, enhancement planned

**Sink SRAM Control:**
- Limitation: Single read operation at a time (low priority)
- Status: Functionally correct, architectural simplification

---

## Validation Philosophy

**RAPIDS follows a strict 100% success requirement for all tests:**

- ❌ Partial success (e.g., 70%) is **NOT acceptable** - indicates bugs or timing issues
- ✅ All tests must achieve **100% success rate** for production readiness
- ✅ RTL is deterministic - 100% success is always achievable
- ✅ Lower thresholds mask real problems and allow regressions

**Example Results:**
- ❌ Before fixes: 5/12 descriptors (42%) - UNACCEPTABLE
- ✅ After fixes: 14/14 tests (100%) - REQUIRED STANDARD

---

## References

**RAPIDS Documentation:**
- `projects/components/rapids/docs/rapids_spec/` - Complete RAPIDS specification
- `projects/components/rapids/PRD.md` - Product requirements document
- `projects/components/rapids/CLAUDE.md` - AI assistant guide
- `projects/components/rapids/TASKS.md` - Current work items

**Test Infrastructure:**
- `projects/components/rapids/dv/tests/fub_tests/` - Individual FUB tests
- `projects/components/rapids/dv/tests/integration_tests/` - Multi-block integration tests
- `bin/CocoTBFramework/tbclasses/rapids/` - Reusable testbench classes

---

**Maintained By:** RTL Design Sherpa Project
**Version:** 1.0
**Last Review:** 2025-10-14
