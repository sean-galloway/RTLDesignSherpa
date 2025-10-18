# Common RTL Library - Known Issues Tracking

**Last Updated:** 2025-10-15

## Directory Structure

This directory tracks all known RTL issues in the Common RTL Library, organized by resolution status:

```
known_issues/
├── README.md           ← This file
├── resolved/           ← Fixed bugs and completed investigations
│   ├── reset_sync.md
│   └── [other resolved issues]
└── active/             ← Unresolved issues and pending enhancements
    └── [active issues if any]
```

---

## Current Status

### ✅ Resolved Issues (1)

| Issue | Component | Status | Date Fixed | Verification |
|-------|-----------|--------|------------|--------------|
| Inverted reset polarity | reset_sync.sv | ✅ FIXED | 2025-10-14 | 4/4 test configs passing |

**Test Results:**
- **reset_sync:** 4/4 configurations passing (100%) - All synchronizer scenarios validated

### ⚠️ Active Issues (0)

**No active issues currently.**

All 86 modules in the Common RTL Library are production-ready with comprehensive test coverage.

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
**File**: `rtl/common/module_name.sv`
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

### Verification
Steps to verify the fix:
1. Test commands
2. Expected results
3. ...
```

### When to Move to Resolved

Move an issue file from `active/` to `resolved/` when:
1. **Fix verified** - RTL fix applied and tests passing
2. **No bug found** - Investigation proves functionality is correct
3. **Workaround documented** - Temporary workaround in place, will revisit later

Update the file with:
- Resolution date
- Fix description or investigation conclusion
- Test verification results
- Any follow-up actions needed

---

## Priority Guidelines

**High Priority:**
- Data corruption bugs
- Synthesis failures
- Timing violations
- Functional incorrectness

**Medium Priority:**
- Missing features that affect usability
- Performance issues
- Documentation gaps

**Low Priority:**
- Edge case limitations
- Minor optimizations
- Cosmetic issues

---

## Issue Reporting

When discovering an issue:

1. **Document thoroughly** - Create detailed issue file
2. **Update this README** - Add to active issues table
3. **Create test** - If possible, create failing test case
4. **Reference in TASKS.md** - Link to task for fixing
5. **Update CLAUDE.md** - Add to anti-patterns/gotchas if relevant

---

## Related Documentation

- **rtl/common/TASKS.md** - Active work items and task tracking
- **rtl/common/PRD.md** - Product requirements and specifications
- **rtl/common/CLAUDE.md** - AI assistant guidance for this subsystem
- **/PRD.md** - Master project requirements

---

**Document Owner:** RTL Design Sherpa Project
**Maintenance Frequency:** Updated as issues are discovered or resolved
