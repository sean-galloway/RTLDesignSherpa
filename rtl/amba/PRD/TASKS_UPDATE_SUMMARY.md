# AMBA TASKS Update Summary

**Date:** 2025-10-06
**Action:** Task list review and updates

---

## Summary of Changes

### 1. TASK-001 Updated to COMPLETE ✅

**File:** `TASK-001-axi_monitor_reporter.md`

**Status Change:** "Ready to Start" → "✅ COMPLETE (2025-10-04)"

**Key Updates:**
- Added "COMPLETED WORK" section documenting RTL fix
- Noted commit c9a60f6 implemented `event_reported_flags` feedback
- Listed 3 RTL files modified
- Verified integration in AXI4 monitors
- Kept original problem description for historical reference
- Added follow-up reference to TASK-016

**Result:** Critical event_reported feedback bug is now properly documented as FIXED.

---

## New Tasks Created

### 2. TASK-016: AXI Monitor Test Validation and Refinement

**File:** `TASK-016-monitor_test_validation.md`
**Priority:** P1 - High
**Status:** 🔴 Not Started

**Purpose:**
Complete final validation of AXI monitor tests following TASK-001 RTL fix.

**Key Deliverables:**
- Run comprehensive test suite (8 tests)
- Fix any remaining test configuration issues
- Validate all AXI4 monitor variants (8 tests total)
- Update documentation

**Why Separate from TASK-001:**
- TASK-001 = RTL implementation (done)
- TASK-016 = Validation/testing (pending)
- Clean separation of concerns

---

### 3. TASK-017: Add WaveDrom Support to APB Monitor Tests

**File:** `TASK-017-wavedrom_apb_monitors.md`
**Priority:** P2 - Medium
**Status:** 🔴 Not Started

**Purpose:**
Add minimal WaveDrom timing diagrams to APB monitor tests.

**Pattern:** Follow GAXI WaveDrom integration approach

**Key Deliverables:**
- Create APB field configuration
- Add wavedrom test function
- Generate 3 WaveJSON files (read, write, error scenarios)
- Update documentation

**Scenarios:**
1. Basic read transaction
2. Basic write transaction
3. Error response (PSLVERR)

**Effort:** 3-4 hours

---

### 4. TASK-018: Add WaveDrom Support to AXI4 Monitor Tests

**File:** `TASK-018-wavedrom_axi4_monitors.md`
**Priority:** P2 - Medium
**Status:** 🔴 Not Started
**Depends On:** TASK-016 (recommended)

**Purpose:**
Add WaveDrom timing diagrams to AXI4 monitor tests showing complex protocol behavior.

**Key Deliverables:**
- Create AXI4 read/write field configurations
- Add wavedrom tests for master read/write monitors
- Generate 8 WaveJSON files (4 read + 4 write scenarios)
- Update documentation with embedded waveforms

**Scenarios (per read/write):**
1. Single-beat transaction
2. Burst transaction (4-beat INCR)
3. Out-of-order completion
4. Error response (SLVERR/DECERR)

**Challenges:**
- Multi-channel complexity (AR+R or AW+W+B)
- Burst transactions
- Out-of-order timing

**Solutions:**
- Labeled groups for channels
- Constraint solver for burst detection
- Crossed edge annotations for reordering

**Effort:** 6-10 hours

---

### 5. TASK-019: Create GAXI Integration Tutorial Documentation

**File:** `TASK-019-gaxi_tutorial_docs.md`
**Priority:** P2 - Medium
**Status:** 🔴 Not Started

**Purpose:**
Document GAXI multi-field integration examples from rtl/amba/testcode/

**Modules to Document:**
- `gaxi_skid_buffer_multi.sv` - Multi-field skid buffer
- `gaxi_skid_buffer_multi_sigmap.sv` - With signal mapping
- `gaxi_fifo_sync_multi.sv` - Sync FIFO with fields
- `gaxi_fifo_async_multi.sv` - Async FIFO with fields
- `gaxi_skid_buffer_async_multi.sv` - Async skid with fields

**Key Deliverables:**
- Create `docs/markdown/TestTutorial/gaxi_multi_field_integration.md`
- Create `docs/markdown/TestTutorial/gaxi_field_configuration.md`
- Update tutorial index
- Document design patterns and use cases

**Focus:**
- Integration patterns (not API docs)
- Real-world examples from testcode/
- When and why to use each pattern
- Common pitfalls

**Note:** NO WaveDrom generation needed - pure documentation task

**Effort:** 4-6 hours

---

### 6. TASK-020: Identify Tests That Would Benefit from WaveDrom

**File:** `TASK-020-identify_wavedrom_candidates.md`
**Priority:** P3 - Low
**Status:** 🔴 Not Started

**Purpose:**
Survey entire test suite to identify high-value WaveDrom candidates.

**Methodology:**
1. Survey all test directories (common, amba, rapids, integ_amba)
2. Categorize by value (high/medium/low)
3. Estimate effort (low/medium/high)
4. Create prioritized recommendations

**Expected Candidates:**
- Arbiter tests (visual arbitration patterns)
- Protocol converters (AXI2APB bridge)
- State machines
- CDC modules
- RAPIDS subsystem

**Deliverable:**
`WAVEDROM_CANDIDATE_SURVEY.md` with:
- Complete survey table
- High/medium/low priority lists
- Implementation recommendations
- Effort estimates

**Follow-up:**
Create individual tasks for each high-priority candidate (TASK-021+)

**Effort:** 4-6 hours (survey and analysis)

---

## TASKS.md Summary Update

**File:** `rtl/amba/PRD/TASKS.md`

**Added New Phase:**
```markdown
## Phase 6: WaveDrom Integration and Documentation
- TASK-016: AXI Monitor Test Validation (P1)
- TASK-017: APB WaveDrom Support (P2)
- TASK-018: AXI4 WaveDrom Support (P2)
- TASK-019: GAXI Tutorial Docs (P2)
- TASK-020: Identify WaveDrom Candidates (P3)
```

**Updated Task Summary Table:**
```
| Phase | Tasks | Complete | In Progress | Not Started |
|-------|-------|----------|-------------|-------------|
| 1: AXI Monitor Core | 1 | 1 | 0 | 0 |
| 2: AXI4 Integration | 4 | 0 | 0 | 4 |
| 3: AXI4 Validation | 2 | 0 | 0 | 2 |
| 4: AXIL Development | 4 | 0 | 0 | 4 |
| 5: Enhancements | 4 | 0 | 0 | 4 |
| 6: WaveDrom & Docs | 5 | 0 | 0 | 5 |
| **TOTAL** | **20** | **1** | **0** | **19** |
```

**Previous:** 15 tasks total
**New:** 20 tasks total (+5 new tasks)

---

## Task Priorities Summary

### P0 - Critical
- None (TASK-001 was P0, now complete)

### P1 - High
- TASK-001: event_reported fix (✅ COMPLETE)
- TASK-002 through TASK-005: AXI4 Integration (🔴 Not Started)
- TASK-006, TASK-007: AXI4 Validation (🔴 Not Started)
- TASK-008 through TASK-011: AXIL Development (🔴 Not Started)
- **TASK-016: Monitor Test Validation** (🔴 Not Started) ← **NEW**

### P2 - Medium
- TASK-012: Fix Error/Orphan Tests (🔴 Not Started)
- TASK-013: Integration Examples (🔴 Not Started)
- TASK-014: Performance Characterization (🔴 Not Started)
- **TASK-017: APB WaveDrom** (🔴 Not Started) ← **NEW**
- **TASK-018: AXI4 WaveDrom** (🔴 Not Started) ← **NEW**
- **TASK-019: GAXI Tutorial Docs** (🔴 Not Started) ← **NEW**

### P3 - Low
- TASK-015: Address/ID Filtering (🔴 Not Started)
- **TASK-020: Identify WaveDrom Candidates** (🔴 Not Started) ← **NEW**

---

## Files Created

1. ✅ `rtl/amba/PRD/TASK-016-monitor_test_validation.md`
2. ✅ `rtl/amba/PRD/TASK-017-wavedrom_apb_monitors.md`
3. ✅ `rtl/amba/PRD/TASK-018-wavedrom_axi4_monitors.md`
4. ✅ `rtl/amba/PRD/TASK-019-gaxi_tutorial_docs.md`
5. ✅ `rtl/amba/PRD/TASK-020-identify_wavedrom_candidates.md`

## Files Modified

1. ✅ `rtl/amba/PRD/TASK-001-axi_monitor_reporter.md` (marked complete)
2. ✅ `rtl/amba/PRD/TASKS.md` (added Phase 6, updated summary)

---

## Recommended Next Actions

### Immediate (P1):
1. **TASK-016:** Validate AXI monitor tests
   - Run full test suite
   - Verify event_reported fix working
   - Fix any test configuration issues
   - **Estimated:** 4-8 hours

### Short-term (P2):
2. **TASK-017:** Add APB WaveDrom support
   - Simple protocol, good starting point
   - **Estimated:** 3-4 hours

3. **TASK-019:** Create GAXI tutorial docs
   - No code needed, pure documentation
   - High educational value
   - **Estimated:** 4-6 hours

### Medium-term (P2):
4. **TASK-018:** Add AXI4 WaveDrom support
   - More complex, defer until after TASK-016
   - **Estimated:** 6-10 hours

### Long-term (P3):
5. **TASK-020:** Survey for WaveDrom candidates
   - Identify future work
   - **Estimated:** 4-6 hours

---

## Context for Future Work

**WaveDrom Pattern Established:**
The GAXI buffer WaveDrom integration (completed 2025-10-06) provides a proven pattern:
- Separate wavedrom test functions (non-intrusive)
- ENABLE_WAVEDROM flag (opt-in)
- Segmented capture (clean scenarios)
- Auto-binding (protocol-aware)
- Field configuration (proper formatting)

**Reference Files:**
- `val/amba/test_gaxi_buffer_sync.py` (lines 163-682)
- `val/amba/test_gaxi_buffer_async.py` (lines 200-572)
- `val/amba/WAVEDROM_INTEGRATION_SUMMARY.md`

**All new WaveDrom tasks (TASK-017, TASK-018) should follow this pattern.**

---

**Maintained By:** RTL Design Sherpa Project
**Last Updated:** 2025-10-06
**Reviewer:** [User]
