# Task: TASK-020 - Identify Tests That Would Benefit from WaveDrom

## Priority
**P3 - Low**

## Status
**🔴 Not Started**

## Description

Survey the entire test suite to identify additional tests that would significantly benefit from WaveDrom timing diagram generation for documentation, debugging, or protocol visualization purposes.

## Background

**Current WaveDrom Coverage:**
- ✅ GAXI buffers (sync/async) - Complete
- ⏸️ APB monitors - Planned (TASK-017)
- ⏸️ AXI4 monitors - Planned (TASK-018)

**Goal:** Create prioritized list of other tests where WaveDrom would add value.

## Prerequisites

- [x] GAXI WaveDrom integration complete (reference pattern)
- [x] WaveDrom framework functional
- [ ] Initial survey of test suite

## Methodology

### Step 1: Survey Test Suite

**Directories to Survey:**
```bash
val/common/       # Common building blocks
val/amba/         # AMBA protocols
val/rapids/         # RAPIDS subsystem
val/integ_amba/   # Integration tests
```

**For Each Test File:**
1. Identify protocol/module being tested
2. Assess complexity of timing behavior
3. Determine if waveforms would clarify behavior
4. Estimate effort to add WaveDrom support

### Step 2: Evaluation Criteria

**High-Value Candidates:**
- ✅ Complex timing relationships (multi-signal dependencies)
- ✅ Protocol-based interfaces (handshakes, phases, states)
- ✅ Educational value (good for documentation)
- ✅ Frequently debugged (waveforms aid debugging)
- ✅ Novel or unique behaviors (worth visualizing)

**Low-Value Candidates:**
- ❌ Simple combinatorial logic
- ❌ Single-signal tests
- ❌ Already well-understood behavior
- ❌ Rarely used modules

### Step 3: Effort Assessment

**Low Effort (1-2 hours):**
- Simple protocol, few signals
- Similar to existing WaveDrom patterns
- Existing field configurations can be reused

**Medium Effort (3-5 hours):**
- Moderate complexity
- Need new field configurations
- Multiple scenarios

**High Effort (6+ hours):**
- Very complex protocol
- Many signals/channels
- Custom constraint patterns needed

## Deliverables

### 1. Survey Spreadsheet/Table

**Format:**
```markdown
| Test File | Module | Protocol | Complexity | Value | Effort | Priority | Notes |
|-----------|--------|----------|------------|-------|--------|----------|-------|
| test_arbiter_rr.sv | Round-robin arbiter | Custom | Medium | High | Low | P1 | Shows arbitration patterns |
| test_counter_bin.sv | Binary counter | Simple | Low | Low | Low | P3 | Too simple for waves |
| ... | ... | ... | ... | ... | ... | ... | ... |
```

**Columns:**
- **Test File:** Path to test file
- **Module:** RTL module being tested
- **Protocol:** Protocol type (AXI, APB, custom, none)
- **Complexity:** Low/Medium/High
- **Value:** How much would WaveDrom help?
- **Effort:** Estimated effort to implement
- **Priority:** P1/P2/P3 recommendation
- **Notes:** Specific scenarios that would benefit

### 2. Prioritized Candidate List

**High Priority (P1):**
- Tests with high value, low-medium effort
- Protocol-heavy tests
- Frequently used modules

**Medium Priority (P2):**
- Medium value, medium effort
- Educational examples
- Integration tests

**Low Priority (P3):**
- Low value or high effort
- Simple tests
- Rarely used modules

### 3. Implementation Recommendations

**For Each High-Priority Candidate:**
- Suggested scenarios to visualize (2-4 per test)
- Required field configurations
- Estimated effort breakdown
- Dependencies on other tasks

## Expected Candidate Categories

### Category 1: Arbiters (Likely High Value)

**Candidates:**
- `val/common/test_arbiter_round_robin*.py`
- `val/amba/test_arbiter_*_monbus.py`

**Why:** Arbitration patterns are visually intuitive, show request/grant timing

**Scenarios:**
- Multiple simultaneous requests
- Priority arbitration
- Round-robin fairness

### Category 2: Counters (Likely Low Value)

**Candidates:**
- `val/common/test_counter_*.py`

**Why:** Simple behavior, low educational value for waveforms

**Exception:** `test_counter_freq_invariant.py` might be interesting (shows frequency adaptation)

### Category 3: FIFOs (Medium Value - Already Have GAXI)

**Candidates:**
- Already covered by GAXI WaveDrom

**Skip:** Redundant with existing GAXI coverage

### Category 4: Protocol Converters (High Value)

**Candidates:**
- `val/integ_amba/test_axi2apb_shim.py` - AXI to APB bridge

**Why:** Shows protocol translation, interesting timing

**Scenarios:**
- AXI transaction → multiple APB transactions
- Backpressure handling
- Error propagation

### Category 5: State Machines (High Value)

**Candidates:**
- Any tests with complex FSMs

**Why:** State transitions are visually clear in waveforms

### Category 6: Clock Domain Crossing (High Value)

**Candidates:**
- Already covered by GAXI async
- Look for other CDC modules in common/

**Why:** CDC timing is critical and hard to debug

### Category 7: RAPIDS Subsystem (Medium-High Value)

**Candidates:**
- `val/rapids/fub_tests/descriptor_engine/`
- `val/rapids/fub_tests/scheduler/`
- `val/rapids/fub_tests/network_interfaces/`

**Why:** Complex subsystem, waveforms aid understanding

**Scenarios:**
- Descriptor fetch and execution
- Task scheduling
- Network interface transactions

## Deliverable Format

**File:** `rtl/amba/PRD/WAVEDROM_CANDIDATE_SURVEY.md`

**Content:**
```markdown
# WaveDrom Candidate Test Survey

**Survey Date:** YYYY-MM-DD
**Surveyor:** [Name]

## Summary

**Tests Surveyed:** XX
**High Priority Candidates:** XX
**Medium Priority Candidates:** XX
**Low Priority Candidates:** XX

## High Priority Recommendations

### 1. Arbiter Tests
**Files:** [list]
**Value:** High - Visual arbitration patterns
**Effort:** Low - Simple protocol
**Scenarios:** [list]

### 2. AXI2APB Bridge
...

## Medium Priority Recommendations
...

## Low Priority (Defer)
...

## Complete Survey Table
[Full table with all tests]
```

## Success Criteria

- [ ] All test directories surveyed
- [ ] Each test categorized (high/medium/low value)
- [ ] Effort estimated for high-priority candidates
- [ ] Survey document created
- [ ] Recommendations clear and actionable
- [ ] At least 5 high-priority candidates identified

## Testing Strategy

**No testing required** - This is a survey/analysis task

## Follow-Up Tasks

**After this task completes:**
- Create individual tasks for each high-priority candidate
- Example: "TASK-021: Add WaveDrom to Arbiter Tests"
- Example: "TASK-022: Add WaveDrom to AXI2APB Bridge Test"

**Each follow-up task should reference:**
- This survey for rationale
- GAXI WaveDrom pattern for implementation approach

## References

**Existing WaveDrom Integration:**
- `val/amba/test_gaxi_buffer_sync.py` (reference pattern)
- `val/amba/test_gaxi_buffer_async.py` (reference pattern)
- `val/amba/WAVEDROM_INTEGRATION_SUMMARY.md` (integration guide)

**Test Directories:**
- `val/common/` - Common building blocks
- `val/amba/` - AMBA protocols
- `val/rapids/` - RAPIDS subsystem
- `val/integ_amba/` - Integration tests

**Framework:**
- `bin/CocoTBFramework/components/wavedrom/`
- `bin/CocoTBFramework/tbclasses/wavedrom_user/`

## Related Tasks

**Completed:**
- GAXI WaveDrom integration (✅)

**In Progress/Planned:**
- TASK-017: APB WaveDrom support
- TASK-018: AXI4 WaveDrom support
- TASK-019: GAXI tutorial docs

**Future (Depends on This Survey):**
- TASK-021+: Individual WaveDrom integration tasks for identified candidates

## Suggested Approach

**Phase 1: Quick Scan (1-2 hours)**
- List all test files
- Quick categorization (protocol-based vs simple logic)
- Identify obvious high-value candidates

**Phase 2: Detailed Analysis (2-3 hours)**
- For each protocol-based test:
  - Read test code to understand scenarios
  - Assess complexity
  - Estimate effort
- Document findings

**Phase 3: Prioritization (1 hour)**
- Rank candidates
- Create implementation roadmap
- Write recommendations

**Total Effort:** 4-6 hours

---

**Task Owner:** TBD
**Created:** 2025-10-06
**Target Completion:** TBD
**Estimated Effort:** 4-6 hours (survey and analysis)
**Output:** WAVEDROM_CANDIDATE_SURVEY.md with prioritized candidate list
