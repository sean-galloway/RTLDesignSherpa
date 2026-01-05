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

# RAPIDS Task List

**Version:** 1.0
**Last Updated:** 2025-10-11
**Status:** Active Development - Validation in Progress
**Owner:** RTL Design Sherpa Project

---

## Task Status Legend

- 🔴 **Blocked** - Cannot proceed due to dependencies
- 🟠 **In Progress** - Currently being worked on
- 🟡 **Planned** - Ready to start, no blockers
- 🟢 **Complete** - Finished and verified
- ⏸️ **Deferred** - Low priority, postponed

## Priority Levels

- **P0 (Critical)** - Blocking progress, must fix immediately
- **P1 (High)** - Required for production readiness
- **P2 (Medium)** - Important but not blocking
- **P3 (Low)** - Nice to have, future enhancement

---

## Critical Issues (P0-P1)

### TASK-001: Fix Scheduler Credit Counter Initialization Bug
**Status:** 🟢 Complete
**Priority:** P0 (Critical)
**Effort:** 1-2 hours
**Assigned:** Completed 2025-10-11

**Description:**
Fixed credit counter initialization bug in scheduler that was preventing credit-based flow control from working. The scheduler uses **exponential credit encoding** where the 4-bit `cfg_initial_credit` value is decoded to actual credit counts.

**Location:**
- File: `projects/components/rapids/rtl/rapids_fub/scheduler.sv`
- Lines: 567-570

**Previous Issue:**
```systemverilog
// WRONG: Always initialized to 0
r_descriptor_credit_counter <= 32'h0;
```

**Applied Fix:**
```systemverilog
// FIXED: Exponential credit encoding: 0→1, 1→2, 2→4, ..., 14→16384, 15→∞
r_descriptor_credit_counter <= (cfg_initial_credit == 4'hF) ? 32'hFFFFFFFF :
                              (cfg_initial_credit == 4'h0) ? 32'h00000001 :
                              (32'h1 << cfg_initial_credit);
```

**Exponential Encoding Table:**

| `cfg_initial_credit` | Actual Credits | Use Case |
|---------------------|----------------|----------|
| 0 | 1 (2^0) | Minimum credits |
| 1 | 2 (2^1) | Very low traffic |
| 2 | 4 (2^2) | Low traffic |
| 4 | 16 (2^4) | Typical |
| 8 | 256 (2^8) | High traffic |
| 14 | 16384 (2^14) | Maximum finite |
| 15 | ∞ (0xFFFFFFFF) | Unlimited credits |

**Impact (Before Fix):**
- Credit-based flow control completely non-functional
- Tests had to work around by disabling credits (`cfg_use_credit = 0`)
- Blocked production deployment with credit management

**Verification Steps (To Complete):**
1. ✅ Applied exponential encoding fix to scheduler.sv:567-570
2. ✅ Updated all documentation with exponential encoding details
3. ⏳ Remove test workarounds in `projects/components/rapids/dv/tests/fub_tests/scheduler/`
4. ⏳ Run: `pytest projects/components/rapids/dv/tests/fub_tests/scheduler/ -v -k credit`
5. ⏳ Verify credit counter initializes with exponential decoding:
   - `cfg_initial_credit = 0` → counter = 1
   - `cfg_initial_credit = 4` → counter = 16
   - `cfg_initial_credit = 8` → counter = 256
   - `cfg_initial_credit = 15` → counter = 0xFFFFFFFF (unlimited)
6. ⏳ Test credit decrement on descriptor acceptance (linear decrement)
7. ⏳ Test credit increment on external requests (linear increment)
8. ⏳ Verify credit warning threshold operation
9. ⏳ Test credit exhaustion blocking behavior
10. ⏳ Test unlimited credits mode (cfg_initial_credit = 15)

**Related Files:**
- ✅ `projects/components/rapids/rtl/rapids_fub/scheduler.sv` (fix applied)
- ✅ `projects/components/rapids/docs/rapids_spec/ch02_blocks/01_01_scheduler.md` (updated with encoding table)
- ✅ `projects/components/rapids/docs/rapids_spec/ch02_blocks/01_00_scheduler_group.md` (updated)
- ✅ `projects/components/rapids/known_issues/scheduler.md` (updated with correct fix)
- ✅ `projects/components/rapids/CLAUDE.md` (updated with exponential encoding guidance)
- ⏳ `projects/components/rapids/PRD.md` (needs update)
- ⏳ `projects/components/rapids/dv/tests/fub_tests/scheduler/test_scheduler.py` (tests to update)

**Dependencies:** None

**Completion Criteria:**
- ✅ Credit counter implements exponential encoding correctly
- ✅ RTL fix applied
- ✅ Specification documentation updated
- ⏳ Test workarounds removed
- ⏳ All scheduler credit tests passing
- ⏳ Known issue documentation updated to "FIXED"

**Notes:**
- **Exponential encoding applies only at initialization** - Once running, the counter operates linearly (increment/decrement by 1)
- This encoding provides wide range (1 to 16384 credits) with compact 4-bit configuration
- Special case: `cfg_initial_credit = 15` → unlimited credits (0xFFFFFFFF)

---

### TASK-002: Implement AXI Timeout Detection in Sink Data Path
**Status:** 🟡 Planned
**Priority:** P2 (Medium)
**Effort:** 4-8 hours
**Assigned:** Unassigned

**Description:**
Implement proper AXI timeout detection in sink data path to replace placeholder implementation.

**Location:**
- File: `projects/components/rapids/rtl/rapids_macro/sink_data_path.sv`
- Line: 283

**Current Issue:**
```systemverilog
// TODO: Add timeout detection from AXI engine
assign error_axi_timeout = 1'b0;
```

**Required Implementation:**
1. Add timeout counter in sink AXI write engine
2. Monitor AXI transaction duration (AW → B channel)
3. Compare against configurable timeout threshold
4. Assert error when threshold exceeded
5. Generate MonBus timeout event packet

**Design Approach:**
```systemverilog
// In sink_axi_write_engine.sv
logic [$clog2(MAX_TIMEOUT)-1:0] r_timeout_counter;
logic r_timeout_error;

always_ff @(posedge aclk or negedge aresetn) begin
    if (!aresetn) begin
        r_timeout_counter <= '0;
        r_timeout_error <= 1'b0;
    end else begin
        if (axi_awvalid && axi_awready) begin
            r_timeout_counter <= '0;  // Start counting
        end else if (transaction_active && !axi_bvalid) begin
            if (r_timeout_counter < cfg_timeout_threshold) begin
                r_timeout_counter <= r_timeout_counter + 1;
            end else begin
                r_timeout_error <= 1'b1;  // Timeout detected
            end
        end

        if (axi_bvalid && axi_bready) begin
            r_timeout_counter <= '0;
            r_timeout_error <= 1'b0;  // Clear on completion
        end
    end
end

assign error_axi_timeout = r_timeout_error;
```

**Verification Steps:**
1. Add timeout detection logic to sink AXI write engine
2. Wire timeout signal to sink_data_path.sv
3. Create test: `projects/components/rapids/dv/tests/integration_tests/test_sink_timeout.py`
4. Simulate slow AXI slave (delayed BVALID)
5. Verify timeout detection triggers at threshold
6. Verify MonBus timeout packet generation
7. Test timeout recovery behavior

**Related Files:**
- `projects/components/rapids/rtl/rapids_fub/sink_axi_write_engine.sv` (add timeout logic)
- `projects/components/rapids/rtl/rapids_macro/sink_data_path.sv` (wire timeout signal)
- `projects/components/rapids/known_issues/sink_data_path.md` (issue documentation)
- Create: `projects/components/rapids/dv/tests/integration_tests/test_sink_timeout.py`

**Dependencies:** None

**Completion Criteria:**
- [ ] Timeout counter implemented
- [ ] Timeout detection working
- [ ] MonBus timeout packets generated
- [ ] Test coverage for timeout scenarios
- [ ] Known issue documentation updated to "FIXED"

---

## Test Infrastructure (P1-P2)

### TASK-003: Create Reusable Testbench Classes in CocoTBFramework
**Status:** 🟡 Planned
**Priority:** P1 (High)
**Effort:** 8-16 hours
**Assigned:** Unassigned

**Description:**
Refactor RAPIDS tests to follow mandatory testbench architecture with reusable TB classes in `bin/CocoTBFramework/tbclasses/rapids/`.

**Current State:**
- 32 test files in `projects/components/rapids/dv/tests/`
- Testbench logic embedded in test files (not reusable)
- Difficult to maintain and extend

**Required Structure:**
```
bin/CocoTBFramework/tbclasses/rapids/
├── scheduler_tb.py              ← NEW: Reusable scheduler testbench
├── descriptor_engine_tb.py      ← NEW: Reusable descriptor engine TB
├── program_engine_tb.py         ← NEW: Reusable program engine TB
├── sink_data_path_tb.py         ← NEW: Reusable sink path TB
├── source_data_path_tb.py       ← NEW: Reusable source path TB
├── rapids_integration_tb.py       ← NEW: Reusable integration TB
└── rapids_helpers.py              ← NEW: Shared utilities
```

**Implementation Steps:**

1. **Create Base Testbench Classes** (2-3 hours)
   - [ ] `scheduler_tb.py` - Scheduler FSM, credit management
   - [ ] `descriptor_engine_tb.py` - Descriptor FIFO, parsing
   - [ ] `program_engine_tb.py` - Program sequencing, alignment

2. **Create Data Path Testbench Classes** (3-4 hours)
   - [ ] `sink_data_path_tb.py` - Sink path (Network → SRAM → AXI)
   - [ ] `source_data_path_tb.py` - Source path (AXI → SRAM → Network)
   - [ ] `rapids_integration_tb.py` - Full RAPIDS integration

3. **Create Helper Utilities** (1-2 hours)
   - [ ] `rapids_helpers.py` - Descriptor generators, traffic patterns
   - [ ] `rapids_monitors.py` - Protocol monitors, checkers
   - [ ] `rapids_drivers.py` - AXIL4, Network drivers

4. **Refactor Existing Tests** (3-5 hours)
   - [ ] Update `projects/components/rapids/dv/tests/fub_tests/scheduler/` to import TB classes
   - [ ] Update `projects/components/rapids/dv/tests/fub_tests/descriptor_engine/` to import TB classes
   - [ ] Update `projects/components/rapids/dv/tests/integration_tests/` to import TB classes
   - [ ] Verify all tests still pass after refactoring

**Example Refactoring:**

**BEFORE (Wrong):**
```python
# projects/components/rapids/dv/tests/fub_tests/scheduler/test_scheduler.py
class SchedulerTB(TBBase):  # ❌ TB class in test file!
    # 200 lines of testbench logic...

@cocotb.test()
async def test_scheduler(dut):
    tb = SchedulerTB(dut)  # Can't be reused elsewhere
    ...
```

**AFTER (Correct):**
```python
# bin/CocoTBFramework/tbclasses/rapids/scheduler_tb.py
class SchedulerTB(TBBase):
    """Reusable scheduler testbench"""
    # 200 lines of REUSABLE testbench logic...

# projects/components/rapids/dv/tests/fub_tests/scheduler/test_scheduler.py
from CocoTBFramework.tbclasses.rapids.scheduler_tb import SchedulerTB

@cocotb.test()
async def test_scheduler(dut):
    tb = SchedulerTB(dut)  # ✅ Imported, reusable!
    ...
```

**Verification Steps:**
1. Create all TB class files in `bin/CocoTBFramework/tbclasses/rapids/`
2. Update test files to import TB classes
3. Run full test suite: `pytest projects/components/rapids/dv/tests/ -v`
4. Verify all tests pass
5. Update documentation

**Related Files:**
- Create: `bin/CocoTBFramework/tbclasses/rapids/*.py`
- Update: All test files in `projects/components/rapids/dv/tests/`
- Update: `projects/components/rapids/CLAUDE.md` with examples

**Dependencies:** None

**Completion Criteria:**
- [ ] All TB classes created in `bin/CocoTBFramework/tbclasses/rapids/`
- [ ] All test files refactored to import TB classes
- [ ] Full test suite passing
- [ ] Documentation updated
- [ ] Example patterns added to CLAUDE.md

---

### TASK-004: Expand Integration Test Coverage
**Status:** 🟡 Planned
**Priority:** P2 (Medium)
**Effort:** 8-12 hours
**Assigned:** Unassigned

**Description:**
Expand integration test suite to cover more complex multi-block scenarios and stress conditions.

**Current Coverage:** ~60% integration scenarios

**Required Test Scenarios:**

1. **Scheduler + Descriptor Engine Integration** (2-3 hours)
   - [ ] Multiple descriptors queued
   - [ ] Descriptor parsing with back-to-back operations
   - [ ] Credit coordination (after TASK-001 complete)
   - [ ] Error injection and recovery

2. **Complete Sink Path End-to-End** (2-3 hours)
   - [ ] Network → SRAM → AXI complete flow
   - [ ] Various packet sizes (small, medium, large)
   - [ ] Burst patterns and fragmentation
   - [ ] Backpressure scenarios
   - [ ] Buffer overflow detection

3. **Complete Source Path End-to-End** (2-3 hours)
   - [ ] AXI → SRAM → Network complete flow
   - [ ] Memory read burst optimization
   - [ ] Network transmission patterns
   - [ ] Backpressure from network
   - [ ] Buffer underflow detection

4. **Bidirectional Traffic** (2-3 hours)
   - [ ] Simultaneous sink and source operations
   - [ ] Resource contention handling
   - [ ] MonBus arbitration under load
   - [ ] Performance characterization

**Test Files to Create:**
```
projects/components/rapids/dv/tests/integration_tests/
├── test_scheduler_descriptor.py     ← NEW
├── test_sink_path_complete.py       ← NEW
├── test_source_path_complete.py     ← NEW
├── test_bidirectional_traffic.py    ← NEW
└── test_stress_scenarios.py         ← NEW
```

**Verification Steps:**
1. Create new integration test files
2. Implement test scenarios
3. Run: `pytest projects/components/rapids/dv/tests/integration_tests/ -v`
4. Measure coverage: `pytest projects/components/rapids/dv/tests/integration_tests/ --cov=projects/components/rapids/rtl/`
5. Target: >80% integration coverage

**Related Files:**
- Create: Test files in `projects/components/rapids/dv/tests/integration_tests/`
- Use: TB classes from `bin/CocoTBFramework/tbclasses/rapids/` (from TASK-003)
- Update: `docs/RAPIDS_Validation_Status_Report.md`

**Dependencies:**
- TASK-003 (TB classes must exist first)

**Completion Criteria:**
- [ ] All integration test files created
- [ ] Tests passing
- [ ] >80% integration coverage achieved
- [ ] Validation report updated

---

### TASK-005: Create System-Level Tests
**Status:** 🟡 Planned
**Priority:** P2 (Medium)
**Effort:** 8-12 hours
**Assigned:** Unassigned

**Description:**
Create comprehensive system-level tests that exercise full RAPIDS operation with realistic traffic patterns.

**Current Coverage:** Minimal system-level testing

**Required Test Scenarios:**

1. **Full DMA Transfer Scenarios** (3-4 hours)
   - [ ] Single large DMA transfer
   - [ ] Multiple concurrent transfers
   - [ ] Chained descriptor sequence
   - [ ] Mixed read/write operations
   - [ ] Completion tracking and verification

2. **Realistic Network Traffic Patterns** (3-4 hours)
   - [ ] Bursty traffic simulation
   - [ ] Variable packet sizes
   - [ ] Network congestion scenarios
   - [ ] Packet loss handling
   - [ ] Throughput characterization

3. **Error Handling and Recovery** (2-3 hours)
   - [ ] AXI error responses (SLVERR, DECERR)
   - [ ] Timeout scenarios
   - [ ] Buffer overflow/underflow
   - [ ] Descriptor errors
   - [ ] Recovery mechanisms

4. **Performance Benchmarking** (2-3 hours)
   - [ ] Maximum throughput measurement
   - [ ] Latency characterization
   - [ ] Resource utilization
   - [ ] Bottleneck identification
   - [ ] Optimization opportunities

**Test Files to Create:**
```
projects/components/rapids/dv/tests/system_tests/
├── test_full_dma.py                 ← NEW
├── test_network_traffic.py          ← NEW
├── test_error_recovery.py           ← NEW
├── test_performance_benchmark.py    ← NEW
└── conftest.py                      ← NEW: Shared fixtures
```

**Performance Targets:**
- Throughput: Match AXI/Network interface bandwidth
- Latency: <100 cycles for small packets
- Concurrent Descriptors: 16+ simultaneously active

**Verification Steps:**
1. Create system test files
2. Implement realistic traffic generators
3. Run: `pytest projects/components/rapids/dv/tests/system_tests/ -v`
4. Collect performance metrics
5. Compare against targets

**Related Files:**
- Create: Test files in `projects/components/rapids/dv/tests/system_tests/`
- Use: TB classes from `bin/CocoTBFramework/tbclasses/rapids/` (from TASK-003)
- Update: `docs/RAPIDS_Validation_Status_Report.md`

**Dependencies:**
- TASK-003 (TB classes)
- TASK-004 (Integration tests)

**Completion Criteria:**
- [ ] All system test files created
- [ ] Tests passing
- [ ] Performance metrics documented
- [ ] Validation report updated

---

## Documentation (P2-P3)

### TASK-006: Create README.md for RAPIDS Subsystem
**Status:** 🟡 Planned
**Priority:** P2 (Medium)
**Effort:** 2-3 hours
**Assigned:** Unassigned

**Description:**
Create quick-start README.md for RAPIDS subsystem to complement PRD.md and CLAUDE.md.

**Content Structure:**
```markdown
# RAPIDS - Rapid AXI Programmable In-band Descriptor System

## Quick Start
- What is RAPIDS?
- Key Features
- Architecture Diagram

## Getting Started
- Integration Example
- Configuration Steps
- Basic Usage Pattern

## Testing
- Running Tests
- Test Organization
- Coverage Status

## Documentation
- PRD.md - Requirements
- CLAUDE.md - AI assistance guide
- TASKS.md - Work items
- rapids_spec/ - Complete specification

## Known Issues
- Link to known_issues/
- Current workarounds

## Resources
- Internal docs
- External references
```

**Verification Steps:**
1. Create `projects/components/rapids/README.md`
2. Add integration example code
3. Add architecture diagram (ASCII art or reference to spec)
4. Link to all related documentation
5. Review for completeness

**Related Files:**
- Create: `projects/components/rapids/README.md`
- Reference: `projects/components/rapids/PRD.md`, `projects/components/rapids/CLAUDE.md`

**Dependencies:** None

**Completion Criteria:**
- [ ] README.md created
- [ ] All sections complete
- [ ] Examples tested
- [ ] Links verified

---

### TASK-007: Update RAPIDS Validation Status Report
**Status:** 🟡 Planned
**Priority:** P2 (Medium)
**Effort:** 2-4 hours
**Assigned:** Unassigned

**Description:**
Update validation status report with current test coverage, known issues, and test results.

**Content to Update:**
1. **Test Coverage Summary**
   - FUB test results
   - Integration test results
   - System test results
   - Coverage percentages

2. **Known Issues Status**
   - Credit counter bug (TASK-001)
   - AXI timeout detection (TASK-002)
   - SRAM control limitations

3. **Test Matrix**
   - Scenarios tested
   - Pass/fail status
   - Regression results

4. **Recommendations**
   - Priority fixes
   - Test expansion areas
   - Performance improvements

**Verification Steps:**
1. Run full test suite: `pytest projects/components/rapids/dv/tests/ -v`
2. Collect coverage data: `pytest projects/components/rapids/dv/tests/ --cov=projects/components/rapids/rtl/ --cov-report=html`
3. Update `docs/RAPIDS_Validation_Status_Report.md`
4. Generate test matrix
5. Review completeness

**Related Files:**
- Update: `docs/RAPIDS_Validation_Status_Report.md`
- Reference: Test results from `projects/components/rapids/dv/tests/`

**Dependencies:**
- TASK-001 (for updated credit test results)
- TASK-004 (for integration test results)
- TASK-005 (for system test results)

**Completion Criteria:**
- [ ] Validation report updated
- [ ] Test matrix complete
- [ ] Coverage data current
- [ ] Recommendations documented

---

## Enhancement and Optimization (P3)

### TASK-008: Enhance SRAM Control for Concurrent Reads
**Status:** ⏸️ Deferred
**Priority:** P3 (Low)
**Effort:** 16-24 hours
**Assigned:** Unassigned

**Description:**
Enhance sink SRAM control to support multiple concurrent read operations for improved performance.

**Current Limitation:**
- Single read operation at a time
- Potential throughput bottleneck
- SRAM bandwidth underutilization

**Enhancement Goals:**
1. Support multiple concurrent reads
2. Implement read operation pipelining
3. Improve memory bandwidth utilization
4. Reduce read latency through parallelism

**Design Approach:**
```systemverilog
// Enhanced SRAM control with multi-read support
parameter int NUM_READ_PORTS = 2;

logic [NUM_READ_PORTS-1:0][ADDR_WIDTH-1:0] r_read_addr;
logic [NUM_READ_PORTS-1:0][DATA_WIDTH-1:0] r_read_data;
logic [NUM_READ_PORTS-1:0] r_read_valid;

// Read port arbitration
// Read address generation
// Read data multiplexing
```

**Impact:**
- Improved throughput in read-heavy workloads
- Better SRAM utilization
- Reduced read latency

**Verification Steps:**
1. Design multi-read architecture
2. Implement in sink_sram_control.sv
3. Create performance tests
4. Compare throughput before/after
5. Verify no regressions

**Related Files:**
- Modify: `projects/components/rapids/rtl/rapids_fub/sink_sram_control.sv`
- Update: `projects/components/rapids/known_issues/sink_sram_control.md`
- Create: `projects/components/rapids/dv/tests/performance_tests/test_multi_read.py`

**Dependencies:**
- TASK-005 (baseline performance data)

**Completion Criteria:**
- [ ] Multi-read support implemented
- [ ] Performance improvement measured
- [ ] Tests passing
- [ ] Documentation updated

**Notes:**
- This is an architectural enhancement, not a bug fix
- Current implementation is functionally correct
- Enhancement deferred until critical tasks complete

---

### TASK-009: Add Performance Monitoring Infrastructure
**Status:** ⏸️ Deferred
**Priority:** P3 (Low)
**Effort:** 8-12 hours
**Assigned:** Unassigned

**Description:**
Add comprehensive performance monitoring infrastructure to RAPIDS for throughput, latency, and utilization tracking.

**Features to Add:**
1. **Throughput Counters**
   - Bytes transferred per channel
   - Transactions per second
   - Bandwidth utilization

2. **Latency Tracking**
   - Descriptor-to-completion latency
   - Memory access latency
   - Network transfer latency

3. **Resource Utilization**
   - SRAM occupancy
   - Transaction table usage
   - Buffer high-water marks

4. **MonBus Performance Packets**
   - Performance metric reporting
   - Threshold detection
   - Statistical summaries

**Implementation Approach:**
```systemverilog
// Performance monitoring module
module miop_perf_monitor #(
    parameter int COUNTER_WIDTH = 32
) (
    input  logic aclk,
    input  logic aresetn,

    // Event inputs
    input  logic desc_start,
    input  logic desc_complete,
    input  logic [31:0] bytes_transferred,

    // Performance outputs
    output logic [COUNTER_WIDTH-1:0] o_total_bytes,
    output logic [COUNTER_WIDTH-1:0] o_total_transactions,
    output logic [15:0] o_avg_latency,

    // MonBus output
    output logic [63:0] monbus_perf_pkt,
    output logic monbus_perf_valid
);
```

**Related Files:**
- Create: `projects/components/rapids/rtl/rapids_fub/miop_perf_monitor.sv`
- Update: `projects/components/rapids/rtl/rapids_macro/miop_top.sv` (integrate monitor)
- Create: `projects/components/rapids/dv/tests/performance_tests/test_perf_monitor.py`

**Dependencies:**
- TASK-005 (system tests for validation)

**Completion Criteria:**
- [ ] Performance monitor module created
- [ ] Integrated into RAPIDS top
- [ ] Tests passing
- [ ] Documentation updated

**Notes:**
- Nice to have, not critical
- Deferred until core functionality complete

---

### TASK-010: Rename RDA to CDA (Compute Direct Access)
**Status:** 🟡 Planned
**Priority:** P2 (Medium)
**Effort:** 4-6 hours
**Assigned:** Unassigned

**Description:**
Rename all references to RDA (Read Direct Access) to CDA (Compute Direct Access) throughout RAPIDS codebase and documentation. This renaming clarifies that the descriptor mechanism supports in-band compute operations, not just read operations.

**Scope:**
1. **RTL Signal Names**
   - `rda_valid` → `cda_valid`
   - `rda_ready` → `cda_ready`
   - `rda_packet` → `cda_packet`
   - `rda_*` → `cda_*` (all related signals)

2. **RTL Comments and Documentation**
   - Update all comments referencing RDA
   - Update port descriptions
   - Update signal explanations

3. **Test Files**
   - Update test variable names
   - Update test function names
   - Update test comments

4. **Specification Documents**
   - `projects/components/rapids/docs/rapids_spec/` - All references
   - `projects/components/rapids/PRD.md` - All references
   - `projects/components/rapids/CLAUDE.md` - All references
   - `projects/components/rapids/README.md` - All references (once created)

**Files Requiring Updates:**
```
RTL Files:
- projects/components/rapids/rtl/rapids_fub/descriptor_engine.sv
- projects/components/rapids/rtl/rapids_fub/program_engine.sv
- projects/components/rapids/rtl/rapids_fub/scheduler.sv
- projects/components/rapids/rtl/rapids_macro/scheduler_group.sv
- projects/components/rapids/rtl/rapids_macro/scheduler_group_array.sv
- projects/components/rapids/rtl/includes/rapids_pkg.sv

Test Files:
- projects/components/rapids/dv/tests/fub_tests/descriptor_engine/test_desc_engine.py
- projects/components/rapids/dv/tests/fub_tests/program_engine/test_prog_engine.py
- projects/components/rapids/dv/tests/fub_tests/scheduler/test_scheduler.py
- projects/components/rapids/dv/tbclasses/* (once created per TASK-003)

Documentation:
- projects/components/rapids/docs/rapids_spec/ch02_blocks/*.md
- projects/components/rapids/docs/rapids_spec/ch03_interfaces/*.md
- projects/components/rapids/PRD.md
- projects/components/rapids/CLAUDE.md
```

**Implementation Steps:**

1. **RTL Updates** (1-2 hours)
   - [ ] Find all `rda_` signal instances
   - [ ] Rename to `cda_` systematically
   - [ ] Update port descriptions
   - [ ] Update internal comments

2. **Test Updates** (1-2 hours)
   - [ ] Update test variable names
   - [ ] Update test assertions
   - [ ] Verify tests still pass

3. **Documentation Updates** (2 hours)
   - [ ] Update specification markdown files
   - [ ] Update PRD.md
   - [ ] Update CLAUDE.md
   - [ ] Update known_issues/ if referenced

4. **Verification** (1 hour)
   - [ ] Search for remaining RDA references: `grep -r "rda" projects/components/rapids/`
   - [ ] Verify no broken references
   - [ ] Run full test suite
   - [ ] Verify documentation consistency

**Search Commands:**
```bash
# Find all RDA references in RTL
grep -r "rda" projects/components/rapids/rtl/ --include="*.sv" --include="*.svh"

# Find all RDA references in tests
grep -r "rda" projects/components/rapids/dv/ --include="*.py"

# Find all RDA references in documentation
grep -r "rda" projects/components/rapids/docs/ --include="*.md"
grep -r "RDA" projects/components/rapids/ --include="*.md"
```

**Verification Steps:**
1. Search for all RDA references before starting
2. Systematically rename in each file category
3. Run RTL lint: `verilator --lint-only projects/components/rapids/rtl/**/*.sv`
4. Run full test suite: `pytest projects/components/rapids/dv/tests/ -v`
5. Search for remaining RDA references after completion
6. Verify documentation builds/renders correctly

**Related Files:**
- Update: All RTL files with RDA signals
- Update: All test files with RDA references
- Update: All documentation with RDA mentions

**Dependencies:**
- None (can be done independently)

**Completion Criteria:**
- [ ] All RTL signals renamed (rda → cda)
- [ ] All test references updated
- [ ] All documentation updated
- [ ] No remaining RDA references found
- [ ] All tests passing
- [ ] RTL linting clean

**Notes:**
- **Rationale:** "Compute Direct Access" better reflects the in-band descriptor capability for compute operations
- **Breaking Change:** This is a naming convention update - external interfaces remain compatible
- **Systematic Approach:** Use search-and-replace with verification at each step
- **Case Sensitivity:** Handle both lowercase `rda` and uppercase `RDA`

---

## Task Dependencies Graph

```
TASK-001 (Fix Credit Bug) ──────────────┐
    │                                    │
    ├─────────────> TASK-003 (TB Classes)
    │                      │
    │                      ├─────> TASK-004 (Integration Tests)
    │                      │              │
    │                      │              ├─────> TASK-005 (System Tests)
    │                      │              │              │
    │                      │              │              ├─────> TASK-007 (Update Report)
    │                      │              │              │
    │                      │              │              └─────> TASK-009 (Perf Monitor)
    │                      │              │
    │                      │              └─────> TASK-008 (SRAM Enhancement)
    │                      │
    │                      └─────> TASK-006 (README)
    │
TASK-002 (AXI Timeout) ─────────────────┘
```

---

## Task Prioritization

### Sprint 1: Critical Bugs (Weeks 1-2)
1. **TASK-001:** Fix scheduler credit counter bug (P1)
2. **TASK-002:** Implement AXI timeout detection (P2)

### Sprint 2: Test Infrastructure (Weeks 3-4)
3. **TASK-003:** Create reusable testbench classes (P1)
4. **TASK-004:** Expand integration test coverage (P2)

### Sprint 3: System Validation (Weeks 5-6)
5. **TASK-005:** Create system-level tests (P2)
6. **TASK-007:** Update validation status report (P2)

### Sprint 4: Documentation (Week 7)
7. **TASK-006:** Create README.md (P2)

### Future Enhancements (Backlog)
8. **TASK-008:** SRAM multi-read enhancement (P3)
9. **TASK-009:** Performance monitoring infrastructure (P3)

---

## Progress Tracking

### Overall Status
- **Total Tasks:** 9
- **Complete:** 0 (0%)
- **In Progress:** 0 (0%)
- **Planned:** 7 (78%)
- **Deferred:** 2 (22%)

### Coverage Goals
- **Current FUB Coverage:** ~85%
- **Current Integration Coverage:** ~60%
- **Current System Coverage:** ~30%
- **Target Coverage:** >90% across all levels

### Test Count
- **Current Tests:** 32
- **Target Tests:** 50+ (after TASK-004 and TASK-005)

---

## Notes

1. **Task Order:** Follow dependency graph for optimal workflow
2. **Test-Driven:** Always create/update tests when fixing bugs
3. **Documentation:** Update docs immediately after task completion
4. **Verification:** Run full regression after each task: `pytest projects/components/rapids/dv/tests/ -v`
5. **Coverage:** Track coverage metrics: `pytest projects/components/rapids/dv/tests/ --cov=projects/components/rapids/rtl/`

---

## Quick Commands

```bash
# Run specific task validation
pytest projects/components/rapids/dv/tests/fub_tests/scheduler/ -v -k credit  # TASK-001
pytest projects/components/rapids/dv/tests/integration_tests/ -v              # TASK-004
pytest projects/components/rapids/dv/tests/system_tests/ -v                   # TASK-005

# Full regression
pytest projects/components/rapids/dv/tests/ -v

# Coverage report
pytest projects/components/rapids/dv/tests/ --cov=projects/components/rapids/rtl/ --cov-report=html

# Lint RTL
verilator --lint-only projects/components/rapids/rtl/rapids_fub/scheduler.sv

# View documentation
cat projects/components/rapids/PRD.md
cat projects/components/rapids/CLAUDE.md
cat projects/components/rapids/docs/rapids_spec/miop_index.md
```

---

## New Tasks (2025-10-19)

### TASK-011: Implement Autonomous Descriptor Chaining
**Status:** 🟡 Planned
**Priority:** P1 (High)
**Effort:** 8-12 hours
**Assigned:** Unassigned

**Description:**
Implement autonomous descriptor chaining in RAPIDS descriptor_engine to automatically fetch chained descriptors without scheduler intervention. This matches the architecture implemented in STREAM.

**Background:**
- STREAM descriptor_engine now implements autonomous chaining via descriptor read address FIFO
- When descriptor fetch completes, check `next_descriptor_ptr` and `last` flag
- If chaining conditions met, automatically queue next descriptor fetch
- APB interface blocked during active descriptor chains

**Required Architecture:**

```systemverilog
// In descriptor_engine.sv:
// 1. Add descriptor read address FIFO (parameterizable depth, e.g., 2-deep)
parameter int DESC_ADDR_FIFO_DEPTH = 2,

// 2. Add channel_idle input
input  logic                        channel_idle,  // From scheduler_group (scheduler_idle && desc_idle)

// 3. Implement autonomous chaining logic
// - APB skid → Descriptor Addr FIFO (initial kick-off)
// - Completed descriptor → Check next_descriptor_ptr and last flag
// - If (next_descriptor_ptr != 0 && !last && !error) → Push to Descriptor Addr FIFO
// - Address validation against cfg_addr0/1_base/limit before pushing
// - APB blocked when !channel_idle (descriptor chain active)

// 4. Error handling
// - On AXI response error: stop chaining, set error flag, block descriptor_valid
```

**Chaining Logic:**

```systemverilog
// Chaining decision
wire w_should_chain = (w_next_descriptor_ptr != '0) && !w_desc_last &&
                      w_next_addr_valid && !r_descriptor_error &&
                      w_desc_fifo_wr_ready;

// Address validation
wire w_next_addr_valid = (w_next_descriptor_ptr >= cfg_addr0_base && w_next_descriptor_ptr <= cfg_addr0_limit) ||
                          (w_next_descriptor_ptr >= cfg_addr1_base && w_next_descriptor_ptr <= cfg_addr1_limit);

// APB blocking
assign apb_ready = w_apb_skid_ready_in && !r_channel_reset_active &&
                    w_desc_addr_fifo_empty && channel_idle;
```

**Integration Requirements:**

At scheduler_group level:
```systemverilog
// Compute channel_idle from both engines
assign channel_idle = scheduler_idle && descriptor_engine_idle;
```

**Verification Steps:**
1. Add `DESC_ADDR_FIFO_DEPTH` parameter to descriptor_engine.sv
2. Add `channel_idle` input port
3. Implement descriptor read address FIFO
4. Add autonomous chaining logic (check next_descriptor_ptr and last)
5. Add address validation before pushing to FIFO
6. Implement error handling (stop chaining, flag error, block descriptor_valid)
7. Block APB when !channel_idle
8. Update scheduler_group to drive channel_idle = scheduler_idle && descriptor_engine_idle
9. Update testbenches to drive channel_idle signal
10. Create test for autonomous chaining with 2-3 chained descriptors

**Related Files:**
- Modify: `projects/components/rapids/rtl/rapids_fub/descriptor_engine.sv`
- Modify: `projects/components/rapids/rtl/rapids_macro/scheduler_group.sv`
- Update: `projects/components/rapids/dv/tbclasses/descriptor_engine_tb.py`
- Create: `projects/components/rapids/dv/tests/fub_tests/descriptor_engine/test_autonomous_chaining.py`
- Update: `projects/components/rapids/PRD.md` (document chaining architecture)

**Dependencies:**
- None

**Completion Criteria:**
- [ ] Descriptor read address FIFO implemented
- [ ] Autonomous chaining logic implemented (check next_descriptor_ptr and last)
- [ ] Address validation implemented
- [ ] Error handling implemented
- [ ] APB blocking when !channel_idle working
- [ ] channel_idle signal integrated at scheduler_group level
- [ ] All tests passing
- [ ] Documentation updated

**Notes:**
- STREAM implementation (projects/components/stream/rtl/stream_fub/descriptor_engine.sv) serves as reference
- This enables chained descriptor sequences without software intervention
- Improves throughput by eliminating per-descriptor software latency

---

### TASK-012: Implement Channel Idle Signal Composition
**Status:** 🟡 Planned
**Priority:** P1 (High)
**Effort:** 2-3 hours
**Assigned:** Unassigned

**Description:**
Implement channel_idle signal at scheduler_group level as logical AND of scheduler_idle and all engine idle signals. This ensures the channel is truly idle only when all components are quiescent.

**Architecture:**

```systemverilog
// At scheduler_group level
assign channel_idle = scheduler_idle &&
                      descriptor_engine_idle &&
                      program_engine_idle &&  // If applicable
                      ctrlrd_engine_idle &&   // If applicable
                      ctrlwr_engine_idle;     // If applicable
```

**Why Both Signals Matter:**

| Signal | Indicates | Used For |
|--------|-----------|----------|
| `scheduler_idle` | No active data transfers, all descriptors processed | Prevents new operations during active transfer |
| `descriptor_engine_idle` | No pending descriptor fetches (FIFO empty) | Prevents new operations during descriptor fetch |
| `program_engine_idle` | No pending program operations | Prevents new operations during programming |
| `channel_idle` (AND of all) | Channel fully quiescent | **Gates external interfaces (APB, RDA, CDA)** |

**Usage in Descriptor Engine:**

```systemverilog
// Descriptor engine blocks APB when channel not idle
assign apb_ready = apb_skid_ready_in &&
                   !r_channel_reset_active &&
                   w_desc_addr_fifo_empty &&
                   channel_idle;  // ← Blocks APB during active chains
```

**Example Scenario:**

```
1. Software writes APB/RDA/CDA → descriptor_addr = 0x1000
   - channel_idle = 1 (all engines idle)
   - Request accepted

2. Descriptor engine fetches descriptor @ 0x1000
   - descriptor_engine_idle = 0 (fetch in progress)
   - channel_idle = 0
   - APB/RDA/CDA BLOCKED

3. Descriptor pushed to scheduler
   - descriptor_engine_idle = 1 (fetch complete)
   - scheduler_idle = 0 (transfer starting)
   - channel_idle = 0
   - APB/RDA/CDA BLOCKED

4. Scheduler completes data transfer
   - Descriptor has next_descriptor_ptr = 0x1100 (chained!)
   - Descriptor engine autonomously fetches @ 0x1100
   - descriptor_engine_idle = 0 (autonomous fetch)
   - channel_idle = 0
   - APB/RDA/CDA BLOCKED

5. Final descriptor completes (last = 1 OR next_ptr = 0)
   - scheduler_idle = 1 (transfer done)
   - descriptor_engine_idle = 1 (no more fetches)
   - all other engines idle = 1
   - channel_idle = 1
   - APB/RDA/CDA UNBLOCKED (ready for next transfer!)
```

**Implementation Steps:**
1. Add scheduler_idle output to scheduler.sv (if not already present)
2. Add descriptor_engine_idle output to descriptor_engine.sv
3. Add program_engine_idle output to program_engine.sv (if applicable)
4. Update scheduler_group.sv to AND all idle signals
5. Connect channel_idle to all relevant engines (descriptor_engine, program_engine)
6. Update testbenches to drive channel_idle
7. Create integration test verifying APB/RDA/CDA blocking during active chains

**Verification Steps:**
1. Verify each engine correctly asserts its idle signal
2. Verify scheduler_group correctly ANDs all idle signals
3. Verify APB interface blocks when !channel_idle
4. Verify RDA interface blocks when !channel_idle (if present)
5. Verify CDA interface blocks when !channel_idle (if present)
6. Test multi-descriptor chain scenario (software blocked until chain completes)
7. Test error scenarios (channel_idle behavior on errors)

**Related Files:**
- Modify: `projects/components/rapids/rtl/rapids_fub/scheduler.sv`
- Modify: `projects/components/rapids/rtl/rapids_fub/descriptor_engine.sv`
- Modify: `projects/components/rapids/rtl/rapids_fub/program_engine.sv`
- Modify: `projects/components/rapids/rtl/rapids_macro/scheduler_group.sv`
- Update: `projects/components/rapids/PRD.md` (document channel_idle architecture)
- Create: `projects/components/rapids/dv/tests/integration_tests/test_channel_idle.py`

**Dependencies:**
- TASK-011 (autonomous chaining uses channel_idle)

**Completion Criteria:**
- [ ] All engines output their idle signals
- [ ] scheduler_group ANDs all idle signals to create channel_idle
- [ ] channel_idle connected to all relevant engines
- [ ] APB/RDA/CDA interfaces block when !channel_idle
- [ ] Integration tests passing
- [ ] Documentation updated

**Notes:**
- This architecture ensures software cannot interrupt active descriptor chains
- STREAM implementation (projects/components/stream/PRD.md Section 5.2) serves as reference
- Critical for reliable autonomous chaining operation

---

**Version History:**
- v1.0 (2025-10-11): Initial creation with 9 tasks
- v1.1 (2025-10-19): Added TASK-011 (autonomous chaining) and TASK-012 (channel_idle)

**Maintained By:** RTL Design Sherpa Project
**Last Review:** 2025-10-19
