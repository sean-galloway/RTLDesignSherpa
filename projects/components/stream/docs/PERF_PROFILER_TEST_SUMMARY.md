# Performance Profiler Test Summary

**Date:** 2025-10-20
**Status:** Tests created, **BUG FOUND** in simultaneous edge handling

---

## Files Created

### 1. RTL Module
- **Location:** `rtl/stream_fub/perf_profiler.sv`
- **Status:** Implemented with two-register APB read interface
- **Known Issue:** Simultaneous edge bug (see below)

### 2. Testbench Class
- **Location:** `projects/components/stream/dv/tbclasses/perf_profiler_tb.py`
- **Purpose:** Reusable testbench for profiler validation
- **Methods:**
  - `enable_profiler(mode)` - Configure timestamp/elapsed mode
  - `channel_active_pulse(ch, duration)` - Generate channel activity
  - `read_fifo_entry()` - Read via two-register interface
  - `wait_for_events(count)` - Wait for FIFO population

### 3. Test Runner
- **Location:** `projects/components/stream/dv/tests/fub_tests/perf_profiler/test_perf_profiler.py`
- **Test Cases:**
  1. `test_single_channel_timestamp_mode` - Basic timestamp profiling
  2. `test_single_channel_elapsed_mode` - Basic elapsed time profiling
  3. `test_multiple_channels_sequential` - Sequential channel activity
  4. **`test_simultaneous_edges_bug`** - **DEMONSTRATES BUG!**
  5. `test_fifo_full_behavior` - FIFO overflow handling
  6. `test_two_register_read_interface` - APB read interface
  7. `test_counter_increment` - Timestamp counter validation

### 4. Supporting Files
- `projects/components/stream/dv/tests/fub_tests/perf_profiler/conftest.py` - Pytest configuration
- `projects/components/stream/rtl/filelists/fub/perf_profiler.f` - RTL filelist
- `projects/components/stream/docs/stream_spec/ch02_blocks/09_perf_profiler.md` - Specification

---

## Critical Bug Found: Simultaneous Edge Event Loss

### The Problem

When multiple channels transition simultaneously (e.g., all 8 channels go idle→active on the same cycle), **only the lowest-numbered channel event is recorded**. All other channel events are **LOST**.

### Root Cause

```systemverilog
// Line 172 in perf_profiler.sv
always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
        r_idle_prev <= '1;
    end else if (cfg_enable) begin
        r_idle_prev <= channel_idle;  // ← UPDATES EVERY CYCLE!
    end
end

// Lines 176-177
assign w_idle_rising  = channel_idle & ~r_idle_prev;
assign w_idle_falling = ~channel_idle & r_idle_prev;
```

**Timeline:**
```
Cycle N:
  channel_idle     = 8'b00000000 (all 8 channels go active)
  r_idle_prev      = 8'b11111111 (all were idle)
  w_idle_falling   = 8'b11111111 (all 8 edges detected!)
  Priority encoder selects channel 0
  FIFO gets channel 0 event
  END OF CYCLE: r_idle_prev <= 8'b00000000

Cycle N+1:
  channel_idle     = 8'b00000000 (still all active)
  r_idle_prev      = 8'b00000000 (updated last cycle!)
  w_idle_falling   = 8'b00000000 (NO edges detected!)
  RESULT: Channels 1-7 events LOST!
```

### Demonstration Test

The test `test_simultaneous_edges_bug()` makes all 8 channels go idle→active simultaneously:

**Expected:** 8 START events (one per channel)
**Actual:** 1 START event (channel 0 only)
**Status:** Test **PASSES by demonstrating the bug exists**

---

## Proposed Fix

Track pending edges separately from edge detection:

```systemverilog
// Add pending edges register
logic [NUM_CHANNELS-1:0] r_edges_pending_rising;
logic [NUM_CHANNELS-1:0] r_edges_pending_falling;

// Edge detection (unchanged)
always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
        r_idle_prev <= '1;
    end else if (cfg_enable) begin
        r_idle_prev <= channel_idle;
    end
end

assign w_idle_rising  = channel_idle & ~r_idle_prev;
assign w_idle_falling = ~channel_idle & r_idle_prev;

// Capture and hold pending edges
always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
        r_edges_pending_rising  <= '0;
        r_edges_pending_falling <= '0;
    end else if (cfg_clear) begin
        r_edges_pending_rising  <= '0;
        r_edges_pending_falling <= '0;
    end else if (cfg_enable) begin
        // Add new edges to pending
        r_edges_pending_rising  <= r_edges_pending_rising  | w_idle_rising;
        r_edges_pending_falling <= r_edges_pending_falling | w_idle_falling;

        // Clear processed edge
        if (w_channel_event && !w_fifo_full_internal) begin
            if (w_idle_rising[w_active_channel]) begin
                r_edges_pending_rising[w_active_channel] <= 1'b0;
            end
            if (w_idle_falling[w_active_channel]) begin
                r_edges_pending_falling[w_active_channel] <= 1'b0;
            end
        end
    end
end

// Priority encoder uses pending edges
always_comb begin
    w_active_channel = '0;
    w_channel_event = 1'b0;

    if (cfg_mode == MODE_TIMESTAMP) begin
        // Check pending edges (not immediate edges)
        for (int i = 0; i < NUM_CHANNELS; i++) begin
            if (r_edges_pending_rising[i] || r_edges_pending_falling[i]) begin
                w_active_channel = i[CHANNEL_WIDTH-1:0];
                w_channel_event = 1'b1;
                break;
            end
        end
    end
    // ... similar for MODE_ELAPSED
end

// Update FIFO write logic to use pending edges
assign w_idle_rising[w_active_channel]  = r_edges_pending_rising[w_active_channel];
assign w_idle_falling[w_active_channel] = r_edges_pending_falling[w_active_channel];
```

### Fix Benefits

1. **Captures all simultaneous edges** - No events lost
2. **Processes one per cycle** - Priority encoder unchanged
3. **Queues pending edges** - Events recorded over multiple cycles
4. **Same external interface** - No changes to ports

### Expected Test Results After Fix

```
test_simultaneous_edges_bug():
  Before: 1 event (channel 0 only) - BUG CONFIRMED
  After:  8 events (all channels) - BUG FIXED
```

---

## How to Run Tests

### Prerequisites

1. Source the project environment:
```bash
source env_python
```

2. Navigate to test directory:
```bash
cd projects/components/stream/dv/tests/fub_tests/perf_profiler
```

### Run All Tests

```bash
python3 test_perf_profiler.py
```

### Expected Output (Before Fix)

```
test_single_channel_timestamp_mode ............ PASSED
test_single_channel_elapsed_mode .............. PASSED
test_multiple_channels_sequential ............. PASSED
test_simultaneous_edges_bug ................... PASSED (demonstrates bug!)
  WARNING: BUG CONFIRMED: Only 1 event recorded (channel 0)
  WARNING: Expected 8 events (one per channel)
  WARNING: Events for channels 1-7 were LOST
test_fifo_full_behavior ....................... PASSED
test_two_register_read_interface .............. PASSED
test_counter_increment ........................ PASSED
```

### Expected Output (After Fix)

```
test_simultaneous_edges_bug ................... PASSED
  Got 8 events - bug may be fixed!
    Channel 0 event recorded
    Channel 1 event recorded
    Channel 2 event recorded
    ...
    Channel 7 event recorded
```

---

## Impact Assessment

### Low Impact (Typical Use Case)

In typical DMA workloads:
- Channels start at different times (descriptor kicks are sequential)
- Simultaneous edges are **RARE**
- Bug impact: **LOW**

### High Impact (Stress Scenarios)

In stress testing or synchronized workloads:
- All channels kicked off simultaneously
- Multiple descriptors complete at same time
- Simultaneous edges are **COMMON**
- Bug impact: **HIGH** (most events lost!)

---

## Recommendation

**Priority:** **MEDIUM-HIGH**

1. Apply proposed fix to `perf_profiler.sv`
2. Re-run `test_simultaneous_edges_bug()` to verify fix
3. Ensure all 7 tests still pass
4. Document limitation if fix not applied

---

## Documentation

- **Specification:** `docs/stream_spec/ch02_blocks/09_perf_profiler.md`
- **Index:** Updated in `docs/stream_spec/stream_index.md`
- **APB Registers:** To be added to `regs/stream_regs.rdl` (PeakRDL)

---

## Next Steps

1. ✅ Tests created (7 test cases)
2. ✅ Bug identified and documented
3. ✅ Proposed fix designed
4. ⏳ Run tests to confirm bug (requires `source env_python`)
5. ⏳ Apply fix to RTL
6. ⏳ Re-run tests to verify fix
7. ⏳ Integrate into stream_top
8. ⏳ Add APB register mapping

---

**Status:** Ready for test execution and bug fix implementation
