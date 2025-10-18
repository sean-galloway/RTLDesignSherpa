# CDC Handshake Optimization - Status Update

**Date:** 2025-10-17
**Component:** `rtl/amba/shared/cdc_handshake_fast.sv`
**Status:** ⚠️ **IN PROGRESS** - Multiple implementation challenges discovered

---

## Summary

Attempted to optimize the CDC handshake module by removing the conservative S_WAIT_ACK_CLR state. **Multiple implementation attempts have failed** due to subtle timing and data integrity issues. This document summarizes what was learned and recommends next steps.

---

## Original Optimization Goal

**Concept:** Remove S_WAIT_ACK_CLR state which waits 10-15 cycles for ACK to clear before accepting next transaction.

**Expected Benefit:** ~30-50% faster throughput for back-to-back transactions

**Safety Rationale:** Once ACK arrives, destination has captured data - no need to wait for ACK to clear

---

## Attempt #1: Direct Back-to-Back (FAILED)

### Implementation
```systemverilog
S_WAIT_ACK: begin
    if (w_ack_sync) begin
        r_req_src <= 1'b0;
        if (src_valid) begin
            r_async_data <= src_data;
            r_req_src    <= 1'b1;  // ❌ Same cycle!
        end
    end
end
```

### Failure Mode
**Bug:** REQ toggled 1→0→1 in same cycle - last assignment wins
**Result:** REQ never went low, destination FSM stuck waiting for REQ to clear
**Test Result:** Timeout after ~10 transactions

### Root Cause
Violated CDC signal visibility requirement - destination synchronizer never observed REQ transition low.

---

## Attempt #2: S_WAIT_REQ_DROP State (FAILED)

### Implementation
```systemverilog
S_WAIT_ACK: begin
    if (w_ack_sync) begin
        r_req_src <= 1'b0;
        if (src_valid) begin
            r_async_data <= src_data;  // Latch here
            r_src_state  <= S_WAIT_REQ_DROP;
        end
    end
end

S_WAIT_REQ_DROP: begin
    r_req_src <= 1'b1;  // Raise after 1 cycle low
end
```

### Failure Mode
**Bug:** Data integrity errors - destination received transaction N-1's data for transaction N
**Result:** 57-61 transaction errors, data mismatches
**Test Result:** Failed with "field mismatch: paddr: src=0x2008 vs dst=0x2004"

### Root Cause
`r_async_data` updated in S_WAIT_ACK, but destination samples it when REQ rises in S_WAIT_REQ_DROP. Race condition - data not stable when destination samples.

---

## Attempt #3: Two-Stage Data Capture (FAILED)

### Implementation
```systemverilog
S_WAIT_ACK: begin
    if (w_ack_sync) begin
        r_req_src <= 1'b0;
        if (src_valid) begin
            r_next_data <= src_data;  // Capture to holding register
            r_src_state <= S_WAIT_REQ_DROP;
        end
    end
end

S_WAIT_REQ_DROP: begin
    r_async_data <= r_next_data;  // Transfer to async register
    r_req_src    <= 1'b1;         // Raise REQ
end
```

### Failure Mode
**Bug:** Still 55 transaction errors
**Result:** Data still arriving incorrectly at destination
**Test Result:** Failed with similar mismatches

### Root Cause (Hypothesis)
Timing issue with when `src_data` is sampled vs when `src_valid` drops. The testbench may not hold `src_valid` long enough, or there's a synchronization issue we haven't identified yet.

---

## Key Lessons Learned

### 1. CDC Signal Visibility is Non-Trivial
- Signals must have minimum pulse widths observable across clock domains
- Even 1-cycle transitions can be invisible if not carefully timed
- 3-stage synchronizers add ~3+ cycles of delay

### 2. Data Setup/Hold Requirements
- `r_async_data` must be stable BEFORE `r_req_src` rises
- Destination samples data when it sees synchronized REQ high
- Any data update must complete before REQ assertion

### 3. Testbench Interface Contracts
- The `GAXIMaster` driver holds `src_valid` for specific durations
- Our FSM must sample data while `src_valid` is guaranteed high
- Timing assumptions between RTL and TB must be carefully validated

### 4. Optimization != Simply Removing States
- State removal is easy
- Maintaining correctness across all edge cases is hard
- CDC adds another layer of complexity

---

## Why is This So Hard?

The original conservative design has a key property:
```
S_IDLE → latch data, raise REQ → S_WAIT_ACK → drop REQ → S_WAIT_ACK_CLR → S_IDLE
```

**Every transition goes through IDLE** where:
- `src_ready = 1` (testbench knows it can present new data)
- `r_req_src = 0` (clean state for next REQ pulse)
- Data latching happens in S_IDLE with clear `src_valid` contract

**Optimized design tries to skip IDLE:**
```
S_WAIT_ACK → S_WAIT_REQ_DROP → back to S_WAIT_ACK (no IDLE!)
```

This breaks the clean data/valid contract because:
- We're not in IDLE so testbench expectations may differ
- We must capture data "mid-flight" during state transitions
- Timing between data capture and REQ assertion is critical

---

## Recommendations

### Option A: Accept Original Design (RECOMMENDED)
**Action:** Abandon optimization, use original `cdc_handshake.sv`
**Rationale:**
- Original design is proven correct
- 10-15 cycle latency is acceptable for CDC (already dealing with 3+ cycle sync delay)
- Complexity/risk of optimization outweighs modest performance gain

### Option B: Use Application-Level Batching
**Action:** Batch multiple transactions into single CDC transfer
**Example:** Transfer 4x 32-bit words as one 128-bit CDC transaction
**Benefit:** Amortize CDC latency over multiple data items
**Effort:** Medium - requires protocol changes

### Option C: Dual-Clock FIFO
**Action:** Use async FIFO instead of handshake protocol
**Benefit:** Higher throughput, decouples clock domains
**Drawback:** Requires FIFO depth sizing, more gates
**Effort:** High - different architecture

### Option D: Continue Debug (NOT RECOMMENDED)
**Action:** Keep debugging current approach
**Risk:** High - may find more subtle bugs
**Time:** Unknown - could be days of waveform analysis
**Recommendation:** Only if performance is **critical** bottleneck

---

## Current Status of Files

### Created Files
- `rtl/amba/shared/cdc_handshake_fast.sv` - Broken optimization (3 failed attempts)
- `val/amba/test_cdc_handshake_fast.py` - Test that exposes the bugs
- `docs/CDC_HANDSHAKE_OPTIMIZATION_ANALYSIS.md` - Original analysis (overly optimistic)
- `docs/CDC_HANDSHAKE_FAST_BUG_ANALYSIS.md` - Bug #1 analysis
- `docs/CDC_HANDSHAKE_OPTIMIZATION_STATUS.md` - This document

### Recommendation for Files
- **Keep analysis documents** - valuable learning experience
- **Delete or mark broken:** `cdc_handshake_fast.sv` and its test
- **Continue using:** Original `cdc_handshake.sv` (proven correct)

---

## Technical Deep Dive: Why Attempt #3 Failed

The most puzzling failure is Attempt #3. Let's analyze the exact timing:

**Expected Flow:**
```
Cycle N (S_WAIT_ACK):   ACK high, src_valid high, src_data = 0x1234
                        r_next_data <= 0x1234
                        r_src_state <= S_WAIT_REQ_DROP

Cycle N+1 (S_WAIT_REQ_DROP): r_async_data <= r_next_data (0x1234)
                             r_req_src    <= 1'b1

Destination (after sync):    Samples r_async_data when w_req_sync rises
                             Should get 0x1234
```

**But tests show destination getting wrong data!**

**Possible Causes:**
1. **src_data changes** between S_WAIT_ACK and S_WAIT_REQ_DROP
   - Testbench drops `src_valid` and changes `src_data` too quickly
   - We sample stale or transitioning data

2. **Synchronizer delay mismatch**
   - REQ arrives at destination before data settles
   - Would need >3 cycle setup time

3. **Multiple simultaneous assignments**
   - Some other code path updating `r_async_data`?
   - Checked - no other paths found

4. **Test harness issue**
   - Monitor sampling at wrong time?
   - Scoreboard comparison logic bug?

**To Debug Further Would Require:**
- Detailed waveform analysis with GTKWave
- Cycle-by-cycle trace of `src_data`, `r_next_data`, `r_async_data`, `r_req_src`
- Verification that testbench holds `src_valid` long enough
- Check destination sampling timing

This level of debug is time-consuming and error-prone.

---

## Final Recommendation

**Do NOT proceed with this optimization.**

The original `cdc_handshake.sv` module is:
- ✅ Proven correct across all test cases
- ✅ Simple 3-state FSM (easy to understand/maintain)
- ✅ Conservative timing (no edge cases)
- ✅ Already optimized for CDC (3-stage synchronizers, minimal logic)

The 10-15 cycle "penalty" from S_WAIT_ACK_CLR is:
- Small compared to overall CDC latency (30+ cycles total)
- Acceptable for typical back-to-back rates
- Eliminated if transactions aren't back-to-back anyway

**Time saved by avoiding this optimization:** Days of debug
**Performance gained if it worked:** ~30% in best case
**Risk of subtle bugs remaining:** High

**Conclusion:** Not worth it. Use the original proven design.

---

**Author:** Claude Code
**Status:** Recommending abandonment of optimization
**Next Steps:** Await user decision on whether to continue or revert

