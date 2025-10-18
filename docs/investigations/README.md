# Research and Experimental Work

**Purpose:** Document optimization attempts, experimental features, and lessons learned (including failures)

---

## ⚠️ CDC Handshake Optimization (ABANDONED)

**Date:** 2025-10-17
**Status:** ❌ **Failed - Do Not Implement**
**Lesson:** Conservative CDC designs exist for good reasons

### Overview

An attempt to optimize the `cdc_handshake.sv` module by removing the conservative S_WAIT_ACK_CLR state to improve back-to-back transaction throughput. After three implementation attempts and extensive debugging, the optimization was **abandoned** in favor of the proven original design.

### Documentation Index

#### Available Documents

1. **[CDC_HANDSHAKE_FAST_BUG_ANALYSIS.md](CDC_HANDSHAKE_FAST_BUG_ANALYSIS.md)** (11K)
   - Analysis of first implementation bug (Attempt #1)
   - REQ signal visibility issue (1→0→1 in same cycle)
   - Why destination FSM deadlocked
   - Proposed fix (which led to Attempt #2)
   - **Why read:** Example of subtle CDC timing bugs

2. **[CDC_HANDSHAKE_OPTIMIZATION_STATUS.md](CDC_HANDSHAKE_OPTIMIZATION_STATUS.md)** (9K)
   - Complete history of all three attempts
   - Failure modes for each attempt:
     - Attempt #1: REQ visibility (destination deadlock)
     - Attempt #2: Data integrity errors (57-61 mismatches)
     - Attempt #3: Persistent data corruption (55 errors)
   - Root cause analysis
   - Recommendations: **abandon optimization**
   - **Why read:** Comprehensive failure post-mortem

### Summary of Attempts

| Attempt | Change | Result | Symptom |
|---------|--------|--------|---------|
| #1 | Remove S_WAIT_ACK_CLR, direct back-to-back | ❌ Failed | REQ never went low → destination deadlock |
| #2 | Added S_WAIT_REQ_DROP state | ❌ Failed | 57-61 data integrity errors |
| #3 | Two-stage data capture (r_next_data) | ❌ Failed | 55 transaction errors |

### Key Lessons Learned

1. **Signal Visibility is Critical**: Synchronizers must observe complete signal transitions
2. **Data Timing is Complex**: `r_async_data` must be stable BEFORE `r_req_src` rises
3. **Conservative Designs Exist for Reasons**: The original S_WAIT_ACK_CLR state prevents subtle bugs
4. **Testing Reveals Truth**: Theoretical analysis can't replace actual verification
5. **CDC Optimizations are Non-Trivial**: Days of debug time for modest performance gains

### Production Recommendations

✅ **DO:**
- Use `rtl/amba/shared/cdc_handshake.sv` (original, proven design)
- Accept the 10-15 cycle "penalty" of S_WAIT_ACK_CLR state
- Focus on application-level optimizations (batching, reducing CDC crossings)

❌ **DO NOT:**
- Attempt to optimize CDC handshake without:
  - Days of debug time
  - Formal verification tools
  - Compelling performance requirement

### Alternative Approaches

If CDC latency is truly a bottleneck:
1. **Application-level batching** - Transfer multiple items per handshake
2. **Reduce CDC crossings** - Keep more logic in one clock domain
3. **Different architecture** - Consider if handshake is the right primitive

---

## Navigation

**Looking for user guides?** See [../guides/](../guides/)
**Looking for design specs?** See [../design/](../design/)
**Looking for RTL reference?** See [../markdown/](../markdown/)
**Back to main docs:** See [../README.md](../README.md)

---

## Contributing to Investigations

When documenting experimental work:

1. **Be honest about failures** - Failures teach more than successes
2. **Document why you tried** - Context for future readers
3. **Explain root causes** - Not just symptoms
4. **Provide clear recommendations** - Should this be used in production?
5. **Update index** - Add new investigations to this README

**Template for new investigations:**
- Overview and motivation
- What was tried
- Results (success/failure)
- Root cause analysis
- Recommendations
- Lessons learned

---

**Maintained by:** RTL Design Sherpa Contributors
**Last Updated:** 2025-10-17
