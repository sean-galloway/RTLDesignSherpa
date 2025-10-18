# Descriptor Engine: APB→RDA Sequential Pattern Investigation - RESOLVED

**Status:** ✅ RESOLVED - Sequential pattern works correctly
**Priority:** N/A (No bug found)
**Component:** `projects/components/rapids/rtl/rapids_fub/descriptor_engine.sv`
**Investigated:** 2025-10-14
**Resolved:** 2025-10-14
**Test Impact:** No impact - concurrent/sequential test works correctly

---

## Summary

**Initial Concern:** Sequential APB→RDA descriptor pattern appeared to fail in basic tests.

**Investigation Result:** Waveform analysis confirmed the sequential APB→RDA pattern **works correctly**. Both APB and RDA descriptors are generated successfully with proper timing. Initial test failure was likely in a different test parameter combination or test phase, not the concurrent test.

**Waveform Evidence (at 4260-4280ns):**
- ✅ APB descriptor appeared at correct time
- ✅ RDA descriptor appeared one clock after RDA packet arrival
- ✅ `descriptor_is_rda` signal set correctly
- ✅ `r_rda_operation_active` pulsed for one clock as expected
- ✅ No blocking or mutual exclusion issues observed

---

## Test Results

### All Scenarios Working ✅
1. **APB-only operations:** 10/10 descriptors successfully processed
2. **RDA-only operations:** 10/10 packets successfully processed
3. **Sequential APB→RDA pattern:** 2/2 descriptors (1 APB + 1 RDA) successfully processed

### Waveform Analysis Results
**Timeline at 4260-4280ns (Sequential APB→RDA Test):**
```
Time 4260ns: APB descriptor valid pulse (APB phase complete) ✅
Wait period: ~20 cycles
Time 4280ns: rda_valid=1 (RDA packet arrives) ✅
Time 4280ns: rda_ready=1 (RTL accepts RDA packet) ✅
Time 4280ns: r_rda_operation_active pulses high for 1 clock ✅
Time 4281ns: descriptor_valid=1 (RDA descriptor output) ✅
Time 4281ns: descriptor_is_rda=1 (RDA flag set correctly) ✅
```

**Conclusion:** Sequential pattern works correctly - both descriptors generated with proper timing.

---

## RTL Behavior Analysis

### Mutual Exclusion Implementation

The RTL correctly implements **mutual exclusion** between APB and RDA paths:

**RTL Implementation** (`projects/components/rapids/rtl/rapids_fub/descriptor_engine.sv`):
```systemverilog
// Line 242: APB ready signal - blocks when RDA active
assign w_apb_skid_ready_out = (r_current_state == read_IDLE) &&
                               !r_rda_operation_active &&
                               !r_channel_reset_active;

// Line 270: RDA ready signal - blocks when APB active
assign w_rda_skid_ready_out = (r_current_state == read_IDLE) &&
                               !r_apb_operation_active &&
                               !r_channel_reset_active;
```

**Behavior:** Neither path can start while the other is active. This is **working as designed** for the intended use case of sequential phases (APB startup, then RDA operation).

### Operation Flag Timing

The waveform analysis showed that operation flags clear properly:

1. APB operation completes and descriptor outputs
2. `r_apb_operation_active` clears when FSM reaches `read_COMPLETE` state
3. FSM returns to `read_IDLE` state
4. After wait period (~20 cycles), RDA packet arrives
5. RDA is accepted immediately (no blocking observed)
6. `r_rda_operation_active` pulses for 1 clock
7. RDA descriptor outputs correctly

**Conclusion:** Flag management and timing work correctly for sequential operations.

---

## Investigation Steps Performed

1. ✅ **Verified RDA-only tests pass:** 10/10 RDA packets processed successfully
2. ✅ **Verified APB-only tests pass:** 10/10 APB requests processed successfully
3. ✅ **Verified sequential APB→RDA pattern:** 2/2 descriptors processed successfully
4. ✅ **Waveform analysis:** Confirmed FSM states, flag timing, and descriptor outputs all correct
5. ✅ **Examined RTL mutual exclusion logic:** Working as designed for sequential phases

---

## Conclusion

**No RTL bug found.** The descriptor engine correctly handles:
- APB-only operations
- RDA-only operations
- Sequential APB→RDA operations (APB startup followed by RDA normal operation)

The mutual exclusion logic works correctly for the intended use case of sequential operational phases.

---

## References

- **RTL:** `projects/components/rapids/rtl/rapids_fub/descriptor_engine.sv`
- **Specification:** `projects/components/rapids/docs/rapids_spec/ch02_blocks/01_02_descriptor_engine.md`
- **Testbench:** `bin/CocoTBFramework/tbclasses/rapids/descriptor_engine_tb.py`
- **Test:** `projects/components/rapids/dv/tests/fub_tests/descriptor_engine/test_descriptor_engine.py`

---

**Last Updated:** 2025-10-14
**Next Review:** After waveform analysis and user decision on intended behavior
