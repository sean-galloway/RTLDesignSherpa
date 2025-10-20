# Performance Profiler Tests

**Status:** Ready to run - Demonstrates simultaneous edge bug
**Test Count:** 7 CocoTB tests

---

## How to Run

### All Tests

```bash
source env_python
cd projects/components/stream/dv/tests/fub_tests/perf_profiler
pytest -v
```

### Single Test

```bash
pytest test_perf_profiler.py::test_simultaneous_edges_bug -v -s
```

---

## Test List

1. **test_single_channel_timestamp_mode** - Basic timestamp profiling
2. **test_single_channel_elapsed_mode** - Basic elapsed time profiling
3. **test_multiple_channels_sequential** - Sequential channel activity
4. **test_simultaneous_edges_bug** - **DEMONSTRATES BUG!**
5. **test_fifo_full_behavior** - FIFO overflow handling
6. **test_two_register_read_interface** - Two-register APB read interface
7. **test_counter_increment** - Timestamp counter validation

---

## Expected Results (Before Fix)

```
test_single_channel_timestamp_mode ............ PASSED
test_single_channel_elapsed_mode .............. PASSED
test_multiple_channels_sequential ............. PASSED
test_simultaneous_edges_bug ................... PASSED (demonstrates bug!)
  WARNING: Only 1 event recorded (channel 0)
  WARNING: Expected 8 events
  WARNING: Events for channels 1-7 LOST
test_fifo_full_behavior ....................... PASSED
test_two_register_read_interface .............. PASSED
test_counter_increment ........................ PASSED
```

---

## The Bug

When all 8 channels transition simultaneously:
- **Expected:** 8 START events (one per channel)
- **Actual:** 1 START event (channel 0 only)
- **Cause:** `r_idle_prev` updates every cycle, losing edges

See: `docs/PERF_PROFILER_TEST_SUMMARY.md` for complete bug analysis and proposed fix.

---

## Test Output Locations

- **Logs:** `logs/test_*_perf_profiler_*.log`
- **Waveforms:** `local_sim_build/test_*/dump.vcd`
- **Build:** `local_sim_build/test_*/`
