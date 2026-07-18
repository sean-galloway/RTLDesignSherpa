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

# STREAM Core Performance Profiling

This directory contains tools for profiling the performance of the STREAM core across various configurations.

## Overview

The performance profiling script (`run_performance_profile.sh`) runs the existing stream_core tests with the **'fast' (no-stress) timing profile** to collect baseline performance metrics. This represents ideal performance when memory responds immediately with no artificial delays.

## Quick Start

```bash
# Run full performance profiling suite
./run_performance_profile.sh

# Run with custom output directory
./run_performance_profile.sh my_perf_results
```

## What Gets Tested

The script runs the following configurations:

### Data Width Comparison (Single Channel)
- 128-bit data width
- 256-bit data width
- 512-bit data width

### Multi-Channel Performance
- Dual channel (128-bit and 256-bit)

### FIFO Depth Comparison (256-bit data width)
- 256 entries
- 512 entries
- 1024 entries

## Output

The script generates:

1. **Individual test logs**: `perf_results/<test_name>.log`
   - Full pytest output for each configuration
   - Detailed transaction logs
   - Verification results

2. **Performance report**: `perf_results/performance_report_<timestamp>.txt`
   - Summary table of all tests
   - Status (PASSED/FAILED/TIMEOUT)
   - Duration for each configuration
   - Extracted performance metrics

## Performance Metrics

The testbench collects:

- **Transfer Duration**: Time to complete descriptor chain (microseconds)
- **Throughput**: Beats per cycle
- **Bandwidth**: MB/s data transfer rate
- **Efficiency**: Percentage of theoretical maximum bandwidth
- **Latency**: First-beat latency

## Interpreting Results

### 'Fast' Timing Profile

The 'fast' timing profile means:
- AXI memory BFMs respond immediately (no artificial delay)
- Descriptor memory available on next cycle
- Source/destination memory ready instantly
- **This represents IDEAL conditions**

### Real-World Performance

Actual performance will be lower due to:
- Memory controller latency (DDR4: 70-100 cycles typical)
- DRAM refresh cycles
- Bus contention
- System load

### Efficiency Metrics

- **>90% efficiency**: Excellent - design is well-pipelined
- **70-90% efficiency**: Good - minor stalls or gaps
- **50-70% efficiency**: Fair - significant stalls
- **<50% efficiency**: Poor - investigate bottlenecks

## Example Output

```
============================================================================
 STREAM Core Performance Profiling Report
============================================================================

Configuration                                 Data Width   Status          Duration
------------------------------------------------------------------------------
Single Channel 128-bit                        128          PASSED          125.40
Single Channel 256-bit                        256          PASSED          68.20
Single Channel 512-bit                        512          PASSED          38.10
Dual Channel 128-bit                          128          PASSED          142.30
...
```

## Customization

To add more test configurations, edit `run_performance_profile.sh` and add entries to the `CONFIGS` array:

```bash
CONFIGS=(
    # Format: "test_name:data_width:fifo_depth:description"
    "nc04_dw0128_fd0512_dc04_nch01_standard_fast:128:512:My Custom Test"
)
```

## Troubleshooting

### Test Timeouts

If tests timeout (default 120s), increase the timeout in the script:

```bash
timeout 300 /mnt/data/github/rtldesignsherpa/venv/bin/python -m pytest ...
```

### Missing Metrics

If performance metrics don't appear in the log, verify the testbench is calling:

```python
stats = tb.get_performance_stats(channel)
```

### Compilation Errors

Ensure all tests pass individually before running the performance suite:

```bash
# Test a single configuration first
WAVES=0 TEST_LEVEL=func pytest test_stream_core.py::test_stream_core_single_channel \
    -k "nc04_dw0128_fd0512_dc04_nch01_standard_fast" -v
```

## Performance Optimization Workflow

1. **Baseline**: Run performance profiling with current design
2. **Identify Bottlenecks**: Check logs for stalls, backpressure, underflow
3. **Optimize**: Modify RTL (add pipelining, increase buffering, etc.)
4. **Re-profile**: Run performance profiling again
5. **Compare**: Check if metrics improved
6. **Iterate**: Repeat until performance goals met

## Related Documentation

- `stream_index.md` - Performance mode descriptions (V1/V2/V3)
- `test_stream_core.py` - Main test implementation
- `../tbclasses/stream_core_tb.py` - Testbench with performance metrics collection

## Known Issues

### Python 3.12 + cocotb-test Compatibility

**Issue:** 512-bit configuration tests may fail with `AttributeError: 'StreamReader' object has no attribute 'flush'`

**Impact:**
- Test cleanup fails after successful transfer completion
- Hardware performance measurement is valid
- Only affects test infrastructure, not RTL functionality

**Workaround:**
1. Extract timing from simulation logs before cleanup fails:
   ```bash
   grep "FULLY COMPLETE" perf_results/params2.log
   ```
2. Use params0 and params1 for automated performance tracking
3. Manually record params2 timing when needed

**Root Cause:** Python 3.12's asyncio StreamReader doesn't have `.flush()` method that cocotb-test expects

**Status:** Tracking with cocotb-test upstream (https://github.com/cocotb/cocotb-test/issues/XXX)

### Data Verification Timeout

**Issue:** Wide data widths (512-bit) may cause verification step to hang with high CPU usage

**Impact:**
- Verification loop is inefficient for large datasets
- Test times out at 120s despite successful transfer

**Workaround:**
- Reduce TEST_LEVEL to 'basic' for wider data widths
- Or skip verification for performance-only testing

**Future Fix:** Optimize verification algorithm or use dedicated performance tests with minimal verification

---

## Performance Summary

See `perf_results/PERFORMANCE_SUMMARY.md` for detailed analysis of the first profiling run:
- params0 (128-bit): 13.11 μs ✅
- params1 (256-bit): 11.53 μs ✅ (12% faster than 128-bit)
- params2 (512-bit): 13.2 μs ⚠️ (transfer succeeded, test infra failed)

---

## Future Enhancements

Planned improvements to performance profiling:

- [ ] Automated comparison of before/after results
- [ ] Graphical performance charts (throughput vs data width, etc.)
- [ ] Stress testing with realistic memory latency profiles
- [ ] Multi-run averaging to reduce noise
- [ ] Performance regression detection in CI
- [ ] Fix Python 3.12 cocotb-test compatibility
- [ ] Dedicated performance test with minimal verification

---

**Last Updated**: 2025-11-23
**Maintained By**: RTL Design Sherpa Team
