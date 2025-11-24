# STREAM Core Burst Matrix Tests

**Date:** 2025-11-23
**Test Level:** `burst`
**Purpose:** Comprehensive validation of burst sizes and SRAM segment sizing

---

## Overview

The burst matrix tests validate the STREAM core across all combinations of read/write burst sizes and SRAM segment sizes with **dual objectives**:

### Primary Goals

1. **SRAM Sizing Validation**: Prove the design rule across all burst/segment combinations
   - **Design Rule:** Minimum SRAM per segment = MAX(2KB, 2 × single_burst_size)

2. **Perfect Streaming Verification**: Ensure continuous data flow with no bubbles or stalls
   - Verify read and write datapaths maintain full bandwidth
   - Confirm SRAM buffering prevents backpressure propagation
   - Validate multi-channel arbitration doesn't create streaming gaps

### Test Configuration

All tests use:
- **2 concurrent channels** (realistic multi-channel arbitration stress)
- **Fast (no-stress) timing** for debugging and analysis
- **6 descriptors per channel** (ensures machinery churn and realistic operation)
- **256-512 beats per transfer** (weighted distribution: [128, 256, 384, 512, 512, 512])
  - Minimum: 256 beats (ensures proper data flow stress)
  - Most transfers: 512 beats (validates full burst/SRAM interaction)

### Future Enhancement

**Register Slice Insertion Study**: Add configurable pipeline register stages to study latency effects on streaming performance. This will demonstrate how additional pipeline depth affects throughput and buffering requirements.

---

## Test Matrix

### 128-bit Configuration (9 tests)

**Segment Size:** 2KB (128 entries × 16 bytes)

| Test | Rd Burst | Wr Burst | Burst Size (bytes) | Meets Rule? |
|------|----------|----------|-------------------|-------------|
| params0 | 8 | 8 | 128/128 | ✓ 2KB > 2×128 |
| params1 | 8 | 16 | 128/256 | ✓ 2KB > 2×256 |
| params2 | 8 | 32 | 128/512 | ✓ 2KB = 2×512 |
| params3 | 16 | 8 | 256/128 | ✓ 2KB > 2×256 |
| params4 | 16 | 16 | 256/256 | ✓ 2KB > 2×256 |
| params5 | 16 | 32 | 256/512 | ✓ 2KB = 2×512 |
| params6 | 32 | 8 | 512/128 | ✓ 2KB = 2×512 |
| params7 | 32 | 16 | 512/256 | ✓ 2KB = 2×512 |
| params8 | 32 | 32 | 512/512 | ✓ 2KB = 2×512 |

**Expected:** All pass (2KB meets minimum for all burst combinations)

### 256-bit Configuration (8 tests)

**Burst combinations tested with 2 segment sizes:**

| Test | Rd Burst | Wr Burst | Segment | FIFO Depth | Burst Size | Meets Rule? |
|------|----------|----------|---------|------------|------------|-------------|
| params9 | 8 | 8 | 2KB | 64 | 256/256 | ✓ 2KB = 2×512 |
| params10 | 8 | 8 | 4KB | 128 | 256/256 | ✓ 4KB > 2×512 |
| params11 | 8 | 16 | 2KB | 64 | 256/512 | ✓ 2KB = 2×512 |
| params12 | 8 | 16 | 4KB | 128 | 256/512 | ✓ 4KB > 2×512 |
| params13 | 16 | 8 | 2KB | 64 | 512/256 | ✓ 2KB = 2×512 |
| params14 | 16 | 8 | 4KB | 128 | 512/256 | ✓ 4KB > 2×512 |
| params15 | 16 | 16 | 2KB | 64 | 512/512 | ✓ 2KB = 2×512 |
| params16 | 16 | 16 | 4KB | 128 | 512/512 | ✓ 4KB > 2×512 |

**Expected:**
- 2KB tests: May show marginal performance (minimum size)
- 4KB tests: Should perform well (comfortable margin)

### 512-bit Configuration (8 tests)

**Burst combinations tested with 2 segment sizes:**

| Test | Rd Burst | Wr Burst | Segment | FIFO Depth | Burst Size | Meets Rule? |
|------|----------|----------|---------|------------|------------|-------------|
| params17 | 8 | 8 | 2KB | 32 | 512/512 | ✓ 2KB = 2×512 |
| params18 | 8 | 8 | 4KB | 64 | 512/512 | ✓ 4KB > 2×512 |
| params19 | 8 | 16 | 2KB | 32 | 512/1KB | ⚠️ 2KB = 2×1KB (minimum!) |
| params20 | 8 | 16 | 4KB | 64 | 512/1KB | ✓ 4KB > 2×1KB |
| params21 | 16 | 8 | 2KB | 32 | 1KB/512 | ⚠️ 2KB = 2×1KB (minimum!) |
| params22 | 16 | 8 | 4KB | 64 | 1KB/512 | ✓ 4KB > 2×1KB |
| params23 | 16 | 16 | 2KB | 32 | 1KB/1KB | ⚠️ 2KB = 2×1KB (minimum!) |
| params24 | 16 | 16 | 4KB | 64 | 1KB/1KB | ✓ 4KB > 2×1KB |

**Expected:**
- 2KB tests with 16-beat bursts: **May fail or show degraded performance** (at absolute minimum)
- 4KB tests: Should pass (comfortable margin)

---

## Running the Tests

### Run All 25 Burst Matrix Tests

```bash
cd projects/components/stream/dv/tests/macro

# Run all burst matrix tests
WAVES=0 TEST_LEVEL=burst pytest test_stream_core.py::test_stream_core_single_channel -v

# Run with waveforms for debugging failures
WAVES=1 TEST_LEVEL=burst pytest test_stream_core.py::test_stream_core_single_channel -v
```

### Run Specific Configurations

```bash
# Run only 128-bit tests (params0-params8)
WAVES=0 TEST_LEVEL=burst pytest test_stream_core.py::test_stream_core_single_channel -k "params[0-8]" -v

# Run only 256-bit tests (params9-params16)
WAVES=0 TEST_LEVEL=burst pytest test_stream_core.py::test_stream_core_single_channel -k "params1[0-6]" -v

# Run only 512-bit tests (params17-params24)
WAVES=0 TEST_LEVEL=burst pytest test_stream_core.py::test_stream_core_single_channel -k "params2[0-4]" -v

# Run specific test
WAVES=0 TEST_LEVEL=burst pytest test_stream_core.py::test_stream_core_single_channel -k "params19" -v
```

### Stop on First Failure

```bash
# Stop immediately on first failure for debugging
WAVES=0 TEST_LEVEL=burst pytest test_stream_core.py::test_stream_core_single_channel --maxfail=1 -x -v
```

---

## Expected Results

### Should PASS

**All 128-bit tests (params0-params8):**
- 2KB segment provides sufficient margin for all burst combinations
- Narrow data width = more beats per KB = better granularity

**Most 256-bit and 512-bit tests with 4KB:**
- 4KB provides comfortable margin above minimum requirement

### May FAIL or Show Degraded Performance

**512-bit with 2KB and 16-beat bursts (params19, params21, params23):**
- 16 beats × 64 bytes = 1KB burst size
- 2KB = 2 × 1KB (exactly at minimum!)
- With 2 concurrent channels + arbitration delays, may underflow

**If these fail:** This validates the design rule - proves 2× is the absolute minimum and multi-channel operation needs margin above that.

**If these pass:** Great! Hardware more efficient than expected, but still not recommended for production.

---

## Debugging Failures

### Enable Waveforms

```bash
WAVES=1 TEST_LEVEL=burst pytest test_stream_core.py::test_stream_core_single_channel -k "params19" -v
```

Waveforms saved to: `local_sim_build/test_stream_core_single_*/dump.vcd`

### Check Specific Failure Pattern

**If you see "data mismatch" errors:**
- SRAM underflow → write engine reading uninitialized memory
- Confirm by checking for "Reading uninitialized memory" warnings in log

**If you see timeout errors:**
- SRAM overflow → read engine stalled waiting for space
- Check for `space_free` signals stuck at 0

**If you see performance degradation:**
- Still completes but slower than expected
- Indicates marginal SRAM sizing - frequent stalls but no corruption

### Streaming Performance Analysis

**Perfect streaming means:**
- AXI read interface: Continuous valid beats during bursts (no bubbles)
- AXI write interface: Continuous valid beats during bursts (no bubbles)
- SRAM controller: Balanced read/write rates with no overflow/underflow
- Multi-channel arbitration: Grant cycles don't create gaps in data flow

**Waveform checks for streaming verification:**
1. AXI AR/R channels: `m_axi_rd_arvalid` and `m_axi_rd_rvalid` stay high during bursts
2. AXI AW/W channels: `m_axi_wr_awvalid` and `m_axi_wr_wvalid` stay high during bursts
3. SRAM fill level: Should stay in safe range (not empty, not full)
4. Channel switching: Arbitration should be quick (< 10 cycles between grants)

---

## Test Configuration Details

All burst matrix tests configured with:
- `num_channels`: 4 (total channels in core)
- `test_channels`: [0, 1] (2 concurrent channels)
- `desc_count`: 6 (descriptors per channel for machinery churn)
- `transfer_sizes`: [256, 384, 512, 768] (8-96 bursts per descriptor depending on burst size)
- `timing_profile`: 'fast' (no artificial delays)

**Why these transfer sizes?**
- Transfer sizes create proper machinery churn by executing multiple bursts per descriptor
- **Example with 16-beat bursts:**
  - 256 beats ÷ 16 = 16 bursts
  - 384 beats ÷ 16 = 24 bursts ← Target machinery stress
  - 512 beats ÷ 16 = 32 bursts
  - 768 beats ÷ 16 = 48 bursts
- **Example with 8-beat bursts:**
  - 768 beats ÷ 8 = 96 bursts ← Maximum machinery stress
- Multi-descriptor chains (6×) ensure scheduler, arbiter, and engines cycle through states
- Combined: 6 descriptors × ~24 bursts = ~144 bursts per channel = excellent machinery exercise

This realistic configuration stresses multi-channel arbitration, SRAM management, and burst engine synchronization while remaining debuggable with fast timing.

---

## Design Rule Validation

These tests validate:

**Minimum SRAM per segment = MAX(2KB, 2 × single_burst_size)**

Where `single_burst_size = burst_beats × (data_width / 8)`

The tests confirm:
1. ✓ 2KB floor is sufficient for narrow widths (128-bit)
2. ✓ 2× burst size scaling works for comfortable configurations
3. ⚠️ Absolute minimum (exactly 2×) may fail with multi-channel arbitration delays
4. ✓ 4× minimum (current validated config) provides good margin

**Recommended for production:** Use 4× minimum for multi-channel, or 2× minimum for single-channel only.

---

**Last Updated:** 2025-11-23
**Maintainer:** RTL Design Sherpa - STREAM Performance Team
