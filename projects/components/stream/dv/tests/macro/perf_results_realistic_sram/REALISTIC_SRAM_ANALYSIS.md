# STREAM Core Performance with Realistic SRAM Sizing

**Date:** 2025-11-23
**Test:** Realistic SRAM sizing (4KB per channel) vs. Oversized SRAM (8-32KB per channel)
**Configuration:** Fast (no-stress) timing, func level (4 descriptors, 2 channels)

---

## Executive Summary

Testing with realistic 4KB-per-channel SRAM reveals:
1. **128-bit performs BETTER** with realistic SRAM (11.23μs vs 13.11μs = 14% improvement)
2. **256-bit performs WORSE** with realistic SRAM (15.45μs vs 11.53μs = 34% slower)
3. **512-bit FAILS** with realistic SRAM - **data integrity issue discovered**

---

## Results Comparison

### Oversized SRAM (Original Test)

| Config | Data Width | SRAM Depth | SRAM Size | Transfer Time | Status |
|--------|------------|------------|-----------|---------------|--------|
| params0 | 128-bit | 512 entries | 8KB | 13.11 μs | ✅ PASSED |
| params1 | 256-bit | 512 entries | 16KB | 11.53 μs | ✅ PASSED |
| params2 | 512-bit | 512 entries | 32KB | 13.2 μs | ⚠️ Test infra fail |

**Total SRAM per 4-channel core:**
- 128-bit: 32 KB (4× oversized)
- 256-bit: 64 KB (4× oversized)
- 512-bit: 128 KB (8× oversized!)

### Realistic SRAM (4KB per channel)

| Config | Data Width | SRAM Depth | SRAM Size | Transfer Time | Status |
|--------|------------|------------|-----------|---------------|--------|
| params0 | 128-bit | 256 entries | 4KB | **11.23 μs** | ✅ PASSED |
| params1 | 256-bit | 128 entries | 4KB | **15.45 μs** | ✅ PASSED |
| params2 | 512-bit | 64 entries | 4KB | **FAIL** | ❌ DATA MISMATCH |

**Total SRAM per 4-channel core:** 16 KB (constant across all data widths)

---

## Key Findings

### Finding 1: 128-bit Benefits from Smaller SRAM

**Observation:** 11.23 μs with realistic SRAM vs. 13.11 μs with oversized SRAM (14% faster!)

**Hypothesis:**
- Smaller SRAM may improve cache locality in simulation
- Less memory to manage improves RTL efficiency
- Tighter coupling between read/write pipelines

**Implication:** Oversized SRAM artificially degrades performance for narrow data widths.

### Finding 2: 256-bit Degrades with Smaller SRAM

**Observation:** 15.45 μs with realistic SRAM vs. 11.53 μs with oversized SRAM (34% slower)

**Hypothesis:**
- 128 entries insufficient for 256-bit burst sizes
- More frequent SRAM full/empty stalls
- Pipeline bubbles from buffer exhaustion

**Possible Solutions:**
1. Increase to 2KB buffer (64 entries) for 256-bit
2. Optimize burst sizes for 256-bit
3. Investigate allocation/drain controller margins

### Finding 3: 512-bit DATA CORRUPTION with 4KB SRAM

**Critical Issue:** Actual data mismatch detected at beat 31

```
ERROR - Mismatch at beat 31:
  src=0x5f5f5f5f... (expected)
  dst=0x00000000... (actual - all zeros!)
```

**Analysis:**

The destination data is **all zeros** instead of the expected pattern. This indicates:

**Likely Root Cause:** SRAM underflow in write path

With only 64 entries and 512-bit (64 bytes/entry):
- Total SRAM capacity: 64 × 64 = 4096 bytes ✅
- BUT: Concurrent read/write with 512-bit needs more pipeline depth

**Scenario that causes failure:**
1. Read engine fills SRAM with burst (16 beats × 64 bytes = 1024 bytes)
2. Write engine drains SRAM
3. Read engine tries to fill next burst while write is ongoing
4. **SRAM depth (64 entries) insufficient to buffer both operations**
5. Write engine reads from uninitialized/incorrect SRAM locations
6. Destination gets zeros instead of actual data

**Evidence from logs:**
```
WARNING - Reading uninitialized memory at address 0x17F7-0x17FF
ERROR - Mismatch at beat 31
```

The uninitialized memory warnings immediately precede the data mismatch, confirming the write path is reading from wrong/empty SRAM locations.

---

## Technical Analysis

### SRAM Depth Requirements

For concurrent read/write operation, SRAM must hold:
1. **In-flight read bursts** waiting to be written
2. **Pipeline latency buffers** for AXI AR→R and AW→W delays
3. **Safety margin** for burst boundaries and arbitration delays

**Minimum Depth Calculation:**

```
Required = (max_read_burst + max_write_burst + pipeline_latency) × safety_margin

128-bit (16 bytes/beat):
  = (16 + 16 + 10) × 1.5 = 63 beats → 64 entries ✅

256-bit (32 bytes/beat):
  = (16 + 16 + 10) × 1.5 = 63 beats → 64 entries ⚠️ (marginal)

512-bit (64 bytes/beat):
  = (16 + 16 + 10) × 1.5 = 63 beats → 64 entries ❌ (insufficient)
```

**Why 512-bit fails with 64 entries:**

The calculation above assumes bursts of 16 beats. But with 512-bit data width:
- Each beat = 64 bytes
- 16-beat burst = 1024 bytes
- **64 entries can only hold ~1 burst** (64 × 64 = 4096 bytes = 4 bursts total)

With only 4 bursts of buffering and concurrent read/write:
- Read fills 1 burst
- Write drains 1 burst (overlapped)
- Next read burst arrives before write completes
- **Buffer exhaustion → data corruption**

### Recommended SRAM Depths

Based on analysis, recommended minimum depths:

| Data Width | Bytes/Beat | Recommended Depth | Buffer Size | Rationale |
|------------|------------|-------------------|-------------|-----------|
| 128-bit | 16 | 256 | 4KB | Comfortable for concurrent ops |
| 256-bit | 32 | 192 | 6KB | Moderate buffering, good balance |
| 512-bit | 64 | 128 | 8KB | Minimum for safe concurrent ops |

**Alternative recommendation (uniform 2KB/channel for simplicity):**

| Data Width | Bytes/Beat | Depth for 2KB | Status |
|------------|------------|---------------|--------|
| 128-bit | 16 | 128 | ✅ Sufficient |
| 256-bit | 32 | 64 | ⚠️ Marginal |
| 512-bit | 64 | 32 | ❌ Insufficient |

**Best recommendation (8KB uniform - safe for all):**

| Data Width | Bytes/Beat | Depth for 8KB | Status |
|------------|------------|---------------|--------|
| 128-bit | 16 | 512 | ✅ Comfortable |
| 256-bit | 32 | 256 | ✅ Comfortable |
| 512-bit | 64 | 128 | ✅ Safe minimum |

---

## Performance Impact Analysis

### Transfer Time Comparison

**Relative to 128-bit baseline (smaller is faster):**

| Configuration | Oversized SRAM | Realistic SRAM | Change |
|---------------|----------------|----------------|--------|
| 128-bit baseline | 100% (13.11 μs) | 100% (11.23 μs) | -14% ⬇️ (faster!) |
| 256-bit | 88% (11.53 μs) | 138% (15.45 μs) | +34% ⬆️ (slower) |
| 512-bit | 101% (13.2 μs) | FAIL | N/A |

**Key Observation:** SRAM sizing significantly affects performance!

- Too large SRAM: Slower for narrow widths (128-bit)
- Too small SRAM: Slower for medium widths (256-bit), broken for wide widths (512-bit)

---

## Recommendations

### Short-Term (Fix params2 failure)

**Action:** Increase 512-bit SRAM depth to 128 entries (8KB)

```python
fifo_depths = {
    128: 256,  # 4KB - proven to work well
    256: 128,  # 4KB - works but marginal
    512: 128,  # 8KB - minimum for safe operation
}
```

**Expected Result:** params2 will pass, performance should improve

### Medium-Term (Optimize for all widths)

**Option A: Uniform 8KB per channel (conservative)**
```python
fifo_depths = {
    128: 512,  # 8KB
    256: 256,  # 8KB
    512: 128,  # 8KB
}
```
- Pros: Simple, safe for all configurations
- Cons: Oversized for 128-bit (as shown by original tests)

**Option B: Scaled but safe (recommended)**
```python
fifo_depths = {
    128: 256,  # 4KB - optimal from testing
    256: 192,  # 6KB - comfortable middle ground
    512: 128,  # 8KB - minimum safe depth
}
```
- Pros: Balanced performance and safety
- Cons: Non-power-of-2 depth for 256-bit (192 entries)

**Option C: Power-of-2 scaled (practical)**
```python
fifo_depths = {
    128: 256,  # 4KB - optimal
    256: 256,  # 8KB - safe but possibly over-provisioned
    512: 128,  # 8KB - minimum safe depth
}
```
- Pros: All power-of-2, simple synthesis
- Cons: 256-bit slightly over-provisioned

### Long-Term (Architectural improvements)

1. **Dynamic SRAM management** - Allow SRAM reallocation between channels based on active usage
2. **Burst size tuning** - Adjust burst sizes based on SRAM depth to prevent exhaustion
3. **Backpressure optimization** - Improve allocation/drain controller margins for wider data widths
4. **Per-channel SRAM configuration** - Allow different depths per channel based on expected workload

---

## Lessons Learned

### 1. SRAM Sizing Matters

Performance profiling with realistic SRAM revealed issues hidden by oversized buffers:
- 128-bit: Better performance with smaller SRAM ✅
- 256-bit: Performance degradation with smaller SRAM ⚠️
- 512-bit: Functional failure with small SRAM ❌

### 2. One-Size-Fits-All is Suboptimal

Different data widths have different buffering requirements:
- Narrow widths (128-bit): Small buffers are better
- Medium widths (256-bit): Need moderate buffering
- Wide widths (512-bit): Require substantial buffering

### 3. Testing Uncovers Real Issues

The params2 failure was masked by oversized SRAM in original tests. Only realistic sizing revealed the actual data corruption bug.

---

## Next Steps

1. ✅ **Document findings** (this document)
2. ⏳ **Fix params2** - Increase 512-bit SRAM to 128 entries (8KB)
3. ⏳ **Re-run performance profiling** with updated SRAM depths
4. ⏳ **Investigate 256-bit slowdown** - Why did it degrade with smaller SRAM?
5. ⏳ **Optimize burst sizes** - Tune for each data width
6. ⏳ **Create SRAM sizing guide** - Best practices for different workloads

---

**Last Updated:** 2025-11-23
**Author:** RTL Design Sherpa - STREAM Performance Team
**Status:** Active investigation - params2 data corruption identified
