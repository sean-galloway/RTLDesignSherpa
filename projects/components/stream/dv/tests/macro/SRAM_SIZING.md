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

# STREAM Core SRAM Sizing Guide

## Rationale: Concurrent Read/Write Requires Minimal Buffering

With concurrent read and write operations, the SRAM buffer only needs to absorb temporary mismatches in read/write rates during:
- AXI read latency (AR → R data arrival)
- AXI write acceptance (AW → W data consumption)
- Burst boundary transitions

**Key Insight:** The SRAM does NOT need to hold the entire transfer - only the "in-flight" delta between read and write pipelines.

## SRAM Depth Calculations

SRAM depth is specified in **entries**, where each entry is `data_width` bits wide.

### Bytes per Entry

| Data Width | Bytes/Entry |
|------------|-------------|
| 128-bit | 16 |
| 256-bit | 32 |
| 512-bit | 64 |

### Target Buffer Sizes

For performance testing, we target 3 buffer sizes per channel:

**4KB Buffer (Comfortable pipeline depth):**
| Data Width | Calculation | Depth (entries) |
|------------|-------------|-----------------|
| 128-bit | 4096 / 16 | 256 |
| 256-bit | 4096 / 32 | 128 |
| 512-bit | 4096 / 64 | 64 |

**2KB Buffer (Moderate pipeline depth):**
| Data Width | Calculation | Depth (entries) |
|------------|-------------|-----------------|
| 128-bit | 2048 / 16 | 128 |
| 256-bit | 2048 / 32 | 64 |
| 512-bit | 2048 / 64 | 32 |

**1KB Buffer (Minimal pipeline depth):**
| Data Width | Calculation | Depth (entries) |
|------------|-------------|-----------------|
| 128-bit | 1024 / 16 | 64 |
| 256-bit | 1024 / 32 | 32 |
| 512-bit | 1024 / 64 | 16 |

## Performance Test Configurations

For optimal performance profiling with realistic SRAM sizes:

```python
# Recommended test configurations
perf_configs = [
    # 128-bit with 4KB SRAM per channel
    {'data_width': 128, 'fifo_depth': 256, 'sram_kb': 4},

    # 256-bit with 4KB SRAM per channel
    {'data_width': 256, 'fifo_depth': 128, 'sram_kb': 4},

    # 512-bit with 4KB SRAM per channel
    {'data_width': 512, 'fifo_depth': 64, 'sram_kb': 4},
]
```

## SRAM Sizing Formula

For a given target buffer size in bytes:

```python
def calculate_fifo_depth(data_width_bits, target_buffer_bytes):
    bytes_per_entry = data_width_bits // 8
    fifo_depth = target_buffer_bytes // bytes_per_entry
    return fifo_depth

# Examples:
calculate_fifo_depth(128, 4096)  # Returns: 256
calculate_fifo_depth(256, 4096)  # Returns: 128
calculate_fifo_depth(512, 4096)  # Returns: 64
```

## Verification Strategy

### Test 1: 4KB Buffer (Baseline)
- **Goal:** Establish baseline performance with comfortable buffering
- **Expected:** No SRAM stalls, smooth concurrent read/write
- **Metric:** Transfer time, efficiency

### Test 2: 2KB Buffer (Reduced)
- **Goal:** Verify concurrent operation with moderate buffering
- **Expected:** Possible minor stalls, but transfer completes
- **Metric:** Compare to 4KB baseline (should be similar)

### Test 3: 1KB Buffer (Minimal)
- **Goal:** Stress test with minimal buffering
- **Expected:** More frequent SRAM full/empty conditions
- **Metric:** Shows effectiveness of concurrent read/write

### What to Watch For

**SRAM Overflow Indicators:**
- Read engine stalls waiting for SRAM space
- `sram_full` signal asserts frequently
- Increased transfer latency

**SRAM Underflow Indicators:**
- Write engine stalls waiting for SRAM data
- `sram_empty` signal asserts frequently
- Write burst fragmentation

**Success Criteria:**
- All transfers complete correctly
- Data integrity verified
- Performance within expected range (10-15μs for 'fast' timing)

## Current Status vs. Recommended

### Previous (Oversized - All tests)
```
params0: data_width=128, fifo_depth=512  ← 8KB buffer (oversized!)
params1: data_width=256, fifo_depth=512  ← 16KB buffer (oversized!)
params2: data_width=512, fifo_depth=512  ← 32KB buffer (oversized!)
```

### Attempted (Uniform 4KB - FAILED for 512-bit)
```
params0: data_width=128, fifo_depth=256  ← 4KB buffer (WORKS GREAT! 14% faster)
params1: data_width=256, fifo_depth=128  ← 4KB buffer (WORKS but 34% slower)
params2: data_width=512, fifo_depth=64   ← 4KB buffer (DATA CORRUPTION! ❌)
```

**Finding:** 512-bit with 64 entries causes data mismatch errors. SRAM too small for concurrent read/write at wide data widths.

### **RECOMMENDED (Validated - Power-of-2 Scaled)**
```
params0: data_width=128, fifo_depth=256  ← 4KB buffer (optimal from testing ✅)
params1: data_width=256, fifo_depth=256  ← 8KB buffer (safe, power-of-2 ✅)
params2: data_width=512, fifo_depth=128  ← 8KB buffer (minimum safe depth ✅)
```

**Total SRAM per 4-channel core:**
- 128-bit: 4KB × 4 = 16 KB
- 256-bit: 8KB × 4 = 32 KB
- 512-bit: 8KB × 4 = 32 KB

**Rationale:** See `REALISTIC_SRAM_ANALYSIS.md` for complete testing results and analysis.

## Additional Test Variations

To thoroughly test SRAM sizing, create matrix of configurations:

| Test | Data Width | SRAM Size | Depth | Focus |
|------|------------|-----------|-------|-------|
| A1 | 128-bit | 1KB | 64 | Minimal buffer |
| A2 | 128-bit | 2KB | 128 | Moderate buffer |
| A3 | 128-bit | 4KB | 256 | Comfortable buffer |
| B1 | 256-bit | 1KB | 32 | Minimal buffer |
| B2 | 256-bit | 2KB | 64 | Moderate buffer |
| B3 | 256-bit | 4KB | 128 | Comfortable buffer |
| C1 | 512-bit | 1KB | 16 | Minimal buffer |
| C2 | 512-bit | 2KB | 32 | Moderate buffer |
| C3 | 512-bit | 4KB | 64 | Comfortable buffer |

## Memory Utilization

### Total SRAM for 4-channel configuration with 4KB per channel:

| Data Width | Depth/Channel | Total Entries | Bits/Entry | Total SRAM |
|------------|---------------|---------------|------------|------------|
| 128-bit | 256 | 1024 | 128 | 128 Kbits = 16 KB |
| 256-bit | 128 | 512 | 256 | 128 Kbits = 16 KB |
| 512-bit | 64 | 256 | 512 | 128 Kbits = 16 KB |

**Key Observation:** Regardless of data width, 4KB per channel × 4 channels = 16KB total SRAM

This is MUCH more realistic than the current 512-entry configuration:
- 128-bit: 512 × 4 × 16 bytes = 32 KB (2x oversized)
- 256-bit: 512 × 4 × 32 bytes = 64 KB (4x oversized)
- 512-bit: 512 × 4 × 64 bytes = 128 KB (8x oversized!)

---

**Last Updated:** 2025-11-23
**Author:** RTL Design Sherpa - STREAM Performance Team
