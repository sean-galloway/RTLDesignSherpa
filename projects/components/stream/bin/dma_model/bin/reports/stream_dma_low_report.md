# STREAM DMA Complete Performance Report
## LOW Performance Mode Analysis

**Payload:** 1024 bytes

**AXI Interface:** 512-bit @ 1.0 GHz (Peak: 57.6 GB/s)
**Memory Latency:** 200 cycles


================================================================================

# STREAM DMA Bottleneck Analysis: LOW Mode

**Payload:** 1024 bytes (16 beats @ 512-bit bus)

**Generated:** STREAM DMA Performance Model v1.0


---

## Configuration Summary

| Parameter | Read Engine | Write Engine |
|-----------|-------------|--------------|
| Max Burst Length | 8 beats | 16 beats |
| Max Outstanding | 1 | 1 |
| Pipeline Depth | 1 | 1 |
| SRAM per Channel | 128 lines (8 KB) | 128 lines (8 KB) |

## Single Channel Analysis

### Read Path
- **Effective Pipeline:** 1 (limited by configuration)
- **Cycles per Burst:** 208.0 cycles
- **Bandwidth:** 4.92 GB/s (8.5% of AXI peak)
- **Bottleneck:** Sequential operation - latency dominates

### Write Path
- **Effective Pipeline:** 1 (limited by configuration)
- **Cycles per Burst:** 216.0 cycles
- **Bandwidth:** 4.74 GB/s (8.2% of AXI peak)
- **Bottleneck:** Sequential operation - latency dominates

## Multi-Channel Scaling Analysis

|   Channels |   Read_BW |   Write_BW |   DMA_Throughput |   Read_Eff |   Write_Eff | Bottleneck   |
|-----------:|----------:|-----------:|-----------------:|-----------:|------------:|:-------------|
|          1 |   4.92308 |    4.74074 |          4.74074 |    8.54701 |     8.23045 | write_path   |
|          2 |   9.84615 |    9.48148 |          9.48148 |   17.094   |    16.4609  | write_path   |
|          4 |  19.6923  |   18.963   |         18.963   |   34.188   |    32.9218  | write_path   |
|          8 |  39.3846  |   37.9259  |         37.9259  |   68.3761  |    65.8436  | write_path   |

## Bottleneck Explanation

**Primary Bottleneck: Write Path**

- Write bandwidth (37.93 GB/s) < Read bandwidth (39.38 GB/s)
- Overall DMA throughput limited to 37.93 GB/s by write engine
- Write path limited by: timing

## Design Limitations

- **Low single-channel efficiency (8.5%)** - requires multiple channels to achieve good throughput

## Optimization Recommendations

- **Upgrade to MEDIUM mode** for 1.5x throughput improvement (37.9 → 57.6 GB/s)
- **Add pipelining** to hide memory latency


================================================================================

# Memory Latency Sensitivity Analysis: LOW Mode

**Payload:** 1024 bytes


---

## Single Channel Performance vs Latency

|   Latency_Cycles |   Read_BW_GBps |   Write_BW_GBps |   Read_Cycles_per_Burst |   Write_Cycles_per_Burst | Read_Limited_By   | Write_Limited_By   |
|-----------------:|---------------:|----------------:|------------------------:|-------------------------:|:------------------|:-------------------|
|               50 |       17.6552  |        15.5152  |                      58 |                       66 | timing            | timing             |
|              100 |        9.48148 |         8.82759 |                     108 |                      116 | timing            | timing             |
|              200 |        4.92308 |         4.74074 |                     208 |                      216 | timing            | timing             |
|              400 |        2.5098  |         2.46154 |                     408 |                      416 | timing            | timing             |
|              800 |        1.26733 |         1.2549  |                     808 |                      816 | timing            | timing             |

## Key Insights

- **LOW mode** pipelining effectiveness vs latency:
  - No pipelining: Performance degrades linearly with latency
  - Bandwidth ∝ 1/(latency + burst_length)


================================================================================

# Summary and Recommendations

## LOW Mode Performance
- **Single Channel:** 4.92 GB/s (read), 4.74 GB/s (write)
- **8 Channels:** 37.93 GB/s DMA throughput
- **Efficiency:** 68.4% of AXI peak
- **Bottleneck:** write_path

## When to Use This Mode
- **Tutorial and learning:** Simple, easy to understand
- **Area-constrained designs:** Minimal logic
- **Low throughput requirements:** < 40 GB/s
