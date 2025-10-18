# STREAM DMA Complete Performance Report
## MEDIUM Performance Mode Analysis

**Payload:** 1024 bytes

**AXI Interface:** 512-bit @ 1.0 GHz (Peak: 57.6 GB/s)
**Memory Latency:** 200 cycles


================================================================================

# STREAM DMA Bottleneck Analysis: MEDIUM Mode

**Payload:** 1024 bytes (16 beats @ 512-bit bus)

**Generated:** STREAM DMA Performance Model v1.0


---

## Configuration Summary

| Parameter | Read Engine | Write Engine |
|-----------|-------------|--------------|
| Max Burst Length | 16 beats | 32 beats |
| Max Outstanding | 4 | 4 |
| Pipeline Depth | 4 | 4 |
| SRAM per Channel | 128 lines (8 KB) | 128 lines (8 KB) |

## Single Channel Analysis

### Read Path
- **Effective Pipeline:** 4 (limited by configuration)
- **Cycles per Burst:** 66.0 cycles
- **Bandwidth:** 15.52 GB/s (26.9% of AXI peak)
- **Bottleneck:** Sequential operation - latency dominates

### Write Path
- **Effective Pipeline:** 4 (limited by configuration)
- **Cycles per Burst:** 66.0 cycles
- **Bandwidth:** 15.52 GB/s (26.9% of AXI peak)
- **Bottleneck:** Sequential operation - latency dominates

## Multi-Channel Scaling Analysis

|   Channels |   Read_BW |   Write_BW |   DMA_Throughput |   Read_Eff |   Write_Eff | Bottleneck   |
|-----------:|----------:|-----------:|-----------------:|-----------:|------------:|:-------------|
|          1 |   15.5152 |    15.5152 |          15.5152 |    26.936  |     26.936  | balanced     |
|          2 |   31.0303 |    31.0303 |          31.0303 |    53.8721 |     53.8721 | balanced     |
|          4 |   57.6    |    57.6    |          57.6    |   100      |    100      | balanced     |
|          8 |   57.6    |    57.6    |          57.6    |   100      |    100      | balanced     |

## Bottleneck Explanation

**Balanced Performance**

- Read and write bandwidth equal: 57.60 GB/s
- No single-path bottleneck - optimal balance achieved
- AXI bus saturated at 57.60 GB/s

## Design Limitations

- **Low single-channel efficiency (26.9%)** - requires multiple channels to achieve good throughput

## Optimization Recommendations

- **Already saturating AXI bus** - no further optimization possible without faster interface


================================================================================

# Memory Latency Sensitivity Analysis: MEDIUM Mode

**Payload:** 1024 bytes


---

## Single Channel Performance vs Latency

|   Latency_Cycles |   Read_BW_GBps |   Write_BW_GBps |   Read_Cycles_per_Burst |   Write_Cycles_per_Burst | Read_Limited_By   | Write_Limited_By   |
|-----------------:|---------------:|----------------:|------------------------:|-------------------------:|:------------------|:-------------------|
|               50 |       35.9298  |        35.9298  |                    28.5 |                     28.5 | timing            | timing             |
|              100 |       24.9756  |        24.9756  |                    41   |                     41   | timing            | timing             |
|              200 |       15.5152  |        15.5152  |                    66   |                     66   | timing            | timing             |
|              400 |        8.82759 |         8.82759 |                   116   |                    116   | timing            | timing             |
|              800 |        4.74074 |         4.74074 |                   216   |                    216   | timing            | timing             |

## Key Insights

- **MEDIUM mode** pipelining effectiveness vs latency:
  - 4-deep pipeline: Partially hides latency
  - Effective latency reduced by 4x at low latencies


================================================================================

# Summary and Recommendations

## MEDIUM Mode Performance
- **Single Channel:** 15.52 GB/s (read), 15.52 GB/s (write)
- **8 Channels:** 57.60 GB/s DMA throughput
- **Efficiency:** 100.0% of AXI peak
- **Bottleneck:** balanced

## When to Use This Mode
- **Typical FPGA implementations:** Balanced performance/area
- **Production systems:** Saturates AXI bus with 8 channels
- **Moderate complexity:** Achievable in most designs
