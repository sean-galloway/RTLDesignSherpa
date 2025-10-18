# STREAM DMA Complete Performance Report
## HIGH Performance Mode Analysis

**Payload:** 1024 bytes

**AXI Interface:** 512-bit @ 1.0 GHz (Peak: 57.6 GB/s)
**Memory Latency:** 200 cycles


================================================================================

# STREAM DMA Bottleneck Analysis: HIGH Mode

**Payload:** 1024 bytes (16 beats @ 512-bit bus)

**Generated:** STREAM DMA Performance Model v1.0


---

## Configuration Summary

| Parameter | Read Engine | Write Engine |
|-----------|-------------|--------------|
| Max Burst Length | 256 beats | 256 beats |
| Max Outstanding | 16 | 16 |
| Pipeline Depth | 16 | 16 |
| SRAM per Channel | 128 lines (8 KB) | 128 lines (8 KB) |

## Single Channel Analysis

### Read Path
- **Effective Pipeline:** 8 (limited by SRAM capacity)
- **Cycles per Burst:** 41.0 cycles
- **Bandwidth:** 24.98 GB/s (43.4% of AXI peak)
- **Bottleneck:** SRAM buffer too small for desired pipeline depth

### Write Path
- **Effective Pipeline:** 8 (limited by SRAM capacity)
- **Cycles per Burst:** 41.0 cycles
- **Bandwidth:** 24.98 GB/s (43.4% of AXI peak)
- **Bottleneck:** SRAM buffer too small for desired pipeline depth

## Multi-Channel Scaling Analysis

|   Channels |   Read_BW |   Write_BW |   DMA_Throughput |   Read_Eff |   Write_Eff | Bottleneck   |
|-----------:|----------:|-----------:|-----------------:|-----------:|------------:|:-------------|
|          1 |   24.9756 |    24.9756 |          24.9756 |    43.3604 |     43.3604 | balanced     |
|          2 |   49.9512 |    49.9512 |          49.9512 |    86.7209 |     86.7209 | balanced     |
|          4 |   57.6    |    57.6    |          57.6    |   100      |    100      | balanced     |
|          8 |   57.6    |    57.6    |          57.6    |   100      |    100      | balanced     |

## Bottleneck Explanation

**Balanced Performance**

- Read and write bandwidth equal: 57.60 GB/s
- No single-path bottleneck - optimal balance achieved
- AXI bus saturated at 57.60 GB/s

## Design Limitations

- **Read pipeline limited to 8** (desired: 16) by SRAM capacity
- **Write pipeline limited to 8** (desired: 16) by SRAM capacity
- **SRAM capacity (128 lines)** insufficient for deep pipelining at current payload size
- **Low single-channel efficiency (43.4%)** - requires multiple channels to achieve good throughput

## Optimization Recommendations

- **Increase SRAM per channel** to enable deeper pipelining for single-channel performance
- **Or use multiple channels** to aggregate bandwidth (current strategy)
- **Already saturating AXI bus** with 8 channels
- **Increase payload size** to take advantage of larger burst capability (256 beats)


================================================================================

# Memory Latency Sensitivity Analysis: HIGH Mode

**Payload:** 1024 bytes


---

## Single Channel Performance vs Latency

|   Latency_Cycles |   Read_BW_GBps |   Write_BW_GBps |   Read_Cycles_per_Burst |   Write_Cycles_per_Burst | Read_Limited_By   | Write_Limited_By   |
|-----------------:|---------------:|----------------:|------------------------:|-------------------------:|:------------------|:-------------------|
|               50 |       46.0225  |        46.0225  |                   22.25 |                    22.25 | SRAM_capacity     | SRAM_capacity      |
|              100 |       35.9298  |        35.9298  |                   28.5  |                    28.5  | SRAM_capacity     | SRAM_capacity      |
|              200 |       24.9756  |        24.9756  |                   41    |                    41    | SRAM_capacity     | SRAM_capacity      |
|              400 |       15.5152  |        15.5152  |                   66    |                    66    | SRAM_capacity     | SRAM_capacity      |
|              800 |        8.82759 |         8.82759 |                  116    |                   116    | SRAM_capacity     | SRAM_capacity      |

## Key Insights

- **HIGH mode** pipelining effectiveness vs latency:
  - Deep pipeline: Significantly hides latency
  - SRAM capacity may limit effectiveness at high latencies


================================================================================

# SRAM Sizing Analysis

**Payload:** 1024 bytes (16 beats)


---

## SRAM Requirements by Performance Mode

| Mode    |   Pipeline_Depth |   SRAM_Lines |   SRAM_KB |   Bursts_Fit |   Eff_Pipeline |   Lines_to_Saturate_1ch | Saturates_8ch   |
|:--------|-----------------:|-------------:|----------:|-------------:|---------------:|------------------------:|:----------------|
| LOW     |                1 |          128 |         8 |           16 |              1 |                     163 | No              |
| MEDIUM  |                4 |          128 |         8 |            8 |              4 |                    1799 | Yes             |
| HIGH    |               16 |          128 |         8 |            8 |              8 |                    1799 | Yes             |
| PERFECT |              256 |         4096 |       256 |          256 |            256 |                    1799 | Yes             |

## Design Tradeoffs

### Current Design (LOW/MEDIUM/HIGH modes)
- **SRAM per channel:** 128 lines (8 KB)
- **Total SRAM (8 channels):** 1024 lines (64 KB)
- **Strategy:** Channel parallelism over deep per-channel buffers

### PERFECT Mode (Theoretical Maximum)
- **SRAM per channel:** 4096 lines (256 KB)
- **Total SRAM (8 channels):** 32768 lines (2048 KB)
- **Increase:** 32x more SRAM per channel
- **Benefit:** Single channel can saturate bus

### Why Not Use PERFECT Mode?
1. **Area Cost:** 16x more SRAM (64 KB → 1024 KB total)
2. **Diminishing Returns:** No throughput gain when using multiple channels
3. **Real-World Usage:** Applications naturally partition across channels
4. **Flexibility:** Multiple channels support concurrent independent operations


================================================================================

# Summary and Recommendations

## HIGH Mode Performance
- **Single Channel:** 24.98 GB/s (read), 24.98 GB/s (write)
- **8 Channels:** 57.60 GB/s DMA throughput
- **Efficiency:** 100.0% of AXI peak
- **Bottleneck:** balanced

## When to Use This Mode
- **High-end FPGA/ASIC:** Maximum realistic performance
- **Full throughput:** Saturates AXI bus with fewer channels
- **Limited by SRAM:** Cannot improve single-channel performance without more SRAM
