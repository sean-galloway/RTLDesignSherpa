# STREAM DMA Complete Performance Report
## PERFECT Performance Mode Analysis

**Payload:** 1024 bytes

**AXI Interface:** 512-bit @ 1.0 GHz (Peak: 57.6 GB/s)
**Memory Latency:** 200 cycles


================================================================================

# STREAM DMA Bottleneck Analysis: PERFECT Mode

**Payload:** 1024 bytes (16 beats @ 512-bit bus)

**Generated:** STREAM DMA Performance Model v1.0


---

## Configuration Summary

| Parameter | Read Engine | Write Engine |
|-----------|-------------|--------------|
| Max Burst Length | 256 beats | 256 beats |
| Max Outstanding | 256 | 256 |
| Pipeline Depth | 256 | 256 |
| SRAM per Channel | 4096 lines (256 KB) | 4096 lines (256 KB) |

## Single Channel Analysis

### Read Path
- **Effective Pipeline:** 256 (limited by configuration)
- **Cycles per Burst:** 16.8 cycles
- **Bandwidth:** 61.02 GB/s (100.0% of AXI peak)
- **Bottleneck:** AXI bus saturated (good!)

### Write Path
- **Effective Pipeline:** 256 (limited by configuration)
- **Cycles per Burst:** 16.8 cycles
- **Bandwidth:** 61.02 GB/s (100.0% of AXI peak)
- **Bottleneck:** AXI bus saturated (good!)

## Multi-Channel Scaling Analysis

|   Channels |   Read_BW |   Write_BW |   DMA_Throughput |   Read_Eff |   Write_Eff | Bottleneck   |
|-----------:|----------:|-----------:|-----------------:|-----------:|------------:|:-------------|
|          1 |      57.6 |       57.6 |             57.6 |        100 |         100 | balanced     |
|          2 |      57.6 |       57.6 |             57.6 |        100 |         100 | balanced     |
|          4 |      57.6 |       57.6 |             57.6 |        100 |         100 | balanced     |
|          8 |      57.6 |       57.6 |             57.6 |        100 |         100 | balanced     |

## Bottleneck Explanation

**Balanced Performance**

- Read and write bandwidth equal: 57.60 GB/s
- No single-path bottleneck - optimal balance achieved
- AXI bus saturated at 57.60 GB/s

## Design Limitations


## Optimization Recommendations

- **For analysis only** - 16x SRAM increase (64 KB → 1024 KB) not recommended
- **Use channel parallelism instead** (MEDIUM/HIGH modes with multiple channels)
- **Increase payload size** to take advantage of larger burst capability (256 beats)


================================================================================

# Memory Latency Sensitivity Analysis: PERFECT Mode

**Payload:** 1024 bytes


---

## Single Channel Performance vs Latency

|   Latency_Cycles |   Read_BW_GBps |   Write_BW_GBps |   Read_Cycles_per_Burst |   Write_Cycles_per_Burst | Read_Limited_By   | Write_Limited_By   |
|-----------------:|---------------:|----------------:|------------------------:|-------------------------:|:------------------|:-------------------|
|               50 |        63.2282 |         63.2282 |                 16.1953 |                  16.1953 | AXI_peak          | AXI_peak           |
|              100 |        62.4747 |         62.4747 |                 16.3906 |                  16.3906 | AXI_peak          | AXI_peak           |
|              200 |        61.0205 |         61.0205 |                 16.7812 |                  16.7812 | AXI_peak          | AXI_peak           |
|              400 |        58.306  |         58.306  |                 17.5625 |                  17.5625 | AXI_peak          | AXI_peak           |
|              800 |        53.5425 |         53.5425 |                 19.125  |                  19.125  | timing            | timing             |

## Key Insights

- **PERFECT mode** pipelining effectiveness vs latency:
  - Unlimited pipeline: Completely hides latency up to SRAM capacity
  - Performance remains constant until SRAM saturation


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

## PERFECT Mode Performance
- **Single Channel:** 61.02 GB/s (read), 61.02 GB/s (write)
- **8 Channels:** 57.60 GB/s DMA throughput
- **Efficiency:** 100.0% of AXI peak
- **Bottleneck:** balanced

## When to Use This Mode
- **Theoretical analysis:** Shows ultimate limits
- **Design exploration:** Understand SRAM sizing requirements
- **NOT recommended for implementation:** Excessive SRAM cost
