# V1 Read Engine Performance Baseline

**Configuration:** V1 (Low Performance - Single Outstanding Transaction)
**Architecture:** ENABLE_CMD_PIPELINE = 0
**Test Methodology:** 1000 commands issued, sustained bandwidth measured

---

## Executive Summary

V1 read engine uses a **single outstanding transaction** architecture:
- Blocks on completion before accepting next request
- Simple control logic (3 flags: r_ar_inflight, r_ar_valid, completion tracking)
- Tutorial-focused design for educational purposes

**Expected Performance:**
- DDR4 (100 cycle latency): ~0.14 beats/cycle
- SRAM (3 cycle latency): ~0.40 beats/cycle

---

## Test Configuration

| Parameter | Value |
|-----------|-------|
| Test Duration | 1000 commands |
| Command Pattern | Back-to-back issuance |
| Memory Model | AXI slave with configurable latency |
| Measurement | Sustained bandwidth (steady state) |

---

## Performance Results - Data Width 128 bits (16 bytes/beat)

### Burst Size: 256 bytes (16 beats)

| Memory Type | Latency (cycles) | Total Cycles | Total Beats | Bandwidth (beats/cycle) | Bandwidth (GB/s @ 200MHz) | Efficiency (%) |
|-------------|------------------|--------------|-------------|-------------------------|---------------------------|----------------|
| SRAM        | 3                | TBD          | 16,000      | TBD                     | TBD                       | TBD            |
| DDR3        | 60               | TBD          | 16,000      | TBD                     | TBD                       | TBD            |
| DDR4        | 100              | TBD          | 16,000      | TBD                     | TBD                       | TBD            |

### Burst Size: 512 bytes (32 beats)

| Memory Type | Latency (cycles) | Total Cycles | Total Beats | Bandwidth (beats/cycle) | Bandwidth (GB/s @ 200MHz) | Efficiency (%) |
|-------------|------------------|--------------|-------------|-------------------------|---------------------------|----------------|
| SRAM        | 3                | TBD          | 32,000      | TBD                     | TBD                       | TBD            |
| DDR3        | 60               | TBD          | 32,000      | TBD                     | TBD                       | TBD            |
| DDR4        | 100              | TBD          | 32,000      | TBD                     | TBD                       | TBD            |

### Burst Size: 1024 bytes (64 beats)

| Memory Type | Latency (cycles) | Total Cycles | Total Beats | Bandwidth (beats/cycle) | Bandwidth (GB/s @ 200MHz) | Efficiency (%) |
|-------------|------------------|--------------|-------------|-------------------------|---------------------------|----------------|
| SRAM        | 3                | TBD          | 64,000      | TBD                     | TBD                       | TBD            |
| DDR3        | 60               | TBD          | 64,000      | TBD                     | TBD                       | TBD            |
| DDR4        | 100              | TBD          | 64,000      | TBD                     | TBD                       | TBD            |

---

## Performance Results - Data Width 256 bits (32 bytes/beat)

### Burst Size: 256 bytes (8 beats)

| Memory Type | Latency (cycles) | Total Cycles | Total Beats | Bandwidth (beats/cycle) | Bandwidth (GB/s @ 200MHz) | Efficiency (%) |
|-------------|------------------|--------------|-------------|-------------------------|---------------------------|----------------|
| SRAM        | 3                | TBD          | 8,000       | TBD                     | TBD                       | TBD            |
| DDR3        | 60               | TBD          | 8,000       | TBD                     | TBD                       | TBD            |
| DDR4        | 100              | TBD          | 8,000       | TBD                     | TBD                       | TBD            |

### Burst Size: 512 bytes (16 beats)

| Memory Type | Latency (cycles) | Total Cycles | Total Beats | Bandwidth (beats/cycle) | Bandwidth (GB/s @ 200MHz) | Efficiency (%) |
|-------------|------------------|--------------|-------------|-------------------------|---------------------------|----------------|
| SRAM        | 3                | TBD          | 16,000      | TBD                     | TBD                       | TBD            |
| DDR3        | 60               | TBD          | 16,000      | TBD                     | TBD                       | TBD            |
| DDR4        | 100              | TBD          | 16,000      | TBD                     | TBD                       | TBD            |

### Burst Size: 1024 bytes (32 beats)

| Memory Type | Latency (cycles) | Total Cycles | Total Beats | Bandwidth (beats/cycle) | Bandwidth (GB/s @ 200MHz) | Efficiency (%) |
|-------------|------------------|--------------|-------------|-------------------------|---------------------------|----------------|
| SRAM        | 3                | TBD          | 32,000      | TBD                     | TBD                       | TBD            |
| DDR3        | 60               | TBD          | 32,000      | TBD                     | TBD                       | TBD            |
| DDR4        | 100              | TBD          | 32,000      | TBD                     | TBD                       | TBD            |

---

## Analysis

**Key Observations:**

1. **Latency Impact:** V1 performance degrades significantly with memory latency
   - Single outstanding transaction blocks until completion
   - No latency hiding capability

2. **Burst Length Effect:** Longer bursts improve efficiency
   - More data transferred per command overhead
   - Amortizes AR channel handshake latency

3. **Data Width Scaling:** Wider data paths improve absolute bandwidth
   - 256-bit achieves 2x bandwidth vs 128-bit at same efficiency

**Bottleneck Analysis:**

V1 architecture is limited by:
- Sequential operation (no pipelining)
- Memory latency directly impacts throughput
- No command queue to hide latency

**Path to Improvement (V2/V3):**

- V2 adds command pipelining → 6.7x improvement target
- V3 adds OOO completion → 7.0x improvement target

---

## Test Execution Details

**Test Script:** `test_performance_baseline_v1_read.py`
**DUT:** `axi_read_engine.sv` with `ENABLE_CMD_PIPELINE = 0`
**Testbench:** `DatapathRdTestTB` with performance measurement extensions

**Measurement Methodology:**
1. Issue 1000 consecutive read commands (back-to-back when ready)
2. Measure total cycles from first AR handshake to last R beat
3. Calculate sustained bandwidth = total_beats / total_cycles
4. Report efficiency = (sustained_bw / ideal_bw) * 100%

**Memory Model Configuration:**
- AXI slave with parameterizable read latency
- No backpressure (always ready after latency)
- Models DDR3/DDR4 timing characteristics

---

**Last Updated:** TBD (awaiting test execution)
**Test Status:** Template created, awaiting baseline measurement
**Next Steps:** Execute performance baseline tests and populate TBD values

