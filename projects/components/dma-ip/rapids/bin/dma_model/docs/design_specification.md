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

# AXI4 Memory Interface Design Specification

## Overview

This document describes the current design of the AXI4 memory interface, including separate read and write paths, SRAM buffering, and drain mechanisms.

---

## System Parameters

### AXI Interface
- **Bus Width**: 512 bits (64 bytes per beat)
- **Frequency**: 1.0 GHz (1 cycle = 1 ns)
- **Peak Theoretical Bandwidth**: 64 GB/s
- **Protocol Efficiency (α)**: 0.9
- **Effective Peak Bandwidth**: 57.6 GB/s
- **Memory Latency**: 200 cycles (fixed)

### Physical Constraints
- **Physical Slots (Custom Side)**: 16 slots maximum
- **Per-Slot Drain Rate**: 4 GB/s (1 beat / 16 cycles)
- **Total Custom Capacity**: 64 GB/s (16 slots × 4 GB/s)

---

## Read Path Specification

### Read Operation Parameters
- **Burst Size**: 2048 bytes (2 KB)
- **Burst Length**: 32 beats (2048 / 64)
- **Pipelining**: **DISABLED** (stop-and-wait)
- **Drain Mode**: **Store-and-Forward**

### Read SRAM Architecture
Each read channel has its own dedicated SRAM:
- **Configuration**: Ping-Pong (2 slots per channel)
- **Slot Size**: 2 KB per slot
- **Total per Channel**: 4 KB (2 × 2 KB)
- **Slots**: Slot A and Slot B
- **Access Pattern**: While one slot drains, the other can be filled

### Read Timing Breakdown (Per Burst, No Pipelining)

```
Total Time = Latency + Data_Return + Drain_Time
           = 200 + 32 + 512 = 744 cycles
```

#### Phase 1: Request & Latency (200 cycles)
- AXI read request issued
- Wait for memory latency
- **Duration**: 200 cycles

#### Phase 2: Data Return (32 cycles)
- Memory returns data over AXI
- Data arrives at 1 beat/cycle
- All 32 beats must arrive before drain can begin
- **Duration**: 32 cycles (burst_length cycles)

#### Phase 3: Store-and-Forward Drain (512 cycles)
- **Critical Constraint**: Entire burst must arrive before draining starts
- Data drains to custom/user side at limited rate
- **Drain Rate**: 1 beat / 16 cycles = 4 GB/s
- **Duration**: 32 beats × 16 cycles/beat = 512 cycles

### Read Performance Calculation

**Single Channel Bandwidth (No Pipelining)**:
```
B_channel = (Payload × Frequency) / Total_Time
          = (2048 bytes × 1 GHz) / 744 cycles
          = 2.753 GB/s
```

**16 Channel Aggregate**:
```
Total_BW = 16 channels × 2.753 GB/s
         = 44.05 GB/s
Limited by: per-channel drain rate × channels
```

### Read Data Flow

```
┌─────────────────────────────────────────────────────────────────┐
│                         READ CHANNEL N                          │
├─────────────────────────────────────────────────────────────────┤
│                                                                 │
│  [AXI Master] ──request──> [Memory]                            │
│       │                       │                                 │
│       │←────── 200 cycles ────┤ (latency)                      │
│       │                       │                                 │
│       │←─── 32 beats @ 1/cyc ─┤ (data return)                  │
│       ↓                                                         │
│  ┌─────────────────────────────────────┐                       │
│  │  PING-PONG SRAM (4 KB total)       │                       │
│  │  ┌──────────┐    ┌──────────┐      │                       │
│  │  │ Slot A   │    │ Slot B   │      │                       │
│  │  │ 2 KB     │    │ 2 KB     │      │                       │
│  │  └────┬─────┘    └────┬─────┘      │                       │
│  └───────┼───────────────┼─────────────┘                       │
│          │ (only one slot drains at a time)                    │
│          │                                                      │
│          └──> [Custom/User Side]                               │
│               Drain: 1 beat / 16 cycles = 4 GB/s               │
│               Duration: 512 cycles for 2KB                      │
│                                                                 │
└─────────────────────────────────────────────────────────────────┘
```

### Read Channel State Machine

```
State: IDLE
  ↓ (issue read request)
State: WAITING_LATENCY (200 cycles)
  ↓ (latency complete)
State: RECEIVING_DATA (32 cycles, 1 beat/cycle)
  ↓ (all data received)
State: DRAINING (512 cycles, 1 beat/16 cycles)
  ↓ (drain complete)
State: IDLE
```

**Key Constraint**: Next read cannot start until current burst is FULLY DRAINED.

---

## Write Path Specification

### Write Operation Parameters
- **Burst Size**: 256 bytes
- **Burst Length**: 4 beats (256 / 64)
- **Max Outstanding**: 32 writes system-wide
- **Pipelining**: Limited by outstanding burst count

### Write SRAM Architecture
Each write channel has its own dedicated SRAM:
- **Configuration**: Similar ping-pong or buffering
- **Buffer Size**: Sufficient for 256-byte bursts
- **Access Pattern**: Custom side fills buffer, AXI drains to memory

### Write Timing Breakdown

```
Total Time = Fill_Time + Latency + Data_Send
```

#### Phase 1: Fill from Custom Side
- Custom side writes data into SRAM buffer
- **Fill Rate**: Depends on custom side source rate
- **Duration**: Variable, assume instantaneous for modeling

#### Phase 2: Memory Write
- AXI write request with data
- **Latency**: 200 cycles
- **Data Transmission**: 4 beats @ 1 beat/cycle
- **Duration**: 200 + 4 = 204 cycles

### Write Performance Calculation

**Single Channel Bandwidth**:
```
B_channel = (256 bytes × 1 GHz) / 204 cycles
          = 1.255 GB/s
```

**With 32 Outstanding Writes**:
- Can have up to 32 write transactions in flight
- Enables much higher aggregate throughput
- Limited by AXI peak bandwidth

### Write Data Flow

```
┌─────────────────────────────────────────────────────────────────┐
│                        WRITE CHANNEL N                          │
├─────────────────────────────────────────────────────────────────┤
│                                                                 │
│  [Custom/User Side] ──data──> [SRAM Buffer]                    │
│                                    │                            │
│                                    │ (256 bytes ready)          │
│                                    ↓                            │
│                               [AXI Master]                      │
│                                    │                            │
│                                    │ (write request + data)     │
│                                    ↓                            │
│                               [Memory]                          │
│                          (latency + 4 beats)                    │
│                                                                 │
└─────────────────────────────────────────────────────────────────┘
```

### Write Outstanding Burst Management

```
System-Wide Outstanding Burst Tracker:
- Max: 32 outstanding writes
- Each write consumes 1 outstanding slot
- Slot released when write completes (after latency + transmission)

Per-Channel:
- Can issue writes as long as system has outstanding slots available
- Multiple channels share the 32-slot pool
```

---

## Channel Independence

### Critical Design Principle
**Each channel operates independently**:

1. **Separate SRAM**: Each channel has its own 4KB SRAM (read) or buffer (write)
2. **Independent Drain**: Each read channel drains at 4 GB/s independently
3. **No Channel Interaction**: Channels do not block each other (except for shared AXI bandwidth)
4. **Parallel Operation**: With 16 channels, all can drain simultaneously at 4 GB/s each

### Aggregate Performance
```
Total System BW = min(
    Sum of channel bandwidths,
    Custom side capacity (64 GB/s),
    AXI peak bandwidth (57.6 GB/s)
)
```

---

## Current Design Limitations

### Read Path Bottlenecks

1. **No Pipelining**
   - Must wait for full burst cycle (744 cycles) before next request
   - Single channel: only 2.753 GB/s (far below 4 GB/s drain capacity)

2. **Store-and-Forward Drain**
   - Cannot begin draining until all 32 beats arrive
   - Wastes 32 cycles waiting for data return
   - Adds sequential dependency

3. **Ping-Pong SRAM Limitation**
   - Only 2 bursts can be buffered (one per slot)
   - Limits potential pipeline depth to 2
   - For 2KB bursts: each burst occupies entire 2KB slot

### Write Path Bottlenecks

1. **Outstanding Burst Limit**
   - 32 writes shared across all channels
   - With many channels, each gets few outstanding slots
   - Example: 16 channels → 2 outstanding per channel average

2. **Small Burst Size**
   - 256 bytes is small
   - More overhead from burst management

---

## Performance Summary

### Current Design (No Optimizations)

| Metric | Read | Write |
|--------|------|-------|
| Burst Size | 2048 bytes | 256 bytes |
| Single Channel BW | 2.753 GB/s | 1.255 GB/s |
| 16 Channel Aggregate | 44.05 GB/s | ~20 GB/s |
| Efficiency (vs AXI peak) | 76% | 35% |
| Primary Bottleneck | Drain time (no pipelining) | Outstanding limit |

### Target Performance
- **Goal**: 50+ GB/s aggregate read bandwidth
- **Current**: 44.05 GB/s
- **Gap**: Need ~6 GB/s improvement (14% gain)

---

## Key Takeaways

1. **Read channels are independent**: Each has its own 4KB SRAM and drains at 4 GB/s
2. **Store-and-forward is the bottleneck**: 512-cycle drain dominates timing
3. **No pipelining kills performance**: Single channel only achieves 2.753 GB/s (69% of 4 GB/s capacity)
4. **16 channels partially compensate**: Aggregate is 44 GB/s, but below target
5. **Optimizations needed**:
   - Enable pipelining (depth=4) → ~70% improvement
   - Streaming drain (saves 32 cycles) → ~5% improvement
   - Monolithic SRAM (better for smaller payloads) → variable improvement

---

## Next Steps for Modeling

To accurately model this system:

1. **Discrete-Event Simulation (SimPy)**:
   - Model each channel as independent process
   - Explicit state machines (IDLE → WAITING → RECEIVING → DRAINING)
   - Track SRAM occupancy and outstanding bursts
   - Measure actual throughput over time

2. **Incremental Optimizations**:
   - Baseline: Current design (no pipelining, store-and-forward)
   - Opt 1: Add pipelining (depth=2, then 4)
   - Opt 2: Enable streaming drain
   - Opt 3: Switch to monolithic SRAM
   - Opt 4: Combine all optimizations

3. **Validation**:
   - Compare SimPy results with analytical model
   - Verify timing matches (744 cycles per burst baseline)
   - Check that 16 channels → 44 GB/s
   - Ensure optimizations produce expected gains
