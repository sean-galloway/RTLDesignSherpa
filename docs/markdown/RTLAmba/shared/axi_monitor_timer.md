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

# AXI Monitor Timer

**Module:** `axi_monitor_timer.sv`
**Location:** `rtl/amba/shared/`
**Status:** Production Ready

---

## Overview

The AXI Monitor Timer provides frequency-invariant timing for the AXI monitor infrastructure by generating consistent timer ticks regardless of the system clock frequency. It combines a cycle-accurate global timestamp counter with a frequency-invariant timer tick generator to support both precise latency measurement and consistent timeout detection across different clock frequencies.

### Key Features

- Frequency-invariant timer tick generation
- Configurable tick frequency via 4-bit selection
- Global timestamp counter (32-bit cycle counter)
- Uses counter_freq_invariant for portable timing
- Zero-latency timestamp (combinational output)
- Consistent timeout behavior across frequencies
- Single clock domain operation
- Minimal resource utilization

---

## Module Purpose

The Timer module solves a critical portability problem in monitor architectures: timeout thresholds specified in cycles become frequency-dependent, requiring reconfiguration when clock frequency changes. By using frequency-invariant timer ticks, timeout thresholds can be specified in abstract "ticks" that represent consistent time periods regardless of the underlying clock frequency.

The global timestamp counter provides cycle-accurate timing for latency measurement and performance analysis, while the timer tick output enables timeout detection with configurable resolution.

---

## Parameters

This module has no parameters. All configuration is runtime via cfg_freq_sel.

---

## Port Groups

### Global Clock and Reset

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| aclk | input | 1 | Clock signal |
| aresetn | input | 1 | Active-low asynchronous reset |

### Timer Configuration

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| cfg_freq_sel | input | 4 | Frequency selection for timer tick (0-15) |

### Timer Outputs

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| timer_tick | output | 1 | Timer tick signal (frequency-invariant) |
| timestamp | output | 32 | Global timestamp counter (cycle count) |

---

## Functional Description

The Timer module implements two independent timing functions that work together to support the monitor infrastructure.

### Global Timestamp Counter

The timestamp counter provides cycle-accurate time reference:

**Implementation:**
- 32-bit up-counter
- Increments every clock cycle
- Resets to zero on aresetn assertion
- Registered output (r_timestamp)

**Purpose:**
- Transaction timestamp marking (addr_timestamp, data_timestamp, resp_timestamp)
- Latency calculation (timestamp differences)
- Performance metric computation
- Event correlation across transactions

**Range and Wraparound:**
- Maximum count: 2^32 - 1 = 4,294,967,295 cycles
- At 1 GHz: ~4.3 seconds before wraparound
- At 100 MHz: ~43 seconds before wraparound
- Wraparound handled naturally in latency calculations (32-bit arithmetic)

**Usage Example:**
```systemverilog
// Transaction manager records timestamp
addr_timestamp <= timestamp;  // When address phase completes

// Later, calculate latency
latency = data_timestamp - addr_timestamp;  // Handles wraparound
```

### Frequency-Invariant Timer Tick

The timer tick provides consistent periodic signal across frequencies:

**Implementation:**
- Uses counter_freq_invariant module from rtl/common/
- Configured via cfg_freq_sel (4-bit selection: 0-15)
- Generates single-cycle pulse (timer_tick) at configured interval
- Combinational output (w_timer_tick)

**Frequency Selection:**
The cfg_freq_sel value selects from predefined frequency ratios:

| cfg_freq_sel | Tick Period (cycles) | 100 MHz Period | 1 GHz Period |
|--------------|---------------------|----------------|--------------|
| 0 | 1 | 10 ns | 1 ns |
| 1 | 2 | 20 ns | 2 ns |
| 2 | 4 | 40 ns | 4 ns |
| 3 | 8 | 80 ns | 8 ns |
| 4 | 16 | 160 ns | 16 ns |
| 5 | 32 | 320 ns | 32 ns |
| 6 | 64 | 640 ns | 64 ns |
| 7 | 128 | 1.28 us | 128 ns |
| 8 | 256 | 2.56 us | 256 ns |
| 9 | 512 | 5.12 us | 512 ns |
| 10 | 1024 | 10.24 us | 1.024 us |
| 11 | 2048 | 20.48 us | 2.048 us |
| 12 | 4096 | 40.96 us | 4.096 us |
| 13 | 8192 | 81.92 us | 8.192 us |
| 14 | 16384 | 163.84 us | 16.384 us |
| 15 | 32768 | 327.68 us | 32.768 us |

**Purpose:**
- Timeout detection timing base
- Consistent timeout duration across frequencies
- Periodic performance metric reporting
- Threshold comparison timing

**Tick Characteristics:**
- Single cycle pulse (asserts high for 1 cycle)
- Precise period (no jitter or drift)
- Synchronous to aclk
- Immediately reflects cfg_freq_sel changes

### Counter Freq Invariant Integration

The module instantiates counter_freq_invariant with specific configuration:

**Instance Configuration:**
```systemverilog
counter_freq_invariant #(
    .COUNTER_WIDTH (1),        // Only need 1-bit counter (tick pulse)
    .PRESCALER_MAX (65536)     // Maximum prescaler value
) timer_counter (
    .clk         (aclk),
    .rst_n       (aresetn),
    .sync_reset_n(1'b1),       // No sync reset
    .freq_sel    (cfg_freq_sel),
    .tick        (w_timer_tick),
    .counter     ()             // Counter output unused
);
```

**Design Rationale:**
- COUNTER_WIDTH=1: Only tick pulse needed, not counter value
- PRESCALER_MAX=65536: Supports full frequency selection range
- sync_reset_n tied high: No need for synchronous reset
- counter output unused: Only tick signal required

**counter_freq_invariant Module:**
- Located in rtl/common/counter_freq_invariant.sv
- Implements programmable frequency divider
- Uses binary counter with configurable threshold
- Generates precise periodic pulses
- See rtl/common/ documentation for detailed behavior

---

## Integration with Monitor Architecture

The Timer module provides fundamental timing services to the entire monitor infrastructure.

### Output Integration

**To Transaction Manager (axi_monitor_trans_mgr):**
- timestamp output provides time reference
- Used to mark transaction phase completion times
- Enables latency calculation in reporter

**To Timeout Module (axi_monitor_timeout):**
- timer_tick output drives timeout detection
- Timeout module increments counters on each tick
- Enables frequency-invariant timeout thresholds

**To Reporter Module (axi_monitor_reporter):**
- Indirect use via transaction table timestamps
- Reporter calculates latencies from timestamp differences
- Performance metrics derived from timestamp data

### Configuration Strategy

**High-Frequency Systems (>500 MHz):**
```systemverilog
cfg_freq_sel = 4'd8;  // 256 cycles (~256ns @ 1GHz)
```
Provides fine timeout granularity without excessive tick rate.

**Medium-Frequency Systems (100-500 MHz):**
```systemverilog
cfg_freq_sel = 4'd6;  // 64 cycles (~640ns @ 100MHz)
```
Balanced granularity and overhead.

**Low-Frequency Systems (<100 MHz):**
```systemverilog
cfg_freq_sel = 4'd4;  // 16 cycles (~160ns @ 100MHz)
```
Finer granularity needed due to lower clock frequency.

**General Guideline:**
Select cfg_freq_sel such that:
```
Tick Period = Target Timeout / (Max Threshold Value)
```
For example, 10us timeout with max threshold=10:
```
Tick Period = 10us / 10 = 1us
@ 100MHz: 1us = 100 cycles -> cfg_freq_sel = 10 (1024 cycles ~ 10us)
```

---

## Usage Example

```systemverilog
// Timer module instance
axi_monitor_timer u_timer (
    .aclk         (axi_clk),
    .aresetn      (axi_rst_n),

    // Frequency selection
    .cfg_freq_sel (4'd6),  // 64 cycles per tick

    // Timer outputs
    .timer_tick   (timer_tick),
    .timestamp    (global_timestamp)
);

// Transaction manager uses timestamp
axi_monitor_trans_mgr #(
    .MAX_TRANSACTIONS (16),
    // ...
) u_trans_mgr (
    .aclk         (axi_clk),
    .aresetn      (axi_rst_n),

    // Timestamp input
    .timestamp    (global_timestamp),

    // ... other connections
);

// Timeout module uses timer tick
axi_monitor_timeout #(
    .MAX_TRANSACTIONS (16),
    // ...
) u_timeout (
    .aclk         (axi_clk),
    .aresetn      (axi_rst_n),

    // Timer tick input
    .timer_tick   (timer_tick),

    // Timeout thresholds (in ticks)
    .cfg_addr_cnt (4'd8),   // 8 ticks
    .cfg_data_cnt (4'd12),  // 12 ticks
    .cfg_resp_cnt (4'd8),   // 8 ticks

    // ... other connections
);

// Timeout duration calculation
// At cfg_freq_sel=6 (64 cycles/tick):
// addr timeout = 8 ticks * 64 cycles = 512 cycles
// data timeout = 12 ticks * 64 cycles = 768 cycles
// resp timeout = 8 ticks * 64 cycles = 512 cycles
```

---

## Design Notes

### Timestamp Wraparound Handling

The 32-bit timestamp counter wraps to zero after ~4.3 seconds at 1 GHz:

**Latency Calculation:**
Latency calculations naturally handle wraparound through unsigned arithmetic:
```systemverilog
latency = end_timestamp - start_timestamp;  // Works across wraparound
```

**Example:**
```
start_timestamp = 0xFFFF_FFFF (max value)
end_timestamp   = 0x0000_0005 (after wraparound)
latency = 0x0000_0005 - 0xFFFF_FFFF = 0x0000_0006 (6 cycles)
```

**Limitations:**
- Maximum measurable latency: 2^31 cycles (half of counter range)
- Exceeding this causes incorrect results
- In practice, transaction latencies << 2^31 cycles

**Mitigation:**
If longer-term timestamps needed, extend timestamp to 64 bits (requires parameter addition).

### Frequency Selection Trade-offs

Choosing cfg_freq_sel involves trade-offs:

**Fine Granularity (Low cfg_freq_sel):**
- Advantages: Precise timeout detection, responsive system
- Disadvantages: High tick rate, more dynamic power
- Use when: Fast timeout response required

**Coarse Granularity (High cfg_freq_sel):**
- Advantages: Lower tick rate, reduced power
- Disadvantages: Coarse timeout resolution, slower detection
- Use when: Power-sensitive or timeout precision less critical

**Recommended Range:**
cfg_freq_sel = 4-8 for most applications (16-256 cycles per tick)

### Dynamic Frequency Scaling

When system clock frequency changes (DFS), consider:

**Timestamp Counter:**
- Continues counting cycles
- Latency measurements in cycles, not absolute time
- Latency will vary with frequency changes

**Timer Tick:**
- Tick period in cycles remains constant
- Tick period in absolute time changes
- May need to adjust cfg_freq_sel to maintain desired timeout duration

**Recommendation:**
If DFS used, adjust cfg_freq_sel proportionally to maintain consistent timeout durations in absolute time.

### Zero Timestamp on Reset

The timestamp counter resets to zero on aresetn assertion:

**Implications:**
- First transaction after reset has timestamp near zero
- Timestamps from before reset invalid after reset
- No timestamp preservation across resets

**Best Practice:**
Reset all monitors simultaneously to ensure consistent timestamp domain across the system.

### Timer Tick Duty Cycle

The timer_tick output is a single-cycle pulse:

**Characteristics:**
- High for exactly 1 cycle
- Low for (tick_period - 1) cycles
- Duty cycle = 1 / tick_period

**Usage:**
Modules should use timer_tick as an enable/trigger signal, not as a clock. It's synchronous to aclk but much slower, making it unsuitable as a clock source.

### Resource Utilization

The timer module has minimal resource cost:

**Registers:**
- 32-bit timestamp counter
- 1-bit counter in counter_freq_invariant
- Prescaler state in counter_freq_invariant

**Combinational Logic:**
- Increment logic for timestamp
- Frequency divider in counter_freq_invariant

**Estimated Area:**
- ~50 FFs (flip-flops)
- ~100 LUTs (look-up tables)
- Negligible relative to full monitor

### Multiple Timer Instances

Each monitor instance can have its own timer if needed:

**Advantages of Separate Timers:**
- Independent frequency selection per monitor
- No timing constraints between monitors
- Simpler physical design (local timing)

**Advantages of Shared Timer:**
- Single timestamp domain across monitors
- Easier event correlation
- Reduced resource utilization

**Recommendation:**
Use shared timer unless monitors operate at different frequencies or in different clock domains.

---

## Related Modules

### Used By
- axi_monitor_base.sv (primary user)
- axi_monitor_filtered.sv (via axi_monitor_base)
- All AXI/AXIL monitor variants

### Uses
- counter_freq_invariant.sv (from rtl/common/)
- Provides frequency-invariant counting capability

### Critical Interfaces
- **To axi_monitor_trans_mgr:**
  - timestamp output (32-bit time reference)
- **To axi_monitor_timeout:**
  - timer_tick output (timeout trigger)

### Related Infrastructure
- axi_monitor_trans_mgr.sv (timestamp consumer)
- axi_monitor_timeout.sv (timer tick consumer)
- axi_monitor_reporter.sv (indirect via timestamps)

---

## References

### Specifications
- Base Module: [axi_monitor_base.md](axi_monitor_base.md)
- Timeout Module: [axi_monitor_timeout.md](axi_monitor_timeout.md)
- Transaction Manager: [axi_monitor_trans_mgr.md](axi_monitor_trans_mgr.md)

### Source Code
- RTL: `rtl/amba/shared/axi_monitor_timer.sv`
- Counter: `rtl/common/counter_freq_invariant.sv`
- Documentation: `docs/markdown/RTLCommon/counter_freq_invariant.md`
- Tests: `val/amba/test_axi4_master_rd_mon.py` (integration)

### Configuration Guides
- [Monitor Base Configuration](./axi_monitor_base.md) - Timeout configuration
- `rtl/amba/PRD.md` - Subsystem requirements

---

**Last Updated:** 2025-10-24

---

## Navigation

- [Back to axi_monitor_base](axi_monitor_base.md)
- [Previous: axi_monitor_timeout](axi_monitor_timeout.md)
- [Back to Shared Infrastructure Index](README.md)
- [Back to RTLAmba Index](../index.md)
