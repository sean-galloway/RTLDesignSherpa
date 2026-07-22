# AXI Monitor Configuration Guide

## Overview

The AXI monitor supports multiple packet types for tracking different aspects of AXI transactions. However, **enabling all packet types simultaneously can overwhelm the monitor bus**, causing packet loss and incorrect behavior.

This guide provides best practices for configuring the monitor based on your specific use case.

---

## Monitor Packet Types

The AXI monitor generates the following packet types:

| Packet Type | Purpose | Use Case |
|------------|---------|----------|
| **Error** | Protocol violations, response errors | Functional debug, compliance testing |
| **Completion** | Transaction completion tracking | Functional verification, transaction counting |
| **Timeout** | Stuck transactions, handshake timeouts | Deadlock detection, performance issues |
| **Threshold** | Active transaction count, latency limits | System health monitoring |
| **Performance** | Latency metrics, throughput, counters | Performance analysis, optimization |
| **Debug** | State changes, pipeline events | Deep debug, waveform correlation |

---

## Configuration Modes

### Mode 1: Functional Debug (Recommended for Verification)

**Goal:** Track transaction completions, errors, and protocol violations

**Configuration:**
```systemverilog
cfg_error_enable      = 1  // Detect SLVERR, DECERR, orphans
cfg_compl_enable      = 1  // Track transaction completions
cfg_timeout_enable    = 1  // Detect stuck transactions
cfg_threshold_enable  = 1  // Monitor active transaction count
cfg_perf_enable       = 0  // ⚠️ DISABLE to avoid monbus congestion
cfg_debug_enable      = 0  // Disable unless doing deep debug
```

**Use Cases:**
- Functional verification
- Protocol compliance testing
- Error detection and handling
- Transaction ordering validation

**Expected Packet Rate:** Low to medium (1-2 packets per transaction)

---

### Mode 2: Performance Analysis

**Goal:** Measure latency, throughput, and performance metrics

**Configuration:**
```systemverilog
cfg_error_enable      = 1  // Still track errors
cfg_compl_enable      = 0  // DISABLE to reduce congestion (safe: see note)
cfg_timeout_enable    = 0  // Disable unless needed
cfg_threshold_enable  = 1  // Monitor latency thresholds
cfg_perf_enable       = 1  // Enable performance packets
cfg_debug_enable      = 0  // Disable unless needed
```

**Runtime-disable note (important history):** this mode runtime-disables
completions while the completion cone is compiled in
(`ENABLE_COMPL_LOGIC=1`). Since commit `95c9490a` this is safe: terminal
transaction-table entries of a disabled class **auto-retire** — released
without emitting a packet or bumping counters — so the table cannot leak.
Before that commit this exact configuration leaked every completed entry
and wedged `block_ready` (and with it the monitored bus) after roughly
`MAX_TRANSACTIONS` transactions. If you need the lifetime completion
counters (`transaction_count`) to keep advancing while suppressing the
packets, use the `cfg_axi_pkt_mask` drop mask in `axi_monitor_filtered`
instead of `cfg_compl_enable=0`.

**Use Cases:**
- Performance benchmarking
- Latency measurement
- Throughput analysis
- System optimization

**Expected Packet Rate:** Low (periodic count rollups; the perf sub-block
emits a completed-count and an error-count packet paced by output-path
idleness, not per transaction)

---

### Mode 3: Deep Debug (Use Sparingly)

**Goal:** Maximum visibility for debugging complex issues

**Configuration:**
```systemverilog
cfg_error_enable      = 1
cfg_compl_enable      = 1
cfg_timeout_enable    = 1
cfg_threshold_enable  = 0  // ⚠️ DISABLE thresholds
cfg_perf_enable       = 0  // ⚠️ DISABLE performance
cfg_debug_enable      = 1  // Enable debug packets
cfg_debug_level       = 2  // Medium verbosity
cfg_debug_mask        = 0xFF  // All events
```

**Use Cases:**
- Debugging intermittent failures
- Root cause analysis
- Waveform correlation

**Expected Packet Rate:** Very high

**⚠️ Warning:** Only use for short test sequences! The monitor bus WILL overflow.

---

## Monitor Bus Congestion: Why It Happens

### The Reporter's Priority Order and Bandwidth Limit

The reporter (`axi_monitor_reporter`) emits packets with a fixed priority:

```
Priority Order (highest to lowest):
1. Error packets       ─┐
2. Timeout packets      ├─ via the reporter FIFO
3. Completion packets  ─┘
4. Threshold packets   ─┐
5. Performance packets  ├─ bypass sources; emit only when the
6. Debug packets       ─┘  FIFO path is idle
```

Two consequences:

- **The bus sustains at most 1 packet per 2 cycles** (the registered
  output stage cannot reload on the same cycle its packet is accepted).
  A completion per transaction plus errors already approaches this under
  back-to-back single-beat traffic — anything more congests.
- **Completions cannot be starved by perf packets** — it is the other way
  around: threshold/perf/debug packets emit only when the FIFO path
  (error/timeout/completion) is idle, so under continuous completion
  traffic the perf rollups may be delayed indefinitely. Disabling
  completions in performance mode exists to give the perf/threshold
  bypass sources bus access, and to cut total packet volume.

**Performance packets** are periodic count rollups (a completed-count
packet and an error-count packet from `axi_monitor_reporter_perf`), paced
by a small FSM that only advances while the output path is idle — they are
not per-transaction.

Congestion does not leak transaction-table slots: an entry whose packet
loses the FIFO race is retried until it reports (or auto-retires if its
class is disabled). The failure mode is delayed/dropped telemetry, not a
stalled bus.

---

## Real-World Filtering Strategies

### Strategy 1: Temporal Filtering (Recommended)

**Switch configurations dynamically based on test phase:**

```python
# Phase 1: Functional verification (completions + errors)
configure_monitor(compl=1, perf=0)
run_functional_tests()

# Phase 2: Performance analysis (perf only)
configure_monitor(compl=0, perf=1)
run_performance_tests()
```

**Benefits:**
- No packet congestion
- Clean separation of concerns
- Faster simulation

---

### Strategy 2: Spatial Filtering

**Use different configurations for different monitors:**

```systemverilog
// Master 0: Track errors and completions
axi_master_0_monitor.cfg_compl_enable = 1;
axi_master_0_monitor.cfg_perf_enable = 0;

// Master 1: Track performance only
axi_master_1_monitor.cfg_compl_enable = 0;
axi_master_1_monitor.cfg_perf_enable = 1;

// Slave: Track errors only
axi_slave_monitor.cfg_compl_enable = 0;
axi_slave_monitor.cfg_perf_enable = 0;
axi_slave_monitor.cfg_error_enable = 1;
```

**Benefits:**
- Distributed monitoring
- Reduced per-monitor traffic
- Targeted analysis

---

### Strategy 3: Event Filtering (Advanced)

**Use threshold and mask registers to filter specific events:**

```systemverilog
// Only report transactions with latency > 1000 cycles
cfg_latency_threshold = 1000;
cfg_threshold_enable = 1;

// Drop selected error event codes (16-bit drop mask indexed by
// event_code[3:0]; a set bit DROPS that event)
cfg_axi_error_mask = 16'h000C;  // drop orphans (codes 2,3), keep SLVERR/DECERR (0,1)
```

**Benefits:**
- Reduced packet volume
- Focus on critical events
- Configurable sensitivity

---

### Strategy 4: Timer Scaling (`cfg_freq_sel`)

`cfg_freq_sel` selects the tick period of the frequency-invariant timer
(`axi_monitor_timer` / `counter_freq_invariant`, 16 entries spanning the
configured 5-220 MHz range by default). It scales the **timeout phase
counters** (`cfg_addr/data/resp_cnt`, and the wrappers' unified
`cfg_timeout_cycles`) so timeout thresholds stay consistent across clock
frequencies. It does **not** pace performance-packet emission — the perf
rollup FSM paces itself off output-path idleness. The wrappers tie
`cfg_freq_sel = 4'b0001` internally.

---

## Testing Recommendations

### For Verification Engineers

**Run separate test configurations:**

```bash
# Test 1: Functional correctness (completions, errors, bursts)
AXI_MON_TEST_MODE=completion pytest test_axi_monitor.py

# Test 2: Performance metrics (latency, throughput)
AXI_MON_TEST_MODE=performance pytest test_axi_monitor.py
```

**Benefits:**
- Faster test execution
- No packet loss
- Clear pass/fail criteria

---

### For System Integrators

**Recommended configuration for full-chip simulation:**

```systemverilog
// Critical interfaces: Enable completions and errors
cfg_error_enable = 1;
cfg_compl_enable = 1;
cfg_timeout_enable = 1;
cfg_perf_enable = 0;  // Disable performance

// Non-critical interfaces: Errors only
cfg_error_enable = 1;
cfg_compl_enable = 0;
cfg_timeout_enable = 0;
cfg_perf_enable = 0;
```

**Rationale:**
- Minimize simulation overhead
- Focus on functional correctness
- Catch protocol violations

---

## Common Mistakes

### ❌ Mistake 1: Enable Everything

```systemverilog
// DON'T DO THIS!
cfg_error_enable = 1;
cfg_compl_enable = 1;
cfg_timeout_enable = 1;
cfg_threshold_enable = 1;
cfg_perf_enable = 1;
cfg_debug_enable = 1;
```

**Problem:** Monitor bus congestion, packet loss, false failures

---

### ❌ Mistake 2: Ignore Packet Priority

```systemverilog
// Expecting timely perf rollups with completions enabled
cfg_compl_enable = 1;
cfg_perf_enable = 1;  // Perf is a bypass source — completions starve IT
```

**Problem:** The FIFO path (error/timeout/completion) always outranks the
threshold/perf/debug bypass sources, so under continuous completion
traffic the perf rollup packets may be delayed indefinitely — and total
volume presses against the 1-packet-per-2-cycles ceiling.

---

### ❌ Mistake 3: Undersizing MAX_TRANSACTIONS on a Shared Master

```systemverilog
// Monitor on a bus shared by 8 channels, sized to ONE channel's limit
MAX_TRANSACTIONS = 16  // per-channel outstanding, x8 channels in flight!
```

**Problem:** The monitor's `block_ready` throttles the shared master from
two channels up. Size `MAX_TRANSACTIONS` to `NUM_CHANNELS x per-channel
outstanding + margin` (this exact mistake shipped in stream_core; fixed in
`95c9490a`). Note tables of 16+ reserve 2 slots for the
saturation-recovery guarantee, and tables deeper than 64 need Verilator's
`--unroll-count` raised in sim builds.

---

## Summary

| Configuration | Error | Compl | Timeout | Thresh | Perf | Use Case |
|--------------|-------|-------|---------|--------|------|----------|
| **Functional** | ✅ | ✅ | ✅ | ✅ | ❌ | Verification, debug |
| **Performance** | ✅ | ❌ | ❌ | ✅ | ✅ | Optimization |
| **Production** | ✅ | ❌ | ✅ | ⚠️ | ❌ | Chip operation |

**Key Takeaway:** Avoid enabling completions and performance
simultaneously under heavy traffic — the bus sustains at most one packet
per two cycles, and the completion stream starves the perf rollups.
(Runtime-disabling either class is safe since `95c9490a`: disabled classes
auto-retire their table entries and cannot wedge the bus.)

---

## Test Example

The comprehensive AXI monitor test demonstrates this principle:

```python
# test_axi_monitor.py supports two modes:

# Mode 1: Completion-focused (default)
$ python test_axi_monitor.py
# → Tests completions, errors, bursts, ordering

# Mode 2: Performance-focused
$ AXI_MON_TEST_MODE=performance python test_axi_monitor.py
# → Tests latency, throughput, thresholds
```

This separation ensures reliable, deterministic test results without monitor bus congestion.