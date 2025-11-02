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
cfg_compl_enable      = 0  // ⚠️ DISABLE to reduce congestion
cfg_timeout_enable    = 0  // Disable unless needed
cfg_threshold_enable  = 1  // Monitor latency thresholds
cfg_perf_enable       = 1  // Enable performance packets
cfg_debug_enable      = 0  // Disable unless needed
```

**Use Cases:**
- Performance benchmarking
- Latency measurement
- Throughput analysis
- System optimization

**Expected Packet Rate:** High (multiple packets per transaction)

**⚠️ Warning:** Performance packets can generate 5-10x more traffic than completion packets!

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

### Problem: Performance Packets Overwhelm Completions

The monitor uses a **priority-based packet arbiter**:

```
Priority Order (highest to lowest):
1. Error packets
2. Timeout packets
3. Completion packets    ← Can be starved!
4. Threshold packets
5. Performance packets   ← Generated continuously
```

**Performance packets** are generated:
- Every N cycles (based on `cfg_freq_sel`)
- For each active transaction
- On latency threshold crossings

With 8 concurrent transactions and `cfg_freq_sel=1` (every 50 cycles):
- **Performance mode:** 8 packets / 50 cycles = **160 packets/1000 cycles**
- **Completion mode:** 8 packets total = **8 packets/1000 cycles**

**Result:** Performance packets can generate **20x more traffic**, starving completion packets!

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

// Only report SLVERR and DECERR (not orphans or protocol errors)
cfg_error_mask = 2'b11;  // Mask specific error types

// Reduce performance packet rate
cfg_freq_sel = 4;  // Report every 200 cycles instead of 50
```

**Benefits:**
- Reduced packet volume
- Focus on critical events
- Configurable sensitivity

---

### Strategy 4: Frequency Reduction

**Reduce performance packet generation frequency:**

```systemverilog
cfg_freq_sel value | Packet period | Packets/sec (100 MHz)
-------------------|---------------|---------------------
       0           |   10 cycles   |  10M packets/sec
       1           |   50 cycles   |   2M packets/sec
       2           |  100 cycles   |   1M packets/sec
       3           |  200 cycles   | 500K packets/sec
       4           |  500 cycles   | 200K packets/sec
```

**Rule of thumb:** Set `cfg_freq_sel` so performance packets are generated **slower than transaction completion rate**.

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
// Expecting completion packets with perf enabled
cfg_compl_enable = 1;
cfg_perf_enable = 1;  // This will starve completions!
```

**Problem:** Completion packets never arrive, tests fail incorrectly

---

### ❌ Mistake 3: Wrong Frequency Selection

```systemverilog
// Generating performance packets too fast
cfg_perf_enable = 1;
cfg_freq_sel = 0;  // Every 10 cycles - TOO FAST!
```

**Problem:** 100K+ packets per transaction, simulation slowdown

---

## Summary

| Configuration | Error | Compl | Timeout | Thresh | Perf | Use Case |
|--------------|-------|-------|---------|--------|------|----------|
| **Functional** | ✅ | ✅ | ✅ | ✅ | ❌ | Verification, debug |
| **Performance** | ✅ | ❌ | ❌ | ✅ | ✅ | Optimization |
| **Production** | ✅ | ❌ | ✅ | ⚠️ | ❌ | Chip operation |

**Key Takeaway:** Never enable completions and performance simultaneously in production tests!

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