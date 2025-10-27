# Bridge QoS Starvation Prevention Design

**Document Version:** 1.0
**Last Updated:** 2025-10-27
**Status:** Design Proposal (Not Yet Implemented)

---

## Executive Summary

This document defines the aging counter mechanism for preventing QoS-based starvation in AXI crossbars. Without aging, low-priority masters can be starved indefinitely by continuous high-priority traffic, violating forward progress guarantees required for system reliability.

---

## Problem Statement

### Current QoS Arbitration (Without Aging)

**Weighted round-robin arbitration favors high-QoS masters:**
- CPU master (QoS=8) gets 8x more bandwidth than debug master (QoS=1)
- Under heavy CPU load, debug master may **never** get serviced
- Violates liveness property: every pending request must eventually complete

### Starvation Scenario Example

```
Time    CPU Request    Debug Request    Grant
----    -----------    -------------    -----
0       PENDING        PENDING          CPU   (QoS=8)
1       PENDING        PENDING          CPU   (QoS=8)
2       PENDING        PENDING          CPU   (QoS=8)
...
100     PENDING        PENDING          CPU   (QoS=8)
...
1000    PENDING        PENDING          CPU   (QoS=8)
∞       PENDING        PENDING          CPU   ← Debug STARVED!
```

**Result:** Debug master's request has been pending for 1000+ cycles but never granted.

---

## Solution: Aging Counters

### Concept

**Track request age and boost priority when too old:**
1. Each master has an **aging counter** that increments while request is pending
2. When counter reaches **aging threshold** (e.g., 256 cycles), boost QoS to maximum
3. Reset counter on grant
4. Ensures **bounded worst-case latency** for all masters

### Architecture

```
Master Input → [Aging Counter] → [QoS Boost Logic] → [Weighted Arbiter] → Grant
                     ↑                   |
                     |                   ↓
                  Request            Effective QoS
                  (Valid)            (Base or Boosted)
```

### Block Diagram

```
                    ┌─────────────────────────────────┐
                    │   Master 0 (CPU, Base QoS=8)    │
                    └───────────────┬─────────────────┘
                                    │
                    ┌───────────────▼─────────────────┐
                    │  Aging Counter (8-bit)          │
                    │  Increment: request && !grant   │
                    │  Reset: grant                   │
                    └───────────────┬─────────────────┘
                                    │
                    ┌───────────────▼─────────────────┐
                    │  QoS Boost Logic                │
                    │  aging >= threshold ? MAX : base│
                    └───────────────┬─────────────────┘
                                    │
                    ┌───────────────▼─────────────────┐
                    │  Weighted Round-Robin Arbiter   │
                    │  Inputs: effective_qos[M]       │
                    │  Outputs: grant[M]              │
                    └─────────────────────────────────┘
```

---

## Implementation Details

### Aging Counter Module

**Location:** Alongside AXI skid buffer wrappers at master inputs

```systemverilog
// Per-master aging counter
logic [AGING_COUNTER_WIDTH-1:0] aging_counter [NUM_MASTERS];
logic [QOS_WIDTH-1:0] effective_qos [NUM_MASTERS];

// Aging counter logic
always_ff @(posedge aclk) begin
    for (int m = 0; m < NUM_MASTERS; m++) begin
        if (!aresetn) begin
            aging_counter[m] <= '0;
        end else if (grant_valid && grant[m]) begin
            // Reset on grant
            aging_counter[m] <= '0;
        end else if (request[m]) begin
            // Increment while pending (saturate at max)
            if (aging_counter[m] < AGING_THRESHOLD) begin
                aging_counter[m] <= aging_counter[m] + 1'b1;
            end
        end
    end
end

// QoS boost logic
always_comb begin
    for (int m = 0; m < NUM_MASTERS; m++) begin
        if (aging_counter[m] >= AGING_THRESHOLD) begin
            // Boost to maximum QoS when aged
            effective_qos[m] = MAX_QOS;
        end else begin
            // Use configured base QoS
            effective_qos[m] = base_qos[m];
        end
    end
end

// Connect to weighted arbiter
arbiter_round_robin_weighted #(
    .CLIENTS(NUM_MASTERS),
    .WAIT_GNT_ACK(1)
) u_arbiter (
    .clk(aclk),
    .rst_n(aresetn),
    .request(request),
    .weight(effective_qos),  // ← Use effective QoS (base or boosted)
    .grant(grant),
    .grant_valid(grant_valid)
);
```

### Configuration Parameters

| Parameter | Description | Default | Range |
|-----------|-------------|---------|-------|
| `ENABLE_AGING` | Enable aging counters | `1` | 0/1 |
| `AGING_THRESHOLD` | Cycles before boost | `256` | 16-65535 |
| `AGING_COUNTER_WIDTH` | Counter width (bits) | `8` | 4-16 |
| `QOS_WIDTH` | QoS field width | `4` | 2-8 |
| `MAX_QOS` | Maximum QoS value | `15` | 2^QOS_WIDTH-1 |

**Recommended Settings:**
- **Low-latency systems:** `AGING_THRESHOLD = 64` (640ns @ 100MHz)
- **Balanced systems:** `AGING_THRESHOLD = 256` (2.56μs @ 100MHz)
- **Throughput-optimized:** `AGING_THRESHOLD = 1024` (10.24μs @ 100MHz)

---

## Behavioral Analysis

### Before Aging (Starvation Possible)

```
Cycle   CPU Req   Debug Req   CPU Age   Debug Age   Grant
-----   -------   ---------   -------   ---------   -----
0       1         1           -         -           CPU   (QoS=8 > QoS=1)
1       1         1           -         -           CPU   (QoS=8 > QoS=1)
2       1         1           -         -           CPU   (QoS=8 > QoS=1)
...     ...       ...         -         -           CPU   ← Debug STARVED!
```

### After Aging (Starvation Prevented)

```
Cycle   CPU Req   Debug Req   CPU Age   Debug Age   Eff QoS        Grant
-----   -------   ---------   -------   ---------   -----------    -----
0       1         1           0         0           CPU=8, Dbg=1   CPU
1       1         1           0         1           CPU=8, Dbg=1   CPU
2       1         1           0         2           CPU=8, Dbg=1   CPU
...
255     1         1           0         255         CPU=8, Dbg=1   CPU
256     1         1           0         256         CPU=8, Dbg=15  Debug ← BOOSTED!
257     0         0           0         0           -              -
```

**Result:** Debug master guaranteed grant within 256 cycles (2.56μs @ 100MHz).

---

## Performance Impact

### Area

| Resource | Without Aging | With Aging (8-bit) | Increase |
|----------|---------------|-------------------|----------|
| **Flip-Flops** | ~50 (arbiter) | ~50 + 8×M | +16% (for M=5) |
| **LUTs** | ~100 (arbiter) | ~100 + 12×M | +60% (for M=5) |
| **Total Area** | Baseline | +20-30% | Modest |

Where M = number of masters.

### Latency

- **High-QoS masters:** No change (still prioritized until aging kicks in)
- **Low-QoS masters:** Bounded worst-case latency = `AGING_THRESHOLD` cycles
- **Average case:** Minimal impact (aging rarely triggers in normal operation)

### Timing

- **Critical path:** Aging counter increment + comparator + QoS mux
- **Impact:** ~1-2 gate delays vs. baseline (negligible at typical clock speeds)
- **Recommendation:** Register outputs if targeting >500 MHz

---

## Test Plan

### Test Scenarios

1. **Normal Operation:** Verify aging doesn't interfere with weighted arbitration
2. **Starvation Prevention:** Continuous high-QoS load, verify low-QoS eventually serviced
3. **Aging Threshold:** Verify boost happens exactly at threshold cycle count
4. **Reset Behavior:** Verify counters reset on grant and system reset
5. **Corner Cases:** All masters aged simultaneously, verify arbiter behavior

### Test Code Example

```python
async def test_aging_prevents_starvation(tb):
    """Verify low-QoS master gets serviced despite heavy high-QoS load"""

    # Configure: CPU=QoS 8, Debug=QoS 1, Aging threshold=256
    tb.configure_qos(cpu=8, debug=1, aging_threshold=256)

    # Generate continuous high-priority CPU requests
    cpu_task = cocotb.start_soon(tb.generate_continuous_requests('cpu'))

    # Send single low-priority debug request
    start_time = get_sim_time('ns')
    await tb.send_request('debug', addr=0x1000, data=0xDEAD)

    # Wait for debug grant (should happen within 256 cycles)
    await tb.wait_for_grant('debug', timeout=300)  # 256 + margin

    end_time = get_sim_time('ns')
    latency_cycles = (end_time - start_time) / 10  # 10ns period

    # Verify bounded latency
    assert latency_cycles <= 256, f"Starvation! Latency={latency_cycles} > 256"

    # Verify aging counter reached threshold
    assert tb.read_aging_counter('debug') >= 256
```

---

## Configuration Examples

### Real-Time System (Strict Latency Bounds)

```python
BridgeConfig(
    enable_aging=True,
    aging_threshold=64,          # 640ns @ 100MHz
    aging_counter_width=8,
    base_qos_weights={
        'cpu_master': 8,         # Highest priority
        'dma_master': 4,         # Medium priority
        'debug_master': 1        # Low priority but guaranteed service
    }
)
```

### Throughput-Optimized System

```python
BridgeConfig(
    enable_aging=True,
    aging_threshold=1024,        # 10.24μs @ 100MHz
    aging_counter_width=12,      # Support larger threshold
    base_qos_weights={
        'cpu_master': 16,        # Very high priority
        'dma_master': 8,
        'debug_master': 1
    }
)
```

### Development/Debug Build (Aggressive Aging)

```python
BridgeConfig(
    enable_aging=True,
    aging_threshold=16,          # 160ns @ 100MHz (very aggressive)
    aging_counter_width=6,
    base_qos_weights={
        'cpu_master': 4,         # Lower weights for testing
        'dma_master': 2,
        'debug_master': 1
    }
)
```

---

## Integration with Bridge Generator

### CSV Configuration Extension

Add aging configuration to `ports.csv`:

```csv
port_name,direction,protocol,channels,prefix,data_width,addr_width,id_width,base_addr,addr_range,ooo,base_qos,aging_enable
rapids_descr_wr,master,axi4,wr,rapids_descr_m_axi_,512,64,8,N/A,N/A,N/A,4,1
cpu_master,master,axi4,rw,cpu_m_axi_,64,32,4,N/A,N/A,N/A,8,1
debug_master,master,axi4,rw,debug_m_axi_,32,32,4,N/A,N/A,N/A,1,1
```

### Generated RTL Structure

```systemverilog
// Generated by bridge_csv_generator.py

// Aging configuration parameters
parameter int ENABLE_AGING = 1;
parameter int AGING_THRESHOLD = 256;
parameter int AGING_COUNTER_WIDTH = 8;

// Base QoS weights (from CSV)
parameter int BASE_QOS_RAPIDS_DESCR = 4;
parameter int BASE_QOS_CPU = 8;
parameter int BASE_QOS_DEBUG = 1;

// Aging counters
logic [AGING_COUNTER_WIDTH-1:0] aging_counter [NUM_MASTERS];
logic [3:0] effective_qos [NUM_MASTERS];

// ... (aging logic as shown above) ...
```

---

## Related Documents

- **TASKS.md:** TASK-017 (QoS Support with Aging Counters)
- **PRD.md:** Section on arbitration and fairness
- **Bridge Generator:** CSV format specification
- **Arbiter Modules:** `arbiter_round_robin_weighted.sv`

---

## Revision History

| Version | Date | Author | Changes |
|---------|------|--------|---------|
| 1.0 | 2025-10-27 | Design Team | Initial design proposal |

---

**Status:** Design proposal - awaiting implementation (TASK-017)
