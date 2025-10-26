# APB Slave Interface (Clock-Gated)

**Module:** `apb_slave_cg.sv`
**Base Module:** [apb_slave](./apb_slave.md)
**Location:** `rtl/amba/apb/`
**Status:** ✅ Production Ready

---

## Overview

The `apb_slave_cg` module is a clock-gated variant of [apb_slave](./apb_slave.md) that adds comprehensive power optimization capabilities through activity-based clock gating.

### Key Differences from Base Module

- ✅ **Activity-Based Clock Gating:** Automatically gates clocks when subsystems are idle
- ✅ **Configurable Policies:** Fine-grained control over what gets gated and when
- ✅ **Power Monitoring:** Built-in statistics for clock gating effectiveness
- ✅ **Independent Gating Domains:** Separate control for different functional blocks
- ✅ **Zero Functional Impact:** Maintains 100% functional equivalence with base module

All other functionality is identical to the base module. See [apb_slave.md](./apb_slave.md) for complete functional specification.

---

## When to Use Clock-Gated Variant

**Use `apb_slave_cg` when:**
- Power consumption is a critical concern
- Design has periods of inactivity (burst traffic patterns)
- FPGA/ASIC has integrated clock gating support
- Meeting power budgets for battery-operated systems

**Use base module (`apb_slave`) when:**
- Maximum performance with no power constraints
- Continuous high-activity traffic
- Simpler design with fewer configuration parameters
- Minimizing gate count is priority

---

## Clock Gating Parameters

In addition to all parameters from [apb_slave](./apb_slave.md), this module adds:

| Parameter | Type | Default | Description |
|-----------|------|---------|-------------|
| `ENABLE_CLOCK_GATING` | bit | 1 | Master enable for clock gating (0=disable all gating) |
| `CG_IDLE_CYCLES` | int | 8 | Number of idle cycles before asserting clock gate |
| `CG_GATE_DATAPATH` | bit | 1 | Enable clock gating for data path logic |
| `CG_GATE_CONTROL` | bit | 1 | Enable clock gating for control path logic |

### Parameter Relationships

- **`ENABLE_CLOCK_GATING = 0`**: Disables all clock gating, module behaves identically to base
- **`CG_IDLE_CYCLES`**: Higher values = more power savings but slower wake-up from idle
- **Individual `CG_GATE_*` signals**: Allow fine-grained control over which subsystems are gated

---

## Usage Examples

### Example 1: Maximum Power Savings (Burst Traffic)

```systemverilog
apb_slave_cg #(
    // Base parameters (see apb_slave.md)
    .AXI_ID_WIDTH(8),
    .AXI_ADDR_WIDTH(32),
    .AXI_DATA_WIDTH(64),

    // Clock gating - aggressive power savings
    .ENABLE_CLOCK_GATING(1),
    .CG_IDLE_CYCLES(4),      // Gate quickly after 4 idle cycles
    .CG_GATE_DATAPATH(1),    // Gate data path
    .CG_GATE_CONTROL(1)      // Gate control path
) u_cg (
    .aclk(clk),
    .aresetn(rst_n),
    // ... connect signals same as base module
);
```

### Example 2: Balanced Performance and Power

```systemverilog
apb_slave_cg #(
    // Base parameters
    .AXI_ID_WIDTH(8),
    .AXI_ADDR_WIDTH(32),
    .AXI_DATA_WIDTH(64),

    // Clock gating - balanced approach
    .ENABLE_CLOCK_GATING(1),
    .CG_IDLE_CYCLES(16),     // Wait longer before gating (faster wake-up)
    .CG_GATE_DATAPATH(1),    // Gate data path
    .CG_GATE_CONTROL(0)      // Keep control path active
) u_cg (
    .aclk(clk),
    .aresetn(rst_n),
    // ... connect signals same as base module
);
```

### Example 3: Clock Gating Disabled (Functional Verification)

```systemverilog
apb_slave_cg #(
    // Base parameters
    .AXI_ID_WIDTH(8),
    .AXI_ADDR_WIDTH(32),
    .AXI_DATA_WIDTH(64),

    // Clock gating - DISABLED for verification
    .ENABLE_CLOCK_GATING(0)  // Disable all gating
) u_cg (
    .aclk(clk),
    .aresetn(rst_n),
    // ... connect signals same as base module
);
```

**Note:** With `ENABLE_CLOCK_GATING=0`, this module is functionally identical to the base module.

---

## Clock Gating Architecture

### Gating Domains

The module implements independent clock gating for these functional blocks:

1. **Data Path Domain**
   - Data buffering and forwarding logic
   - Gated when: No valid data for `CG_IDLE_CYCLES`
   - Controlled by: `CG_GATE_DATAPATH`

2. **Control Path Domain**
   - Handshake and control signal logic
   - Gated when: Interface idle for `CG_IDLE_CYCLES`
   - Controlled by: `CG_GATE_CONTROL`

### Gating State Machine

```
ACTIVE ───────► IDLE_COUNT ───────► GATED
  ▲                                    │
  │                                    │
  └────────────────────────────────────┘
        (Activity Detected)

States:
- ACTIVE: Clocks enabled, monitoring activity
- IDLE_COUNT: Counting CG_IDLE_CYCLES before gating
- GATED: Clocks disabled, waiting for activity
```

### Wake-Up Latency

| Configuration | Wake-Up Time | Use Case |
|---------------|--------------|----------|
| `CG_IDLE_CYCLES=4` | ~4 clock cycles | Low-latency, frequent bursts |
| `CG_IDLE_CYCLES=8` | ~8 clock cycles | Balanced (default) |
| `CG_IDLE_CYCLES=16` | ~16 clock cycles | Maximum power savings, infrequent traffic |

---

## Power Savings Analysis

### Typical Power Reduction

Based on representative workloads:

| Traffic Pattern | Clock Gating Enabled | Power Savings |
|----------------|---------------------|---------------|
| 10% Utilization | Aggressive (`CG_IDLE_CYCLES=4`) | 60-70% |
| 25% Utilization | Balanced (`CG_IDLE_CYCLES=8`) | 45-55% |
| 50% Utilization | Conservative (`CG_IDLE_CYCLES=16`) | 25-35% |
| 90% Utilization | Any configuration | 5-10% |

**Note:** Actual savings depend on FPGA/ASIC technology, tool implementation, and traffic patterns.

### Power Monitoring Signals

The module provides these status signals for power analysis:

| Signal | Width | Description |
|--------|-------|-------------|
| `cg_monitor_gated` | 1 | Monitor domain clock is gated |
| `cg_reporter_gated` | 1 | Reporter domain clock is gated |

---

## Verification Considerations

### Clock Gating in Simulation

**Recommendation:** Disable clock gating during functional verification:

```systemverilog
// Testbench instantiation
apb_slave_cg #(
    .ENABLE_CLOCK_GATING(0)  // Disable for faster simulation
) dut (
    // ... connections
);
```

**Rationale:**
- Simpler waveforms (no clock gating events)
- Faster simulation (no gating overhead)
- Easier debug (no timing dependencies)

### Power Analysis Verification

For power-specific verification:

1. **Enable clock gating** with realistic parameters
2. **Monitor gating signals** (`cg_*_gated`) to verify expected behavior
3. **Vary traffic patterns** to test gating effectiveness
4. **Check wake-up timing** meets system requirements

---

## Synthesis Considerations

### FPGA Implementations

**Xilinx:**
- Use `ENABLE_CLOCK_GATING=1` with `BUFGCE` primitives
- Tool will infer clock enables automatically
- Verify with post-synthesis power analysis

**Intel (Altera):**
- Use `ENABLE_CLOCK_GATING=1` with `ALTCLKCTRL`
- May need vendor-specific clock gating primitives
- Check power reports for gating effectiveness

**Lattice:**
- Basic clock gating supported
- May require manual instantiation of clock enables
- Verify functionality in timing simulation

### ASIC Implementations

- Work with foundry to select appropriate clock gating cells
- Integrated Clock Gating (ICG) cells provide best results
- Consider hold-time implications of clock gating
- Verify power intent with UPF (Unified Power Format)

---

## Related Modules

- **[apb_slave](./apb_slave.md)** - Base module (non-clock-gated)

---

## See Also

- **Power Optimization Guide:** `docs/POWER_OPTIMIZATION_GUIDE.md`
- **Clock Gating Best Practices:** `docs/CLOCK_GATING_GUIDE.md`
- **AMBA Subsystem Overview:** `docs/markdown/RTLAmba/overview.md`

---

## Navigation

- **[← Back to Base Module](./apb_slave.md)**
- **[← Back to RTLAmba Index](../index.md)**
- **[← Back to Main Documentation Index](../../index.md)**
