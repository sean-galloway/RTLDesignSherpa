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

# AMBA Clock Gate Controller

**Module:** `amba_clock_gate_ctrl.sv`
**Location:** `rtl/amba/shared/`
**Status:** Production Ready

---

## Overview

The AMBA Clock Gate Controller provides dynamic clock gating capability tailored for AMBA protocol interfaces. It monitors transaction activity on both user-side and AXI-side interfaces to automatically gate the clock during idle periods, reducing dynamic power consumption while maintaining protocol correctness.

### Key Features

- Automatic activity detection from user and AXI valid signals
- Configurable idle threshold before gating activation
- Integration with standard ICG (Integrated Clock Gate) cells
- Registered wakeup signal for metastability protection
- Global enable/disable control
- Idle status monitoring
- Zero added latency when clock is ungated

---

## Module Purpose

AMBA protocol interfaces often experience periods of inactivity during system operation. Traditional always-on clocking wastes power during these idle periods. The AMBA Clock Gate Controller solves this by:

1. Monitoring transaction activity on both interfaces
2. Detecting extended idle periods
3. Automatically gating the clock to save power
4. Instantly ungating when new activity arrives

**Use Cases:**
- Power-critical AMBA interface implementations
- Battery-powered systems with intermittent bus activity
- Multi-master systems where individual masters idle frequently
- ASIC designs requiring aggressive dynamic power reduction

**Key Benefit:** Transparent power saving with no protocol impact (activity detection ensures clock availability when needed).

---

## Parameters

| Parameter | Type | Default | Description |
|-----------|------|---------|-------------|
| CG_IDLE_COUNT_WIDTH | int | 4 | Width of idle counter (determines maximum idle threshold) |
| ICW | int | CG_IDLE_COUNT_WIDTH | Shorthand alias for idle count width |

**Idle Count Range:**
- Minimum: 0 (immediate gating when idle)
- Maximum: 2^CG_IDLE_COUNT_WIDTH - 1
- Default (4-bit): 0 to 15 cycles

---

## Port Groups

### Clock and Reset

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| clk_in | input | 1 | Input clock (always running, feeds ICG cell) |
| aresetn | input | 1 | Active-low asynchronous reset |

### Configuration Interface

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| cfg_cg_enable | input | 1 | Global clock gating enable (1=allow gating, 0=always ungated) |
| cfg_cg_idle_count | input | ICW | Idle cycle threshold before gating activates |

### Activity Monitoring

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| user_valid | input | 1 | User-side activity indicator (any valid signal from user interface) |
| axi_valid | input | 1 | AXI-side activity indicator (any valid signal from AXI interface) |

### Clock Gating Outputs

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| clk_out | output | 1 | Gated output clock (drives clocked logic) |
| gating | output | 1 | Gating active indicator (1=clock currently gated) |
| idle | output | 1 | Idle status (1=no activity detected, 0=activity present) |

---

## Functional Description

### Activity Detection Logic

The module combines activity signals from both user and AXI interfaces to form a unified wakeup signal:

```
wakeup = user_valid OR axi_valid
```

**Why Both Interfaces?**
- User interface: Detects upstream master activity
- AXI interface: Detects downstream slave activity
- Combined: Ensures clock active for bidirectional traffic

**Registered Wakeup:**
```systemverilog
always_ff @(posedge clk_in or negedge aresetn) begin
    if (!aresetn)
        r_wakeup <= 1'b1;  // Default: Active (clock ungated at reset)
    else
        r_wakeup <= user_valid || axi_valid;
end
```

**Key Property:** Wakeup signal is registered to:
1. Prevent metastability (if activity signals cross clock domains)
2. Provide stable input to downstream clock gate control
3. Default to active state during reset (ensures clock available)

### Idle Signal Generation

Idle status is the inverse of wakeup:

```
idle = ~r_wakeup
```

**Interpretation:**
- idle = 1: No activity for at least 1 cycle (eligible for gating)
- idle = 0: Recent activity detected (clock must remain ungated)

**Usage:** Exported for monitoring/debug (system can observe interface idle status).

### Clock Gating Control Integration

The module instantiates a base clock gate controller:

```systemverilog
clock_gate_ctrl #(
    .IDLE_CNTR_WIDTH    (ICW)
) u_clock_gate_ctrl (
    .clk_in             (clk_in),
    .aresetn            (aresetn),
    .cfg_cg_enable      (cfg_cg_enable),
    .cfg_cg_idle_count  (cfg_cg_idle_count),
    .wakeup             (r_wakeup),
    .clk_out            (clk_out),
    .gating             (gating)
);
```

**Base Controller Operation:**
1. Monitors r_wakeup signal
2. Increments idle counter when wakeup=0 (idle)
3. Gates clock when counter >= cfg_cg_idle_count
4. Ungates immediately when wakeup=1 (activity)

### Gating Threshold Behavior

**cfg_cg_idle_count Examples (4-bit counter):**

| Value | Behavior |
|-------|----------|
| 0 | Aggressive: Gate clock immediately when idle detected (1 cycle delay) |
| 1 | Gate after 1 idle cycle |
| 4 | Conservative: Gate after 4 consecutive idle cycles |
| 15 | Maximum delay: Gate after 15 consecutive idle cycles |

**Trade-off:**
- Low threshold: Maximum power saving, higher gating/ungating frequency
- High threshold: Reduced gating overhead, less power saving

**Recommendation:** Start with moderate value (4-8) and tune based on measured activity patterns.

### Gating/Ungating Timing

**Gating Sequence (Activity → Idle):**
1. Cycle N: user_valid=1, axi_valid=0 → r_wakeup=1 (active)
2. Cycle N+1: user_valid=0, axi_valid=0 → r_wakeup=0 (idle)
3. Idle counter starts incrementing
4. Cycle N+1+cfg_cg_idle_count: Counter threshold reached
5. Clock gates on next cycle edge (gating=1)

**Ungating Sequence (Idle → Activity):**
1. Clock currently gated (gating=1)
2. Cycle M: user_valid=1 (new activity arrives)
3. Cycle M+1: r_wakeup=1 (registered)
4. Clock ungates immediately (gating=0)
5. Normal operation resumes with no lost cycles

**Critical Property:** Ungating is immediate (no counter delay) to ensure zero protocol impact.

---

## Usage Example

### Basic Integration with AXI Interface

```systemverilog
// Instantiate AMBA clock gate controller
amba_clock_gate_ctrl #(
    .CG_IDLE_COUNT_WIDTH    (4)  // 0-15 cycle threshold
) u_clock_gate (
    // Input clock (always running)
    .clk_in                 (axi_aclk_raw),
    .aresetn                (axi_aresetn),

    // Configuration
    .cfg_cg_enable          (power_save_enable),     // From system config
    .cfg_cg_idle_count      (4'd4),                  // Gate after 4 idle cycles

    // Activity monitoring (OR together all valid signals)
    .user_valid             (s_axi_awvalid | s_axi_wvalid | s_axi_arvalid),
    .axi_valid              (m_axi_awvalid | m_axi_wvalid | m_axi_arvalid |
                             m_axi_rvalid  | m_axi_bvalid),

    // Gated clock output
    .clk_out                (axi_aclk_gated),
    .gating                 (clock_gated_status),
    .idle                   (interface_idle)
);

// Use gated clock for all clocked logic
always_ff @(posedge axi_aclk_gated or negedge axi_aresetn) begin
    if (!axi_aresetn) begin
        // Reset logic
    end else begin
        // Normal operation with gated clock
    end
end

// Monitor gating status for debug/power measurement
assign power_gating_active = clock_gated_status;
assign bus_idle_indicator = interface_idle;
```

### Multi-Master Arbitration with Clock Gating

```systemverilog
// Individual clock gating per master interface
genvar i;
generate
    for (i = 0; i < NUM_MASTERS; i++) begin : gen_master_cg
        amba_clock_gate_ctrl #(
            .CG_IDLE_COUNT_WIDTH    (4)
        ) u_master_cg (
            .clk_in                 (system_clk),
            .aresetn                (aresetn),
            .cfg_cg_enable          (cg_enable[i]),
            .cfg_cg_idle_count      (cg_threshold[i]),

            // Monitor master i activity
            .user_valid             (master_valid[i]),
            .axi_valid              (1'b0),  // No AXI side for master interface

            .clk_out                (master_clk_gated[i]),
            .gating                 (master_gating[i]),
            .idle                   (master_idle[i])
        );
    end
endgenerate

// Power monitoring: Count active masters
assign num_masters_active = NUM_MASTERS - $countones(master_idle);
```

### Dynamic Threshold Adjustment

```systemverilog
// Adjust gating threshold based on system load
logic [3:0] dynamic_threshold;

always_comb begin
    case (system_load_level)
        2'b00: dynamic_threshold = 4'd2;   // Light load: Aggressive gating
        2'b01: dynamic_threshold = 4'd4;   // Medium load: Moderate gating
        2'b10: dynamic_threshold = 4'd8;   // High load: Conservative gating
        2'b11: dynamic_threshold = 4'd15;  // Critical load: Minimal gating
    endcase
end

amba_clock_gate_ctrl #(
    .CG_IDLE_COUNT_WIDTH    (4)
) u_adaptive_cg (
    .clk_in                 (clk),
    .aresetn                (rst_n),
    .cfg_cg_enable          (1'b1),
    .cfg_cg_idle_count      (dynamic_threshold),  // Runtime adjustable
    .user_valid             (activity),
    .axi_valid              (1'b0),
    .clk_out                (clk_gated),
    .gating                 (gating),
    .idle                   (idle)
);
```

---

## Design Notes

### Wakeup Signal Registration

**Design Decision:** The wakeup signal is registered before passing to clock gate controller.

**Rationale:**
1. **Metastability Protection:** Activity signals may originate from different clock domains
2. **Stable Input:** Clock gate controller receives glitch-free wakeup signal
3. **Reset Safety:** Defaults to active (1'b1) ensuring clock availability during reset

**Trade-off:** Adds 1 cycle latency to activity detection, but ensures robust operation.

### Activity Signal Selection

**Best Practices:**

**For User Interface (Upstream):**
```systemverilog
// AXI Master Interface
user_valid = awvalid | wvalid | arvalid

// AXI Slave Interface
user_valid = awready | wready | arready | rvalid | bvalid
```

**For AXI Interface (Downstream):**
```systemverilog
// AXI Master Interface
axi_valid = awready | wready | arready | rvalid | bvalid

// AXI Slave Interface
axi_valid = awvalid | wvalid | arvalid
```

**Why Not Ready Signals?**
- Valid signals indicate actual transaction progress
- Ready signals may assert speculatively
- Valid-based detection prevents premature gating

### Integration with ICG Cells

The base clock_gate_ctrl module expects integration with standard ICG cell:

**Typical ICG Cell Interface:**
```systemverilog
// Standard ICG cell instantiation (inside clock_gate_ctrl)
ICG u_icg (
    .CLK        (clk_in),
    .EN         (gate_enable),  // From controller FSM
    .CLK_OUT    (clk_out)
);
```

**ASIC Integration:**
- Use library-specific ICG cell (vendor-provided)
- Ensure glitch-free enable signal (provided by controller)
- Consider test mode bypass for scan insertion

**FPGA Integration:**
- Use global clock mux primitives (BUFGMUX, BUFGCE)
- Some FPGAs have dedicated clock gating resources
- Alternative: Fine-grained clock enable on flip-flops

### Power Measurement Methodology

**Estimating Power Savings:**

1. **Measure Idle Time:**
```systemverilog
logic [31:0] idle_cycle_count;
always_ff @(posedge clk_in) begin
    if (idle)
        idle_cycle_count <= idle_cycle_count + 1;
end
```

2. **Calculate Gating Efficiency:**
```
Gating Efficiency = (gating_active_cycles / total_cycles) × 100%
```

3. **Estimate Power Reduction:**
```
Dynamic Power Saving ≈ Gating Efficiency × Clock Tree Power
```

**Typical Results:**
- Low-activity interfaces: 60-80% gating efficiency
- Burst-heavy traffic: 20-40% gating efficiency
- Clock tree power: 20-30% of total dynamic power
- Overall savings: 5-20% total chip dynamic power

### Performance Considerations

**Latency Impact:**
- No added latency when clock ungated (activity present)
- 1 cycle wakeup registration latency
- Ungating is immediate (no idle counter delay)

**Throughput Impact:**
- Zero impact: Clock always available for valid transactions
- Activity detection ensures ungating before transaction arrival

**Area Overhead:**
- Minimal: Single register + base controller
- Base controller: Small FSM + counter
- Typical: <100 gates total

---

## Related Modules

### Used By
- AXI interface wrappers requiring power optimization
- AMBA protocol bridges with intermittent activity
- Multi-master interconnect fabrics
- Power-critical peripheral interfaces

### Uses
- **clock_gate_ctrl.sv** - Base clock gating controller (idle counter, FSM)
- **reset_defs.svh** - Standard reset macro definitions

### See Also
- **clock_gate_ctrl.sv** - Generic clock gating controller (rtl/common/)
- **icg.sv** - Integrated clock gate cell wrapper

---

## References

### Source Code
- RTL: `rtl/amba/shared/amba_clock_gate_ctrl.sv`
- Base Controller: `rtl/common/clock_gate_ctrl.sv`
- Tests: `val/common/test_clock_gate_ctrl.py`

### Documentation
- Architecture: `docs/markdown/RTLAmba/shared/README.md`
- Common Module: `docs/markdown/RTLCommon/clock_gate_ctrl.md`
- Design Guide: `rtl/amba/PRD.md`

### Industry Standards
- IEEE 1801 (UPF) - Unified Power Format for power-aware design
- ARM AMBA specifications - Clock gating recommendations

---

**Last Updated:** 2025-10-24

---

## Navigation

- [Back to Shared Infrastructure Index](README.md)
- [Back to RTLAmba Index](../README.md)
