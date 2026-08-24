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

The AMBA clock gate controller adds dynamic clock gating to AMBA protocol interfaces. It watches transaction activity on both the user side and the AXI side, gates the clock during idle stretches, and wakes on new activity — cutting dynamic power without touching protocol behavior.

AMBA interfaces idle a lot in real systems, and an always-on clock burns power the whole time. This module does something about it:

1. Monitors transaction activity on both interfaces
2. Detects extended idle periods
3. Gates the clock automatically to save power
4. Ungates on new activity without waiting for the idle counter

**Use cases:**
- Power-critical AMBA interface implementations
- Battery-powered systems with intermittent bus activity
- Multi-master systems where individual masters idle frequently
- ASIC designs requiring aggressive dynamic power reduction

**Key benefit:** transparent power saving with no protocol impact — the activity detection guarantees the clock is there when a transfer needs it.

### Key Features

- Automatic activity detection from user and AXI valid signals
- Configurable idle threshold before gating activation
- Integration with standard ICG (Integrated Clock Gate) cells
- Registered wakeup signal for metastability protection
- Global enable/disable control
- Idle status monitoring
- Zero added latency while the clock is already ungated (wake-up from gated costs 1 register stage here; see Performance Considerations)

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

## Ports

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

The module ORs the activity signals from both interfaces into one wakeup:

```
wakeup = user_valid OR axi_valid
```

**Why both interfaces?**
- User interface: catches upstream master activity
- AXI interface: catches downstream slave activity
- Combined: keeps the clock alive for bidirectional traffic

**Registered wakeup:**
```systemverilog
always_ff @(posedge clk_in or negedge aresetn) begin
    if (!aresetn)
        r_wakeup <= 1'b1;  // Default: Active (clock ungated at reset)
    else
        r_wakeup <= user_valid || axi_valid;
end
```

Registering the wakeup buys you three things:

1. Metastability protection, if the activity signals cross clock domains
2. A stable, glitch-free input to the downstream clock gate control
3. A default-active state during reset, so the clock is always available coming out of it

### Idle Signal Generation

Idle is just the inverse of wakeup:

```
idle = ~r_wakeup
```

**Reading it:**
- idle = 1: no activity for at least 1 cycle (eligible for gating)
- idle = 0: recent activity detected (clock must stay ungated)

It's exported for monitoring and debug, so the system can observe per-interface idle status directly.

### Clock Gating Control Integration

The real work is delegated to the base clock gate controller:

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

**Base controller operation:**

1. Monitors r_wakeup
2. Reloads the idle counter with cfg_cg_idle_count on any activity, and counts DOWN while wakeup=0
3. Gates the clock when the counter reaches 0
4. Ungates when wakeup=1 (activity), without waiting for the idle counter

### Gating Threshold Behavior

**cfg_cg_idle_count examples (4-bit counter):**

| Value | Behavior |
|-------|----------|
| 0 | Aggressive: gate in the SAME cycle the registered wakeup first reads 0 (2 clocks after the last bus activity on single-stage families, 3 on two-stage families) |
| 1 | Gate after 1 idle cycle |
| 4 | Conservative: Gate after 4 consecutive idle cycles |
| 15 | Maximum delay: Gate after 15 consecutive idle cycles |

**The trade-off:**
- Low threshold: maximum power saving, more gating/ungating churn
- High threshold: less gating overhead, less power saved

Start with a moderate value (4-8) and tune against measured activity patterns. There's no universally right answer here — it depends on your burst shape.

---

## Timing

### Gating Sequence (Activity → Idle)

1. Cycle N: user_valid=1, axi_valid=0 → r_wakeup=1 during cycle N+1 (registered)
2. Cycle N+1: user_valid=0, axi_valid=0 → r_wakeup=0 (idle)
3. Idle counter starts counting down from cfg_cg_idle_count
4. Cycle N+1+cfg_cg_idle_count: counter threshold reached
5. Clock gates on next cycle edge (gating=1)

### Ungating Sequence (Idle → Activity)

1. Clock currently gated (gating=1)
2. Cycle M: user_valid=1 (new activity arrives)
3. Cycle M+1: r_wakeup=1 (registered); gating=0 combinationally
4. Cycle M+2: first usable gated-clock rising edge
5. Normal operation resumes with no lost cycles

The part that matters: ungating does not wait on the idle counter. It still costs 1 register stage here, so the first usable gated-clock edge arrives 2 clocks after activity asserts (3 on the two-stage APB, APB5, and AXI5-Stream wrappers).

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

**Design decision:** the wakeup signal is registered before it reaches the clock gate controller.

**Why:**
1. **Metastability protection:** activity signals may originate from different clock domains
2. **Stable input:** the clock gate controller sees a glitch-free wakeup
3. **Reset safety:** defaults to active (1'b1), so the clock is available during reset

**The cost:** one register stage on activity detection, so the first usable gated-clock edge arrives 2 clocks after activity asserts (3 on the two-stage APB, APB5, and AXI5-Stream wrappers, which register activity again before this module). A clean, glitch-free gate enable is worth that cycle.

### Activity Signal Selection

**For the user interface (upstream):**
```systemverilog
// AXI Master Interface
user_valid = awvalid | wvalid | arvalid

// AXI Slave Interface
user_valid = awready | wready | arready | rvalid | bvalid
```

**For the AXI interface (downstream):**
```systemverilog
// AXI Master Interface
axi_valid = awready | wready | arready | rvalid | bvalid

// AXI Slave Interface
axi_valid = awvalid | wvalid | arvalid
```

**Why not ready signals?**
- Valid signals indicate actual transaction progress
- Ready signals may assert speculatively
- Valid-based detection prevents premature gating

### Integration with ICG Cells

The base clock_gate_ctrl expects a standard ICG cell underneath:

**Typical ICG cell interface:**
```systemverilog
// Standard ICG cell instantiation (inside clock_gate_ctrl)
ICG u_icg (
    .CLK        (clk_in),
    .EN         (gate_enable),  // From controller FSM
    .CLK_OUT    (clk_out)
);
```

**ASIC integration:**
- Use the library-specific ICG cell (vendor-provided)
- The enable must be glitch-free (the controller provides that)
- Consider test mode bypass for scan insertion

**FPGA integration:**
- Use global clock mux primitives (BUFGMUX, BUFGCE)
- Some FPGAs have dedicated clock gating resources
- Alternative: fine-grained clock enable on the flip-flops themselves

### Power Measurement Methodology

**Estimating power savings:**

1. **Measure idle time:**
```systemverilog
logic [31:0] idle_cycle_count;
always_ff @(posedge clk_in) begin
    if (idle)
        idle_cycle_count <= idle_cycle_count + 1;
end
```

2. **Calculate gating efficiency:**
```
Gating Efficiency = (gating_active_cycles / total_cycles) × 100%
```

3. **Estimate power reduction:**
```
Dynamic Power Saving ≈ Gating Efficiency × Clock Tree Power
```

**Typical results:**
- Low-activity interfaces: 60-80% gating efficiency
- Burst-heavy traffic: 20-40% gating efficiency
- Clock tree power: 20-30% of total dynamic power
- Overall savings: 5-20% total chip dynamic power

### Performance Considerations

**Latency impact:**
- No added latency when the clock is already ungated (activity present)
- Activity is registered once (AXI4, AXI5, AXI4-Lite, AXI4-Stream) or twice (APB, APB5, AXI5-Stream) before reaching the ICG enable, which is combinational. The one exception is `apb4_slave_cdc_cg`, which drives this module combinationally (`assign pclk_user_valid = s_apb_PSEL || w_rsp_valid;`) and therefore registers once despite being APB — 2 clocks to the first usable gated edge, not 3. This module contributes the single `r_wakeup` stage; two-stage families add one more in the wrapper.
- First usable gated-clock rising edge: 2 clocks (single-stage families) or 3 clocks (two-stage families) after activity asserts
- Ungating does not wait on the idle counter

**Throughput impact:**
- Zero: the clock is always available for valid transactions
- Activity detection ungates before the transaction arrives

**Area overhead:**
- Minimal: single register + base controller
- Base controller: small FSM + counter
- Typical: <100 gates total

---

## Related Modules

### Used By
- AXI interface wrappers requiring power optimization
- AMBA protocol bridges with intermittent activity
- Multi-master interconnect fabrics
- Power-critical peripheral interfaces

### Uses
- **clock_gate_ctrl.sv** — base clock gating controller (idle counter, FSM)
- **reset_defs.svh** — standard reset macro definitions

### See Also
- **clock_gate_ctrl.sv** — generic clock gating controller (rtl/common/)
- **icg.sv** — integrated clock gate cell wrapper

---

## Testing

- Tests: `val/common/test_clock_gate_ctrl.py`

The module is also covered from `val/amba/` with the rest of the shared area — run it with `make -C val/amba clean-all && make -C val/amba run-all-func-parallel`.

---

## References

### Source Code
- RTL: `rtl/amba/shared/amba_clock_gate_ctrl.sv`
- Base Controller: `rtl/common/clock_gate_ctrl.sv`

### Documentation
- Architecture: `docs/markdown/rtl-amba/shared/README.md`
- Common Module: `docs/markdown/rtl-common/clock_gate_ctrl.md`
- Design Guide: `docs/markdown/rtl-amba/index.md`

### Industry Standards
- IEEE 1801 (UPF) — Unified Power Format for power-aware design
- ARM AMBA specifications — clock gating recommendations

---

**Last Updated:** 2025-10-24

---

## Navigation

- [Back to Shared Infrastructure Index](README.md)
- [Back to rtl-amba Index](../index.md)
