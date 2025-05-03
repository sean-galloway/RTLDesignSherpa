# amba_clock_gate_ctrl

This SystemVerilog module implements a clock gating controller for AMBA interfaces. It monitors activity on both user and AXI sides of an interface and gates the clock when the interface is idle for a configurable duration, helping to reduce power consumption in systems with intermittent activity.

## Module Parameters

- `CG_IDLE_COUNT_WIDTH`: Default width of the idle counter (default: 4). This parameter determines the width of the counter used to track idle cycles before activating clock gating.
- `ICW`: An alias for `CG_IDLE_COUNT_WIDTH` for more concise references within the module.

## Ports

### Clock and Reset
- `clk_in`: The input clock signal to be gated.
- `aresetn`: The active-low reset signal.

### Configuration Interface
- `i_cfg_cg_enable`: Global clock gate enable signal. When set to 1, the clock gating functionality is enabled; when set to 0, clock gating is disabled.
- `i_cfg_cg_idle_count [ICW-1:0]`: Idle countdown value. This sets the number of idle cycles that must elapse before clock gating is activated.

### Activity Monitoring
- `i_user_valid`: Any user-side valid signal. This is used to detect activity on the user side of the interface.
- `i_axi_valid`: Any AXI-side valid signal. This is used to detect activity on the AXI side of the interface.

### Clock Gating Control Outputs
- `clk_out`: The gated clock output. This is the clock signal that is provided to downstream logic.
- `o_gating`: Active gating indicator. When high, indicates that clock gating is currently active.
- `o_idle`: All buffers empty indicator. When high, indicates that all interfaces are idle with no pending transactions.

## Functionality

1. **Activity Detection**: The module continuously monitors the `i_user_valid` and `i_axi_valid` signals to detect when there is activity on either the user side or the AXI side of the interface.

2. **Idle Detection**: The module maintains an internal signal `r_wakeup` which is synchronized with the input clock and tracks the activity status of the interface. When both `i_user_valid` and `i_axi_valid` are low, `r_wakeup` becomes low after one clock cycle, indicating idle status. The `o_idle` output is the inverse of `r_wakeup`, providing a direct indicator of idle status.

3. **Clock Gating Control**: The module uses a base `clock_gate_ctrl` instance to handle the actual clock gating logic. This submodule:
   - Counts a configurable number of idle cycles (`i_cfg_cg_idle_count`) before enabling clock gating
   - Immediately disables clock gating when activity is detected
   - Manages the clock gating process including proper phase alignment

4. **Configuration**: The module's behavior can be customized through:
   - `i_cfg_cg_enable`: Allows enabling or disabling the clock gating functionality
   - `i_cfg_cg_idle_count`: Configures how many idle cycles must pass before activating clock gating

## Usage Examples

1. **Basic Usage**: Connect the module between a clock source and its consumers, with activity detection signals.

```systemverilog
amba_clock_gate_ctrl #(
    .CG_IDLE_COUNT_WIDTH(4)  // 4-bit counter, count up to 15 cycles
) i_amba_clock_gate_ctrl (
    .clk_in           (aclk),
    .aresetn          (aresetn),
    .i_cfg_cg_enable  (1'b1),  // Enable clock gating
    .i_cfg_cg_idle_count(4'd10),  // Gate after 10 idle cycles
    .i_user_valid     (user_valid),
    .i_axi_valid      (axi_valid),
    .clk_out          (gated_aclk),
    .o_gating         (cg_active),
    .o_idle           (interface_idle)
);
```

2. **Dynamic Reconfiguration**: The module allows dynamic adjustment of idle threshold.

```systemverilog
// Variable threshold based on operation mode
logic [3:0] idle_threshold;
always_comb begin
    case (operation_mode)
        LOW_POWER: idle_threshold = 4'd2;  // Quick entry to clock gating
        NORMAL:    idle_threshold = 4'd10; // Standard threshold
        PERF:      idle_threshold = 4'd15; // Extended threshold for performance
    endcase
end

amba_clock_gate_ctrl i_cg_ctrl (
    // ... other connections ...
    .i_cfg_cg_idle_count(idle_threshold),
    // ... other connections ...
);
```

## Implementation Details

1. **Input Registration**: The module registers the combined status of `i_user_valid` and `i_axi_valid` as `r_wakeup`, ensuring synchronization with the clock domain.

2. **Idle Detection Logic**: The module simply negates the `r_wakeup` signal to derive the `o_idle` signal, indicating when all buffers are empty and the interface is idle.

3. **Submodule Instantiation**: The module instantiates the `clock_gate_ctrl` module which handles the actual clock gating functions based on the idle detection provided by the AMBA-specific signals.

## Notes and Considerations

1. **Reset Behavior**: Upon reset, the `r_wakeup` signal is initialized to 1, preventing immediate clock gating after reset.

2. **Integration Considerations**: This module is typically instantiated within AXI/APB interface modules that need power-saving capabilities (e.g., `axi_master_rd_cg`, `axi_slave_wr_cg`).

3. **Performance Impact**: While clock gating saves power, there is a latency penalty when reactivating the clock. Configure the `i_cfg_cg_idle_count` parameter appropriately to balance power savings and performance requirements.

4. **Clock Domain Crossing**: This module assumes `i_user_valid` and `i_axi_valid` are synchronized to `clk_in`. If they come from different clock domains, additional synchronization may be required.

---

[Return to Index](index.md)

---