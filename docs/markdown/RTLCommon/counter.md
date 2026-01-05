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

# Basic Counter Module

## Overview
The `counter` module is a simple, configurable up-counter that generates a tick pulse when reaching its maximum value. It's designed for basic timing applications where a periodic signal is needed.

## Module Declaration
```systemverilog
module counter #(
    parameter int MAX = 32767
) (
    input  logic clk,
    input  logic rst_n,
    output logic tick
);
```

## Parameters

### MAX
- **Type**: `int`
- **Default**: `32767`
- **Description**: Maximum count value before wrapping to zero
- **Range**: Any positive integer
- **Width Calculation**: Counter width is automatically calculated as `$clog2(MAX+1)`

## Ports

### Inputs
| Port | Width | Type | Description |
|------|-------|------|-------------|
| `clk` | 1 | `logic` | System clock input |
| `rst_n` | 1 | `logic` | Active-low asynchronous reset |

### Outputs
| Port | Width | Type | Description |
|------|-------|------|-------------|
| `tick` | 1 | `logic` | Pulse output when counter reaches MAX |

## Internal Architecture

### Counter Register
```systemverilog
logic [$clog2(MAX+1)-1:0] r_count;
```
- **Width**: Automatically sized to accommodate MAX value
- **Reset Value**: `'0` (zero)
- **Operation**: Increments every clock cycle until reaching MAX

### State Machine Behavior
The counter operates as a simple state machine:

1. **Reset State**: `r_count = 0`, `tick = 0`
2. **Counting State**: `r_count` increments each cycle
3. **Maximum State**: `r_count = MAX`, `tick = 1` for one cycle
4. **Wrap State**: `r_count` returns to 0, cycle repeats

## Implementation Details

### Main Counter Logic
```systemverilog
always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
        r_count <= '0;
    end else begin
        if (r_count == MAX[$clog2(MAX+1)-1:0]) begin
            r_count <= '0;
        end else begin
            r_count <= r_count + 1'b1;
        end
    end
end
```

### Tick Generation
```systemverilog
assign tick = (r_count == MAX[$clog2(MAX+1)-1:0]);
```

### Key Features
- **Automatic Width Sizing**: Counter width adapts to MAX parameter
- **Wrap-around Operation**: Automatically returns to zero after MAX
- **Single Cycle Tick**: Tick pulse lasts exactly one clock cycle
- **Asynchronous Reset**: Immediate reset capability

## Timing Characteristics

### Period Calculation
- **Total Period**: `MAX + 1` clock cycles
- **Tick Frequency**: `f_clk / (MAX + 1)`
- **Duty Cycle**: `1 / (MAX + 1)`

### Examples
| MAX Value | Counter Width | Period (cycles) | Tick Frequency |
|-----------|---------------|-----------------|----------------|
| 7 | 3 bits | 8 | f_clk/8 |
| 15 | 4 bits | 16 | f_clk/16 |
| 99 | 7 bits | 100 | f_clk/100 |
| 999 | 10 bits | 1000 | f_clk/1000 |

## Usage Examples

### 1. Basic Timer (1ms tick at 100MHz)
```systemverilog
counter #(
    .MAX(99999)  // 100,000 cycles = 1ms at 100MHz
) timer_1ms (
    .clk(clk_100mhz),
    .rst_n(rst_n),
    .tick(tick_1ms)
);
```

### 2. Heartbeat Generator (1Hz at 50MHz)
```systemverilog
counter #(
    .MAX(49999999)  // 50M cycles = 1 second at 50MHz
) heartbeat (
    .clk(clk_50mhz),
    .rst_n(rst_n),
    .tick(heartbeat_1hz)
);
```

### 3. Simple Divider (Divide by 8)
```systemverilog
counter #(
    .MAX(7)  // 8 cycles total
) div8 (
    .clk(clk_in),
    .rst_n(rst_n),
    .tick(clk_div8)
);
```

## Design Considerations

### Resource Usage
- **LUTs**: Approximately `$clog2(MAX+1)` LUTs for the counter
- **FFs**: `$clog2(MAX+1)` flip-flops for the counter register
- **Logic Levels**: Single level for tick generation

### Performance
- **Maximum Frequency**: Limited by counter increment logic
- **Reset Recovery**: One clock cycle after reset deassertion
- **Propagation Delay**: Tick output has minimal combinational delay

### Power Optimization
- **Clock Gating**: Consider gating when tick output not needed
- **Reset Strategy**: Asynchronous reset reduces reset tree loading
- **Parameter Selection**: Smaller MAX values reduce power consumption

## Synthesis Considerations

### Parameter Constraints
```systemverilog
initial begin
    assert (MAX > 0) else $error("MAX must be positive");
    assert (MAX < 2**31) else $warning("Large MAX may impact synthesis");
end
```

### Optimization Hints
- **Binary MAX Values**: Powers of 2 minus 1 optimize better (7, 15, 31, etc.)
- **Tool Directives**: Consider synthesis attributes for timing-critical paths
- **Reset Inference**: Ensure reset is properly inferred as asynchronous

## Common Applications
1. **Periodic Timers**: Generating regular time intervals
2. **Clock Division**: Creating slower clock enables
3. **Timeout Generation**: Watchdog timers and timeouts
4. **Sampling Control**: Periodic data sampling triggers
5. **LED Blinking**: Visual indicators and status displays
6. **Protocol Timing**: Communication protocol timeouts

## Verification Considerations

### Test Scenarios
1. **Basic Counting**: Verify counting from 0 to MAX
2. **Wrap Behavior**: Confirm return to zero after MAX
3. **Tick Generation**: Verify single-cycle tick pulse
4. **Reset Functionality**: Test asynchronous reset operation
5. **Parameter Sweep**: Test various MAX values

### Coverage Points
- Counter reaches MAX value
- Counter wraps from MAX to 0
- Tick pulse generation timing
- Reset during counting operation

## Limitations
1. **No Enable Control**: Always counting when not in reset
2. **Up-Counter Only**: Cannot count down or bidirectionally
3. **Fixed Increment**: Always increments by 1
4. **No Load Capability**: Cannot load arbitrary values
5. **Single Output**: Only provides tick signal, not count value

## Related Modules
- `counter_load_clear`: Adds load and clear functionality
- `counter_bin`: Specialized for FIFO applications
- `counter_freq_invariant`: Frequency-independent timing
- `clock_pulse`: Similar functionality with different interface

## Navigation

- **[← Back to RTLCommon Index](index.md)**
- **[← Back to Main Documentation Index](../../index.md)**
