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

# Counter with Load and Clear

## Overview

The `counter_load_clear` module is a counter with a loadable terminal count and a clear — the workhorse you reach for when a plain counter isn't quite enough. You get precise control over counting behavior through configurable match values, which makes it a natural fit for timing applications, protocol implementations, and configurable delay generation.

## Module Interface
```systemverilog
module counter_load_clear #(
    parameter int MAX = 32'd32
) (
    input logic                     clk,
    input logic                     rst_n,
    input logic                     clear,
    input logic                     increment,
    input logic                     load,
    input logic [$clog2(MAX)-1:0]   loadval,
    output logic [$clog2(MAX)-1:0]  count,
    output logic                    done
);
```

## Parameters

| Parameter | Type | Default | Description |
|-----------|------|---------|-------------|
| `MAX` | `int` | `32'd32` | Maximum possible count value |

`MAX` ranges from `2` to `2^32-1` (the RTL header states the same). MAX=1 gives
`$clog2(1) = 0`, so `loadval` and `count` would be zero-width. The parameter
determines the counter width and the maximum loadable value: counter width = `$clog2(MAX)`.

## Ports

### Inputs

| Port | Width | Description |
|------|-------|-------------|
| `clk` | 1 | System clock |
| `rst_n` | 1 | Active-low asynchronous reset |
| `clear` | 1 | Synchronous clear (highest priority) |
| `increment` | 1 | Enable counter increment |
| `load` | 1 | Load new match value |
| `loadval` | `$clog2(MAX)` | New terminal count value |

### Outputs

| Port | Width | Description |
|------|-------|-------------|
| `count` | `$clog2(MAX)` | Current counter value |
| `done` | 1 | Terminal count reached flag |

## Functional Description

### Internal Registers

```systemverilog
logic [$clog2(MAX)-1:0] count;        // Current count value
logic [$clog2(MAX)-1:0] r_match_val;  // Terminal count register
```

### Priority Logic

Control is priority-based, and the order matters:

1. **Asynchronous Reset** (Highest Priority)
   - Resets both `count` and `r_match_val` to 0
   - Independent of clock edge

2. **Load Operation** (High Priority)
   - Updates `r_match_val` with `loadval`
   - Can occur simultaneously with other operations

3. **Clear Operation** (Medium Priority)
   - Immediately sets `count` to 0
   - Overrides increment operation

4. **Increment Operation** (Lowest Priority)
   - Advances counter or wraps to 0 at terminal count
   - Only when `increment` is asserted

### Main Control Logic

```systemverilog
always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
        count <= 'b0;
        r_match_val <= 'b0;
    end else begin
        // Load has independent priority
        if (load) r_match_val <= loadval;

        // Clear has highest operational priority
        if (clear) begin
            count <= 'b0;
        end else if (increment) begin
            count <= (count == r_match_val) ? 'b0 : count + 'b1;
        end
    end
end
```

### Done Signal Generation

```systemverilog
assign done = (count == r_match_val);
```

### Advanced Variants

### 1. Dual-Rate Timer

```systemverilog
// Timer with fast/slow modes
logic fast_mode;
logic [15:0] timer_period;

always_comb begin
    timer_period = fast_mode ? 16'd99 : 16'd999;  // 100 vs 1000 cycles
end

counter_load_clear #(.MAX(65536)) dual_timer (
    .clk(clk),
    .rst_n(rst_n),
    .clear(timer_done),         // Auto-restart
    .increment(1'b1),
    .load(timer_done),          // Reload on completion
    .loadval(timer_period),
    .count(timer_value),
    .done(timer_done)
);
```

### 2. PWM Generator

```systemverilog
// Simple PWM with configurable duty cycle
logic [7:0] duty_cycle;  // 0-255
logic pwm_out;

counter_load_clear #(.MAX(256)) pwm_counter (
    .clk(clk),
    .rst_n(rst_n),
    .clear(1'b0),
    .increment(1'b1),
    .load(1'b1),
    .loadval(8'd255),           // Always count 0-255
    .count(pwm_count),
    .done()
);

assign pwm_out = (pwm_count < duty_cycle);
```

### 3. Burst Generator

```systemverilog
// Generate bursts of N pulses
logic [7:0] burst_length;
logic start_burst, burst_active, burst_complete;

counter_load_clear #(.MAX(256)) burst_counter (
    .clk(clk),
    .rst_n(rst_n),
    .clear(start_burst),
    .increment(burst_active),
    .load(start_burst),
    .loadval(burst_length - 1),
    .count(burst_count),
    .done(burst_complete)
);

// State machine for burst control
always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
        burst_active <= 1'b0;
    end else begin
        if (start_burst)
            burst_active <= 1'b1;
        else if (burst_complete)
            burst_active <= 1'b0;
    end
end
```

### 4. Communication Timeout

```systemverilog
// UART receive timeout
logic rx_active, rx_timeout, char_received;
parameter RX_TIMEOUT_CYCLES = 1000;

counter_load_clear #(.MAX(2048)) rx_timer (
    .clk(clk),
    .rst_n(rst_n),
    .clear(char_received),      // Reset on new character
    .increment(rx_active),      // Only count when receiving
    .load(rx_active && !char_received),
    .loadval(RX_TIMEOUT_CYCLES-1),
    .count(),
    .done(rx_timeout)
);
```
## Timing Characteristics

### Basic Operation

```
Clock     : __|‾|__|‾|__|‾|__|‾|__|‾|__|‾|__|‾|__|‾|__
Reset_n   : _____|‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾
Load      : __________|‾‾‾|_________________________
LoadVal   : < 3 >
Clear     : __________________________________|‾‾‾|_
Increment : ________________|‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾|_
Count     : < 0 >< 0 >< 0 >< 1 >< 2 >< 3 >< 0 >
Done      : ‾‾‾‾‾‾‾‾‾‾‾‾‾‾_____________|‾‾‾|_______
```

`done` is combinational (`count == r_match_val`) and both reset to 0, so it
is **high out of reset** and stays high until the load writes a non-zero
match value. It is not a pulse that only appears at terminal count.

### Load During Count

Load only writes `r_match_val`; it does **not** stall the count. With
`increment` held high, `count` advances every cycle (including the load cycle).
Here `load` asserts while `count == 2`, so `r_match_val` becomes 5 starting the
next cycle — before `count` reaches the old match value 3 — so the counter never
wraps at 3 and instead runs to the new match 5:

```
Clock     : __|‾|__|‾|__|‾|__|‾|__|‾|__|‾|__|‾|__
Load      : ___________|‾‾‾|___________________
LoadVal   : < 5 >
Increment : |‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾|
Count     : < 0 >< 1 >< 2 >< 3 >< 4 >< 5 >< 0 >
r_match   : < 3 >< 3 >< 3 >< 5 >< 5 >< 5 >< 5 >
Done      : ________________________|‾‾‾|______
```

(If `load` had instead arrived after `count` already reached 3, the counter
would have wrapped at 3 first — the outcome depends on load timing relative to
the old match value.)

### Maximum Frequency

- **Typical**: 300-500 MHz in modern FPGAs
- **Critical Path**: Increment + comparison logic
- **Optimization**: Consider pipelining for extreme speeds

### Latency

- **Load Operation**: 1 cycle to update match value
- **Clear Operation**: 1 cycle to reset count
- **Done Signal**: Combinational (0 cycles)

## Usage Examples

### 1. Basic Counting Mode

```systemverilog
// Simple timer: count to 100
counter_load_clear #(.MAX(1000)) timer (
    .clk(clk),
    .rst_n(rst_n),
    .clear(1'b0),
    .increment(1'b1),
    .load(1'b1),
    .loadval(8'd99),    // Count 0-99 (100 cycles)
    .count(timer_count),
    .done(timer_done)
);
```

### 2. Configurable Delay Mode

```systemverilog
// Variable delay generator
logic [7:0] delay_setting;
logic start_delay, delay_complete;

counter_load_clear #(.MAX(256)) delay_gen (
    .clk(clk),
    .rst_n(rst_n),
    .clear(start_delay),        // Start new delay
    .increment(1'b1),
    .load(start_delay),         // Load new value when starting
    .loadval(delay_setting),
    .count(),
    .done(delay_complete)
);
```

### 3. Retriggerable Timer Mode

```systemverilog
// Watchdog timer that resets on activity
logic activity_detected, timeout;

counter_load_clear #(.MAX(10000)) watchdog (
    .clk(clk),
    .rst_n(rst_n),
    .clear(activity_detected),  // Reset on activity
    .increment(1'b1),
    .load(1'b1),
    .loadval(16'd9999),         // 10000 cycle timeout
    .count(),
    .done(timeout)
);
```

1. **Timer Modules**: Configurable timing generation
2. **Protocol Engines**: Timeout and retry mechanisms
3. **PWM Controllers**: Variable duty cycle generation
4. **Burst Generators**: Programmable pulse trains
5. **Watchdog Timers**: System monitoring and reset
6. **Clock Dividers**: Variable frequency division
7. **Test Pattern Generators**: Configurable test sequences

### Design Patterns

### Pattern 1: Auto-Reloading Timer

```systemverilog
wire auto_reload = timer_done;
counter_load_clear timer (
    .clear(auto_reload),
    .load(auto_reload),
    .loadval(PERIOD-1),
    .done(timer_done),
    ...
);
```

### Pattern 2: Conditional Counting

```systemverilog
wire count_enable = condition_met && !paused;
counter_load_clear conditional_timer (
    .increment(count_enable),
    ...
);
```

### Pattern 3: Dynamic Period Adjustment

```systemverilog
logic period_changed;
wire reload_needed = timer_done || period_changed;

counter_load_clear adaptive_timer (
    .clear(reload_needed),
    .load(reload_needed),
    .loadval(current_period),
    ...
);
```
## Testing

### Test Scenarios

1. **Basic Counting**: Verify normal increment operation
2. **Terminal Count**: Test done signal generation
3. **Load Operation**: Verify match value updates
4. **Clear Priority**: Test clear overrides increment
5. **Simultaneous Operations**: Load + clear + increment
6. **Boundary Conditions**: Count = 0, count = match_val
7. **Reset Behavior**: Async reset during various operations

### Coverage Model

```systemverilog
covergroup load_clear_cg @(posedge clk);
    cp_count: coverpoint count {
        bins zero = {0};
        bins low = {[1:MAX/4]};
        bins mid = {[MAX/4+1:3*MAX/4]};
        bins high = {[3*MAX/4+1:MAX-1]};
    }

    cp_match_val: coverpoint r_match_val {
        bins zero = {0};
        bins low = {[1:MAX/4]};
        bins mid = {[MAX/4+1:3*MAX/4]};
        bins high = {[3*MAX/4+1:MAX-1]};
    }

    cp_operations: coverpoint {clear, increment, load} {
        bins clear_only = {3'b100};
        bins inc_only = {3'b010};
        bins load_only = {3'b001};
        bins clear_inc = {3'b110};
        bins clear_load = {3'b101};
        bins inc_load = {3'b011};
        bins all_ops = {3'b111};
        bins no_ops = {3'b000};
    }

    cp_done: coverpoint done;

    // Cross coverage
    cross_done_ops: cross cp_operations, done;
endgroup
```

### Assertions

```systemverilog
// Count stays within the match value ONLY for the load-then-count pattern.
// This property does NOT hold in general: if a smaller match is loaded while
// count is already above it (load 5, count up to 5, then load 2), then
// count (5) > r_match_val (2) and the counter free-runs modulo 2^WIDTH until it
// happens to equal the new match again -- there is no terminal-count clamp,
// only the equality wrap. Do not copy this assertion into a testbench that
// dynamically REDUCES the terminal count; it will fail on correct RTL.
property count_bounds;   // holds only when match is never reduced below count
    @(posedge clk) disable iff (!rst_n)
    count <= r_match_val;
endproperty

// Done should be true when count equals match
property done_when_match;
    @(posedge clk) disable iff (!rst_n)
    (count == r_match_val) |-> done;
endproperty

// Clear should reset count to 0
property clear_resets_count;
    @(posedge clk) disable iff (!rst_n)
    clear |=> (count == 0);
endproperty

// Load should update match value
property load_updates_match;
    @(posedge clk) disable iff (!rst_n)
    load |=> (r_match_val == $past(loadval));
endproperty

assert property (count_bounds);
assert property (done_when_match);
assert property (clear_resets_count);
assert property (load_updates_match);
```

## Design Notes

### Resource Usage

- **Flip-Flops**: `$clog2(MAX)` for count + `$clog2(MAX)` for match = `2 × $clog2(MAX)`
- **LUTs**: Increment logic, comparator, and control logic

### Timing Optimization

```systemverilog
// For high-speed operation, pipeline the comparison
logic done_pipe;
always_ff @(posedge clk) begin
    done_pipe <= (count == r_match_val);
end
```

### Parameter Validation

```systemverilog
initial begin
    assert (MAX > 0) else $error("MAX must be positive");
    assert (MAX <= 2**30) else $warning("Large MAX may impact synthesis");
end
```

## Related Modules

- **counter** - Basic counter without load/clear
- **counter_freq_invariant** - Uses this module for prescaling
- Standard timer and PWM controller implementations

## Navigation

- **[← Back to rtl-common Index](index.md)**
- **[← Back to Main Documentation Index](../index.md)**
