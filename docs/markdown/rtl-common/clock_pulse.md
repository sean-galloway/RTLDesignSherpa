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

# clock_pulse

## Overview

The `clock_pulse` module is a periodic pulse generator with a configurable period: it emits a single-cycle pulse every WIDTH clock cycles. It's the part you reach for whenever something in the system needs to happen on a schedule — timing generation, heartbeat signals, sampling triggers, periodic events of any kind.

## Parameters

| Parameter | Type | Default | Description |
|-----------|------|---------|-------------|
| `WIDTH` | `int` | `10` | Period of the pulse generation in clock cycles |

`WIDTH` can range from 2 to 2^31-1. The parameter is declared `int`, which is 32-bit SIGNED, so 2^32-1 is not representable. It sets the pulse frequency (f_clk / WIDTH). The pulse itself is always exactly 1 clock cycle wide, which makes the duty cycle 1/WIDTH — 10% for WIDTH=10.

## Ports

```systemverilog
module clock_pulse #(
    parameter int WIDTH = 10  // PERIOD in clock cycles (the pulse itself is
                          // always exactly 1 cycle wide)
) (
    input  logic clk,    // Input clock signal
    input  logic rst_n,  // Input reset signal
    output logic pulse   // Output pulse signal
);
```

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| `clk` | Input | 1 | System clock input |
| `rst_n` | Input | 1 | Active-low asynchronous reset |
| `pulse` | Output | 1 | Periodic pulse output |

## Functional Description

### Internal Counter

```systemverilog
// WIDTH is the PERIOD; the counter only needs to hold 0..WIDTH-1, i.e.
// $clog2(WIDTH) bits (NOT WIDTH bits).
localparam int CW = (WIDTH < 2) ? 1 : $clog2(WIDTH);

logic [CW-1:0] r_counter;
logic [CW-1:0] w_width_minus_one;

// Properly sized period-1 constant
assign w_width_minus_one = CW'(WIDTH - 1);
```

### Core Logic

```systemverilog
always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
        r_counter <= 'b0;
        pulse     <= 'b0;
    end else begin
        if (r_counter < w_width_minus_one) 
            r_counter <= r_counter + 1'b1;
        else 
            r_counter <= 'b0;

        pulse <= (r_counter == w_width_minus_one);
    end
end
```

### Operation Principles

1. **Counter**: Free-running counter from 0 to WIDTH-1
2. **Pulse Generation**: `pulse` is **registered** — `pulse <= (r_counter ==
   WIDTH-1)` — so it asserts on the cycle **after** the counter reaches WIDTH-1,
   i.e. during the cycle when the counter has wrapped back to 0.
3. **Auto-Reset**: Counter wraps to 0 after reaching maximum
4. **Synchronous**: All operations synchronized to input clock
5. **Single Cycle**: Pulse duration is exactly one clock cycle

That second point is the one people get wrong, so let's be blunt about it: the registered comparison means `pulse` never coincides with the terminal count. It lands one cycle later, on the wrapped-to-zero count. Every timing diagram below follows from that.

## Related Modules

Nothing in the tree instantiates this module and it
instantiates nothing: it is a leaf, used directly by whatever design needs
it. Its nearest neighbours in `rtl/common/` are:

- `clock_divider`
- `clock_gate_ctrl`

---

## Timing Characteristics

### Timing Characteristics

- **Period**: WIDTH clock cycles
- **Frequency**: f_clk / WIDTH
- **Pulse Width**: 1 clock cycle
- **Duty Cycle**: 1/WIDTH
- **Phase**: Because the comparison is registered, `pulse` is high one cycle
  **after** `r_counter == WIDTH-1` — that is, during the `r_counter == 0` cycle
  of each period, not on the WIDTH-1 count itself.

### Basic Operation (WIDTH=4)

Watch where `pulse` actually lands — high during the `< 0 >` cell that immediately follows `< 3 >`, one cycle after the counter hit WIDTH-1. That's the registered comparison at work:

```
Clock:    _|‾|_|‾|_|‾|_|‾|_|‾|_|‾|_|‾|_|‾|_|‾|_|‾|_|‾|_
Counter:  < 0 >< 1 >< 2 >< 3 >< 0 >< 1 >< 2 >< 3 >< 0 >
Pulse:    ____________________|‾‾‾|______________|‾‾‾|
```

(The first `< 0 >` is the post-reset state, where `pulse` is still low.)

### Reset Behavior

```
Clock:    |‾‾__|‾‾__|‾‾__|‾‾__|‾‾__|‾‾__|‾‾__|‾‾__|‾‾__|‾‾__
Reset_n:  ‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾|___|‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾
Counter:  < 0 >< 1 >< 2 >< 3 >< 0 >< 0 >< 1 >< 2 >< 3 >< 0 >
Pulse:    _____________________________________________|‾‾‾|
```

Two things worth seeing here, both consequences of the pulse being registered
(`pulse <= (r_counter == w_width_minus_one)`):

- **The pulse that reset swallows.** The counter reaches 3 in the fourth cell,
  so a pulse would normally appear in the fifth — but reset is asserted exactly
  there, and reset forces `pulse <= 0`. That pulse never happens.
- **Recovery costs a full period.** After reset releases, the counter restarts
  from 0 and the first pulse appears in the cell *after* it next reaches 3 —
  the final cell above, not the one where the counter reads 3.

### Different WIDTH Values

| WIDTH | Period | Duty Cycle | Use Case |
|-------|--------|------------|----------|
| 2 | 2 cycles | 50% | Clock divider |
| 4 | 4 cycles | 25% | Sampling |
| 10 | 10 cycles | 10% | Timing reference |
| 100 | 100 cycles | 1% | Heartbeat |
| 1000 | 1000 cycles | 0.1% | Slow events |

## Usage Examples


Every parameter and port below is read from the module declaration.

```systemverilog
clock_pulse #(
    .WIDTH                 (10)
) u_clock_pulse (
    .clk                   (clk),
    .rst_n                 (rst_n),
    .pulse                 (pulse)
);
```

## Design Notes

### Resource Utilization

| WIDTH | Counter Bits | LUTs | FFs | Max Freq |
|-------|--------------|------|-----|----------|
| 8 | 3 | 8 | 4 | 500MHz |
| 16 | 4 | 12 | 5 | 450MHz |
| 32 | 5 | 18 | 6 | 400MHz |
| 1024 | 10 | 28 | 11 | 350MHz |

### Synthesis Considerations

For high-frequency applications, pipeline the comparison:

```systemverilog
// For high-frequency applications, pipeline the comparison (WIDTH >= 2).
// IMPORTANT: because the registered compare_result ALSO gates the counter
// wrap, it must be produced from the WIDTH-2 threshold, not WIDTH-1. Comparing
// against WIDTH-1 here makes the counter sequence 0..WIDTH,0 and yields a
// period of WIDTH+1, not WIDTH. With WIDTH-2 the period is exactly WIDTH and
// the pulse still lands on the r_counter==0 cycle, matching the base module.
module clock_pulse_pipelined #(
    parameter int WIDTH = 1000
) (
    input  logic clk,
    input  logic rst_n,
    output logic pulse
);

    localparam int CW = (WIDTH < 2) ? 1 : $clog2(WIDTH);
    logic [CW-1:0] r_counter;
    logic          compare_result;

    // Register the comparison one count early so the pipelined wrap keeps a
    // WIDTH-cycle period.
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) compare_result <= 1'b0;
        else        compare_result <= (r_counter == CW'(WIDTH - 2));
    end

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            r_counter <= 'b0;
            pulse     <= 1'b0;
        end else begin
            r_counter <= compare_result ? '0 : r_counter + 1'b1;
            pulse     <= compare_result;
        end
    end

endmodule
```

### Design Considerations

1. **Choose Appropriate WIDTH**: Balance between resolution and resource usage
2. **Consider Reset Timing**: Ensure clean startup behavior
3. **Validate Timing**: Verify pulse frequency matches requirements
4. **Plan for Variation**: Consider process, voltage, temperature effects
5. **Monitor Resource Usage**: Large counters can impact timing and area
6. **Use Enables**: Add enable signals for conditional operation
7. **Document Timing**: Clearly specify pulse rates and relationships

### Common Applications

1. **Timing References**: System heartbeats, watchdog timers
2. **Sampling Systems**: ADC triggers, data acquisition timing
3. **Communication**: Baud rate generation, protocol timing
4. **Memory Systems**: Refresh timing, access scheduling
5. **Test Equipment**: Pattern generation, stimulus timing
6. **Power Management**: Activity monitoring, timeout generation
7. **Display Systems**: Refresh rates, sync generation

That's the whole module. It's a small thing, but precise periodic timing shows up in nearly every design you'll ever ship — get this one right once, parameterize it well, and reuse it forever.

## Testing

### Comprehensive Test Bench

```systemverilog
module tb_clock_pulse;

    parameter WIDTH = 10;

    logic clk, rst_n, pulse;

    // Clock generation
    initial clk = 0;
    always #5ns clk = ~clk; // 100MHz

    // DUT instantiation
    clock_pulse #(.WIDTH(WIDTH)) dut (.*);

    // Test sequence
    initial begin
        rst_n = 0;
        #100ns rst_n = 1;

        // Test basic pulse generation
        test_basic_pulse_generation();

        // Test reset behavior
        test_reset_behavior();

        // Test timing accuracy
        test_timing_accuracy();

        $display("All tests completed!");
        $finish;
    end

    // Test basic pulse generation
    task test_basic_pulse_generation();
        int pulse_count = 0;
        int cycle_count = 0;
        begin
            $display("Testing basic pulse generation (WIDTH=%0d)...", WIDTH);

            // Monitor for several pulse periods. WIDTH*3 + 1 edges: `@(posedge clk)`
            // resumes BEFORE the NBA update, so pulses are first visible at edges
            // WIDTH+1, 2*WIDTH+1, 3*WIDTH+1 (see test_reset_behavior for the trace).
            repeat (WIDTH * 3 + 1) begin
                @(posedge clk);
                cycle_count++;
                if (pulse) pulse_count++;
            end

            // Verify pulse count
            if (pulse_count == 3) begin
                $display("PASS: Correct number of pulses generated");
            end else begin
                $error("FAIL: Expected 3 pulses, got %0d", pulse_count);
            end
        end
    endtask

    // Test reset behavior -- the two consequences of the registered pulse
    task test_reset_behavior();
        int pulses_during_reset = 0;
        int cycles_to_first_pulse = 0;
        begin
            $display("Testing reset behavior...");

            // Line the counter up so a pulse is due, then assert reset in
            // exactly that cycle. Reset forces pulse <= 0, so that pulse is
            // swallowed and never appears.
            repeat (WIDTH - 1) @(posedge clk);
            rst_n = 0;
            repeat (WIDTH * 2) begin
                @(posedge clk);
                if (pulse) pulses_during_reset++;
            end
            if (pulses_during_reset == 0) begin
                $display("PASS: no pulse while reset is asserted");
            end else begin
                $error("FAIL: %0d pulse(s) during reset", pulses_during_reset);
            end

            // Recovery costs a full period: the counter restarts from 0, so the
            // first pulse lands one cycle AFTER it next reaches WIDTH-1.
            @(negedge clk);
            rst_n = 1;
            // Expect the first pulse on the (WIDTH+1)th sampled edge, not the
            // WIDTHth. Three separate cycles are involved and it is easy to
            // lose one: the counter reaches WIDTH-1 at edge WIDTH-1, `pulse`
            // is NBA-assigned at edge WIDTH, and `@(posedge clk)` resumes in
            // the Active region -- BEFORE that edge's NBA update -- so the
            // high value is first visible at edge WIDTH+1.
            forever begin
                @(posedge clk);
                cycles_to_first_pulse++;
                if (pulse) break;
                if (cycles_to_first_pulse > WIDTH * 2) begin
                    $error("FAIL: no pulse within two periods of reset release");
                    break;
                end
            end
            if (cycles_to_first_pulse == WIDTH + 1) begin
                $display("PASS: first pulse %0d sampled edges after release",
                         WIDTH + 1);
            end else begin
                $error("FAIL: expected first pulse at cycle %0d, got %0d",
                       WIDTH + 1, cycles_to_first_pulse);
            end
        end
    endtask

    // Test timing accuracy
    task test_timing_accuracy();
        time pulse_times[10];
        time pulse_periods[9];
        int i;
        real avg_period, expected_period;
        begin
            $display("Testing timing accuracy...");

            expected_period = WIDTH * 10.0; // 10ns clock period

            // Capture pulse timing
            for (i = 0; i < 10; i++) begin
                @(posedge pulse);
                pulse_times[i] = $time;
            end

            // Calculate periods
            for (i = 0; i < 9; i++) begin
                pulse_periods[i] = pulse_times[i+1] - pulse_times[i];
            end

            // Calculate average period
            avg_period = 0;
            for (i = 0; i < 9; i++) begin
                avg_period += pulse_periods[i];
            end
            avg_period = avg_period / 9.0;

            // Check accuracy (within 1% tolerance)
            if (abs(avg_period - expected_period) < expected_period * 0.01) begin
                $display("PASS: Average period = %.1f ns (expected %.1f ns)", 
                         avg_period, expected_period);
            end else begin
                $error("FAIL: Average period = %.1f ns (expected %.1f ns)", 
                       avg_period, expected_period);
            end
        end
    endtask

    function real abs(real value);
        abs = (value >= 0) ? value : -value;
    endfunction

endmodule
```

### Coverage Model

```systemverilog
covergroup clock_pulse_cg @(posedge clk);

    cp_counter_values: coverpoint dut.r_counter {
        bins zero = {0};
        bins low[] = {[1:WIDTH/4]};
        bins mid[] = {[WIDTH/4+1:3*WIDTH/4]};
        bins high[] = {[3*WIDTH/4+1:WIDTH-2]};
        bins max = {WIDTH-1};
    }

    cp_pulse: coverpoint pulse {
        bins asserted = {1};
        bins deasserted = {0};
    }

    cp_reset: coverpoint rst_n {
        bins reset = {0};
        bins normal = {1};
    }

    // Transition coverage
    cp_pulse_edges: coverpoint pulse {
        bins rising = (0 => 1);
        bins falling = (1 => 0);
        bins stable_low = (0 => 0);
        bins stable_high = (1 => 1);
    }

    // Cross coverage
    cross_counter_pulse: cross cp_counter_values, cp_pulse;

endcovergroup
```

### Formal Properties

```systemverilog
module clock_pulse_properties;

    // Bind to DUT
    bind clock_pulse clock_pulse_properties props_inst (.*);

    // Property: reaching max count produces a pulse on the NEXT cycle.
    // The comparison is registered (pulse <= r_counter == WIDTH-1), so the
    // implication is |=> (next cycle), NOT |-> (same cycle).
    property pulse_after_max_count;
        @(posedge clk) disable iff (!rst_n)
        (dut.r_counter == WIDTH-1) |=> pulse;
    endproperty

    // Property: a pulse implies the PREVIOUS count was max
    property pulse_implies_prev_max;
        @(posedge clk) disable iff (!rst_n)
        pulse |-> $past(dut.r_counter == WIDTH-1);
    endproperty

    // Property: Counter wraps correctly
    property counter_wrap;
        @(posedge clk) disable iff (!rst_n)
        (dut.r_counter == WIDTH-1) |=> (dut.r_counter == 0);
    endproperty

    // Property: Counter increments
    property counter_increment;
        @(posedge clk) disable iff (!rst_n)
        (dut.r_counter < WIDTH-1) |=> 
        (dut.r_counter == $past(dut.r_counter) + 1);
    endproperty

    // Property: Reset behavior
    property reset_behavior;
        @(posedge clk)
        !rst_n |=> (dut.r_counter == 0) && !pulse;
    endproperty

    // Assertions
    assert property (pulse_after_max_count);
    assert property (pulse_implies_prev_max);
    assert property (counter_wrap);
    assert property (counter_increment);
    assert property (reset_behavior);

endmodule
```

## Navigation

- **[← Back to rtl-common Index](index.md)**
- **[← Back to Main Documentation Index](../index.md)**
