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

# Frequency Invariant Counter

## Overview

The `counter_freq_invariant` module divides an arbitrary input clock down to a
1 MHz tick, so your design can count real time without knowing its clock
frequency at compile time. You pick the division factor at run time through
`freq_sel`, which indexes a lookup table built at elaboration time from the
`MIN_FREQ_MHZ`, `MAX_FREQ_MHZ`, `NUM_FREQ_ENTRIES` and `FREQ_STRATEGY`
parameters.

The whole module rests on one convenient identity: **the division factor and the
clock frequency in MHz are the same number**. A 100 MHz clock has 100 cycles per
microsecond, so dividing by 100 yields a 1 MHz tick. The LUT just stores
frequencies in MHz and uses them directly as divisors. Elegant, once you see it.

One bit of history: an earlier revision of this module had a hardcoded 68-entry
frequency table and a fixed 4-bit `freq_sel`. That table is gone; the LUT is now
generated from parameters and `freq_sel` is sized to match `NUM_FREQ_ENTRIES`.

## Module Declaration

```systemverilog
module counter_freq_invariant #(
    // User parameters
    parameter int COUNTER_WIDTH    = 16,     // Width of output microsecond counter
    parameter int MIN_FREQ_MHZ     = 5,      // Lowest supported clock (MHz)
    parameter int MAX_FREQ_MHZ     = 220,    // Highest supported clock (MHz)
    parameter int NUM_FREQ_ENTRIES = 16,     // Number of LUT entries
    parameter int FREQ_STRATEGY    = 0,      // 0 = LINEAR, 1 = POW2
    parameter bit DEBUG_LUT        = 1'b0,   // Print LUT at time 0

    // Derived parameters (do not override)
    parameter int SEL_WIDTH     = (NUM_FREQ_ENTRIES > 1) ? $clog2(NUM_FREQ_ENTRIES) : 1,
    parameter int DIV_WIDTH     = $clog2(MAX_FREQ_MHZ + 1),
    parameter int PRESCALER_MAX = 2 ** DIV_WIDTH
) (
    input  logic                      clk,
    input  logic                      rst_n,
    input  logic                      sync_reset_n,
    input  logic [SEL_WIDTH-1:0]      freq_sel,
    output logic [COUNTER_WIDTH-1:0]  o_counter,
    output logic                      tick
);
```

## Parameters

| Parameter | Type | Default | Description |
|-----------|------|---------|-------------|
| COUNTER_WIDTH | int | 16 | Width of the microsecond counter. Wraps at 2^COUNTER_WIDTH. |
| MIN_FREQ_MHZ | int | 5 | Lowest clock frequency in the LUT, in MHz. Must be >= 1. |
| MAX_FREQ_MHZ | int | 220 | Highest clock frequency in the LUT, in MHz. Must be >= MIN_FREQ_MHZ. |
| NUM_FREQ_ENTRIES | int | 16 | Number of LUT entries. Must be >= 1. Sets `SEL_WIDTH`. |
| FREQ_STRATEGY | int | 0 | LUT distribution: 0 = LINEAR, 1 = POW2. |
| DEBUG_LUT | bit | 1'b0 | Print the generated LUT at simulation time 0. Simulation only. |

: counter_freq_invariant user parameters

**Derived parameters -- do not override.** `SEL_WIDTH`, `DIV_WIDTH` and
`PRESCALER_MAX` appear in the parameter list only so they can size ports and
internal counters. They're computed from the user parameters:

| Derived | Expression | Value at defaults |
|---------|------------|-------------------|
| SEL_WIDTH | `$clog2(NUM_FREQ_ENTRIES)`, min 1 | 4 |
| DIV_WIDTH | `$clog2(MAX_FREQ_MHZ + 1)` | 8 |
| PRESCALER_MAX | `2 ** DIV_WIDTH` | 256 |

: Derived parameters at the default configuration

Bad combinations get caught early: the three `$error` checks in the
`param_check` initial block reject `MIN_FREQ_MHZ < 1`,
`MAX_FREQ_MHZ < MIN_FREQ_MHZ`, and `NUM_FREQ_ENTRIES < 1` at elaboration.

## Ports

### Inputs

| Port | Width | Description |
|------|-------|-------------|
| `clk` | 1 | Input clock, any frequency covered by the LUT |
| `rst_n` | 1 | Active-low asynchronous reset |
| `sync_reset_n` | 1 | Synchronous run/reset. 0 holds the counter cleared; 1 runs. |
| `freq_sel` | SEL_WIDTH | LUT index selecting the division factor |

### Outputs

| Port | Width | Description |
|------|-------|-------------|
| `o_counter` | COUNTER_WIDTH | Microsecond counter, wraps at 2^COUNTER_WIDTH |
| `tick` | 1 | Single-cycle pulse, once per microsecond |

One naming gotcha: the output is `o_counter`, not `counter`.

## Architecture and Implementation

```
        freq_sel ---> [ LUT mux ] ---> division_factor
                            |
clk, rst_n ---> [ change detect ] ---> clear_pulse
                            |
                            v
                   [ counter_load_clear ] ---> prescaler_done
                            |
                            v
                   [ counter + tick reg ] ---> o_counter, tick
```

### LUT Generation Strategies

The LUT is built at elaboration time by a generate loop that evaluates a pure
integer function per index, so synthesis infers a mux or ROM rather than any
runtime arithmetic. That's what you want — no multiplier hiding in your timing
report.

**LINEAR (`FREQ_STRATEGY = 0`, default)**

```
freq[i] = MIN_FREQ_MHZ + (MAX_FREQ_MHZ - MIN_FREQ_MHZ) * i / (NUM_FREQ_ENTRIES - 1)
```

Uniform steps across the range. Integer division truncates. Good for FPGA
bring-up where predictable coverage of the operating range matters.

**POW2 (`FREQ_STRATEGY = 1`)**

```
freq[i] = min(MIN_FREQ_MHZ * 2^i, MAX_FREQ_MHZ)
```

Doubling from the minimum, clamped at the maximum. Gives finer resolution at the
low end and saturates once `MAX_FREQ_MHZ` is reached.

**Default LUT (LINEAR, 5-220 MHz, 16 entries)**

| freq_sel | Clock (MHz) | Cycles per us | freq_sel | Clock (MHz) | Cycles per us |
|----------|-------------|---------------|----------|-------------|---------------|
| 0 | 5 | 5 | 8 | 119 | 119 |
| 1 | 19 | 19 | 9 | 134 | 134 |
| 2 | 33 | 33 | 10 | 148 | 148 |
| 3 | 48 | 48 | 11 | 162 | 162 |
| 4 | 62 | 62 | 12 | 177 | 177 |
| 5 | 76 | 76 | 13 | 191 | 191 |
| 6 | 91 | 91 | 14 | 205 | 205 |
| 7 | 105 | 105 | 15 | 220 | 220 |

: Default LINEAR LUT. Division factor equals the clock frequency in MHz.

Set `DEBUG_LUT` and the table your parameters actually produce prints at time 0 —
much better than working it out by hand and being wrong.

**Same table under POW2**

Same range, same entry count, `FREQ_STRATEGY = 1`: you get 5, 10, 20, 40,
80, 160 MHz and then saturation at 220 MHz for indices 6 through 15. POW2 only
earns its keep when `NUM_FREQ_ENTRIES` is close to `log2(MAX/MIN) + 1`; beyond
that the remaining entries are duplicates.

### Division Factor Lookup

```systemverilog
logic [DIV_WIDTH-1:0] w_div_table [NUM_FREQ_ENTRIES];

generate
    for (genvar gi = 0; gi < NUM_FREQ_ENTRIES; gi++) begin : gen_div_entry
        assign w_div_table[gi] = DIV_WIDTH'(freq_mhz_at_idx(gi));
    end
endgenerate

logic [DIV_WIDTH-1:0] w_division_factor;
assign w_division_factor = w_div_table[freq_sel];
```

### Change Detection

A clear pulse fires whenever `freq_sel` changes or `sync_reset_n` is low. One
subtlety worth noticing: `r_clear_pulse` resets to 1, not 0, so the counter
starts life in the cleared state.

```systemverilog
always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
        r_prev_freq_sel <= '0;
        r_clear_pulse   <= 1'b1;    // start in reset state
    end else begin
        r_prev_freq_sel <= freq_sel;
        r_clear_pulse   <= (freq_sel != r_prev_freq_sel) || !sync_reset_n;
    end
end
```

### Prescaler

```systemverilog
counter_load_clear #(
    .MAX(PRESCALER_MAX)
) prescaler_counter (
    .clk       (clk),
    .rst_n     (rst_n),
    .clear     (r_clear_pulse),
    .increment (1'b1),
    .load      (1'b1),
    .loadval   (w_division_factor - DIV_WIDTH'(1)),
    .done      (w_prescaler_done),
    .count     ()
);
```

### Counter and Tick

`tick` pulses on **every** prescaler completion, once per microsecond. It is not
gated on the counter reaching its maximum — people assume otherwise, and it
leads to off-by-2^N bugs in timeout logic. Don't.

```systemverilog
always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
        o_counter <= '0;
        tick      <= 1'b0;
    end else begin
        if (r_clear_pulse) begin
            o_counter <= '0;
            tick      <= 1'b0;
        end else if (w_prescaler_done && sync_reset_n) begin
            o_counter <= o_counter + 1'b1;
            tick      <= 1'b1;
        end else begin
            tick <= 1'b0;
        end
    end
end
```

## Performance Characteristics

### Timing

| Property | Value |
|----------|-------|
| Tick period | `division_factor` input clock cycles = 1 us |
| Counter wrap period | `2^COUNTER_WIDTH` microseconds |
| Latency | 2 cycles (prescaler stage plus output register) |
| Reconfiguration | Immediate: a `freq_sel` change clears and reloads |

: counter_freq_invariant timing properties

At the default `COUNTER_WIDTH` of 16, the counter wraps every 65536 us, or about
65.5 ms. Size your timeout logic accordingly.

### Resource Use

| Element | Size |
|---------|------|
| Prescaler counter | `$clog2(PRESCALER_MAX)` bits |
| Microsecond counter | `COUNTER_WIDTH` bits |
| Change detection | `SEL_WIDTH + 1` flops |
| LUT | `NUM_FREQ_ENTRIES x DIV_WIDTH` bits of constant mux or ROM |

: Resource use by element

### Critical Path

The critical path runs through the prescaler increment and its terminal-count
comparison. Raising `MAX_FREQ_MHZ` widens `DIV_WIDTH` and lengthens that path —
something to watch if you're pushing frequency.

## Usage Examples

### 1. Microsecond timebase on an unknown FPGA clock

```systemverilog
logic [15:0] usec_count;
logic        usec_tick;

counter_freq_invariant #(
    .COUNTER_WIDTH   (16),
    .MIN_FREQ_MHZ    (5),
    .MAX_FREQ_MHZ    (220),
    .NUM_FREQ_ENTRIES(16),
    .FREQ_STRATEGY   (0)
) u_timebase (
    .clk         (sys_clk),
    .rst_n       (sys_rst_n),
    .sync_reset_n(1'b1),
    .freq_sel    (cfg_freq_sel),   // 4 bits at these parameters
    .o_counter   (usec_count),
    .tick        (usec_tick)
);
```

### 2. ASIC range, 100 MHz to 1 GHz

```systemverilog
counter_freq_invariant #(
    .COUNTER_WIDTH   (16),
    .MIN_FREQ_MHZ    (100),
    .MAX_FREQ_MHZ    (1000),
    .NUM_FREQ_ENTRIES(32),
    .FREQ_STRATEGY   (0)
) u_timer (
    .clk         (core_clk),
    .rst_n       (core_rst_n),
    .sync_reset_n(1'b1),
    .freq_sel    (cfg_freq_sel),   // 5 bits at NUM_FREQ_ENTRIES = 32
    .o_counter   (usec_count),
    .tick        (usec_tick)
);
```

`DIV_WIDTH` becomes `$clog2(1001)` = 10 bits here, and `PRESCALER_MAX` 1024.

### 3. Millisecond timeout built on the tick

```systemverilog
logic [9:0] r_msec;

always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n)                 r_msec <= '0;
    else if (usec_tick && usec_count[9:0] == 10'd0) r_msec <= r_msec + 1'b1;
end
```

A cheaper alternative is to watch a bit of `o_counter` directly: bit 9 toggles
approximately every 512 us.

### 4. Gating the timer with sync_reset_n

```systemverilog
// Hold the timer cleared while calibration is running
counter_freq_invariant #(
    .COUNTER_WIDTH(16)
) u_cal_timer (
    .clk         (clk),
    .rst_n       (rst_n),
    .sync_reset_n(!enter_calibration_mode),
    .freq_sel    (cfg_freq_sel),
    .o_counter   (cal_usec),
    .tick        (cal_tick)
);
```

## Verification

Test: `val/common/test_counter_freq_invariant.py`

Scenarios worth covering:

1. Every `freq_sel` index produces the expected tick period for its LUT entry
2. Changing `freq_sel` mid-operation clears and restarts cleanly
3. Asynchronous reset and `sync_reset_n` both clear `o_counter` and `tick`
4. `o_counter` wraps correctly at 2^COUNTER_WIDTH
5. Both `FREQ_STRATEGY` values generate the expected LUT
6. `NUM_FREQ_ENTRIES = 1` degenerate case elaborates and runs

## Design Considerations

### Choosing the LUT Range

`MIN_FREQ_MHZ` and `MAX_FREQ_MHZ` should bracket the clock frequencies the
design will actually see. Widening the range without raising
`NUM_FREQ_ENTRIES` coarsens the LINEAR steps, and a clock that falls between two
LUT entries produces a tick that is off by the rounding error. At the defaults
the step is about 14 MHz, so a 70 MHz clock selecting index 5 (76 MHz) ticks
roughly 8% slow. That's not an error term you can wave away in a watchdog.

If you need an exact tick at one known frequency, there's a cleaner path: set
`NUM_FREQ_ENTRIES` to 1 and `MIN_FREQ_MHZ` equal to `MAX_FREQ_MHZ` equal to that
frequency. `SEL_WIDTH` clamps to 1 in that case and `freq_sel` should be tied
to 0.

## Related Modules

- **counter_bin** - basic binary counter
- **counter_load_clear** - programmable counter, used here as the prescaler
- **clock_divider** - integer clock division producing a divided clock, not a tick
- **clock_pulse** - configurable pulse generator

## Navigation

- **[← Back to rtl-common Index](index.md)**
- **[← Back to Main Documentation Index](../index.md)**
