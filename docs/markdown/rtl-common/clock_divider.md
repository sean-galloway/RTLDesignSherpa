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

**[← Back to Main Index](../index.md)** | **[rtl-common Index](index.md)**

# Clock Divider

Multiple divided clocks from one input clock, all tapped off a single shared counter so they come out phase-aligned.

**WARNING:** NOT recommended for functional clocks! Use PLL/MMCM/clock manager primitives instead. This module is intended for testbenches, debug outputs, and non-critical timing applications.

## Overview

The `clock_divider` module generates multiple divided clock signals from a single input clock using configurable pick-off points from a shared master counter. Because every output taps the same counter, the divided clocks come out synchronized and phase-aligned — the behavior you need for multi-rate digital signal processing, communication systems, and power management applications.

```systemverilog
module clock_divider #(
    parameter int N             = 4,  // Number of output clocks
    parameter int PO_WIDTH      = 8,  // Width of the Pick off registers
    parameter int COUNTER_WIDTH = 64  // Width of the counter
) (
    input  logic                    clk,             // Input clock signal
    input  logic                    rst_n,           // Active low reset signal
    input  logic [(N*PO_WIDTH-1):0] pickoff_points,  // the pick off point config registers
    output logic [           N-1:0] divided_clk      // Divided clock signals
);
```

## Parameters

| Parameter | Type | Default | Description |
|-----------|------|---------|-------------|
| N | int | 4 | Number of independently configurable output clocks. Range: 1 to 16 (practical limit). Determines number of output clock domains and resource usage (N registers + N muxes). |
| PO_WIDTH | int | 8 | Bit width of each pick-off point configuration register. Range: 4 to 8 bits. Must be > `$clog2(COUNTER_WIDTH)` to avoid truncation — equivalently `PO_WIDTH >= $clog2(COUNTER_WIDTH + 1)`, which ensures PO_WIDTH can hold the value COUNTER_WIDTH without truncation. Examples: CW=16 needs PO≥5, CW=32 needs PO≥6, CW=64 needs PO≥7. Larger width allows finer counter bit selection but uses more configuration storage. Typical: PO_WIDTH=8 for COUNTER_WIDTH up to 128. |
| COUNTER_WIDTH | int | 64 | Bit width of the master binary counter. Range: 2 to 64 bits (practical range). Determines maximum division ratio (2^COUNTER_WIDTH). Example: WIDTH=16 → max division ratio = 65536. Larger counters enable slower frequencies but consume more resources. |

### Parameter Relationships

- **Addressing Constraint**: `PO_WIDTH > $clog2(COUNTER_WIDTH)` (strictly
  greater — the RTL `$fatal`s at elaboration if `PO_WIDTH <= $clog2(COUNTER_WIDTH)`).
  E.g. `COUNTER_WIDTH=16` needs `PO_WIDTH ≥ 5`.
- **Division Range**: Each output can divide by 2^1 to 2^COUNTER_WIDTH
- **Configuration Width**: Total configuration bits = `N × PO_WIDTH`

## Ports

### Inputs

| Port | Width | Description |
|------|-------|-------------|
| clk | 1 | Master input clock (source to be divided) |
| rst_n | 1 | Active-low asynchronous reset |
| pickoff_points | N×PO_WIDTH | Packed pickoff point configuration array |

**pickoff_points Format:**
```
Bit Packing: {po[N-1], ..., po[1], po[0]}
Each po[i] (PO_WIDTH bits): Counter bit index to sample for output i
```

### Outputs

| Port | Width | Description |
|------|-------|-------------|
| divided_clk | N | Divided clock outputs (registered) |

## Functional Description

### Counter Operation

- Free-running binary counter increments every input clock cycle
- Wraps at 2^COUNTER_WIDTH (no overflow flag)
- Each bit toggles at half the frequency of the previous bit
  - Bit 0: clk/2 (toggles every cycle)
  - Bit 1: clk/4 (toggles every 2 cycles)
  - Bit N: clk/2^(N+1)

### Pickoff Point Selection

- Each output `i` samples `counter[pickoff_points[i]]`
- Division ratio = 2^(pickoff_point+1)
- Example: pickoff=3 → samples counter[3] → divides by 16

### Out-of-Range Handling

- If `pickoff_points[i] ≥ COUNTER_WIDTH`, clamps to `COUNTER_WIDTH-1` (MSB)
- Prevents illegal bit indexing
- MSB provides slowest possible division

### Output Registration

- All `divided_clk` outputs are registered for glitch-free operation
- Adds 1 cycle latency but prevents combinational glitches
- Reset clears all outputs to 0 (low phase)

### Division Ratios (100MHz Input Clock)

| pickoff_point | Counter Bit | Division Ratio | Output Freq | Period |
|---------------|-------------|----------------|-------------|---------|
| 0 | [0] | 2 | 50MHz | 20ns |
| 1 | [1] | 4 | 25MHz | 40ns |
| 2 | [2] | 8 | 12.5MHz | 80ns |
| 3 | [3] | 16 | 6.25MHz | 160ns |
| 4 | [4] | 32 | 3.125MHz | 320ns |
| 5 | [5] | 64 | 1.5625MHz | 640ns |
| 10 | [10] | 2048 | 48.8kHz | 20.5µs |
| 15 | [15] | 65536 | 1.5kHz | 655µs |
| 19 | [19] | 1048576 | 95Hz | 10.5ms |
| 23 | [23] | 16777216 | 6Hz | 168ms |

### Duty Cycle

- All divided clocks have 50% duty cycle
- Result of sampling counter bit (toggle behavior)
- High for 2^(pickoff_point) input cycles
- Low for 2^(pickoff_point) input cycles

### Internal Signals

```systemverilog
logic [COUNTER_WIDTH-1:0] r_divider_counters;  // Free-running binary counter
localparam int ADDR_WIDTH = $clog2(COUNTER_WIDTH);  // Address width
```

## Timing

### Latency

- **Output Latency**: 1 cycle (registered output)
- **Clock-to-Q**: Standard flip-flop delay
- **Propagation**: Counter increment → mux → output register

### Phase Relationships

- All divided clocks share same counter → phase-locked to each other
- Divided clocks have phase offset relative to input clock
- Phase offset depends on counter reset value (0)

### Jitter

- Input clock jitter propagates to outputs
- Additional quantization jitter: ±1 input clock cycle
- For low-jitter clocks: Use dedicated PLL/clock synthesis

### Maximum Frequency

- **Limiting Factor**: Counter width and mux depth
- **Typical Performance**:
  - COUNTER_WIDTH=16: ~500 MHz (modern FPGAs)
  - COUNTER_WIDTH=32: ~400 MHz
  - COUNTER_WIDTH=64: ~300 MHz

### Resource Scaling

| COUNTER_WIDTH | N Outputs | FFs | LUTs (mux, est.) | fmax (Est.) |
|---------------|-----------|-----|------------------|-------------|
| 16 | 4 | 20 | ~12 | 500 MHz |
| 32 | 4 | 36 | ~28 | 400 MHz |
| 64 | 4 | 68 | ~52 | 300 MHz |
| 16 | 8 | 24 | ~24 | 500 MHz |

FF counts are exact (COUNTER_WIDTH counter bits + N output registers). The LUT
column is `N * ceil((COUNTER_WIDTH-1)/5)` for the pickoff muxes on a 6-LUT
architecture, excluding the clamp comparators; earlier revisions of this table
listed 8/10/12, which did not scale with the mux width and understated the
wide-counter cases by several times. fmax figures remain unsourced estimates.

## Usage Example

### Four Debug Clocks

```systemverilog
// Generate clk/4, clk/16, clk/256, clk/65536
logic [31:0] pickoff_cfg;
assign pickoff_cfg = {8'd15, 8'd7, 8'd3, 8'd1};  // {po3, po2, po1, po0}

clock_divider #(
    .N(4),              // 4 outputs
    .PO_WIDTH(8),       // 8-bit pickoff point
    .COUNTER_WIDTH(16)  // 16-bit counter (max div = 65536)
) u_clk_div (
    .clk           (clk_100mhz),
    .rst_n         (rst_n),
    .pickoff_points(pickoff_cfg),
    .divided_clk   ({clk_1p5khz, clk_390khz, clk_6p25mhz, clk_25mhz})
);
```

### Baud Rate Generator (Approximate)

```systemverilog
// For 9600 baud from 100MHz:
// Ideal: 100MHz / 9600 ≈ 10417 (not power-of-2)
// Closest power-of-2: 2^13 = 8192 → 100MHz/8192 = 12.2kHz
// WARNING: 12.2kHz vs 9.6kHz is a ~27% error -- FAR beyond the ~2-3% a UART
// can tolerate, and it is NOT a 16x-oversampling clock for 9600 baud either.
// A power-of-2 divider CANNOT hit standard baud rates. For a real UART use
// counter_load_clear (arbitrary modulus), not this divider.

logic [7:0] baud_pickoff = 8'd12;  // 2^13 = 8192 division (illustrative only)

clock_divider #(
    .N(1),
    .PO_WIDTH(8),
    .COUNTER_WIDTH(16)
) u_baud_clk (
    .clk           (sys_clk),
    .rst_n         (rst_n),
    .pickoff_points(baud_pickoff),
    .divided_clk   (uart_baud_x16)  // 16× oversampling clock
);
```

**Note:** For precise baud rates (not power-of-2), use `counter_load_clear` instead.

### Runtime-Programmable Divider

```systemverilog
// APB-configurable clock divider
logic [7:0] cfg_pickoff_0, cfg_pickoff_1;

always_ff @(posedge pclk) begin
    if (pwrite && paddr == ADDR_PICKOFF_0) cfg_pickoff_0 <= pwdata[7:0];
    if (pwrite && paddr == ADDR_PICKOFF_1) cfg_pickoff_1 <= pwdata[7:0];
end

clock_divider #(
    .N(2),
    .PO_WIDTH(8),
    .COUNTER_WIDTH(24)
) u_cfg_clk_div (
    .clk           (core_clk),
    .rst_n         (core_rst_n),
    .pickoff_points({cfg_pickoff_1, cfg_pickoff_0}),
    .divided_clk   ({clk_out_1, clk_out_0})
);
```

### Test Clock Generation

```systemverilog
// Generate 8 test clocks for debug
clock_divider #(
    .N(8),              // 8 debug clocks
    .PO_WIDTH(8),
    .COUNTER_WIDTH(32)  // Support ultra-slow clocks
) u_test_clks (
    .clk           (ref_clk),
    .rst_n         (test_rst_n),
    .pickoff_points({8'd20, 8'd18, 8'd16, 8'd14, 8'd12, 8'd10, 8'd8, 8'd6}),
    .divided_clk   (test_clk_bus)
);
```

## Design Notes

### Changing Pickoff Points at Runtime

```systemverilog
// To avoid glitches when changing pickoff configuration:
// 1. Assert rst_n (reset)
// 2. Change pickoff_points
// 3. Wait for configuration to settle
// 4. Deassert rst_n
// 5. Outputs start with new division ratios

// The sequence spans three clocks, so it is a small FSM in the logic that owns
// the configuration registers. It cannot be written as one always_ff with
// embedded `@(posedge cfg_clk)` statements: IEEE 1800 allows exactly one event
// control on an always_ff and none inside its body, so that form does not
// compile.

typedef enum logic [1:0] {CFG_IDLE, CFG_LOAD, CFG_RELEASE} cfg_state_t;

cfg_state_t                r_cfg_state;
logic [(N*PO_WIDTH)-1:0]   r_pickoff;
logic                      r_div_rst_n;

always_ff @(posedge cfg_clk or negedge cfg_rst_n) begin
    if (!cfg_rst_n) begin
        r_cfg_state <= CFG_IDLE;
        r_div_rst_n <= 1'b1;
        r_pickoff   <= DEFAULT_PICKOFF_POINTS;
    end else begin
        case (r_cfg_state)
            CFG_IDLE: if (cfg_write) begin
                r_div_rst_n <= 1'b0;         // 1. hold the divider in reset
                r_cfg_state <= CFG_LOAD;
            end
            CFG_LOAD: begin
                r_pickoff   <= cfg_data;     // 2. safe now: outputs are held low
                r_cfg_state <= CFG_RELEASE;
            end
            CFG_RELEASE: begin
                r_div_rst_n <= 1'b1;         // 3. restart on the new ratios
                r_cfg_state <= CFG_IDLE;
            end
            default: r_cfg_state <= CFG_IDLE;
        endcase
    end
end

clock_divider #(
    .N            (N),
    .PO_WIDTH     (PO_WIDTH),
    .COUNTER_WIDTH(COUNTER_WIDTH)
) u_div (
    .clk           (cfg_clk),
    .rst_n         (r_div_rst_n),   // divider reset is driven by the FSM above
    .pickoff_points(r_pickoff),
    .divided_clk   (divided_clk)
);
```

Note that `divided_clk` is held low for the two cycles the FSM spends in reset;
downstream logic must tolerate the gap rather than assume a continuous clock.
Treat these outputs as enables into a synchronous fabric, not as clocks driving
a separate domain -- see the warning under Synthesis Considerations.

### Synthesis Considerations

**Resource Utilization:**
- **Flip-Flops**: COUNTER_WIDTH (counter) + N (output registers)
- **LUTs**: one COUNTER_WIDTH-to-1 mux per output (pickoff selection), plus a
  clamp comparator per output. On a 6-input LUT architecture a CW-to-1 bit mux
  costs about `ceil((CW-1)/5)` LUTs, so the mux cost scales with COUNTER_WIDTH
  -- it is not a fixed overhead.
- **Example (N=4, COUNTER_WIDTH=16)**: ~20 FFs, ~12 LUTs for the muxes plus
  clamp logic. These are analytic estimates, not synthesis results.

**Timing Optimization:**
- **Critical Path**: Counter increment → mux → output register
- **For high-frequency operation**:
  - Reduce COUNTER_WIDTH (if possible)
  - Pipeline counter output (add register stage)
  - Use dedicated clock resources (PLL/MMCM)

**Power Optimization:**
- **Clock Gating**: Gate counter when no divided clocks needed
- **Selective Outputs**: Only generate divided clocks actually used
- **Example**:
```systemverilog
logic counter_enable;
assign counter_enable = |divided_clk_enable;  // Only run when needed

always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) r_divider_counters <= 0;
    else if (counter_enable) r_divider_counters <= r_divider_counters + 1;
end
```

### Important Warnings

This is the part that bites people, so read it twice.

#### NOT for Functional Clocks
**Do NOT use for:**
- Primary system clocks
- Clocking synchronous logic
- Production designs requiring precise timing

**Use PLL/MMCM/Clock Manager instead:**
- Dedicated clock synthesis primitives
- Clean clock tree
- Proper static timing analysis (STA)
- Phase-locked loops for low jitter
- Precise frequency generation

#### Derived Clock Hazards
Using `divided_clk` as a clock creates a **derived clock**:
- Complicates timing analysis
- STA tools may not properly constrain
- Potential setup/hold violations
- Clock domain crossing issues

#### Only Power-of-2 Divisions
- This module ONLY supports power-of-2 division ratios (2, 4, 8, 16, ...)
- For arbitrary ratios (e.g., divide by 7, 100, 1000): Use `counter_load_clear`

#### Glitches During Configuration Changes
- Changing `pickoff_points` at runtime can cause glitches
- Always reset module when changing configuration
- Do NOT change configuration while outputs are actively used

## Related Modules

- `counter_bin.sv` - Simple binary counter (related, not instantiated here —
  `clock_divider` keeps its own `r_divider_counters` array)
- `counter_freq_invariant.sv` - Time-based counter with 1MHz tick
- `counter_load_clear.sv` - Arbitrary division ratios (not power-of-2)
- `clock_pulse.sv` - Configurable pulse generator
- `clock_gate_ctrl.sv` - Clock gating for power management

## Testing

### Test Scenarios

1. **Single Output**: N=1 with various pickoff points
2. **Multiple Outputs**: N=4 with different divisions
3. **Out-of-Range Clamping**: pickoff ≥ COUNTER_WIDTH
4. **Runtime Changes**: Modify pickoff_points dynamically
5. **Reset Behavior**: All outputs low after reset
6. **Division Verification**: Measure output frequencies
7. **Edge Cases**:
   - pickoff=0 (divide by 2)
   - pickoff=COUNTER_WIDTH-1 (slowest division)
   - pickoff > COUNTER_WIDTH (clamping)

### Coverage Points

```systemverilog
covergroup clock_divider_cg @(posedge clk);
    cp_pickoff_range: coverpoint pickoff_points[7:0] {
        bins low = {[0:3]};
        bins mid = {[4:11]};
        bins high = {[12:15]};
        bins oob = {[16:255]};  // Out-of-bounds (will clamp)
    }

    cp_outputs: coverpoint divided_clk {
        bins all_outputs[] = {[1:$]};
    }
endgroup
```

## Navigation

- **[← Back to rtl-common Index](index.md)**
- **[← Back to Main Documentation Index](../index.md)**
