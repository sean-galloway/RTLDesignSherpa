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

# Reset Synchronizer Module

## Purpose
The `reset_sync` module is a parameterized reset synchronizer with asynchronous assertion and synchronous deassertion. That combination is the whole point: reset needs to hit immediately when it fires, but it has to come *off* on a clock edge. Release it asynchronously and every flop downstream gets a setup/hold gamble. This is the standard circuit for proper reset distribution, and it exists to keep reset release from going metastable or violating timing.

## Key Features
- Asynchronous reset assertion (immediate)
- Synchronous reset deassertion (clocked)
- Parameterizable synchronization depth
- Metastability resolution
- Standard reset synchronizer topology
- Clean reset release timing

## Parameters

| Parameter | Type | Default | Description |
|-----------|------|---------|-------------|
| N | int | 3 | Number of synchronization stages. Must be >= 2; an elaboration `$error` rejects anything smaller. |
| KEEP_ATTRS | bit | 1'b1 | Attach vendor CDC attributes (`ASYNC_REG`, `SHREG_EXTRACT`, `altera_attribute`, `syn_preserve`) to the chain so tools recognize it and do not extract it into an SRL. |
| IN_ACTIVE_LOW | bit | 1'b1 | Polarity of the `rst_n` input. 1 = active-low (default), 0 = active-high. |
| OUT_ACTIVE_LOW | bit | 1'b1 | Polarity of the `sync_rst_n` output. 1 = active-low (default), 0 = active-high. |
| ASYNC_ASSERT | bit | 1'b1 | 1 = asynchronous assert with synchronous deassert (FPGA best practice). 0 = fully synchronous style, where assertion is also clocked. |

: reset_sync parameters

**Polarity without renaming ports.** `IN_ACTIVE_LOW` and `OUT_ACTIVE_LOW` let the
module sit in an active-high reset domain while the ports stay named `rst_n`
and `sync_rst_n`. The input gets normalized to an internal active-high form on
the way in, and the requested polarity gets applied on the way out:

```systemverilog
wire rst_in_h = IN_ACTIVE_LOW ? ~rst_n : rst_n;
...
sync_rst_n = OUT_ACTIVE_LOW ? ~sync_rst_h : sync_rst_h;
```

The names stick around for compatibility, which means a `reset_sync` with
`OUT_ACTIVE_LOW = 0` drives an active-**high** reset out of a port still called
`sync_rst_n`. Check the parameter, not the name.

## Ports

### Inputs
| Port | Width | Description |
|------|-------|-------------|
| `clk` | 1 | System clock for synchronization |
| `rst_n` | 1 | Asynchronous input reset (active-low) |

### Outputs
| Port | Width | Description |
|------|-------|-------------|
| `sync_rst_n` | 1 | Synchronized reset output (active-low) |

## Reset Synchronizer Theory

### The Reset Problem
Reset release is where synchronous designs get hurt. Mishandle it and you're
looking at:
- **Metastability**: When reset is released asynchronously relative to clock
- **Timing Violations**: Setup/hold violations during reset release
- **Race Conditions**: Different flip-flops releasing from reset at different times

### Asynchronous Assert, Synchronous Deassert
The behavior you actually want:
- **Assert**: Immediate (asynchronous) when reset input becomes active
- **Deassert**: Synchronized to clock edge to ensure clean timing

## Implementation Details

### Synchronization Register Chain

```systemverilog
logic [N-1:0] r_sync_reg = '0;
```

An N-stage shift register provides the synchronization delay. Here's the part
that trips everyone up: the chain carries the **active-high** internal form of
the reset — a 1 in the chain means "reset asserted". That's the opposite of
what the port names suggest, and it's the single most common source of confusion
when people read this module.

### Reset Logic

```systemverilog
// ASYNC_ASSERT = 1 (default): async assert, sync deassert
always_ff @(posedge clk or posedge rst_in_h) begin
    if (rst_in_h) r_sync_reg <= '1;                 // hold asserted through chain
    else          r_sync_reg <= {r_sync_reg[N-2:0], 1'b0};
end
```

While reset is asserted, the chain is held at all ones. Once it releases, zeros
shift in from the LSB, and after N clock edges the MSB has cleared and the reset
is considered released.

With `ASYNC_ASSERT = 0` the sensitivity list drops `rst_in_h` and assertion gets
sampled on the clock edge like any other synchronous load:

```systemverilog
always_ff @(posedge clk) begin
    if (rst_in_h) r_sync_reg <= '1;
    else          r_sync_reg <= {r_sync_reg[N-2:0], 1'b0};
end
```

That style can't assert reset while the clock is stopped — which is exactly why
the asynchronous-assert variant is the default.

### Output Assignment

```systemverilog
wire sync_rst_h = r_sync_reg[N-1];
always_comb begin
    sync_rst_n = OUT_ACTIVE_LOW ? ~sync_rst_h : sync_rst_h;
end
```

The MSB of the chain is the active-high synchronized reset; the output stage
applies the requested polarity.

The RTL body is written out four times inside a `generate`, once per combination
of `ASYNC_ASSERT` and `KEEP_ATTRS`, because the vendor attributes have to be
attached at the declaration. All four variants are logically identical apart
from the attributes and the sensitivity list. Yes, it's repetitive. That's the
attribute syntax's fault, not the author's.

## Timing Behavior

### Reset Assertion (Asynchronous)
```
rst_n:      ‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾╲_________________________
sync_rst_n: ‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾╲_________________________
                                ^
                           Immediate assertion
```

### Reset Deassertion (Synchronous, N=3)
```
clk:        ____╱‾╲____╱‾╲____╱‾╲____╱‾╲____╱‾╲____╱‾╲____
rst_n:      _________________╱‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾
r_sync_reg: 111  111  111  110  100  000  000  000  000
sync_rst_n: _________________________╱‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾
                                    ^
                            Synchronized deassertion
                            (N clock cycles after rst_n release)
```

### State Sequence for N=3

Default polarities (`IN_ACTIVE_LOW = 1`, `OUT_ACTIVE_LOW = 1`), so `rst_n = 0`
means reset asserted and `sync_rst_n = 0` means reset asserted downstream.
Remember the chain holds the active-high form, so 111 is "asserted".

| Clock | rst_n | rst_in_h | r_sync_reg | sync_rst_n | Description |
|-------|-------|----------|------------|------------|-------------|
| - | 0 | 1 | 111 | 0 | Reset asserted, chain forced to all ones |
| 1 | 1 | 0 | 110 | 0 | Reset released; first 0 shifted in |
| 2 | 1 | 0 | 100 | 0 | Second 0 shifted in |
| 3 | 1 | 0 | 000 | 1 | MSB clears; reset released downstream |
| 4+ | 1 | 0 | 000 | 1 | Stable, out of reset |

: reset_sync state sequence for N=3 at default polarities

The output releases on the third clock edge after `rst_n` goes high — those N
cycles are the metastability margin the chain exists to buy you.

## Special Implementation Notes

### 1. Why the chain looks inverted

The chain stores the **active-high** form of the reset, while the ports are named
for the active-low one. Read the dataflow in order and the confusion evaporates:

- `rst_in_h` is the input normalized to active-high
- while `rst_in_h` is 1, the chain is forced to all ones (reset asserted)
- when `rst_in_h` falls, zeros shift in from the LSB
- after N edges the MSB is 0, and the output stage inverts it back to the
  requested polarity

So during reset the register holds 1s and after release it drains to 0s — the
opposite of what the port names alone would tell you.

### 2. Metastability Resolution
The N stages buy you multiple clock cycles for metastability to resolve:
- Each flip-flop stage gets a chance to resolve potential metastability
- Probability of metastability propagation: (MTBF)^(-N)
- N=2 typically sufficient, N=3 provides extra margin

### 3. Initialization

```systemverilog
logic [N-1:0] r_sync_reg = '0;
```

The declaration initializer gives FPGA configuration a defined starting value.
Note which value: 0, the *released* state. So on an FPGA the design comes out of
configuration with reset already deasserted unless `rst_n` is asserted. On an
ASIC the initializer is ignored, and the first asynchronous assertion establishes
the state.

### 4. Vendor attributes

With `KEEP_ATTRS = 1` (the default) the chain carries `ASYNC_REG = "TRUE"` and
`SHREG_EXTRACT = "NO"` for Xilinx, `altera_attribute` forcing synchronizer
identification for Intel, and `syn_preserve` for Synplify. These do two jobs:
they stop the tool from packing the chain into an SRL primitive — which would
quietly destroy your metastability margin — and they let CDC reports recognize
it as a synchronizer. Set `KEEP_ATTRS = 0` only if your flow objects to the
attributes.

### 5. Parameterization Benefits

Configurable N lets you tune for different requirements:
- **N=2**: Minimum permitted, fast reset release
- **N=3**: Standard choice, good metastability margin
- **N>=4**: Conservative, slower release in exchange for maximum metastability protection

## Parameter Selection Guidelines

### Choosing N Value

#### N=2 (Minimum)
```systemverilog
reset_sync #(.N(2)) rst_sync_inst (
    .clk(sys_clk),
    .rst_n(external_rst_n),
    .sync_rst_n(internal_rst_n)
);
```
- **Use when**: Fast reset release required
- **Risk**: Minimal metastability margin
- **Applications**: High-speed designs with good clock quality

#### N=3 (Recommended)
```systemverilog
reset_sync #(.N(3)) rst_sync_inst (
    .clk(sys_clk),
    .rst_n(external_rst_n), 
    .sync_rst_n(internal_rst_n)
);
```
- **Use when**: Standard applications
- **Benefit**: Good balance of speed vs. metastability margin
- **Applications**: Most digital designs

#### N≥4 (Conservative)
```systemverilog
reset_sync #(.N(4)) rst_sync_inst (
    .clk(sys_clk),
    .rst_n(external_rst_n),
    .sync_rst_n(internal_rst_n)
);
```
- **Use when**: Critical applications, poor clock quality
- **Benefit**: Maximum metastability protection
- **Trade-off**: Slower reset release

## Applications

### Global Reset Distribution
```systemverilog
// Synchronize external reset for internal use
reset_sync #(.N(3)) global_rst_sync (
    .clk(system_clock),
    .rst_n(external_reset_n),
    .sync_rst_n(global_reset_n)
);

// Use synchronized reset throughout design
always_ff @(posedge system_clock or negedge global_reset_n) begin
    if (!global_reset_n) begin
        // Reset state
    end else begin
        // Normal operation
    end
end
```

### Clock Domain Crossing
```systemverilog
// Separate reset synchronizers for each clock domain
reset_sync #(.N(3)) clk_a_rst_sync (
    .clk(clk_a),
    .rst_n(system_rst_n),
    .sync_rst_n(clk_a_rst_n)
);

reset_sync #(.N(3)) clk_b_rst_sync (
    .clk(clk_b), 
    .rst_n(system_rst_n),
    .sync_rst_n(clk_b_rst_n)
);
```

### Power-On Reset
```systemverilog
// Synchronize power-on reset
reset_sync #(.N(3)) por_sync (
    .clk(main_clk),
    .rst_n(power_on_rst_n),
    .sync_rst_n(system_rst_n)
);
```

### Reset Controller Integration
```systemverilog
module reset_controller (
    input  logic sys_clk,
    input  logic external_rst_n,
    input  logic watchdog_rst_n,
    input  logic sw_rst,
    output logic sync_rst_n
);

    logic combined_rst_n;
    
    // Combine all reset sources
    assign combined_rst_n = external_rst_n & watchdog_rst_n & ~sw_rst;
    
    // Synchronize the combined reset
    reset_sync #(.N(3)) rst_sync_inst (
        .clk(sys_clk),
        .rst_n(combined_rst_n),
        .sync_rst_n(sync_rst_n)
    );

endmodule
```

## Design Considerations

### Reset Tree Planning
```systemverilog
// Plan reset distribution hierarchy
// Level 1: Global reset synchronizer
// Level 2: Domain-specific reset synchronizers  
// Level 3: Module-level reset distribution
```

### Clock Quality Requirements
- **Clean Clock**: Stable, low-jitter clock required
- **Clock Frequency**: Must be running during reset release
- **Clock Gating**: Avoid gating clock used for reset synchronization

### Reset Source Management
```systemverilog
// Multiple reset sources need careful combination
wire combined_reset = por_n & external_rst_n & watchdog_rst_n & ~soft_reset;
```

## Common Design Mistakes

### Incorrect Sensitivity List
```systemverilog
// WRONG: Missing async reset in sensitivity list
always_ff @(posedge clk) begin
    if (!rst_n) r_sync_reg <= '0;
    else r_sync_reg <= {r_sync_reg[N-2:0], 1'b1};
end

// CORRECT: Include async reset
always_ff @(posedge clk or negedge rst_n) begin
    // ... correct implementation
end
```

### Wrong Reset Polarity
```systemverilog
// Ensure consistent reset polarity throughout design
// This module uses active-low reset (rst_n)
```

### Clock Domain Issues
```systemverilog
// Each clock domain needs its own reset synchronizer
// Don't share synchronized reset across clock domains
```

## Verification Considerations

### Test Scenarios
- Reset assertion during various clock phases
- Reset deassertion timing verification
- Multiple reset assertion/deassertion cycles
- Clock jitter during reset release
- Power-on behavior

### Assertions
```systemverilog
// Verify synchronous deassertion
property sync_deassert;
    @(posedge clk) 
    $rose(rst_n) |-> ##N $rose(sync_rst_n);
endproperty

// Verify asynchronous assertion  
property async_assert;
    $fell(rst_n) |-> $fell(sync_rst_n);
endproperty
```

### Coverage Points
- All reset assertion scenarios
- Reset release with different clock phases
- Multiple consecutive reset cycles
- Parameter variation coverage (different N values)

## Test Verification

### Test Coverage
Test coverage for the reset_sync module lives in:
- **Testbench Class**: `bin/TBClasses/reset_sync_tb.py`
- **Test Runner**: `val/common/test_reset_sync.py`

### Test Scenarios
**Basic Reset Synchronization** - Verifies N-cycle synchronization delay
**Immediate Reset Assertion** - Verifies asynchronous assertion behavior
**Multiple Reset Cycles** - Tests repeated reset/release sequences
**Reset Glitch Filtering** - Validates recovery from short reset pulses

### Running Tests
```bash
# Run all reset_sync tests (4 configurations: N=2,3,4,5)
pytest val/common/test_reset_sync.py -v

# Run specific configuration
pytest val/common/test_reset_sync.py::test_reset_sync[2-min] -v

# Run with waveform generation
pytest val/common/test_reset_sync.py -v -s
```

### Test Results
All 4 parameter configurations passing (100% success rate):
- N=2 (min) - PASSED
- N=3 (typical) - PASSED
- N=4 (safe) - PASSED
- N=5 (max) - PASSED

**Bug Discovery**: the test suite caught a critical RTL bug on the initial run —
an inverted reset polarity. Exactly the kind of bug that sails through a smoke
test and ruins someone's bring-up. Thorough verification earns its keep.

## Related Modules

### Reset Synchronizer Variants
- **Positive-edge reset**: For active-high reset systems
- **Multi-domain reset**: For complex clock domain systems
- **Reset pulse generator**: For generating reset pulses
- **Reset debouncer**: For mechanical switch inputs

### Integration with Other Modules
- Clock domain crossing modules
- PLL/clock management units
- Power management controllers
- System controllers and reset managers

## Navigation

- **[← Back to rtl-common Index](index.md)**
- **[← Back to Main Documentation Index](../index.md)**
