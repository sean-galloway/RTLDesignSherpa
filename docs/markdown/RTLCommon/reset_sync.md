# Reset Synchronizer Module

## Purpose
The `reset_sync` module implements a parameterized reset synchronizer that provides asynchronous assertion and synchronous deassertion of reset signals. This is a critical circuit for proper reset distribution in synchronous digital systems, ensuring that reset release occurs synchronously with the clock to prevent metastability and timing violations.

## Key Features
- Asynchronous reset assertion (immediate)
- Synchronous reset deassertion (clocked)
- Parameterizable synchronization depth
- Metastability resolution
- Standard reset synchronizer topology
- Clean reset release timing

## Port Description

### Parameters
- **N**: Number of synchronization stages (default: 3)

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
In synchronous digital systems, reset signals must be carefully managed to avoid:
- **Metastability**: When reset is released asynchronously relative to clock
- **Timing Violations**: Setup/hold violations during reset release
- **Race Conditions**: Different flip-flops releasing from reset at different times

### Asynchronous Assert, Synchronous Deassert
The ideal reset behavior is:
- **Assert**: Immediate (asynchronous) when reset input becomes active
- **Deassert**: Synchronized to clock edge to ensure clean timing

## Implementation Details

### Synchronization Register Chain
```systemverilog
logic [N-1:0] r_sync_reg = {N{1'b0}};
```
An N-stage shift register initialized to all zeros provides the synchronization delay.

### Reset Logic (Corrected Implementation)
```systemverilog
always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin                             // When rst_n is LOW (active reset)
        r_sync_reg <= {N{1'b0}};                 // Clear register (reset asserted)
    end else begin                                // When rst_n is HIGH (inactive)
        r_sync_reg <= {r_sync_reg[N-2:0], 1'b1}; // Shift in 1's (releasing reset)
    end
end
```

**Critical Bug Fix (2025-10-14):**
- **Original bug**: Logic was inverted (`if (rst_n)` instead of `if (!rst_n)`)
- **Impact**: Module was completely non-functional - reset never worked correctly
- **Discovered by**: Comprehensive test suite (val/common/test_reset_sync.py)
- **Fix**: Corrected reset polarity check
- **Verification**: All 4 test configurations passing (N=2, 3, 4, 5)

### Output Assignment
```systemverilog
assign sync_rst_n = r_sync_reg[N-1];
```
The synchronized reset output comes from the final stage of the shift register.

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
r_sync_reg: 000  000  000  001  011  111  111  111  111
sync_rst_n: _________________________╱‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾
                                    ^
                            Synchronized deassertion
                            (N clock cycles after rst_n release)
```

### State Sequence for N=3
| Clock | rst_n | r_sync_reg | sync_rst_n | Description |
|-------|-------|------------|------------|-------------|
| - | 0 | 000 | 0 | Reset active, output low |
| 1 | 0 | 001 | 0 | First 1 shifted in |
| 2 | 0 | 011 | 0 | Second 1 shifted in |
| 3 | 0 | 111 | 1 | Third 1 reaches output |
| 4+ | 0 | 111 | 1 | Reset deasserted, stable |

## Special Implementation Notes

### 1. Inverted Logic Explanation
The seemingly counterintuitive reset condition logic serves a specific purpose:
- During reset: shift register accumulates 1's
- After reset release: shift register is cleared, then accumulates 1's again
- This ensures N clock cycles of delay before output goes high

### 2. Metastability Resolution
The N-stage design provides multiple clock cycles for metastability resolution:
- Each flip-flop stage resolves potential metastability
- Probability of metastability propagation: (MTBF)^(-N)
- N=2 typically sufficient, N=3 provides extra margin

### 3. Initialization
```systemverilog
logic [N-1:0] r_sync_reg = {N{1'b0}};
```
Explicit initialization ensures predictable power-on behavior.

### 4. Parameterization Benefits
Configurable N allows optimization for different requirements:
- **N=2**: Minimum recommended, fast reset release
- **N=3**: Standard choice, good metastability margin
- **N≥4**: Conservative, slower but very robust

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
- **Benefit**: Good balance of speed vs. robustness
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
The reset_sync module has comprehensive test coverage via:
- **Testbench Class**: `bin/CocoTBFramework/tbclasses/reset_sync_tb.py`
- **Test Runner**: `val/common/test_reset_sync.py`

### Test Scenarios
✅ **Basic Reset Synchronization** - Verifies N-cycle synchronization delay
✅ **Immediate Reset Assertion** - Verifies asynchronous assertion behavior
✅ **Multiple Reset Cycles** - Tests repeated reset/release sequences
✅ **Reset Glitch Filtering** - Validates recovery from short reset pulses

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
- N=2 (min) - ✅ PASSED
- N=3 (typical) - ✅ PASSED
- N=4 (safe) - ✅ PASSED
- N=5 (max) - ✅ PASSED

**Bug Discovery**: The comprehensive test suite discovered a critical RTL bug during initial test run (inverted reset polarity), demonstrating the value of thorough verification.

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

- **[← Back to RTLCommon Index](index.md)**
- **[← Back to Main Documentation Index](../../index.md)**
