# Binary-Gray Counter Module

## Overview
The `counter_bingray` module is a dual-output counter that simultaneously provides both binary and Gray code representations of the same count value. This is essential for asynchronous FIFO implementations where Gray code is required to prevent metastability when crossing clock domains, while binary values are needed for arithmetic operations.

## Module Declaration
```systemverilog
module counter_bingray #(
    parameter int WIDTH = 4
) (
    input  logic             clk,
    input  logic             rst_n,
    input  logic             enable,
    output logic [WIDTH-1:0] counter_bin,
    output logic [WIDTH-1:0] counter_bin_next,
    output logic [WIDTH-1:0] counter_gray
);
```

## Parameters

### WIDTH
- **Type**: `int`
- **Default**: `4`
- **Description**: Bit width of both binary and Gray code outputs
- **Range**: Any positive integer ≥ 1
- **Impact**: Determines maximum count value (2^WIDTH - 1)

## Ports

### Inputs
| Port | Width | Type | Description |
|------|-------|------|-------------|
| `clk` | 1 | `logic` | System clock input |
| `rst_n` | 1 | `logic` | Active-low asynchronous reset |
| `enable` | 1 | `logic` | Counter enable control |

### Outputs
| Port | Width | Type | Description |
|------|-------|------|-------------|
| `counter_bin` | WIDTH | `logic` | Binary counter output (registered) |
| `counter_bin_next` | WIDTH | `logic` | Next binary value (combinational) |
| `counter_gray` | WIDTH | `logic` | Gray code output (registered) |

## Architecture Details

### Internal Logic
```systemverilog
logic [WIDTH-1:0] w_counter_bin, w_counter_gray;

assign w_counter_bin = enable ? (counter_bin + 1) : counter_bin;
assign w_counter_gray = w_counter_bin ^ (w_counter_bin >> 1);
assign counter_bin_next = w_counter_bin;
```

### Gray Code Conversion
The module implements the standard binary-to-Gray conversion:
- **MSB**: `gray[WIDTH-1] = binary[WIDTH-1]`
- **Other bits**: `gray[i] = binary[i] ^ binary[i+1]` for i = 0 to WIDTH-2

## Gray Code Theory

### Why Gray Code?
Gray code (reflected binary code) has the property that adjacent values differ by exactly one bit. This is crucial for:

1. **Metastability Prevention**: When crossing clock domains, only one bit changes at a time
2. **Glitch Elimination**: Reduces intermediate states during transitions
3. **Asynchronous Safety**: Safe for use in asynchronous circuits

### Gray Code Sequence Example (4-bit)
| Decimal | Binary | Gray | Changes |
|---------|--------|------|---------|
| 0 | 0000 | 0000 | - |
| 1 | 0001 | 0001 | bit 0 |
| 2 | 0010 | 0011 | bit 1 |
| 3 | 0011 | 0010 | bit 0 |
| 4 | 0100 | 0110 | bit 2 |
| 5 | 0101 | 0111 | bit 0 |
| 6 | 0110 | 0101 | bit 1 |
| 7 | 0111 | 0100 | bit 0 |
| 8 | 1000 | 1100 | bit 3 |
| 9 | 1001 | 1101 | bit 0 |
| 10 | 1010 | 1111 | bit 1 |
| 11 | 1011 | 1110 | bit 0 |
| 12 | 1100 | 1010 | bit 2 |
| 13 | 1101 | 1011 | bit 0 |
| 14 | 1110 | 1001 | bit 1 |
| 15 | 1111 | 1000 | bit 0 |

## Implementation Analysis

### Combinational Logic
```systemverilog
// Next binary calculation
w_counter_bin = enable ? (counter_bin + 1) : counter_bin;

// Gray code conversion  
w_counter_gray = w_counter_bin ^ (w_counter_bin >> 1);
```

### Sequential Logic
```systemverilog
always_ff @(posedge clk, negedge rst_n) begin
    if (!rst_n) begin
        counter_bin  <= 'b0;
        counter_gray <= 'b0;
    end else begin
        counter_bin  <= w_counter_bin;
        counter_gray <= w_counter_gray;
    end
end
```

## Timing Characteristics

### Critical Paths
1. **Binary Increment**: Standard binary addition timing
2. **Gray Conversion**: XOR tree with log(WIDTH) levels
3. **Combined Path**: Increment + conversion in same cycle

### Propagation Delays
- **Clock-to-Q**: Standard flip-flop delay
- **Combinational**: Depends on addition and XOR logic depth
- **Setup Time**: Must account for longest combinational path

## Application: Asynchronous FIFO

### FIFO Pointer Implementation
```systemverilog
// Write domain counter
counter_bingray #(.WIDTH(ADDR_WIDTH+1)) wr_counter (
    .clk(wr_clk),
    .rst_n(wr_rst_n),
    .enable(wr_enable),
    .counter_bin(wr_bin),
    .counter_bin_next(wr_bin_next),
    .counter_gray(wr_gray)
);

// Read domain counter  
counter_bingray #(.WIDTH(ADDR_WIDTH+1)) rd_counter (
    .clk(rd_clk),
    .rst_n(rd_rst_n), 
    .enable(rd_enable),
    .counter_bin(rd_bin),
    .counter_bin_next(rd_bin_next),
    .counter_gray(rd_gray)
);
```

### Cross-Domain Synchronization
```systemverilog
// Synchronize Gray code pointers across domains
logic [ADDR_WIDTH:0] wr_gray_sync, rd_gray_sync;

// Write domain: synchronize read Gray pointer
synchronizer #(.WIDTH(ADDR_WIDTH+1)) rd_sync (
    .clk(wr_clk),
    .rst_n(wr_rst_n),
    .data_in(rd_gray),
    .data_out(rd_gray_sync)
);

// Read domain: synchronize write Gray pointer
synchronizer #(.WIDTH(ADDR_WIDTH+1)) wr_sync (
    .clk(rd_clk),
    .rst_n(rd_rst_n), 
    .data_in(wr_gray),
    .data_out(wr_gray_sync)
);
```

### FIFO Status Generation
```systemverilog
// FIFO empty: Gray pointers equal
assign fifo_empty = (rd_gray == wr_gray_sync);

// FIFO full: Binary addresses equal, MSBs different
wire [ADDR_WIDTH-1:0] wr_addr = wr_bin[ADDR_WIDTH-1:0];
wire [ADDR_WIDTH-1:0] rd_addr_sync = gray2bin(rd_gray_sync)[ADDR_WIDTH-1:0];
wire wr_msb = wr_bin[ADDR_WIDTH];
wire rd_msb_sync = gray2bin(rd_gray_sync)[ADDR_WIDTH];

assign fifo_full = (wr_addr == rd_addr_sync) && (wr_msb != rd_msb_sync);
```

## Advanced Features

### Almost Full/Empty Flags
```systemverilog
// Calculate occupancy using binary values
wire [ADDR_WIDTH:0] occupancy = wr_bin - gray2bin(rd_gray_sync);

// Generate status flags
assign almost_full = (occupancy >= ALMOST_FULL_THRESH);
assign almost_empty = (occupancy <= ALMOST_EMPTY_THRESH);
```

### Gray-to-Binary Conversion Function
```systemverilog
function automatic [WIDTH-1:0] gray2bin;
    input [WIDTH-1:0] gray;
    integer i;
    begin
        gray2bin[WIDTH-1] = gray[WIDTH-1];
        for (i = WIDTH-2; i >= 0; i--) begin
            gray2bin[i] = gray2bin[i+1] ^ gray[i];
        end
    end
endfunction
```

## Design Examples

### 1. 8-bit Asynchronous FIFO Pointer
```systemverilog
parameter FIFO_DEPTH = 256;
parameter ADDR_WIDTH = $clog2(FIFO_DEPTH);
parameter PTR_WIDTH = ADDR_WIDTH + 1;  // Extra bit for full detection

counter_bingray #(
    .WIDTH(PTR_WIDTH)
) fifo_wr_ptr (
    .clk(wr_clk),
    .rst_n(async_rst_n),
    .enable(wr_enable && !fifo_full),
    .counter_bin(wr_ptr_bin),
    .counter_bin_next(wr_ptr_bin_next),
    .counter_gray(wr_ptr_gray)
);
```

### 2. Clock Domain Crossing Counter
```systemverilog
// Source domain
counter_bingray #(.WIDTH(8)) src_counter (
    .clk(src_clk),
    .rst_n(src_rst_n),
    .enable(src_enable),
    .counter_bin(src_bin),
    .counter_bin_next(),
    .counter_gray(src_gray)
);

// Destination domain receives synchronized Gray value
logic [7:0] dest_gray_sync;
synchronizer #(.WIDTH(8)) sync_inst (
    .clk(dest_clk),
    .rst_n(dest_rst_n),
    .data_in(src_gray),
    .data_out(dest_gray_sync)
);
```

## Verification Strategy

### Test Scenarios
1. **Sequential Counting**: Verify both outputs increment correctly
2. **Gray Code Properties**: Ensure single-bit changes between adjacent values
3. **Reset Behavior**: Confirm both outputs reset to zero
4. **Enable Control**: Test hold behavior when disabled
5. **Rollover**: Verify proper wrap-around from maximum value

### Coverage Points
```systemverilog
covergroup counter_bingray_cg @(posedge clk);
    cp_binary: coverpoint counter_bin {
        bins all_values[] = {[0:2**WIDTH-1]};
    }
    
    cp_gray: coverpoint counter_gray {
        bins all_values[] = {[0:2**WIDTH-1]};
    }
    
    cp_enable: coverpoint enable {
        bins enabled = {1};
        bins disabled = {0};
    }
    
    cp_transitions: coverpoint counter_bin {
        bins transitions[] = ([0:2**WIDTH-2] => [1:2**WIDTH-1]);
        bins rollover = (2**WIDTH-1 => 0);
    }
endgroup
```

### Assertions
```systemverilog
// Verify Gray code has single bit changes
property gray_single_bit_change;
    @(posedge clk) disable iff (!rst_n)
    enable && !$isunknown(counter_gray) |->
    $countones(counter_gray ^ $past(counter_gray)) <= 1;
endproperty

assert property (gray_single_bit_change);

// Verify binary and Gray relationship
property bin_gray_relationship;
    @(posedge clk) disable iff (!rst_n)
    counter_gray == (counter_bin ^ (counter_bin >> 1));
endproperty

assert property (bin_gray_relationship);
```

## Synthesis Considerations

### Resource Utilization
- **Flip-Flops**: 2×WIDTH (separate for binary and Gray)
- **LUTs**: Increment logic + XOR tree for Gray conversion
- **Critical Path**: Through binary increment and Gray conversion

### Optimization Techniques
```systemverilog
// Optional: Pipeline Gray conversion for high speed
logic [WIDTH-1:0] counter_gray_pipe;
always_ff @(posedge clk) begin
    counter_gray_pipe <= w_counter_gray;
end
```

### Tool-Specific Attributes
```systemverilog
(* ASYNC_REG = "TRUE" *) logic [WIDTH-1:0] counter_gray; // Xilinx
// synthesis attribute ASYNC_REG of counter_gray is "TRUE"  // Altera/Intel
```

## Performance Characteristics

### Maximum Frequency
- **Typical**: 200-400 MHz in modern FPGAs
- **Limitation**: Binary increment + Gray conversion logic depth
- **Optimization**: Pipeline for higher frequencies

### Power Consumption
- **Dynamic**: Proportional to switching activity
- **Static**: Minimal for CMOS technology
- **Optimization**: Clock gating when enable is inactive

## Common Applications
1. **Asynchronous FIFO Pointers**: Primary use case
2. **Clock Domain Crossing Counters**: Safe multi-domain counting
3. **Position Encoders**: Mechanical/optical encoder interfaces
4. **State Machine Counters**: When glitch-free operation required
5. **Memory Address Generation**: For dual-port memory systems

## Troubleshooting Guide

### Common Issues
1. **Metastability**: Ensure proper synchronization of Gray values
2. **Timing Violations**: Pipeline Gray conversion if needed
3. **Incorrect FIFO Status**: Verify Gray-to-binary conversion
4. **Reset Skew**: Use proper reset synchronization

### Debug Techniques
1. **Simulation**: Verify Gray code properties with assertions
2. **Logic Analyzer**: Capture actual transitions in hardware
3. **Timing Analysis**: Check setup/hold requirements
4. **Cross-Domain Checks**: Verify synchronizer timing

## WaveDrom Visualization

**High-quality waveforms showcasing Binary-Gray counter operation are available!**

The following timing diagrams demonstrate the dual-output counter design across 4 key scenarios:

### Scenario 1: Binary vs Gray Code Comparison

![BinGray Comparison](../../assets/WAVES/counter_bingray/bingray_counter_binary_vs_gray.png)

**WaveJSON:** [bingray_counter_binary_vs_gray.json](../../assets/WAVES/counter_bingray/bingray_counter_binary_vs_gray.json)

Side-by-side comparison of both outputs:
- Binary: Normal sequential counting (0→1→2→3→...)
- Gray: Single-bit transitions between values
- Shows full cycle demonstrating encoding differences
- Illustrates why Gray code is CDC-safe

### Scenario 2: Single-Bit Transitions (CDC Safety) ⭐ **KEY FEATURE**

![BinGray Single-Bit Transitions](../../assets/WAVES/counter_bingray/bingray_counter_single_bit_transitions.png)

**WaveJSON:** [bingray_counter_single_bit_transitions.json](../../assets/WAVES/counter_bingray/bingray_counter_single_bit_transitions.json)

Gray code CDC safety property:
- Each Gray transition changes EXACTLY one bit
- Hamming distance = 1 between adjacent values
- **Critical for fifo_async CDC mechanism**
- Prevents metastability in clock domain crossing

### Scenario 3: Lookahead Signal (counter_bin_next)

![BinGray Lookahead](../../assets/WAVES/counter_bingray/bingray_counter_lookahead.png)

**WaveJSON:** [bingray_counter_lookahead.json](../../assets/WAVES/counter_bingray/bingray_counter_lookahead.json)

Combinational lookahead feature:
- Predicts next binary value one cycle ahead
- Useful for FIFO full/empty prediction
- Shows enable gating behavior
- Enables early decision-making

### Scenario 4: Enable and Reset Control

![BinGray Enable and Reset](../../assets/WAVES/counter_bingray/bingray_counter_enable_reset.png)

**WaveJSON:** [bingray_counter_enable_reset.json](../../assets/WAVES/counter_bingray/bingray_counter_enable_reset.json)

Control signal behavior:
- Both outputs hold when enable=0
- Asynchronous reset to zero
- Clean state transitions
- Reset during counting demonstration

---

**To regenerate these waveforms:**
```bash
pytest val/common/test_counter_bingray_wavedrom.py -v
# Then convert JSON to PNG:
cd docs/markdown/assets/WAVES/counter_bingray
for f in *.json; do wavedrom-cli -i "$f" -p "${f%.json}.png"; done
```

**What Makes Binary-Gray Counters Special:**

The waveforms highlight the unique dual-output design:
- **Dual Encoding**: Binary for arithmetic, Gray for CDC safety
- **Single-Bit Transitions**: Gray code changes one bit at a time
- **Lookahead**: counter_bin_next provides one-cycle prediction
- **CDC-Safe**: Safe for asynchronous clock domain crossing

**Relationship to fifo_async:**

Binary-Gray counters are the foundation of the standard `fifo_async` module:
- **fifo_async** uses this counter for read/write pointers
- Gray outputs cross clock domains safely
- Binary outputs used for arithmetic (occupancy, address generation)
- Logarithmic width (`$clog2(DEPTH) + 1`) for resource efficiency

**Comparison Table:**

| Feature | BinGray Counter | Johnson Counter |
|---------|----------------|-----------------|
| **Output Width** | `$clog2(DEPTH) + 1` bits | `DEPTH` bits |
| **CDC Method** | Standard Gray code | Johnson code |
| **Depth Support** | Power-of-2 only | Any even number |
| **Resource Efficiency** | Logarithmic (better for large depths) | Linear |
| **Conversion** | XOR tree (simple) | Position detection (complex) |
| **Used In** | `fifo_async` (standard) | `fifo_async_div2` (flexible) |

**Comparison with Other Modules:**

- `test_counter_johnson_wavedrom.py` - Johnson counter (even depths, linear width)
- `test_fifo_async_wavedrom.py` - BinGray counter in action (async FIFO, power-of-2)
- `test_fifo_async_div2_wavedrom.py` - Johnson counter in action (async FIFO, even depths)

## Test and Verification

**Comprehensive Test Suite:**
- `val/common/test_counter_bingray.py` - Full functional verification
- `val/common/test_counter_bingray_wavedrom.py` - WaveDrom timing diagrams ⭐

**Run Tests:**
```bash
# Full functional test (basic/medium/full levels)
pytest val/common/test_counter_bingray.py -v

# WaveDrom waveform generation
pytest val/common/test_counter_bingray_wavedrom.py -v
```

## Navigation

- **[← Back to RTLCommon Index](index.md)**
- **[← Back to Main Documentation Index](../../index.md)**
