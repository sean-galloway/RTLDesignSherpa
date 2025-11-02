# Binary Counter with Load and Variable Increment

A FIFO-optimized binary counter supporting standard increment, variable increment, and direct load operations with configurable wraparound behavior for efficient FIFO pointer management.

## Overview

The `counter_bin_load` module extends basic binary counting with three distinct operating modes: standard +1 increment, variable-amount increment, and direct load operations. It is specifically optimized for FIFO pointer management where drop/flush operations require jumping the read pointer by arbitrary amounts. The module implements FIFO-style wraparound at 2×MAX with MSB toggle for full/empty detection.

## Module Declaration

```systemverilog
module counter_bin_load #(
    parameter int WIDTH = 5,     // Counter bit width
    parameter int MAX = 10       // Maximum count value (wraps at MAX-1)
) (
    // Derived localparam (computed internally - not user-settable):
    // localparam int WRAP_BOUNDARY = 2 * MAX;  // Wraparound boundary

    input  logic             clk,               // Clock input
    input  logic             rst_n,             // Active-low asynchronous reset
    input  logic             enable,            // Count +1 enable
    input  logic             add_enable,        // Variable increment enable
    input  logic [WIDTH-1:0] add_value,         // Value to add
    input  logic             load,              // Load enable (highest priority)
    input  logic [WIDTH-1:0] load_value,        // Value to load
    output logic [WIDTH-1:0] counter_bin_curr,  // Current count (registered)
    output logic [WIDTH-1:0] counter_bin_next   // Next count (combinational)
);
```

## Parameters

### User-Settable Parameters

| Parameter | Type | Default | Description |
|-----------|------|---------|-------------|
| WIDTH | int | 5 | Counter bit width (range: 2-64) |
| MAX | int | 10 | Maximum count value before wraparound (range: 2 to 2^(WIDTH-1)) |

**WIDTH Guidelines:**
- **Minimum**: 2 bits (required for MSB inversion behavior)
- **Typical**: FIFO address width + 1 (e.g., 4 for 8-entry FIFO: 3 addr + 1 MSB)
- **Maximum**: 64 bits (practical limit for synthesis)

**MAX Constraints:**
- Must fit within WIDTH-1 bits (excludes MSB)
- Example: WIDTH=4 → MAX ≤ 8 (3 bits for addresses 0-7, 1 MSB for full/empty)
- FIFO depth is typically MAX (e.g., MAX=8 → 8-entry FIFO)

### Derived Localparam (Computed Internally)

| Localparam | Computation | Description |
|------------|-------------|-------------|
| WRAP_BOUNDARY | 2 × MAX | Wraparound boundary for add operations |

**Note:** WRAP_BOUNDARY is computed internally and cannot be overridden by users.

## Ports

### Inputs

| Port | Width | Description |
|------|-------|-------------|
| clk | 1 | System clock (rising edge active) |
| rst_n | 1 | Active-low asynchronous reset |
| enable | 1 | Standard +1 increment enable |
| add_enable | 1 | Variable increment enable |
| add_value | WIDTH | Value to add when add_enable=1 |
| load | 1 | Load enable (highest priority operation) |
| load_value | WIDTH | Value to load when load=1 |

### Outputs

| Port | Width | Description |
|------|-------|-------------|
| counter_bin_curr | WIDTH | Current counter value (registered output) |
| counter_bin_next | WIDTH | Next counter value (combinational preview) |

## Functionality

### Operation Priority

The module implements a three-level priority hierarchy:

1. **Load Operation** (Highest Priority): `load = 1`
   - Directly sets `counter_bin_next = load_value`
   - Used for: Flush all, jump to specific position

2. **Variable Increment**: `add_enable = 1` (when `load = 0`)
   - Adds `add_value` to current count: `counter_bin_next = counter_bin_curr + add_value`
   - Wraps at `2×MAX`: Subtracts `2×MAX` if sum ≥ `2×MAX`
   - Used for: Drop multiple entries, bulk operations

3. **Standard Increment**: `enable = 1` (when `load = 0` and `add_enable = 0`)
   - Adds 1 to current count: `counter_bin_next = counter_bin_curr + 1`
   - Special FIFO wraparound: MSB toggles at MAX-1, lower bits clear
   - Used for: Normal FIFO read/write pointer increment

4. **Hold**: All enables = 0
   - Maintains current value: `counter_bin_next = counter_bin_curr`

### FIFO-Optimized Wraparound

#### Standard Increment Mode (enable=1):

```
For MAX=8, WIDTH=4:
Count sequence: 0, 1, 2, 3, 4, 5, 6, 7, 8 (toggle MSB, clear lower)
Binary:         0000 → 0001 → ... → 0111 → 1000 (MSB inverts, lower bits = 0)
                0000 → 0001 → ... → 0111 → 1000 → 1001 → ... → 1111 → 0000
```

**Key Feature:** MSB toggles when lower bits reach MAX-1
- This creates a 2×MAX count range: 0 to (2×MAX - 1)
- MSB different between write/read pointers → FIFO full or empty

#### Variable Increment Mode (add_enable=1):

```
Wraparound at 2×MAX:
Example: counter_bin_curr = 14, add_value = 5, MAX = 8, WRAP_BOUNDARY = 16
Sum = 14 + 5 = 19 ≥ 16 → counter_bin_next = 19 - 16 = 3
```

**Key Feature:** Full 0 to (2×MAX - 1) range with modulo arithmetic

### Full/Empty Detection Pattern

```systemverilog
// In FIFO controller:
logic full, empty;
assign full  = (wr_ptr[WIDTH-2:0] == rd_ptr[WIDTH-2:0]) &&
               (wr_ptr[WIDTH-1] != rd_ptr[WIDTH-1]);  // MSB different

assign empty = (wr_ptr[WIDTH-2:0] == rd_ptr[WIDTH-2:0]) &&
               (wr_ptr[WIDTH-1] == rd_ptr[WIDTH-1]);  // MSB same
```

**Why This Works:**
- Normal operation: wr_ptr advances, MSBs eventually differ → full
- After wraparound: rd_ptr catches up, MSBs match again → empty
- MSB acts as "lap counter" for circular buffer

## Implementation Details

### Priority Logic

```systemverilog
always_comb begin
    counter_bin_next = counter_bin_curr;  // Default: hold

    if (load) begin
        // Highest priority: Direct load
        counter_bin_next = load_value;

    end else if (add_enable) begin
        // Variable increment with wraparound at 2*MAX
        w_sum_ext = {1'b0, counter_bin_curr} + {1'b0, add_value};

        if (w_sum_ext >= WRAP_BOUNDARY) begin
            counter_bin_next = w_sum_ext[WIDTH-1:0] - WIDTH'(WRAP_BOUNDARY);
        end else begin
            counter_bin_next = w_sum_ext[WIDTH-1:0];
        end

    end else if (enable) begin
        // Standard +1 with MSB toggle at MAX-1
        if (counter_bin_curr[WIDTH-2:0] == (MAX - 1)) begin
            counter_bin_next = {~counter_bin_curr[WIDTH-1], {(WIDTH-1){1'b0}}};
        end else begin
            counter_bin_next = counter_bin_curr + 1;
        end
    end
    // else: hold (default assignment)
end
```

### Registered Output

```systemverilog
always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n)
        counter_bin_curr <= 'b0;  // Reset to 0
    else
        counter_bin_curr <= counter_bin_next;
end
```

**Reset Behavior:** Counter initializes to 0 on `rst_n = 0`

### Combinational Next-Value Preview

The `counter_bin_next` output provides a one-cycle lookahead of the counter value, useful for:
- FIFO full/empty prediction
- Pre-computing next address
- Pipelined operations

## Usage Examples

### FIFO Read Pointer with Drop Support

```systemverilog
// 8-entry FIFO with drop capability
localparam int FIFO_DEPTH = 8;
localparam int PTR_WIDTH = $clog2(FIFO_DEPTH) + 1;  // +1 for MSB

logic [PTR_WIDTH-1:0] rd_ptr, rd_ptr_next;
logic rd_en, drop_valid;
logic [PTR_WIDTH-1:0] drop_count;

counter_bin_load #(
    .WIDTH(PTR_WIDTH),      // 4 bits: 3 for addr (0-7) + 1 MSB
    .MAX(FIFO_DEPTH)        // Wrap at 8
) u_rd_ptr (
    .clk              (clk),
    .rst_n            (rst_n),
    .enable           (rd_en & !fifo_empty),        // Normal read
    .add_enable       (drop_valid),                 // Drop multiple
    .add_value        (drop_count),                 // How many to drop
    .load             (flush_all),                  // Flush operation
    .load_value       (wr_ptr),                     // Jump to write ptr
    .counter_bin_curr (rd_ptr),
    .counter_bin_next (rd_ptr_next)
);

// Use lower bits for memory address
assign rd_addr = rd_ptr[PTR_WIDTH-2:0];
```

### FIFO Write Pointer

```systemverilog
logic [PTR_WIDTH-1:0] wr_ptr, wr_ptr_next;
logic wr_en;

counter_bin_load #(
    .WIDTH(PTR_WIDTH),
    .MAX(FIFO_DEPTH)
) u_wr_ptr (
    .clk              (clk),
    .rst_n            (rst_n),
    .enable           (wr_en & !fifo_full),
    .add_enable       (1'b0),               // No variable increment for write
    .add_value        ('0),
    .load             (flush_all),          // Reset to read pointer
    .load_value       (rd_ptr),
    .counter_bin_curr (wr_ptr),
    .counter_bin_next (wr_ptr_next)
);

assign wr_addr = wr_ptr[PTR_WIDTH-2:0];
```

### Full/Empty Status Logic

```systemverilog
// Full: Lower bits match, MSB different
assign fifo_full = (wr_ptr[PTR_WIDTH-2:0] == rd_ptr[PTR_WIDTH-2:0]) &&
                   (wr_ptr[PTR_WIDTH-1] != rd_ptr[PTR_WIDTH-1]);

// Empty: All bits match
assign fifo_empty = (wr_ptr == rd_ptr);

// Count calculation (handles wraparound)
logic [PTR_WIDTH-1:0] fifo_count;
assign fifo_count = (wr_ptr >= rd_ptr) ? (wr_ptr - rd_ptr) :
                                          (2*FIFO_DEPTH - rd_ptr + wr_ptr);
```

### Packet Drop Controller

```systemverilog
// Drop N packets from FIFO
logic [7:0] packets_to_drop;
logic drop_start;

// State machine for multi-cycle drop
typedef enum logic [1:0] {
    IDLE,
    DROPPING
} drop_state_t;
drop_state_t drop_state;

always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
        drop_state <= IDLE;
        drop_valid <= 1'b0;
        drop_count <= '0;
    end else begin
        case (drop_state)
            IDLE: begin
                if (drop_start && packets_to_drop > 0) begin
                    drop_valid <= 1'b1;
                    drop_count <= packets_to_drop;
                    drop_state <= DROPPING;
                end
            end

            DROPPING: begin
                drop_valid <= 1'b0;  // Single-cycle pulse
                drop_state <= IDLE;
            end
        endcase
    end
end

// Connect to counter
counter_bin_load #(
    .WIDTH(PTR_WIDTH),
    .MAX(FIFO_DEPTH)
) u_rd_ptr (
    .clk        (clk),
    .rst_n      (rst_n),
    .enable     (rd_en & !fifo_empty),
    .add_enable (drop_valid),
    .add_value  (drop_count),
    .load       (1'b0),
    .load_value ('0),
    .counter_bin_curr(rd_ptr),
    .counter_bin_next(rd_ptr_next)
);
```

## Timing Characteristics

### Latency and Throughput

- **Increment Latency**: 1 cycle (registered output)
- **Next-Value Availability**: 0 cycles (combinational `counter_bin_next`)
- **Throughput**: 1 operation per cycle
- **Reset Recovery**: 1 cycle (asynchronous reset)

### Operation Timing Diagrams

#### Standard Increment (enable=1):

```
Cycle:    0    1    2    3    4    5    6    7    8    9
clk:      ‾|_|‾|_|‾|_|‾|_|‾|_|‾|_|‾|_|‾|_|‾|_|‾|_|‾|_
enable:   ______|‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾
curr:     0000  0000  0001  0010  0011  0100  0101  0110
next:     0000  0001  0010  0011  0100  0101  0110  0111
```

#### Variable Increment (add_enable=1, add_value=3):

```
Cycle:    0    1    2    3
clk:      ‾|_|‾|_|‾|_|‾|_
add_en:   ______|‾|_______
add_val:  ------[3]-------
curr:     0010  0010  0101
next:     0010  0101  0110
                 ↑ +3
```

#### Load Operation (load=1, load_value=12):

```
Cycle:    0    1    2
clk:      ‾|_|‾|_|‾|_
load:     ______|‾|___
load_val: ------[C]---
curr:     0011  0011  1100
next:     0011  1100  1101
                 ↑ direct load
```

## Design Considerations

### When to Use counter_bin_load

✅ **Appropriate Use Cases:**
- FIFO read/write pointers with drop/flush
- Circular buffer management with skip operations
- Packet queue pointers with bulk discard
- Ring buffer pointers with reset capability
- Any counter needing jump-to-position capability

### When to Use Alternatives

**Use `counter_bin.sv` if:**
- Only need standard +1 increment
- No load or variable increment required
- Simpler interface preferred

**Use `counter_load_clear.sv` if:**
- Need load/clear but not FIFO wraparound
- Don't need MSB toggle behavior
- Variable increment not required

### Parameter Selection Guidelines

**WIDTH Calculation:**
```systemverilog
// For FIFO with N entries:
localparam int FIFO_DEPTH = 16;
localparam int PTR_WIDTH = $clog2(FIFO_DEPTH) + 1;  // +1 for MSB

// Example: 16-entry FIFO
// FIFO_DEPTH = 16
// PTR_WIDTH = 4 + 1 = 5 bits
// Lower 4 bits = address (0-15)
// MSB = full/empty indicator
```

**MAX Selection:**
- Set MAX equal to FIFO depth
- MAX must be power of 2 for efficient address decoding
- MAX must fit in WIDTH-1 bits

### Critical Paths

1. **Add Operation**: Extended addition + wraparound comparison
   - Longest path: `counter_bin_curr + add_value` → overflow detection → modulo
2. **Standard Increment**: Comparison + MSB toggle
   - Path: Lower bits comparison → MSB invert + clear
3. **Load Operation**: Direct assignment
   - Shortest path: Mux select

**Optimization Tip:** If add operation is critical path, consider pipelining:
```systemverilog
// Pipeline add operation
logic [WIDTH-1:0] r_add_result;
always_ff @(posedge clk) begin
    r_add_result <= counter_bin_curr + add_value;
end
```

## Performance Characteristics

### Resource Utilization

| Configuration | FFs | LUTs | Description |
|--------------|-----|------|-------------|
| WIDTH=4, MAX=8 | 4 | ~12 | Minimal (8-entry FIFO) |
| WIDTH=5, MAX=16 | 5 | ~16 | Small (16-entry FIFO) |
| WIDTH=9, MAX=256 | 9 | ~30 | Medium (256-entry FIFO) |
| WIDTH=13, MAX=4096 | 13 | ~45 | Large (4K-entry FIFO) |

**Area Scaling:** Approximately linear with WIDTH due to adder and comparator

### Maximum Frequency

- **Typical**: 300-500 MHz (modern FPGAs)
- **Limiting Factor**: Add operation with wraparound detection
- **Optimization**: Pipeline add path for >500 MHz

## Verification Notes

Test suite location: `val/common/test_counter_bin_load.py`

**Key Test Scenarios:**
- Standard increment (enable=1)
- Variable increment with various add_value
- Load operation priority verification
- Wraparound behavior at 2×MAX
- MSB toggle at MAX-1 for standard increment
- Full/empty condition verification
- Priority hierarchy (load > add > enable)
- Reset behavior

**Test Command:**
```bash
pytest val/common/test_counter_bin_load.py -v
```

## Common Pitfalls

❌ **Anti-Pattern 1**: Incorrect WIDTH for FIFO depth

```systemverilog
// WRONG: WIDTH = $clog2(FIFO_DEPTH)
localparam int WIDTH = $clog2(16);  // = 4 bits
// Problem: No MSB for full/empty detection!

// RIGHT: WIDTH = $clog2(FIFO_DEPTH) + 1
localparam int WIDTH = $clog2(16) + 1;  // = 5 bits
// Lower 4 bits = address, MSB = full/empty indicator
```

❌ **Anti-Pattern 2**: Ignoring operation priority

```systemverilog
// WRONG: Trying to increment while load is active
load <= 1'b1;
enable <= 1'b1;  // This will be IGNORED!
// Result: Counter loads load_value, enable has no effect

// RIGHT: Ensure only one operation active
load <= drop_all;
enable <= rd_en & !drop_all;  // Mutually exclusive
```

❌ **Anti-Pattern 3**: add_value exceeds 2×MAX

```systemverilog
// WRONG: add_value larger than valid range
// MAX = 8, add_value = 20
// Result: Multiple wraparounds, unpredictable behavior

// RIGHT: Constrain add_value
assert property (@(posedge clk) add_enable |-> add_value < 2*MAX);
```

❌ **Anti-Pattern 4**: Using wrong bits for memory address

```systemverilog
// WRONG: Using full counter including MSB
assign mem_addr = wr_ptr;  // Includes MSB!
// Result: Addresses 0-15 appear as 0-15 and 16-31

// RIGHT: Use only lower bits
assign mem_addr = wr_ptr[WIDTH-2:0];  // Exclude MSB
```

## Related Modules

- **counter_bin.sv** - Simple binary counter (no load or variable increment)
- **counter_load_clear.sv** - Counter with load/clear (no FIFO wraparound)
- **counter_freq_invariant.sv** - Time-based counter (millisecond/microsecond timing)
- **gaxi_drop_fifo_sync.sv** - Uses counter_bin_load for drop-capable FIFO
- **gaxi_fifo_sync.sv** - Standard synchronous FIFO with this counter

## Navigation

- **[← Back to RTLCommon Index](index.md)**
- **[← Back to Main Documentation Index](../../index.md)**
