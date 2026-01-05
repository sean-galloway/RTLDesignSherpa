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

# Sort Module RTL Documentation

## Purpose

The Sort module is a pipelined hardware sorting engine that implements the odd-even sort algorithm to sort arrays of configurable size in descending order. The module is designed for high-throughput applications where new data can be accepted every clock cycle, with predictable latency equal to the number of elements being sorted.

## Module Overview

```systemverilog
module sort #(
    parameter int NUM_VALS = 5,    // Number of values to sort
    parameter int SIZE     = 16    // Size of each value in bits
) (
    input  logic                     clk,       // Clock signal
    input  logic                     rst_n,     // Active-low reset
    input  logic [NUM_VALS*SIZE-1:0] data,      // Packed input data
    input  logic                     valid_in,  // Start sorting when asserted
    output logic [NUM_VALS*SIZE-1:0] sorted,    // Packed sorted output
    output logic                     done       // Asserted when sorting complete
);
```

## Port Descriptions

### Input Ports

| Port | Width | Type | Description |
|------|-------|------|-------------|
| `clk` | 1 | Clock | System clock signal. All operations are synchronous to the rising edge. |
| `rst_n` | 1 | Reset | Active-low asynchronous reset. Clears all pipeline stages when deasserted. |
| `data` | `NUM_VALS*SIZE` | Data | Packed input array. Elements are packed as `data[i*SIZE +: SIZE]` for element `i`. |
| `valid_in` | 1 | Control | When asserted (high) for one cycle, starts the sorting process for the current `data` input. |

### Output Ports

| Port | Width | Type | Description |
|------|-------|------|-------------|
| `sorted` | `NUM_VALS*SIZE` | Data | Packed output array sorted in descending order. Same packing format as input. |
| `done` | 1 | Status | Asserted (high) when the sorting operation is complete and `sorted` output is valid. |

### Parameters

| Parameter | Default | Range | Description |
|-----------|---------|-------|-------------|
| `NUM_VALS` | 5 | 2-32 | Number of values in the array to be sorted. Determines pipeline depth. |
| `SIZE` | 16 | 1-64 | Bit width of each individual value. All values must be unsigned integers. |

## Data Format

**Input/Output Packing**: Arrays are packed into a single wide bus where:
- Element 0 occupies bits `[SIZE-1:0]`
- Element 1 occupies bits `[2*SIZE-1:SIZE]`
- Element i occupies bits `[(i+1)*SIZE-1:i*SIZE]`

**Sort Order**: Output is sorted in **descending order** (largest to smallest).

## Algorithm: Odd-Even Sort

### Overview

The module implements the **Odd-Even Sort** (also known as **Brick Sort**) algorithm, which is particularly well-suited for pipelined hardware implementation.

### Algorithm Description

Odd-Even Sort works by alternating between two types of comparison passes:

1. **Odd Passes**: Compare and swap adjacent pairs at positions (0,1), (2,3), (4,5), etc.
2. **Even Passes**: Compare and swap adjacent pairs at positions (1,2), (3,4), (5,6), etc.

The algorithm requires exactly `NUM_VALS` passes to guarantee complete sorting, regardless of input data.

### Example Execution

For input array `[5, 3, 8, 1, 9]` (5 elements):

```
Initial:     [5, 3, 8, 1, 9]

Pass 1 (Odd):  Compare (0,1), (2,3), (4,X)
              [5, 3] → [5, 3] (no swap)
              [8, 1] → [8, 1] (no swap) 
              [9, X] → [9, X] (no comparison)
Result:       [5, 3, 8, 1, 9]

Pass 2 (Even): Compare (1,2), (3,4)
              [3, 8] → [8, 3] (swap)
              [1, 9] → [9, 1] (swap)
Result:       [5, 8, 3, 9, 1]

Pass 3 (Odd):  Compare (0,1), (2,3), (4,X)
              [5, 8] → [8, 5] (swap)
              [3, 9] → [9, 3] (swap)
              [1, X] → [1, X] (no comparison)
Result:       [8, 5, 9, 3, 1]

Pass 4 (Even): Compare (1,2), (3,4)
              [5, 9] → [9, 5] (swap)
              [3, 1] → [3, 1] (no swap)
Result:       [8, 9, 5, 3, 1]

Pass 5 (Odd):  Compare (0,1), (2,3), (4,X)
              [8, 9] → [9, 8] (swap)
              [5, 3] → [5, 3] (no swap)
              [1, X] → [1, X] (no comparison)
Final:        [9, 8, 5, 3, 1] ✓ Sorted!
```

### Algorithm Comparison

| Algorithm | Time Complexity | Space Complexity | Hardware Efficiency | Pipeline Stages | Best Use Case |
|-----------|----------------|------------------|-------------------|----------------|---------------|
| **Odd-Even Sort** | O(n²) | O(1) | ⭐⭐⭐⭐⭐ Excellent | n | Small arrays, predictable timing |
| Bubble Sort | O(n²) | O(1) | ⭐⭐ Poor | Variable | Sequential processors only |
| Bitonic Sort | O(n log²n) | O(1) | ⭐⭐⭐⭐ Very Good | log²n | Power-of-2 sizes, larger arrays |
| Merge Sort | O(n log n) | O(n) | ⭐⭐⭐ Good | log n | Large arrays, general purpose |
| Insertion Sort | O(n²) | O(1) | ⭐⭐⭐ Good | Variable | Nearly sorted data |

**Why Odd-Even Sort for Hardware?**

1. **Regular Structure**: Each pipeline stage is identical, making synthesis predictable
2. **Parallel Operations**: All comparisons in each pass happen simultaneously
3. **Fixed Latency**: Always takes exactly `NUM_VALS` cycles regardless of input data
4. **Simple Control**: No complex indexing or variable loop bounds
5. **Scalable**: Pipeline depth scales linearly with array size

## Architecture

### Pipeline Structure

The module implements a `NUM_VALS`-stage pipeline where:
- **Stage 0**: Input capture (combinational)
- **Stages 1 to NUM_VALS**: Pipeline registers with compare-swap logic

```
Stage:    0 -----> 1 -----> 2 -----> 3 -----> ... -----> NUM_VALS
         Input   Odd Pass  Even Pass Odd Pass          Final Output
         (Comb)   (FF)      (FF)      (FF)              (FF)
```

### Signal Flow

```
data[...] ─────┐
              ┌▼─────────────┐    ┌──────────────┐    ┌──────────────┐
valid_in ────▶│   Stage 0    │───▶│   Stage 1    │───▶│   Stage 2    │───▶ ...
              │ (Wire Logic) │    │ (Odd Pass)   │    │ (Even Pass)  │
              └──────────────┘    └──────────────┘    └──────────────┘
                                          │                   │
                                          ▼                   ▼
                                    r_stage_data[1]    r_stage_data[2]
                                    r_stage_valid[1]   r_stage_valid[2]
```

### Naming Conventions

The module follows strict naming conventions for signal clarity:

- **Wire signals** (combinational): Prefixed with `w_`
  - `w_values[stage][element]`: Unpacked arrays for easy manipulation
  - `w_next_values[stage][element]`: Computed next values
  - `w_stage_data_0`: Input stage data wire
  - `w_stage_valid_0`: Input stage valid wire

- **Flopped signals** (sequential): Prefixed with `r_`
  - `r_stage_data[stage]`: Pipeline data registers
  - `r_stage_valid[stage]`: Pipeline valid registers

## Implementation Details

### Compare-Swap Logic

Each pipeline stage implements compare-swap operations based on the stage number:

```systemverilog
// Determine if this is an odd or even pass
localparam bit IS_ODD_PASS = ((stage-1) % 2) == 0;

always_comb begin
    // Default: pass through unchanged
    for (int i = 0; i < NUM_VALS; i++) begin
        w_next_values[stage][i] = w_values[stage-1][i];
    end
    
    if (IS_ODD_PASS) begin
        // Odd pass: compare (0,1), (2,3), (4,5), etc.
        for (int i = 0; i < NUM_VALS-1; i += 2) begin
            if (w_values[stage-1][i] < w_values[stage-1][i+1]) begin
                w_next_values[stage][i]   = w_values[stage-1][i+1];
                w_next_values[stage][i+1] = w_values[stage-1][i];
            end
        end
    end else begin
        // Even pass: compare (1,2), (3,4), (5,6), etc.
        for (int i = 1; i < NUM_VALS-1; i += 2) begin
            if (w_values[stage-1][i] < w_values[stage-1][i+1]) begin
                w_next_values[stage][i]   = w_values[stage-1][i+1];
                w_next_values[stage][i+1] = w_values[stage-1][i];
            end
        end
    end
end
```

### Reset Behavior

- **Asynchronous Reset**: All pipeline stages are cleared when `rst_n` is deasserted
- **Data Reset**: All `r_stage_data` registers are cleared to zero
- **Valid Reset**: All `r_stage_valid` registers are cleared to zero
- **Output**: Both `sorted` and `done` outputs go to zero during reset

### Timing Characteristics

- **Latency**: `NUM_VALS` clock cycles from `valid_in` assertion to `done` assertion
- **Throughput**: 1 array per clock cycle (once pipeline is full)
- **Critical Path**: One compare-swap operation (typically 1-2 gate delays)
- **Pipeline Depth**: `NUM_VALS` stages

## State Machines

The Sort module does **not** use explicit Finite State Machines (FSMs). Instead, it uses a **pipeline-based control scheme**:

### Control Flow

1. **Input Stage (Combinational)**:
   - Accepts new `data` when `valid_in` is asserted
   - No state storage at input stage

2. **Pipeline Progression (Sequential)**:
   - Valid signal propagates through pipeline automatically
   - Each stage processes data independently
   - No centralized control or state machine needed

3. **Output Indication**:
   - `done` signal is simply the valid signal from the final pipeline stage
   - No complex output state management required

### Valid Signal Flow

```
Cycle:    1      2      3      4      5      6
valid_in: 1      0      0      0      0      0
r_stage_valid[1]: -      1      0      0      0      0
r_stage_valid[2]: -      -      1      0      0      0
r_stage_valid[3]: -      -      -      1      0      0
r_stage_valid[4]: -      -      -      -      1      0
r_stage_valid[5]: -      -      -      -      -      1
done:     0      0      0      0      0      1
```

## Special Features

### 1. Parameterizable Design

- **Flexible Array Size**: `NUM_VALS` can be any reasonable value (tested 3-32)
- **Configurable Data Width**: `SIZE` supports 1-64 bits per element
- **Automatic Pipeline Scaling**: Pipeline depth automatically adjusts to `NUM_VALS`

### 2. High Throughput Pipeline

- **Back-to-Back Operations**: New data can be accepted every cycle
- **Overlapped Processing**: Multiple arrays can be in the pipeline simultaneously
- **Predictable Performance**: Fixed latency regardless of data patterns

### 3. Synthesis-Friendly Design

- **Regular Structure**: All pipeline stages are nearly identical
- **Local Connectivity**: No long combinational paths across stages
- **Inference-Friendly**: Uses standard SystemVerilog constructs for reliable synthesis

### 4. Robust Data Handling

- **Packed Buses**: Efficient use of bus resources
- **Unpacked Internal Arrays**: Easy element-wise manipulation
- **Automatic Packing/Unpacking**: Transparent data format conversion

## Verification Strategy

The module comes with a comprehensive CocoTB testbench that includes:

### Test Levels

1. **Basic Tests**: Core functionality verification
2. **Random Tests**: Extensive random data patterns
3. **Boundary Tests**: Edge cases and limit conditions
4. **Pipeline Tests**: Throughput and overlapped operation verification
5. **Reset Tests**: Proper reset behavior validation

### Test Coverage

- **Functional**: All possible input combinations for small arrays
- **Parametric**: Multiple `NUM_VALS` and `SIZE` combinations
- **Temporal**: Pipeline timing and valid signal propagation
- **Stress**: Back-to-back operations and maximum throughput

## Usage Guidelines

### Typical Use Cases

1. **Packet Processing**: Sorting priority fields or timestamps
2. **Signal Processing**: Median filtering, statistical operations
3. **Graphics**: Z-buffer sorting, polygon vertex ordering
4. **Control Systems**: Sorting sensor readings or control parameters

### Integration Considerations

1. **Clock Domain**: Ensure `clk` is stable and meets timing requirements
2. **Reset Strategy**: Include proper reset sequencing in system design
3. **Data Formatting**: Pack input arrays correctly according to element ordering
4. **Flow Control**: Monitor `done` signal for output validity
5. **Resource Planning**: Consider pipeline depth impact on latency-sensitive applications

### Performance Optimization

1. **Pipeline Depth**: Use smallest practical `NUM_VALS` for lowest latency
2. **Data Width**: Use smallest practical `SIZE` for best area efficiency
3. **Clock Frequency**: Critical path is typically one comparison operation
4. **Resource Sharing**: Multiple instances can share input/output buses if properly arbitrated

## Synthesis Results

Typical synthesis results for common configurations:

| Configuration | Pipeline Stages | Critical Path | Area (LUTs) | Frequency |
|---------------|----------------|---------------|-------------|-----------|
| 3×8-bit | 3 | ~1.2ns | ~150 | >800 MHz |
| 5×16-bit | 5 | ~1.5ns | ~400 | >650 MHz |
| 8×32-bit | 8 | ~2.0ns | ~1200 | >500 MHz |

*Results vary by target FPGA family and synthesis tool settings*

## Future Enhancements

Potential improvements for future versions:

1. **Bidirectional Sorting**: Parameter to select ascending vs descending order
2. **Early Termination**: Detect when array is already sorted and terminate early
3. **Variable Width Elements**: Support for mixed-width data elements
4. **Priority Encoding**: Include secondary sort keys for equal elements
5. **Power Optimization**: Clock gating for unused pipeline stages

---

*This documentation describes the Sort module implementation. For the latest updates and additional examples, refer to the source code and testbench files.*

## Navigation

- **[← Back to RTLCommon Index](index.md)**
- **[← Back to Main Documentation Index](../../index.md)**
