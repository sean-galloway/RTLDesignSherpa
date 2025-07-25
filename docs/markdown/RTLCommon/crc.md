# dataint_crc Module Documentation

## Purpose
The `dataint_crc` module implements a highly configurable Cyclic Redundancy Check (CRC) calculator. It supports various CRC algorithms with customizable polynomial, data width, reflection options, and cascaded processing for wide data inputs.

## Module Declaration
```systemverilog
module dataint_crc #(
    parameter string ALGO_NAME = "DEADF1F0",
    parameter int DATA_WIDTH = 64,
    parameter int CHUNKS = DATA_WIDTH / 8,
    parameter int CRC_WIDTH = 64,
    parameter int REFIN = 1,
    parameter int REFOUT = 1,
    parameter int CW = CRC_WIDTH,
    parameter int DW = DATA_WIDTH,
    parameter int CH = CHUNKS
) (
    input  logic [CRC_WIDTH-1:0]  POLY,
    input  logic [CRC_WIDTH-1:0]  POLY_INIT,
    input  logic [CRC_WIDTH-1:0]  XOROUT,
    input  logic                  clk,
    input  logic                  rst_n,
    input  logic                  load_crc_start,
    input  logic                  load_from_cascade,
    input  logic [    CHUNKS-1:0] cascade_sel,
    input  logic [DATA_WIDTH-1:0] data,
    output logic [ CRC_WIDTH-1:0] crc
);
```

## Parameters
| Parameter | Default | Description |
|-----------|---------|-------------|
| `ALGO_NAME` | "DEADF1F0" | Algorithm name (for documentation) |
| `DATA_WIDTH` | 64 | Width of input data in bits |
| `CHUNKS` | DATA_WIDTH/8 | Number of 8-bit chunks for processing |
| `CRC_WIDTH` | 64 | Width of CRC polynomial and result |
| `REFIN` | 1 | Reflect input data (1=reflect, 0=direct) |
| `REFOUT` | 1 | Reflect output result (1=reflect, 0=direct) |
| `CW`, `DW`, `CH` | Aliases | Convenient aliases for width parameters |

## Ports
| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| `POLY` | Input | CRC_WIDTH | CRC polynomial |
| `POLY_INIT` | Input | CRC_WIDTH | Initial CRC value |
| `XOROUT` | Input | CRC_WIDTH | Final XOR value |
| `clk` | Input | 1 | Clock signal |
| `rst_n` | Input | 1 | Active-low asynchronous reset |
| `load_crc_start` | Input | 1 | Load initial CRC value |
| `load_from_cascade` | Input | 1 | Load CRC from cascade chain |
| `cascade_sel` | Input | CHUNKS | One-hot selection for cascade output |
| `data` | Input | DATA_WIDTH | Input data for CRC calculation |
| `crc` | Output | CRC_WIDTH | Calculated CRC value |

## Functionality

### Core Operation
The module processes data in 8-bit chunks through a cascade of CRC calculation blocks:
1. **Input Processing**: Data is optionally reflected based on `REFIN` parameter
2. **Cascade Processing**: Each 8-bit chunk is processed sequentially
3. **Output Processing**: Result is optionally reflected and XORed based on parameters

### CRC Calculation Flow
1. Initialize CRC register with `POLY_INIT`
2. Process data through cascade chain
3. Apply output reflection if `REFOUT` is enabled
4. XOR final result with `XOROUT`

## Implementation Details

### Key Features
- **Configurable Width**: Supports arbitrary CRC and data widths
- **Reflection Support**: Independent input and output bit reflection
- **Cascaded Processing**: Handles wide data inputs efficiently
- **Algorithm Flexibility**: Runtime configurable polynomial and parameters

### Cascade Architecture
The module uses a cascade of `dataint_crc_xor_shift_cascade` blocks:
- Each block processes 8 bits of data
- Blocks are chained together for wide data processing
- `cascade_sel` allows selection of intermediate results

### Input Reflection Logic
```systemverilog
// When REFIN != 0, bits are reflected within each byte
if (REFIN != 0) begin
    for (i = 0; i < CH; i++) begin
        for (j = 0; j < 8; j++) begin
            assign w_block_data[i][j] = data[i*8+7-j];
        end
    end
end
```

### Output Reflection Logic
```systemverilog
// When REFOUT != 0, entire CRC result is bit-reversed
if (REFOUT != 0) begin
    for (idx = 0; idx < CW; idx++) 
        assign w_result[idx] = r_crc_value[(CW-1)-idx];
end
```

## State Machine
The module operates with the following control states:

### Control States
1. **RESET**: CRC register holds initial value
2. **START**: Load `POLY_INIT` into CRC register
3. **CASCADE_LOAD**: Load intermediate cascade result
4. **PROCESSING**: Normal CRC calculation mode

### State Transitions
- `rst_n` (async) → RESET
- `load_crc_start` → START
- `load_from_cascade` → CASCADE_LOAD

## Special Implementation Features

### Dynamic Cascade Selection
The module supports selecting intermediate cascade results:
```systemverilog
always_comb begin
    w_selected_cascade_output = POLY_INIT;
    for (int i = 0; i < CH; i++) begin
        if (cascade_sel[i]) begin
            w_selected_cascade_output = w_cascade[i];
        end
    end
end
```

### Debug Support
The module includes simulation-only debug features:
- Flattened arrays for waveform viewing
- Protected by `synopsys translate_off/on` directives

### Generate Blocks
Extensive use of generate blocks for:
- Input reflection logic
- Cascade chain instantiation
- Output reflection logic
- Debug signal flattening

## Usage Example
```systemverilog
// CRC-32 calculator
dataint_crc #(
    .ALGO_NAME("CRC32"),
    .DATA_WIDTH(32),
    .CRC_WIDTH(32),
    .REFIN(1),
    .REFOUT(1)
) crc32_calc (
    .POLY(32'h04C11DB7),
    .POLY_INIT(32'hFFFFFFFF),
    .XOROUT(32'hFFFFFFFF),
    .clk(clk),
    .rst_n(rst_n),
    .load_crc_start(start_crc),
    .load_from_cascade(1'b0),
    .cascade_sel(4'b1000), // Select final chunk
    .data(input_data),
    .crc(crc_result)
);
```

## Applications
- Ethernet frame checking
- File integrity verification
- Communication protocol error detection
- Data storage error correction
- Custom CRC algorithm implementation