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

# dataint_parity

## Overview

A generic parity generator and checker in one. It computes parity bits over data chunks and verifies incoming parity against them, supporting both even and odd schemes across as many data segments as you carve your bus into.

### Module Declaration

```systemverilog
module dataint_parity #(
    parameter int CHUNKS = 4,  // Number of chunks to check parity
    parameter int WIDTH  = 32  // Total width of the data
) (
    input  logic [ WIDTH-1:0] data_in,      // Data input
    input  logic [CHUNKS-1:0] parity_in,    // Parity input for checking
    input  logic              parity_type,  // 1=even, 0=odd
    output logic [CHUNKS-1:0] parity,       // Generated parity bits
    output logic [CHUNKS-1:0] parity_err    // Error indicators
);
```

## Parameters

| Parameter | Default | Description |
|-----------|---------|-------------|
| `CHUNKS` | 4 | Number of data chunks to process |
| `WIDTH` | 32 | Total width of input data in bits |

### Calculated Parameters

| Parameter | Formula | Description |
|-----------|---------|-------------|
| `ChunkSize` | `WIDTH / CHUNKS` | Size of each chunk in bits |
| `ExtraBits` | `WIDTH % CHUNKS` | Remaining bits if WIDTH not evenly divisible |

## Ports

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| `data_in` | Input | WIDTH | Input data to calculate/check parity |
| `parity_in` | Input | CHUNKS | Expected parity bits for verification |
| `parity_type` | Input | 1 | Parity type (1=even, 0=odd) |
| `parity` | Output | CHUNKS | Calculated parity bits |
| `parity_err` | Output | CHUNKS | Error flags (1=parity mismatch) |

## Functional Description

### Dual Operation Modes

The module does both jobs at once:
1. **Generates Parity**: Calculates parity for each data chunk
2. **Checks Parity**: Compares that calculated parity with the input parity

### Parity Types

- **Even Parity** (`parity_type = 1`): The parity bit makes the total 1s even
- **Odd Parity** (`parity_type = 0`): The parity bit makes the total 1s odd

### Data Chunking

Data gets divided into chunks, with a small wrinkle for widths that don't divide evenly:
- Most chunks: `ChunkSize` bits each
- The last chunk picks up any extra bits when `WIDTH % CHUNKS ≠ 0`

### Generate Block Architecture

```systemverilog
genvar i;
generate
    for (i = 0; i < CHUNKS; i++) begin : gen_parity
        // Calculate bounds for each chunk
        localparam int LowerBound = i * ChunkSize;
        localparam int UpperBound = (i < CHUNKS - 1) ? 
            ((i + 1) * ChunkSize) - 1 : WIDTH - 1;
        
        // Calculate parity for this chunk
        wire calculated_parity = parity_type ? 
            ^data_in[UpperBound:LowerBound] :      // Even parity
            ~^data_in[UpperBound:LowerBound];      // Odd parity
            
        assign parity[i] = calculated_parity;
        assign parity_err[i] = (calculated_parity != parity_in[i]);
    end
endgenerate
```

### Chunk Boundary Calculation

Each chunk's bounds are worked out statically:
- **Regular Chunks** (i < CHUNKS-1): Fixed-size chunks
- **Last Chunk** (i = CHUNKS-1): Mops up any remainder bits

### Parity Calculation Logic

For each chunk:
1. **XOR Reduction**: `^data_in[UpperBound:LowerBound]`
2. **Parity Type Application**:
   - Even parity: take the XOR result as-is
   - Odd parity: invert it

### Error Detection

Error checking is just a compare — calculated against expected:

```systemverilog
assign parity_err[i] = (calculated_parity != parity_in[i]);
```

### Example Configurations

32-bit data, 4 chunks (8 bits each):

```
Chunk 0: data_in[7:0]    → parity[0], parity_err[0]
Chunk 1: data_in[15:8]   → parity[1], parity_err[1]
Chunk 2: data_in[23:16]  → parity[2], parity_err[2]
Chunk 3: data_in[31:24]  → parity[3], parity_err[3]
```

30-bit data, 4 chunks (uneven division):

```
Chunk 0: data_in[6:0]    (7 bits)  → parity[0], parity_err[0]
Chunk 1: data_in[13:7]   (7 bits)  → parity[1], parity_err[1]
Chunk 2: data_in[20:14]  (7 bits)  → parity[2], parity_err[2]
Chunk 3: data_in[29:21]  (9 bits)  → parity[3], parity_err[3]
```

### Key Features

- **Scalable Architecture**: Parameterizable chunk count, flexible data width, uneven divisions handled for you
- **Simultaneous Operation**: Generation and checking run concurrently, each chunk minds its own business, and all chunks evaluate at the same time
- **Parity Flexibility**: You can flip the parity type during operation; all chunks share the same parity type; both common parity schemes covered

## Timing Characteristics
- **Combinational Logic**: Zero clock delay
- **Critical Path**: XOR tree depth ≈ log₂(ChunkSize)
- **Propagation Delay**: Minimal for typical chunk sizes
- **Area**: Grows linearly with CHUNKS and WIDTH; just XOR trees, so very little logic per chunk
- **Power**: Low — simple combinational logic, and power tracks the data switching

## Usage Examples

### Basic Parity Generation

```systemverilog
dataint_parity #(
    .CHUNKS(8),
    .WIDTH(64)
) parity_gen (
    .data_in(input_data),
    .parity_in(8'b0),           // Not used for generation
    .parity_type(1'b1),         // Even parity
    .parity(generated_parity),
    .parity_err()               // Not used for generation
);
```

### Parity Checking

```systemverilog
dataint_parity #(
    .CHUNKS(4),
    .WIDTH(32)
) parity_check (
    .data_in(received_data),
    .parity_in(received_parity),
    .parity_type(1'b0),         // Odd parity
    .parity(recalc_parity),
    .parity_err(error_flags)
);

// Check for any errors
wire any_parity_error = |error_flags;
```

### Error Correction System

```systemverilog
logic [CHUNKS-1:0] error_location;
logic [WIDTH-1:0]  corrected_data;

dataint_parity #(.CHUNKS(CHUNKS), .WIDTH(WIDTH)) parity_checker (
    .data_in(received_data),
    .parity_in(received_parity),
    .parity_type(even_parity),
    .parity(recalc_parity),
    .parity_err(error_location)
);

// Simple error correction (single-bit errors only)
always_comb begin
    corrected_data = received_data;
    for (int i = 0; i < CHUNKS; i++) begin
        if (error_location[i]) begin
            // Flip bits in the erroneous chunk
            // (Simplified - real correction needs more sophisticated logic)
        end
    end
end
```

## Design Notes

### Applications

- Memory parity checking
- Communication protocol verification
- Data bus integrity monitoring
- Storage system error detection
- Real-time parity generation and concurrent error checking
- Multi-segment data validation and protocol compliance verification
- Building block for ECC systems and larger error correction schemes
- Interface protection, debug and validation tools

Related application areas:
- **ECC Systems**: Building block for Hamming codes
- **Network Protocols**: Ethernet, UART parity
- **Memory Systems**: DRAM/SRAM parity protection
- **Communication**: RS-232, SPI, I2C error detection

### Chunk Size Selection

- **Power of 2**: Usually the friendliest for alignment
- **Protocol Requirements**: Match whatever your system demands
- **Error Granularity**: Smaller chunks pin errors down tighter

### Parity Type Selection

- **Even Parity**: The more common choice in digital systems
- **Odd Parity**: Gives you all-zeros detection
- **System Compatibility**: Match the existing standard

### Width Considerations

- **Alignment**: Think about data bus alignment
- **Extra Bits**: Handle remainder bits sensibly
- **Performance**: Balance chunk count against granularity

## Testing

`val/common/test_dataint_parity.py` exercises this module. It collects 16 parameter cases at the default `REG_LEVEL`.

```bash
source env_python
pytest val/common/test_dataint_parity.py -v
```

---

## Navigation

- **[← Back to rtl-common Index](index.md)**
- **[← Back to Main Documentation Index](../index.md)**
