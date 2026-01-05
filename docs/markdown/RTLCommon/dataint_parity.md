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

# dataint_parity Module Documentation

## Purpose
The `dataint_parity` module implements a generic parity generator and checker. It can generate parity bits for data chunks and verify existing parity bits, supporting both even and odd parity schemes across multiple data segments.

## Module Declaration
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

## Calculated Parameters
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

## Functionality

### Dual Operation Modes
The module simultaneously:
1. **Generates Parity**: Calculates parity for each data chunk
2. **Checks Parity**: Compares calculated parity with input parity

### Parity Types
- **Even Parity** (`parity_type = 1`): Parity bit makes total 1s even
- **Odd Parity** (`parity_type = 0`): Parity bit makes total 1s odd

### Data Chunking
Data is divided into chunks with special handling for non-even divisions:
- Most chunks: `ChunkSize` bits each
- Last chunk: May include extra bits if `WIDTH % CHUNKS ≠ 0`

## Implementation Details

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
Each chunk's boundaries are calculated statically:
- **Regular Chunks** (i < CHUNKS-1): Fixed size chunks
- **Last Chunk** (i = CHUNKS-1): Includes any remaining bits

### Parity Calculation Logic
For each chunk:
1. **XOR Reduction**: `^data_in[UpperBound:LowerBound]`
2. **Parity Type Application**:
   - Even parity: Use XOR result directly
   - Odd parity: Invert XOR result

### Error Detection
Error detection compares calculated vs. expected parity:
```systemverilog
assign parity_err[i] = (calculated_parity != parity_in[i]);
```

## Key Features

### Scalable Architecture
- **Parameterizable Chunks**: Any number of data segments
- **Flexible Data Width**: Supports any total data width
- **Automatic Sizing**: Handles non-even chunk divisions

### Simultaneous Operation
- **Generation and Checking**: Both operations happen concurrently
- **Independent Chunks**: Each chunk operates independently
- **Parallel Processing**: All chunks processed simultaneously

### Parity Flexibility
- **Runtime Configurable**: Parity type can change during operation
- **Per-Module Setting**: All chunks use same parity type
- **Standard Support**: Supports both common parity schemes

## Example Configurations

### 32-bit Data, 4 Chunks (8 bits each)
```
Chunk 0: data_in[7:0]    → parity[0], parity_err[0]
Chunk 1: data_in[15:8]   → parity[1], parity_err[1]
Chunk 2: data_in[23:16]  → parity[2], parity_err[2]
Chunk 3: data_in[31:24]  → parity[3], parity_err[3]
```

### 30-bit Data, 4 Chunks (uneven division)
```
Chunk 0: data_in[6:0]    (7 bits)  → parity[0], parity_err[0]
Chunk 1: data_in[13:7]   (7 bits)  → parity[1], parity_err[1]
Chunk 2: data_in[20:14]  (7 bits)  → parity[2], parity_err[2]
Chunk 3: data_in[29:21]  (9 bits)  → parity[3], parity_err[3]
```

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

## Performance Characteristics

### Timing
- **Combinational Logic**: Zero clock delay
- **Critical Path**: XOR tree depth ≈ log₂(ChunkSize)
- **Propagation Delay**: Minimal for typical chunk sizes

### Area
- **Linear Scaling**: Area increases with CHUNKS and WIDTH
- **Efficient Implementation**: Simple XOR trees
- **Low Overhead**: Minimal logic per chunk

### Power
- **Low Power**: Simple combinational logic
- **Activity Dependent**: Power scales with data switching

## Applications

### Error Detection
- Memory parity checking
- Communication protocol verification
- Data bus integrity monitoring
- Storage system error detection

### Data Integrity
- Real-time parity generation
- Concurrent error checking
- Multi-segment data validation
- Protocol compliance verification

### System Integration
- Building block for ECC systems
- Component in larger error correction schemes
- Interface protection
- Debug and validation tools

## Design Considerations

### Chunk Size Selection
- **Power of 2**: Often preferred for alignment
- **Protocol Requirements**: Match system requirements
- **Error Granularity**: Smaller chunks = finer error localization

### Parity Type Selection
- **Even Parity**: More common in digital systems
- **Odd Parity**: Provides all-zeros detection
- **System Compatibility**: Match existing standards

### Width Considerations
- **Alignment**: Consider data bus alignment
- **Extra Bits**: Handle remainder bits appropriately
- **Performance**: Balance chunk count vs. granularity

## Related Applications
- **ECC Systems**: Building block for Hamming codes
- **Network Protocols**: Ethernet, UART parity
- **Memory Systems**: DRAM/SRAM parity protection
- **Communication**: RS-232, SPI, I2C error detection

## Navigation

- **[← Back to RTLCommon Index](index.md)**
- **[← Back to Main Documentation Index](../../index.md)**
