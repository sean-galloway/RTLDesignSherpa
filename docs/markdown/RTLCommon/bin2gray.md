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

# Binary to Gray Code Converter

## Overview
The `bin2gray` module implements a purely combinational binary-to-Gray code converter. Gray code (also known as reflected binary code or unit distance code) is a binary numeral system where two successive values differ in only one bit. This property makes Gray code essential for reducing glitches and metastability in digital systems, particularly in asynchronous designs and clock domain crossings.

## Module Declaration
```systemverilog
module bin2gray #(
    parameter int WIDTH = 4
) (
    input  wire [WIDTH-1:0] binary,
    output wire [WIDTH-1:0] gray
);
```

## Parameters

### WIDTH
- **Type**: `int`
- **Default**: `4`
- **Description**: Bit width of both input and output
- **Range**: Any positive integer ≥ 1
- **Common Values**: 4, 8, 16, 32 for address counters and data buses
- **Impact**: Determines the number of XOR gates required

## Ports

### Inputs
| Port | Width | Type | Description |
|------|-------|------|-------------|
| `binary` | WIDTH | `wire` | Input binary value |

### Outputs
| Port | Width | Type | Description |
|------|-------|------|-------------|
| `gray` | WIDTH | `wire` | Output Gray code value |

## Gray Code Theory

### Mathematical Definition
Gray code conversion follows a simple mathematical relationship:
- **MSB**: `gray[WIDTH-1] = binary[WIDTH-1]` (MSB unchanged)
- **Other bits**: `gray[i] = binary[i] ⊕ binary[i+1]` for i = 0 to WIDTH-2

### Why Gray Code?
Gray code solves several problems in digital systems:

1. **Single Bit Transitions**: Adjacent values differ by exactly one bit
2. **Glitch Reduction**: Eliminates intermediate states during transitions
3. **Metastability Prevention**: Safer for asynchronous clock domain crossings
4. **Mechanical Encoders**: Natural for optical/magnetic position encoders

### Gray Code Sequence Examples

#### 2-bit Gray Code
| Decimal | Binary | Gray | Transition |
|---------|--------|------|------------|
| 0 | 00 | 00 | - |
| 1 | 01 | 01 | bit 0 |
| 2 | 10 | 11 | bit 1 |
| 3 | 11 | 10 | bit 0 |

#### 3-bit Gray Code
| Decimal | Binary | Gray | Changed Bit |
|---------|--------|------|-------------|
| 0 | 000 | 000 | - |
| 1 | 001 | 001 | 0 |
| 2 | 010 | 011 | 1 |
| 3 | 011 | 010 | 0 |
| 4 | 100 | 110 | 2 |
| 5 | 101 | 111 | 0 |
| 6 | 110 | 101 | 1 |
| 7 | 111 | 100 | 0 |

#### 4-bit Gray Code (Complete Table)
| Dec | Binary | Gray | Dec | Binary | Gray |
|-----|--------|------|-----|--------|------|
| 0 | 0000 | 0000 | 8 | 1000 | 1100 |
| 1 | 0001 | 0001 | 9 | 1001 | 1101 |
| 2 | 0010 | 0011 | 10 | 1010 | 1111 |
| 3 | 0011 | 0010 | 11 | 1011 | 1110 |
| 4 | 0100 | 0110 | 12 | 1100 | 1010 |
| 5 | 0101 | 0111 | 13 | 1101 | 1011 |
| 6 | 0110 | 0101 | 14 | 1110 | 1001 |
| 7 | 0111 | 0100 | 15 | 1111 | 1000 |

## Implementation Analysis

### Core Logic
```systemverilog
genvar i;
generate
    for (i = 0; i < WIDTH - 1; i++) begin : gen_gray
        assign gray[i] = binary[i] ^ binary[i+1];
    end
endgenerate

assign gray[WIDTH-1] = binary[WIDTH-1];
```

### Logic Structure
The implementation creates a chain of XOR gates:
- **Lower bits**: Each gray bit is XOR of current and next binary bits
- **MSB**: Directly assigned from binary MSB
- **Propagation**: Single level of logic (all XORs in parallel)

### Gate-Level Implementation
For WIDTH = 4:
```
binary[3] ────────────────────────→ gray[3]
binary[2] ────┬──────────────────→ gray[2]
              │     
binary[1] ────┼─────XOR──────────→ gray[1]  
              │      │
binary[0] ────┼──────┼───XOR─────→ gray[0]
              │      │    │
              └──────┘    └─ binary[1]
                     └─ binary[2]
```

### Timing Characteristics
- **Propagation Delay**: Single XOR gate delay (typically 0.1-0.3ns in modern processes)
- **Critical Path**: Through one XOR gate only
- **Fan-out**: Each binary bit drives at most 2 XOR gates
- **Scalability**: Constant delay regardless of WIDTH

## Design Examples and Applications

### 1. Asynchronous FIFO Pointer
```systemverilog
module async_fifo_ptr #(
    parameter int ADDR_WIDTH = 4
) (
    input  logic                  clk,
    input  logic                  rst_n,
    input  logic                  enable,
    output logic [ADDR_WIDTH:0]   gray_ptr,
    output logic [ADDR_WIDTH-1:0] addr
);

    logic [ADDR_WIDTH:0] binary_ptr, binary_ptr_next;
    
    // Binary counter
    assign binary_ptr_next = enable ? (binary_ptr + 1) : binary_ptr;
    
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n)
            binary_ptr <= 'b0;
        else
            binary_ptr <= binary_ptr_next;
    end
    
    // Binary to Gray conversion
    bin2gray #(
        .WIDTH(ADDR_WIDTH + 1)
    ) ptr_converter (
        .binary(binary_ptr),
        .gray(gray_ptr)
    );
    
    // Extract address (lower bits of binary counter)
    assign addr = binary_ptr[ADDR_WIDTH-1:0];

endmodule
```

### 2. Clock Domain Crossing Counter
```systemverilog
module cross_domain_counter #(
    parameter int WIDTH = 8
) (
    // Source domain
    input  logic             src_clk,
    input  logic             src_rst_n,
    input  logic             src_enable,
    
    // Destination domain  
    input  logic             dst_clk,
    input  logic             dst_rst_n,
    output logic [WIDTH-1:0] dst_count_binary,
    output logic [WIDTH-1:0] dst_count_gray
);

    // Source domain counter
    logic [WIDTH-1:0] src_binary, src_gray;
    
    always_ff @(posedge src_clk or negedge src_rst_n) begin
        if (!src_rst_n)
            src_binary <= 'b0;
        else if (src_enable)
            src_binary <= src_binary + 1;
    end
    
    // Convert to Gray in source domain
    bin2gray #(.WIDTH(WIDTH)) src_converter (
        .binary(src_binary),
        .gray(src_gray)
    );
    
    // Synchronize Gray code to destination domain
    logic [WIDTH-1:0] dst_gray_sync;
    
    synchronizer #(.WIDTH(WIDTH)) gray_sync (
        .clk(dst_clk),
        .rst_n(dst_rst_n),
        .data_in(src_gray),
        .data_out(dst_gray_sync)
    );
    
    // Convert back to binary in destination domain
    gray2bin #(.WIDTH(WIDTH)) dst_converter (
        .gray(dst_gray_sync),
        .binary(dst_count_binary)
    );
    
    assign dst_count_gray = dst_gray_sync;

endmodule
```

### 3. Rotary Encoder Interface
```systemverilog
module rotary_encoder_interface #(
    parameter int POSITION_WIDTH = 12
) (
    input  logic                        clk,
    input  logic                        rst_n,
    input  logic [POSITION_WIDTH-1:0]   encoder_binary,
    output logic [POSITION_WIDTH-1:0]   encoder_gray,
    output logic [POSITION_WIDTH-1:0]   position_filtered,
    output logic                        position_changed
);

    // Convert encoder binary position to Gray
    bin2gray #(
        .WIDTH(POSITION_WIDTH)
    ) encoder_conv (
        .binary(encoder_binary),
        .gray(encoder_gray)
    );
    
    // Synchronize and filter
    logic [POSITION_WIDTH-1:0] gray_sync, gray_prev;
    
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            gray_sync <= 'b0;
            gray_prev <= 'b0;
        end else begin
            gray_sync <= encoder_gray;
            gray_prev <= gray_sync;
        end
    end
    
    // Detect changes (only one bit should change in Gray code)
    logic valid_transition;
    assign valid_transition = ($countones(gray_sync ^ gray_prev) <= 1);
    
    // Convert back to binary for position output
    gray2bin #(.WIDTH(POSITION_WIDTH)) pos_converter (
        .gray(gray_sync),
        .binary(position_filtered)
    );
    
    assign position_changed = valid_transition && (gray_sync != gray_prev);

endmodule
```

### 4. Address Scrambling for Memory Testing
```systemverilog
module memory_address_scrambler #(
    parameter int ADDR_WIDTH = 16
) (
    input  logic [ADDR_WIDTH-1:0] linear_addr,
    output logic [ADDR_WIDTH-1:0] scrambled_addr
);

    logic [ADDR_WIDTH-1:0] gray_addr;
    
    // Convert linear address to Gray code for scrambling
    bin2gray #(.WIDTH(ADDR_WIDTH)) scrambler (
        .binary(linear_addr),
        .gray(gray_addr)
    );
    
    // Additional scrambling (optional)
    assign scrambled_addr = {gray_addr[0], gray_addr[ADDR_WIDTH-1:1]};

endmodule
```

### 5. Multi-Bit Synchronizer with Gray Code
```systemverilog
module gray_code_synchronizer #(
    parameter int WIDTH = 8,
    parameter int SYNC_STAGES = 2
) (
    input  logic             src_clk,
    input  logic             src_rst_n,
    input  logic [WIDTH-1:0] src_data,
    
    input  logic             dst_clk,
    input  logic             dst_rst_n,
    output logic [WIDTH-1:0] dst_data
);

    // Convert to Gray in source domain
    logic [WIDTH-1:0] src_gray;
    
    bin2gray #(.WIDTH(WIDTH)) src_conv (
        .binary(src_data),
        .gray(src_gray)
    );
    
    // Multi-stage synchronizer for Gray code
    logic [WIDTH-1:0] sync_regs [SYNC_STAGES];
    
    always_ff @(posedge dst_clk or negedge dst_rst_n) begin
        if (!dst_rst_n) begin
            for (int i = 0; i < SYNC_STAGES; i++) begin
                sync_regs[i] <= 'b0;
            end
        end else begin
            sync_regs[0] <= src_gray;
            for (int i = 1; i < SYNC_STAGES; i++) begin
                sync_regs[i] <= sync_regs[i-1];
            end
        end
    end
    
    // Convert back to binary in destination domain
    gray2bin #(.WIDTH(WIDTH)) dst_conv (
        .gray(sync_regs[SYNC_STAGES-1]),
        .binary(dst_data)
    );

endmodule
```

## Companion Gray-to-Binary Converter

### Implementation
```systemverilog
module gray2bin #(
    parameter int WIDTH = 4
) (
    input  wire [WIDTH-1:0] gray,
    output wire [WIDTH-1:0] binary
);

    genvar i;
    
    // MSB is unchanged
    assign binary[WIDTH-1] = gray[WIDTH-1];
    
    // Other bits: XOR accumulation from MSB down
    generate
        for (i = WIDTH-2; i >= 0; i--) begin : gen_binary
            assign binary[i] = binary[i+1] ^ gray[i];
        end
    endgenerate

endmodule
```

### Gray-to-Binary Truth Table (4-bit)
| Gray | Binary | Conversion Process |
|------|--------|--------------------|
| 0000 | 0000 | bin[3]=0, bin[2]=0⊕0=0, bin[1]=0⊕0=0, bin[0]=0⊕0=0 |
| 0001 | 0001 | bin[3]=0, bin[2]=0⊕0=0, bin[1]=0⊕0=0, bin[0]=0⊕1=1 |
| 0011 | 0010 | bin[3]=0, bin[2]=0⊕0=0, bin[1]=0⊕1=1, bin[0]=1⊕1=0 |
| 0010 | 0011 | bin[3]=0, bin[2]=0⊕0=0, bin[1]=0⊕1=1, bin[0]=1⊕0=1 |

## Advanced Implementations

### 1. Parameterized Converter with Validation
```systemverilog
module bin2gray_validated #(
    parameter int WIDTH = 4,
    parameter bit ENABLE_CHECKS = 1
) (
    input  logic [WIDTH-1:0] binary,
    output logic [WIDTH-1:0] gray,
    output logic             valid
);

    // Basic conversion
    bin2gray #(.WIDTH(WIDTH)) converter (
        .binary(binary),
        .gray(gray)
    );
    
    // Optional validation
    generate
        if (ENABLE_CHECKS) begin : validation
            logic [WIDTH-1:0] binary_check;
            
            // Round-trip conversion check
            gray2bin #(.WIDTH(WIDTH)) check_converter (
                .gray(gray),
                .binary(binary_check)
            );
            
            assign valid = (binary == binary_check);
        end else begin : no_validation
            assign valid = 1'b1;
        end
    endgenerate

endmodule
```

### 2. Pipelined Converter for High Speed
```systemverilog
module bin2gray_pipelined #(
    parameter int WIDTH = 32,
    parameter int PIPELINE_STAGES = 2
) (
    input  logic             clk,
    input  logic             rst_n,
    input  logic [WIDTH-1:0] binary_in,
    input  logic             valid_in,
    output logic [WIDTH-1:0] gray_out,
    output logic             valid_out
);

    // Pipeline registers
    logic [WIDTH-1:0] binary_pipe [PIPELINE_STAGES];
    logic valid_pipe [PIPELINE_STAGES];
    logic [WIDTH-1:0] gray_pipe [PIPELINE_STAGES];
    
    // Stage 0: Input registration
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            binary_pipe[0] <= 'b0;
            valid_pipe[0] <= 1'b0;
        end else begin
            binary_pipe[0] <= binary_in;
            valid_pipe[0] <= valid_in;
        end
    end
    
    // Conversion in stage 0
    bin2gray #(.WIDTH(WIDTH)) stage0_conv (
        .binary(binary_pipe[0]),
        .gray(gray_pipe[0])
    );
    
    // Additional pipeline stages
    generate
        for (genvar s = 1; s < PIPELINE_STAGES; s++) begin : pipeline_stages
            always_ff @(posedge clk or negedge rst_n) begin
                if (!rst_n) begin
                    gray_pipe[s] <= 'b0;
                    valid_pipe[s] <= 1'b0;
                end else begin
                    gray_pipe[s] <= gray_pipe[s-1];
                    valid_pipe[s] <= valid_pipe[s-1];
                end
            end
        end
    endgenerate
    
    // Output assignment
    assign gray_out = gray_pipe[PIPELINE_STAGES-1];
    assign valid_out = valid_pipe[PIPELINE_STAGES-1];

endmodule
```

### 3. Bidirectional Converter
```systemverilog
module bidirectional_gray_converter #(
    parameter int WIDTH = 8
) (
    input  logic             direction,  // 0: bin→gray, 1: gray→bin
    input  logic [WIDTH-1:0] data_in,
    output logic [WIDTH-1:0] data_out
);

    logic [WIDTH-1:0] bin_to_gray_out, gray_to_bin_out;
    
    // Both converters always active
    bin2gray #(.WIDTH(WIDTH)) b2g (
        .binary(data_in),
        .gray(bin_to_gray_out)
    );
    
    gray2bin #(.WIDTH(WIDTH)) g2b (
        .gray(data_in),
        .binary(gray_to_bin_out)
    );
    
    // Mux output based on direction
    assign data_out = direction ? gray_to_bin_out : bin_to_gray_out;

endmodule
```

## Verification and Testing

### Comprehensive Test Bench
```systemverilog
module tb_bin2gray;

    parameter int WIDTH = 4;
    parameter int MAX_VAL = (1 << WIDTH) - 1;
    
    logic [WIDTH-1:0] binary, gray;
    logic [WIDTH-1:0] expected_gray;
    logic [WIDTH-1:0] binary_check;
    
    // DUT
    bin2gray #(.WIDTH(WIDTH)) dut (
        .binary(binary),
        .gray(gray)
    );
    
    // Reference converter for checking
    gray2bin #(.WIDTH(WIDTH)) check_conv (
        .gray(gray),
        .binary(binary_check)
    );
    
    // Test sequence
    initial begin
        $display("Testing %d-bit Binary to Gray converter", WIDTH);
        
        // Test all possible values
        for (int i = 0; i <= MAX_VAL; i++) begin
            binary = i;
            expected_gray = compute_gray_reference(i);
            
            #1; // Allow propagation
            
            // Check conversion correctness
            if (gray !== expected_gray) begin
                $error("Mismatch: binary=%b, expected_gray=%b, actual_gray=%b", 
                       binary, expected_gray, gray);
            end
            
            // Check round-trip conversion
            if (binary_check !== binary) begin
                $error("Round-trip failed: original=%b, recovered=%b", 
                       binary, binary_check);
            end
            
            // Check single-bit change property
            if (i > 0) begin
                logic [WIDTH-1:0] prev_gray = compute_gray_reference(i-1);
                int bit_changes = $countones(gray ^ prev_gray);
                if (bit_changes != 1) begin
                    $error("Multiple bit change: %d→%d, gray %b→%b, changes=%d",
                           i-1, i, prev_gray, gray, bit_changes);
                end
            end
            
            $display("PASS: %d → binary:%b → gray:%b", i, binary, gray);
        end
        
        $display("All tests passed!");
        $finish;
    end
    
    // Reference Gray code computation
    function [WIDTH-1:0] compute_gray_reference(input [WIDTH-1:0] bin);
        compute_gray_reference[WIDTH-1] = bin[WIDTH-1];
        for (int i = WIDTH-2; i >= 0; i--) begin
            compute_gray_reference[i] = bin[i] ^ bin[i+1];
        end
    endfunction

endmodule
```

### Property-Based Verification
```systemverilog
module bin2gray_properties #(
    parameter int WIDTH = 4
);

    logic [WIDTH-1:0] binary, gray;
    
    // Bind to DUT
    bind bin2gray bin2gray_properties #(WIDTH) props_inst (.*);
    
    // Property: MSB preservation
    property msb_unchanged;
        gray[WIDTH-1] == binary[WIDTH-1];
    endproperty
    
    // Property: Single bit change between consecutive values
    property single_bit_change;
        logic [WIDTH-1:0] bin_plus_one = binary + 1;
        logic [WIDTH-1:0] gray_plus_one;
        
        // Compute Gray code for binary+1
        assign gray_plus_one[WIDTH-1] = bin_plus_one[WIDTH-1];
        for (genvar i = 0; i < WIDTH-1; i++) begin
            assign gray_plus_one[i] = bin_plus_one[i] ^ bin_plus_one[i+1];
        end
        
        // Check single bit difference
        (binary < (2**WIDTH - 1)) |-> ($countones(gray ^ gray_plus_one) == 1);
    endproperty
    
    // Property: Round-trip conversion
    property round_trip_conversion;
        logic [WIDTH-1:0] recovered_binary;
        
        // Convert back to binary
        assign recovered_binary[WIDTH-1] = gray[WIDTH-1];
        for (genvar i = WIDTH-2; i >= 0; i--) begin
            assign recovered_binary[i] = recovered_binary[i+1] ^ gray[i];
        end
        
        recovered_binary == binary;
    endproperty
    
    // Assertions
    assert property (msb_unchanged);
    assert property (single_bit_change);
    assert property (round_trip_conversion);

endmodule
```

### Coverage Model
```systemverilog
covergroup bin2gray_cg;
    
    cp_binary_values: coverpoint binary {
        bins zero = {0};
        bins powers_of_two[] = {1, 2, 4, 8, 16}; // For appropriate WIDTH
        bins max_value = {2**WIDTH - 1};
        bins mid_range[] = {[1:2**(WIDTH-1)-1]};
        bins upper_range[] = {[2**(WIDTH-1):2**WIDTH-2]};
    }
    
    cp_gray_values: coverpoint gray {
        bins all_values[] = {[0:2**WIDTH-1]};
    }
    
    cp_bit_patterns: coverpoint binary {
        bins alternating_01 = {8'b01010101}; // For WIDTH=8
        bins alternating_10 = {8'b10101010};
        bins all_ones = {'1};
        bins all_zeros = {'0};
    }
    
    // Cross coverage between input patterns and outputs
    cross_binary_gray: cross cp_binary_values, cp_gray_values;

endcovergroup
```

## Synthesis Optimization

### Resource Utilization
For different widths, typical FPGA resource usage:

| WIDTH | LUTs | Delay (ns) | Max Freq (MHz) |
|-------|------|------------|----------------|
| 4 | 3 | 0.2 | 800+ |
| 8 | 7 | 0.2 | 800+ |
| 16 | 15 | 0.3 | 600+ |
| 32 | 31 | 0.4 | 500+ |

### Timing Optimization
```systemverilog
// For critical timing paths, add pipeline register
module bin2gray_registered #(
    parameter int WIDTH = 16
) (
    input  logic             clk,
    input  logic             rst_n,
    input  logic [WIDTH-1:0] binary,
    output logic [WIDTH-1:0] gray
);

    logic [WIDTH-1:0] gray_comb;
    
    // Combinational conversion
    bin2gray #(.WIDTH(WIDTH)) conv (
        .binary(binary),
        .gray(gray_comb)
    );
    
    // Output register
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n)
            gray <= 'b0;
        else
            gray <= gray_comb;
    end

endmodule
```

### Power Optimization
```systemverilog
// Clock gating for power savings
module bin2gray_gated #(
    parameter int WIDTH = 8
) (
    input  logic             clk,
    input  logic             rst_n,
    input  logic             enable,
    input  logic [WIDTH-1:0] binary,
    output logic [WIDTH-1:0] gray
);

    logic gated_clk;
    
    // Clock gate
    clock_gate cg_inst (
        .clk(clk),
        .enable(enable),
        .gated_clk(gated_clk)
    );
    
    // Registered converter
    bin2gray_registered #(.WIDTH(WIDTH)) conv (
        .clk(gated_clk),
        .rst_n(rst_n),
        .binary(binary),
        .gray(gray)
    );

endmodule
```

## Common Applications Summary

### 1. **Asynchronous FIFOs**: Prevent metastability in pointer comparisons
### 2. **Clock Domain Crossing**: Safe multi-bit signal transfer
### 3. **Position Encoders**: Mechanical/optical encoder interfaces  
### 4. **Memory Address Generation**: Reduce EMI and power spikes
### 5. **Test Pattern Generation**: Controlled single-bit transitions
### 6. **Error Detection**: Single-bit error detection schemes
### 7. **ADC/DAC Interfaces**: Reduce glitches in conversion systems

## Design Guidelines

### 1. **Always Use for Async Boundaries**: Gray code is essential for safe asynchronous transfers
### 2. **Consider Timing**: Purely combinational - no setup/hold concerns
### 3. **Verify Single-Bit Property**: Always verify adjacent values differ by one bit
### 4. **Plan for Back-Conversion**: Usually need Gray-to-Binary converter too
### 5. **Check Width Requirements**: Ensure sufficient bits for application range

The Binary-to-Gray converter is a fundamental building block in digital design, providing robust solutions for asynchronous interfaces and glitch-free operations. Its simplicity and reliability make it indispensable for safe digital system design.

## Navigation

- **[← Back to RTLCommon Index](index.md)**
- **[← Back to Main Documentation Index](../../index.md)**
