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

# dataint_ecc_hamming_decode_secded

## Overview

A Hamming decoder with SECDED — Single Error Correction, Double Error Detection. It decodes Hamming-encoded data, detects and fixes single-bit errors, and raises a flag when two bits have gone bad (which it can see but not repair).

### Module Declaration

```systemverilog
module dataint_ecc_hamming_decode_secded #(
    parameter int WIDTH = 4,
    parameter int DEBUG = 0
) (
    input  logic                      clk,
    rst_n,
    input  logic                      enable,
    input  logic [WIDTH+ParityBits:0] hamming_data,
    output logic [         WIDTH-1:0] data,
    output logic                      error_detected,
    output logic                      double_error_detected
);
```

## Parameters

| Parameter | Default | Description |
|-----------|---------|-------------|
| `WIDTH` | 4 | Width of original data in bits |
| `DEBUG` | 0 | Enable debug output (1=enabled, 0=disabled) |

### Calculated Parameters

| Parameter | Formula | Description |
|-----------|---------|-------------|
| `ParityBits` | `$clog2(WIDTH + $clog2(WIDTH) + 1)` | Number of Hamming parity bits |
| `TotalWidth` | `WIDTH + ParityBits + 1` | Total encoded data width |

## Ports

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| `clk` | Input | 1 | Clock signal |
| `rst_n` | Input | 1 | Active-low asynchronous reset |
| `enable` | Input | 1 | Enable decoding operation |
| `hamming_data` | Input | TotalWidth | Encoded data with ECC bits |
| `data` | Output | WIDTH | Decoded original data |
| `error_detected` | Output | 1 | Single or double error detected |
| `double_error_detected` | Output | 1 | Double error specifically detected |

## Functional Description

### Decoding Process

1. **Syndrome Generation**: Calculate the parity check syndrome
2. **Overall Parity Check**: Verify the SECDED bit
3. **Error Classification**: Work out the error type and location
4. **Error Correction**: Fix single-bit errors
5. **Data Extraction**: Pull the corrected original data back out

### Error Detection Logic

| Overall Parity | Syndrome | Error Type | Action |
|----------------|----------|------------|---------|
| Match | Zero | No Error | Pass data through |
| Mismatch | Non-zero | Single Error (Hamming) | Correct using syndrome |
| Mismatch | Zero | Single Error (SECDED) | No correction needed |
| Match | Non-zero | Double Error | Flag error, no correction |

### Key Functions

#### `bit_position(k)` Function

Tells you where data bit `k` ended up in the encoded stream:

```systemverilog
function automatic integer bit_position(input integer k);
    integer j, pos;
    begin
        pos = k + 1;  // Account for parity bit at position 0
        for (j = 0; j < ParityBits; j++) begin
            if (pos >= (2 ** j)) pos = pos + 1;  // Skip parity positions
        end
        bit_position = pos - 1;  // Convert to 0-based index
    end
endfunction
```

#### `get_covered_bits(parity_bit)` Function

Hands back a bitmask of every position a given parity bit covers:

```systemverilog
function automatic [TotalWidth-1:0] get_covered_bits(input integer parity_bit);
    integer j;
    begin
        get_covered_bits = 0;
        // FIXED: Exclude SECDED bit from Hamming parity calculations
        for (j = 0; j < TotalWidth - 1; j++) begin
            if (|(((j + 1) >> parity_bit) & 1)) 
                get_covered_bits[j] = 1'b1;
        end
    end
endfunction
```

### Syndrome Generation

```systemverilog
always_comb begin : create_syndrome_covered_bits
    if (enable) begin
        for (i = 0; i < ParityBits; i++) begin
            parity_pos = (2 ** i) - 1;  // Parity bit positions
            w_syndrome_in[i] = hamming_data[parity_pos];  // Stored parity
            w_syndrome[i] = 1'b0;

            w_covered_bits = get_covered_bits(i);
            for (bit_index = 0; bit_index < TotalWidth; bit_index++) begin
                // Calculate parity over covered bits (excluding parity bit itself)
                if (w_covered_bits[bit_index] && (bit_index != parity_pos))
                    w_syndrome[i] = w_syndrome[i] ^ hamming_data[bit_index];
            end

            // Compare with stored parity to get syndrome
            w_syndrome[i] = w_syndrome[i] ^ w_syndrome_in[i];
        end
    end
end
```

### Overall Parity Check

```systemverilog
always_comb begin : check_overall_parity
    w_overall_parity_in = hamming_data[TotalWidth-1];  // SECDED bit
    if (enable) begin
        w_overall_parity = ^hamming_data[TotalWidth-2:0];  // Calculated parity
    end else begin
        w_overall_parity = 'b0;
    end
end
```

### Control States

There's no fancy FSM here — just `enable` gating two logical states:

1. **IDLE**: `enable = 0` - No processing
2. **DECODE**: `enable = 1` - Active decoding and error correction

### Error Correction Logic

```systemverilog
always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
        r_data_with_parity <= 'b0;
        error_detected <= 'b0;
        double_error_detected <= 'b0;
    end else if (enable) begin
        r_data_with_parity <= hamming_data;  // Default assignment
        error_detected <= 'b0;
        double_error_detected <= 'b0;

        // SECDED error detection logic
        if (w_overall_parity != w_overall_parity_in) begin
            error_detected <= 1'b1;

            if (w_syndrome != {ParityBits{1'b0}}) begin
                // Single-bit error in Hamming data - correct it
                r_data_with_parity[w_syndrome_0_based] <= 
                    ~hamming_data[w_syndrome_0_based];
            end
            // Single-bit error in SECDED bit - no correction needed

        end else if (w_syndrome != {ParityBits{1'b0}}) begin
            // Double-bit error detected
            error_detected <= 1'b1;
            double_error_detected <= 1'b1;
        end
    end
end
```

### Data Extraction

```systemverilog
genvar j;
generate
    for (j = 0; j < WIDTH; j++) begin : gen_block
        assign data[j] = r_data_with_parity[bit_position(j)];
    end
endgenerate
```

That peels just the original data bits out of the corrected encoded word.

### Error Handling Details

Syndrome interpretation:
- **Syndrome = 0**: No error in the Hamming bits
- **Syndrome ≠ 0**: Points to the error bit position (1-based)
- **Zero-based Syndrome**: `w_syndrome_0_based = w_syndrome - 1`

The SECDED bit is what lets you tell apart:
- Single-bit errors (correctable)
- Double-bit errors (detectable, but you're out of luck on correction)
- No errors

The correction sequence:
1. Calculate the syndrome from the received parity bits
2. Check overall parity (the SECDED bit)
3. Single error detected? Flip the bit at the syndrome position
4. Double error detected? Flag it, but leave the data alone

### Error Correction Capabilities

- **Single Error Correction**: Automatically fixes single-bit errors
- **Double Error Detection**: Flags double-bit errors but can't correct them
- **Error Location**: The syndrome points right at the bad bit
- **SECDED Protection**: The extra parity bit buys you double-error detection

### Debug Support

Fair warning: the `DEBUG` parameter is a **no-op** today. The RTL's only nod to it is an empty `initial begin if (DEBUG != 0) begin ... end end` placeholder with no `$display` statements. Turn it on and you'll get exactly no output in the current implementation.

## Timing Characteristics
- **Latency**: One clock cycle for error correction
- **Throughput**: One word per clock cycle
- **Detection Rate**: 100% for single and double errors
- **Critical Path**: Syndrome calculation and error correction
- **Pipeline Stages**: Consider pipelining if you're pushing frequency
- **Area**: Scales with data width and parity requirements
- **Power**: Moderate — the combinational parity math costs you

## Usage Examples

### Basic Decoder

```systemverilog
dataint_ecc_hamming_decode_secded #(
    .WIDTH(8),
    .DEBUG(0)
) hamming_decoder (
    .clk(clk),
    .rst_n(rst_n),
    .enable(decode_enable),
    .hamming_data(encoded_input),
    .data(decoded_data),
    .error_detected(single_or_double_error),
    .double_error_detected(uncorrectable_error)
);
```

### Error Handling System

```systemverilog
always_ff @(posedge clk) begin
    if (error_detected) begin
        if (double_error_detected) begin
            // Log uncorrectable error
            error_log <= error_log + 1;
            // Request retransmission
            request_retransmit <= 1'b1;
        end else begin
            // Log corrected error
            corrected_errors <= corrected_errors + 1;
            // Continue with corrected data
        end
    end
end
```

## Design Notes

### Applications

- ECC memory systems
- Communication error correction
- Storage system integrity
- Real-time data processing
- Safety-critical systems
- Network protocol implementation

## Related Modules

- **`dataint_ecc_hamming_encode_secded`**: Corresponding encoder
- Used together for complete ECC system implementation

## Testing

`val/common/test_dataint_ecc_hamming_secded.py` covers this module. It builds an `ecc_secded_wrapper` instantiating the encoder and decoder together and drives injected single- and double-bit errors through the pair.

The test is named for the PAIR rather than the module, which is why an
earlier audit looking only for `val/**/test_dataint_ecc_hamming_decode_secded.py` reported it as
having no coverage. It does.

Treat any behaviour described on this page as unverified by simulation.

---

## Navigation

- **[← Back to rtl-common Index](index.md)**
- **[← Back to Main Documentation Index](../index.md)**
