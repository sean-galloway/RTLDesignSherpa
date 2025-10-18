`timescale 1ns / 1ps

//==============================================================================
// Module: grayj2bin
//==============================================================================
// Description:
//   Converts Johnson counter Gray code to binary representation. Johnson counters
//   produce a special form of Gray code where only one bit changes between states,
//   making them ideal for asynchronous clock domain crossing. This module decodes
//   the Johnson code back to standard binary for address generation.
//
//------------------------------------------------------------------------------
// Parameters:
//------------------------------------------------------------------------------
//   JCW:
//     Description: Johnson Counter Width (number of bits in Johnson code)
//     Type: int
//     Range: 2 to 128
//     Default: 10
//     Constraints: Typically equal to DEPTH for even-numbered FIFO depths
//
//   WIDTH:
//     Description: Binary output width in bits
//     Type: int
//     Range: 1 to 32
//     Default: 4
//     Constraints: Must be $clog2(JCW) + 1 to represent full count range
//
//   INSTANCE_NAME:
//     Description: Instance name for debug/waveform identification
//     Type: string
//     Default: ""
//     Constraints: String identifier (debugging only)
//
//   Derived Parameters (localparam - computed automatically):
//     N: Bit width for leading/trailing one position ($clog2(JCW))
//     PAD_WIDTH: Zero-padding width for output alignment
//
//------------------------------------------------------------------------------
// Notes:
//------------------------------------------------------------------------------
//   - Johnson counter creates 2*JCW unique states with JCW flip-flops
//   - Single bit transition property ensures CDC safety
//   - Decoding uses leading_one_trailing_one module for position detection
//   - MSB of binary output indicates wrap-around (second half of sequence)
//   - Used in fifo_async_div2 for pointer conversion
//
//------------------------------------------------------------------------------
// Related Modules:
//------------------------------------------------------------------------------
//   - counter_johnson.sv - Generates Johnson counter sequences
//   - leading_one_trailing_one.sv - Position detection helper
//   - fifo_async_div2.sv - Primary user of this converter
//
//------------------------------------------------------------------------------
// Test:
//------------------------------------------------------------------------------
//   Location: val/common/test_grayj2bin.py
//   Run: pytest val/common/test_grayj2bin.py -v
//
//==============================================================================
module grayj2bin #(
    parameter int    JCW = 10,
    parameter int    WIDTH = 4,
    parameter string INSTANCE_NAME = ""
) (
    input  logic              clk,
    input  logic              rst_n,
    input  logic  [JCW-1:0]   gray,
    output logic  [WIDTH-1:0] binary
);

    localparam int N = $clog2(JCW);
    localparam int PAD_WIDTH = (WIDTH > N+1) ? WIDTH-N-1 : 0;

    logic [N-1:0]     w_leading_one;
    logic [N-1:0]     w_trailing_one;
    logic [WIDTH-1:0] w_binary;
    logic             w_all_zeroes;
    logic             w_all_ones;
    logic             w_valid;

    // Leading/trailing detection
    leading_one_trailing_one #(
        .WIDTH(JCW),
        .INSTANCE_NAME(INSTANCE_NAME)
    ) u_leading_one_trailing_one (
        .data              (gray),
        .leadingone        (w_leading_one),
        .leadingone_vector (),
        .trailingone       (w_trailing_one),
        .trailingone_vector(),
        .all_zeroes        (w_all_zeroes),
        .all_ones          (w_all_ones),
        .valid             (w_valid)
    );

    // Restore original working logic
    always_comb begin
        if (w_all_zeroes || w_all_ones) begin
            w_binary = {WIDTH{1'b0}};
        end else if (gray[JCW-1]) begin
            // Second half: use leading one position directly
            w_binary = {{(WIDTH-N){1'b0}}, w_trailing_one};
        end else begin
            // First half: use trailing one + 1
            w_binary = {{(WIDTH-N){1'b0}}, (w_leading_one + 1'b1)};
        end
    end

    assign binary[WIDTH-1]   = gray[JCW-1];                 // MSB = wrap
    assign binary[WIDTH-2:0] = w_binary[WIDTH-2:0];         // Lower binary

endmodule : grayj2bin
