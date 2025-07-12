`timescale 1ns / 1ps

// Fibonacci LFSR, parameteried
module shifter_lfsr_fibonacci #(
    parameter int WIDTH           = 8,   // Width of the LFSR
    parameter int TAP_INDEX_WIDTH = 12,
    parameter int TAP_COUNT       = 4,   // Number of taps
    parameter int TIW = TAP_INDEX_WIDTH
) (
    input  logic                     clk,
    input  logic                     rst_n,
    input  logic                     enable,     // enable the lfsr
    input  logic                     seed_load,  // enable the seed for the lfsr
    input  logic [        WIDTH-1:0] seed_data,  // seed value
    input  logic [TAP_COUNT*TIW-1:0] taps,       // Concatenated tap positions
    output logic [        WIDTH-1:0] lfsr_out,   // LFSR output
    output logic                     lfsr_done  // the lfsr has wrapped around to the seed
);
    // Calculate feedback bit based on tap positions
    logic [WIDTH-1:0] w_taps;
    logic [WIDTH-1:0] r_lfsr;
    logic w_feedback;
    logic [TIW-1:0]   w_tap_positions [0:TAP_COUNT-1]; // verilog_lint: waive unpacked-dimensions-range-ordering

    ////////////////////////////////////////////////////////////////////////////
    // Split concatenated tap positions into separate groups for each tap
    always_comb begin
        for (int i = 0; i < TAP_COUNT; i++) w_tap_positions[i] = taps[i*TIW+:TIW];
    end

    always_comb begin
        w_taps = 'b0;
        for (int i = 0; i < TAP_COUNT; i++)
            /* verilator lint_off WIDTHTRUNC */
            if (w_tap_positions[i] > 0) w_taps[w_tap_positions[i]-1'b1] = 1'b1;
            /* verilator lint_on WIDTHTRUNC */
    end

    ////////////////////////////////////////////////////////////////////////////
    // Calculate feedback by XORing tapped bits
    assign w_feedback = ^(r_lfsr & w_taps);

    ////////////////////////////////////////////////////////////////////////////
    // observe when the lfsr has looped back
    assign lfsr_done = (lfsr_out == seed_data) ? 1'b1 : 1'b0;

    // Output value immediately
    assign lfsr_out = r_lfsr;

    always_ff @(posedge clk or negedge rst_n) begin
        if (~rst_n) begin
            r_lfsr <= 'b0;  // initialization to all 0's
        end else begin
            if (enable) begin
                if (seed_load) begin
                    r_lfsr <= seed_data;  // Load seed
                end else if (|r_lfsr) begin // Only shift if we have non-zero value
                    // Fibonacci LFSR: Shift right, feedback to MSB
                    r_lfsr <= {w_feedback, r_lfsr[WIDTH-1:1]};
                end
            end
        end
    end

endmodule : shifter_lfsr_fibonacci
