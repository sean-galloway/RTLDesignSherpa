`timescale 1ns / 1ps

// Fibonacci LFSR, parameteried
module shifter_lfsr_fibonacci #(
    parameter int WIDTH           = 8,   // Width of the LFSR
    parameter int TAP_INDEX_WIDTH = 12,
    parameter int TAP_COUNT       = 4    // Number of taps
) (
    input  logic                     i_clk,
    input  logic                     i_rst_n,
    input  logic                     i_enable,     // enable the lfsr
    input  logic                     i_seed_load,  // enable the seed for the lfsr
    input  logic [        WIDTH-1:0] i_seed_data,  // seed value
    input  logic [TAP_COUNT*TIW-1:0] i_taps,       // Concatenated tap positions
    output logic [        WIDTH-1:0] o_lfsr_out,   // LFSR output
    output logic                     ow_lfsr_done  // the lfsr has wrapped around to the seed
);

    localparam int TIW = TAP_INDEX_WIDTH;
    // Calculate feedback bit based on tap positions
    logic [WIDTH:0] w_taps;
    logic [WIDTH:0] r_lfsr;
    logic w_feedback;
    logic [TIW-1:0]   w_tap_positions [0:TAP_COUNT-1]; // verilog_lint: waive unpacked-dimensions-range-ordering

    ////////////////////////////////////////////////////////////////////////////
    // Split concatenated tap positions into separate groups for each tap
    integer i;
    always_comb begin
        for (i = 0; i < TAP_COUNT; i++) w_tap_positions[i] = i_taps[i*TIW+:TIW];
    end

    always_comb begin
        w_taps = 'b0;
        for (i = 0; i < TAP_COUNT; i++)
        if (w_tap_positions[i] > 0) w_taps[w_tap_positions[i]] = 1'b1;
    end

    ////////////////////////////////////////////////////////////////////////////
    // Calculate feedback by XORing tapped bits
    assign w_feedback   = ^(r_lfsr[WIDTH:1] & w_taps[WIDTH:1]);

    ////////////////////////////////////////////////////////////////////////////
    // observe when the lfsr has looped back
    assign ow_lfsr_done = (r_lfsr[WIDTH:1] == i_seed_data) ? 1'b1 : 1'b0;

    always_ff @(posedge i_clk or posedge i_rst_n) begin
        if (~i_rst_n) begin
            r_lfsr <= {WIDTH{1'b0}};  // initialization to all 0's
        end else begin
            if (i_enable) begin
                if (i_seed_load) r_lfsr <= i_seed_data;
                else begin
                    r_lfsr <= {r_lfsr[WIDTH-1:0], w_feedback};
                end
            end
        end
    end

    assign o_lfsr_out = r_lfsr;

endmodule : shifter_lfsr_fibonacci
