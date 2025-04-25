`timescale 1ns / 1ps

// Galois LFSR, parameterized with right shift to match Fibonacci LFSR style
module shifter_lfsr_galois #(
    parameter int WIDTH = 8,           // Width of the LFSR
    parameter int TAP_INDEX_WIDTH = 12,
    parameter int TAP_COUNT = 4,        // Number of taps
    parameter int TIW = TAP_INDEX_WIDTH
) (
    input  logic                     i_clk,
    input  logic                     i_rst_n,
    input  logic                     i_enable,     // enable the lfsr
    input  logic                     i_seed_load,  // enable the seed for the lfsr
    input  logic [     WIDTH-1:0]    i_seed_data,  // seed value
    input  logic [TAP_COUNT*TIW-1:0] i_taps,       // Concatenated tap positions
    output logic [     WIDTH-1:0]    o_lfsr_out,   // LFSR output
    output logic                     ow_lfsr_done  // the lfsr has wrapped around to the seed
);

    logic [WIDTH-1:0]  r_lfsr;
    logic [TIW-1:0]    w_tap_positions [0:TAP_COUNT-1];  // verilog_lint: waive unpacked-dimensions-range-ordering
    logic              w_feedback;
    logic [WIDTH-1:0]  next_lfsr;

    ////////////////////////////////////////////////////////////////////////////
    // Split concatenated tap positions into separate groups for each tap
    always_comb begin
        for (int i = 0; i < TAP_COUNT; i++) begin
            w_tap_positions[i] = i_taps[i*TIW+:TIW];
        end
    end

    // Observe when the lfsr has looped back
    assign ow_lfsr_done = (o_lfsr_out == i_seed_data) ? 1'b1 : 1'b0;

    // Get the LSB for feedback
    assign w_feedback = r_lfsr[0];

    // Calculate next LFSR state with proper Galois feedback
    always_comb begin
        // Start with right shift (include 0 in MSB)
        next_lfsr = {1'b0, r_lfsr[WIDTH-1:1]};

        // Apply Galois feedback taps if LSB is 1
        if (w_feedback) begin
            for (int j = 0; j < TAP_COUNT; j++) begin
                /* verilator lint_off WIDTHEXPAND */
                if (w_tap_positions[j] > 0 && w_tap_positions[j] <= WIDTH) begin
                    // Apply XOR to the tap positions
                    next_lfsr[w_tap_positions[j]-1] = next_lfsr[w_tap_positions[j]-1] ^ 1'b1;
                /* verilator lint_on WIDTHEXPAND */
                end
            end
        end
    end

    // Update LFSR state
    always_ff @(posedge i_clk or negedge i_rst_n) begin
        if (~i_rst_n) begin
            // Reset LFSR to a non-zero value
            r_lfsr <= {WIDTH{1'b1}};  // initialization to all 1's
        end else if (i_enable) begin
            if (i_seed_load) begin
                r_lfsr <= i_seed_data;
            end else begin
                // Update with the next state calculated in combinational logic
                r_lfsr <= next_lfsr;
            end
        end
    end

    assign o_lfsr_out = r_lfsr[WIDTH-1:0];

endmodule : shifter_lfsr_galois
