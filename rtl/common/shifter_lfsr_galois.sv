`timescale 1ns / 1ps

// Galois LFSR, parameteried
module shifter_lfsr_galois #(
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

    // Individual tap positions
    logic [TIW-1:0] w_tap_positions [0:TAP_COUNT-1]; // verilog_lint: waive unpacked-dimensions-range-ordering

    ////////////////////////////////////////////////////////////////////////////
    // Split concatenated tap positions into separate groups for each tap
    integer i;
    always_comb begin
        for (i = 0; i < TAP_COUNT; i++) w_tap_positions[i] = i_taps[i*TIW+:TIW];
    end

    // observe when the lfsr has looped back
    assign ow_lfsr_done = (o_lfsr_out[WIDTH:1] == i_seed_data) ? 1'b1 : 1'b0;

    integer j;
    always_ff @(posedge i_clk or negedge i_rst_n) begin
        if (!i_rst_n) begin
            // Reset LFSR to a non-zero value
            o_lfsr_out <= {WIDTH{1'b1}};  // initialization to all 1's
        end else if (i_enable) begin
            if (i_seed_load) o_lfsr_out <= i_seed_data;
            else begin
                // Update LFSR state
                o_lfsr_out <= {o_lfsr_out[WIDTH-2:0], o_lfsr_out[WIDTH-1]};
                for (j = 0; j < TAP_COUNT; j++) begin
                    // XOR with feedback bit if the tap is active
                    if (w_tap_positions[j] > 0) begin
                        o_lfsr_out[w_tap_positions[j]-1] <=
                                o_lfsr_out[WIDTH-1] ^ o_lfsr_out[w_tap_positions[j]-1];
                    end
                end
            end
        end
    end

    // Synopsys translate_off
    // Synopsys translate_on

endmodule : shifter_lfsr_galois
