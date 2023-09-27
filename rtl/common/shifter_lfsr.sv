`timescale 1ns / 1ps

module shifter_lfsr #(
    parameter int N = 5  // LFSR width
) (
    input wire i_clk,
    i_rst_n,
    input wire i_enable,
    input wire i_seed_load,
    input wire [N-1:0] i_seed_data,
    input wire [N-1:0] i_taps,  // Taps to XNor; see the attached pdf for the proper taps to use
    output reg [N-1:0] o_lfsr_data,
    output reg ow_lfsr_done
);

    reg [N-1:0] r_lfsr_reg;
    reg         r_xnor_out;

    always_ff @(posedge i_clk or negedge i_rst_n) begin
        if (!i_rst_n) begin
            r_lfsr_reg <= 0;
        end else begin
            if (i_enable) begin
                if (i_seed_load) begin
                    r_lfsr_reg <= seed_data;
                end else begin
                    r_lfsr_reg <= {r_lfsr_reg[N-2:0], r_xnor_out};
                end
            end
        end
    end

    always_ff @(posedge i_clk or negedge i_rst_n) begin
        if (!i_rst_n) r_xnor_out <= 'b0;
        else r_xnor_out <= ~^(r_lfsr_reg & i_taps);
    end

    assign o_lfsr_data  = r_lfsr_reg;
    assign ow_lfsr_done = (lfsr_reg[N:1] == seed_data) ? 1'b1 : 1'b0;

endmodule : shifter_lfsr
