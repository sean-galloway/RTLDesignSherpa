`timescale 1ns / 1ps

// Paramerized Reset Synchronizer
module reset_sync #(
    parameter int N = 3
) (
    // clocks and resets
    input  logic i_clk,
    input  logic i_rst_n,
    output logic o_sync_rst_n
);

    logic [N-1:0] r_sync_reg = {N{1'b0}};

    always @(posedge clk or negedge i_rst_n) begin
        if (i_rst_n) begin
            r_sync_reg <= {N{1'b0}};
        end else begin
            r_sync_reg <= {r_sync_reg[N-2:0], 1'b1};
        end
    end

    assign o_sync_rst_n = r_sync_reg[N-1];

endmodule : reset_sync
