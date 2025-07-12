`timescale 1ns / 1ps

// Paramerized Reset Synchronizer
module reset_sync #(
    parameter int N = 3
) (
    // clocks and resets
    input  logic clk,
    input  logic rst_n,
    output logic sync_rst_n
);

    logic [N-1:0] r_sync_reg = {N{1'b0}};

    always_ff @(posedge clk or negedge rst_n) begin
        if (rst_n) begin
            r_sync_reg <= {N{1'b0}};
        end else begin
            r_sync_reg <= {r_sync_reg[N-2:0], 1'b1};
        end
    end

    assign sync_rst_n = r_sync_reg[N-1];

endmodule : reset_sync
