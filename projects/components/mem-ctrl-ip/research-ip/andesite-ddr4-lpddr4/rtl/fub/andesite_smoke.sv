// SPDX-License-Identifier: MIT
// Infra smoke module: proves the lint/filelist pipeline. Deleted in P4 cleanup.
module andesite_smoke (
    input  logic       clk,
    input  logic       rst_n,
    output logic [4:0] op_o
);
    import andesite_pkg::*;
    import mc_common_pkg::*;   // Vivado: pkg export of the family symbols is not honored; import explicitly

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n)
            op_o <= 5'h0;
        else
            op_o <= OP_ACT;
    end
endmodule
