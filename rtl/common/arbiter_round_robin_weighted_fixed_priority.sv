`timescale 1ns / 1ps

module arbiter_round_robin_weighted_fixed_priority #(
    parameter int CLIENTS = 4
) (
    input        [CLIENTS-1:0] i_req,
    output logic [CLIENTS-1:0] ow_grant
);

    logic w_found;

    always_comb begin
        ow_grant = {CLIENTS{1'b0}};
        w_found  = 1'b0;
        for (int i = 0; i < CLIENTS; i++) begin
            if (i_req[i] && !w_found) begin
                ow_grant[i] = 1'b1;
                w_found = 1'b1;
            end
        end
    end

endmodule : arbiter_round_robin_weighted_fixed_priority
