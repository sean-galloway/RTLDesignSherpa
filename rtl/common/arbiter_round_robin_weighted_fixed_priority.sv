`timescale 1ns / 1ps

module arbiter_round_robin_weighted_fixed_priority #(
    parameter int CLIENTS = 4
) (
    input        [CLIENTS-1:0] req,
    output logic [CLIENTS-1:0] grant
);

    logic w_found;

    always_comb begin
        grant = {CLIENTS{1'b0}};
        w_found  = 1'b0;
        for (int i = 0; i < CLIENTS; i++) begin
            if (req[i] && !w_found) begin
                grant[i] = 1'b1;
                w_found = 1'b1;
            end
        end
    end

endmodule : arbiter_round_robin_weighted_fixed_priority
