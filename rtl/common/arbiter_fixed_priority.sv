`timescale 1ns / 1ps

// I got this design from:
// https://chipress.online/?s=fixed_prio_arb
// I've made a few tweaks and clean up items; I parameterized it.

module arbiter_fixed_priority #(
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

endmodule : arbiter_fixed_priority
