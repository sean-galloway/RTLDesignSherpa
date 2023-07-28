`timescale 1ns / 1ps

// I got this design from:
// https://chipress.online/?s=fixed_prio_arb
// I've made a few tweaks and clean up items; I parameterized it.

module fixed_prio_arb #(parameter CLIENTS = 8)
(
    input        [CLIENTS-1:0]  req,
    output logic [CLIENTS-1:0]  grant
);

    logic found;

    always_comb begin
        grant = {CLIENTS{1'b0}};
        found = 1'b0;
        for (int i = 0; i < CLIENTS; i++) begin
            if (req[i] && !found) begin
                grant[i] = 1'b1;
                found = 1'b1;
            end
        end
    end

endmodule: fixed_prio_arb
