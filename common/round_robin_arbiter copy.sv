`timescale 1ns / 1ps

// Mostly based on code from this github:
// https://github.com/gsw73/ffs_arbiter/blob/master/design.sv
// I made a couple of tweaks myself to make it more efficient if only one agent is requesting
module round_robin_arbiter #(parameter CLIENTS=16)
(
    input                      clk,
    input                      rst_n,
    input [CLIENTS-1:0]        req,
    output logic [CLIENTS-1:0] grant
);

    logic [CLIENTS-1:0] mask;
    logic [CLIENTS-1:0] mask_req;
    logic [CLIENTS-1:0] raw_grant;
    logic [CLIENTS-1:0] mask_grant;
    
    // mask update logic
    always_ff @(posedge clk or negedge rst_n)
        begin
            if (~rst_n)
                mask <= {CLIENTS{1'b1}};
            else
            begin
                mask <= {CLIENTS{1'b0}};
                for (int i = 0; i < CLIENTS; i = i + 1)
                begin
                    if (grant[i])
                        mask[i] <= 1'b1;
                end
            end
        end
    
    // masked requests
    assign mask_req = req & mask;

    // grant for raw reqrequests in case mask == 3'b000
    fixed_prio_arb u_arb_raw (.req(req), .grant(raw_grant));
    
    // grant for masked requests in case mask != 3'b000
    fixed_prio_arb u_arb_mask (.req(mask_req), .grant(mask_grant));

    // final grant
    assign grant = (mask_req == {CLIENTS{1'b0}}) ? raw_grant : mask_grant;

endmodule: round_robin_arbiter