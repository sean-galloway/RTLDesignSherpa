`timescale 1ns / 1ps

// I got this design from:
// https://chipress.online/2019/06/23/round-robin-arbiter-the-wrong-design-and-the-right-design/
// I've made a few tweaks and clean up items; I parameterized it.

module rrb_arb
#(  parameter CLIENTS = 8)
(
    input                     clk,
    input                     rst_n,
    input [CLIENTS-1:0]       req,
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

    // grant for raw requests in case mask == 3'b000
    fixed_prio_arb #(CLIENTS) u_arb_raw  (.req(req), .grant(raw_grant));
    
    // grant for masked requests in case mask != 3'b000
    fixed_prio_arb #(CLIENTS) u_arb_mask (.req(mask_req), .grant(mask_grant));

    // final grant
    assign grant = (mask_req == {CLIENTS{1'b0}}) ? raw_grant : mask_grant;

endmodule: rrb_arb