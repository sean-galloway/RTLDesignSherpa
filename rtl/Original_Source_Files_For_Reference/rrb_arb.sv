// https://chipress.online/2019/06/23/round-robin-arbiter-the-wrong-design-and-the-right-design/
module rrb_arb
(
    input                   clk,
    input                   rst_n,

    input [2:0]             req,
    
    output logic [2:0]      grant
);

    logic [2:0] mask;
    logic [2:0] mask_req;
    logic [2:0] raw_grant;
    logic [2:0] mask_grant;
    
    // mask update logic
    always_ff @(posedge clk or negedge rst_n)
        if (~rst_n)
            mask <= 3'b111;
        else if (grant[0])
            mask <= 3'b110;
        else if (grant[1])
            mask <= 3'b100;
        else if (grant[2])
            mask <= 3'b000;
    
    // masked requests
    assign mask_req = req & mask;

    // grant for raw requests in case mask == 3'b000
    fixed_prio_arb u_arb_raw (.req(req), .grant(raw_grant));
    
    // grant for masked requests in case mask != 3'b000
    fixed_prio_arb u_arb_mask (.req(mask_req), .grant(mask_grant));

    // final grant
    assign grant = (mask_req == 3'b000) ? raw_grant : mask_grant;

endmodule: rrb_arb