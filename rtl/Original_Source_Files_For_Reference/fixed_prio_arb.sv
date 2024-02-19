// https://chipress.online/?s=fixed_prio_arb
module fixed_prio_arb
(
    input [2:0]         req,
    
    output logic [2:0]  grant
);

    always_comb begin
        case (1'b1)
            req[0]: grant = 3'b001;
            req[1]: grant = 3'b010;
            req[2]: grant = 3'b100;
            default:grant = 3'b000;
        endcase
    end

endmodule: fixed_prio_arb