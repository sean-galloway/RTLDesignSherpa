`timescale 1ns / 1ps

module math_multiplier_booths #(
    parameter N=16,
    parameter Nd2 = N/2
) (
    input  logic signed [N-1:0]   i_a,
    input  logic signed [N-1:0]   i_b,
    output logic signed [2*N-1:0] ow_product
);

    logic [2:0]     w_select[Nd2-1:0];
    logic [N:0]     w_MxS[Nd2-1:0];
    logic [2*N-1:0] w_shift_MxS[Nd2-1:0];

    logic [N:0]     inv_i_a;
    integer         i,j;

    assign inv_i_a = ~i_a + 1'b1;

    // Assuming that the parameters are declared as before
    logic [N:0]     w_encoded_result[Nd2-1:0];  // Outputs from Booth's encoders
    logic [2:0]     w_select[Nd2-1:0];
    integer         i,j;

    // Create the Booth Group Selects
    always_comb begin
        // Populate the 3-bit groups for Booth's encoding
        w_select[0] = {i_b[1],i_b[0],1'b0};
        for(i=1; i<Nd2; i=i+1)
            w_select[i] = {i_b[2*i+1],i_b[2*i],i_b[2*i-1]};
    end

    // Instantiate Nd2 Booth encoders
    genvar k;
    generate
        for (k=0; k<Nd2; k=k+1) begin : booth_encoder_gen
            math_multiplier_booth_radix_4_encoder #(.N(N)) booth_encoder_inst (
                .i_booth_group      (w_select[k]),
                .i_multiplier       (i_a),
                .i_neg_multiplier   (inv_i_a),
                .ow_booth_out       (w_encoded_result[k])
            );
        end
    endgenerate

    // Do the final shifting of the results
    always_comb begin
        // Shift the partial products
        for(i=0; i<Nd2; i=i+1) begin
            w_shift_MxS[i] = $signed(w_encoded_result[i]);  // Use the output from Booth's encoder
            for(j=0; j<i; j=j+1) begin
                w_shift_MxS[i] = {w_shift_MxS[i],2'b00}; 
            end
        end
    end

    // Use CLA's to get the final product
    math_adder_hierarchical #(.N(2*N), .C(Nd2))
    u_math_adder_hierarchical(
        .i_numbers (w_shift_MxS),
        .ow_sum    (ow_product)
    );

`ifdef DEBUG
    initial begin
        #1;  // Wait for 10 time units to let values settle.
        $display("------------------------");
        $display("----- Booths Debug -----");
        $display("N: %d", N);
        $display("Nd2: %d", Nd2);
        $display("i_a: %b", i_a);
        $display("i_b: %b", i_b);
        $display("prod: %b", ow_product);
        $display("------------------------");
    end
`endif
    // synopsys translate_off
    initial begin
        $dumpfile("dump.vcd");
        $dumpvars(0, math_multiplier_booths);
    end
    // synopsys translate_on

endmodule : math_multiplier_booths
