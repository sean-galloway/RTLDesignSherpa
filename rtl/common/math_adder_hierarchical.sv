`timescale 1ns / 1ps

// Makes a tree of CLA's, C (the count of numbers) is padded to the next power of 2 with 0's
module math_adder_hierarchical #(
    parameter N = 16,
    parameter C = 10
)(
    input  logic [N-1:0]           i_numbers[C-1:0],
    output logic [N+$clog2(C)-1:0] ow_sum
);

    localparam C_PADDED = 2**$clog2(C);
    localparam STAGES = $clog2(C_PADDED);

    logic [N-1:0] w_intermediate_sums[STAGES+1][C_PADDED];
    logic         w_c                [STAGES+1][C_PADDED];

    genvar i, stage;

    // Initialize first stage with input numbers, and pad with zeros if necessary
    generate
        for (genvar k = 0; k < C_PADDED; k=k+1) begin : gen_loop
            assign w_intermediate_sums[0][k] = (k < C) ? i_numbers[k] : '0;
            assign w_c[0][k] = 1'b0;
        end
    endgenerate

    // Stages of addition
    generate
        for(stage = 0; stage < STAGES; stage=stage+1) begin
            for(i = 0; i < C_PADDED >> stage; i=i+2) begin
                math_adder_carry_lookahead #(N) adder_inst (
                    .i_a(w_intermediate_sums[stage][i]),
                    .i_b(w_intermediate_sums[stage][i + 1]),
                    .i_c((stage == 0) ? 1'b0: (i == 0) ? 1'b0 : w_c[stage][i]),
                    .ow_sum(w_intermediate_sums[stage + 1][i/2]),
                    .ow_carry(w_c[stage+1][i/2])
                );
            end
        end
    endgenerate

    assign ow_sum = w_intermediate_sums[STAGES][0];

    // synopsys translate_off
`ifdef DEBUG
    // Debug signals
    logic [(N*C)-1:0] flat_i_numbers;
    for (i = 0; i < C; i = i+1) begin
        assign flat_i_numbers[i*N +: N] = i_numbers[i];
    end

    logic [(N*(STAGES+1)*C_PADDED)-1:0] flat_intermediate_sums;
    for (stage = 0; stage < STAGES; stage=stage+1) begin
        for (i = 0; i < C_PADDED; i=i+1) begin
            assign flat_intermediate_sums[(stage*C_PADDED + i)*N +: N] = w_intermediate_sums[stage][i];
        end
    end

    logic [((STAGES+1)*C_PADDED)-1:0] flat_w_c;
    for (stage = 0; stage < STAGES; stage=stage+1) begin
        for (i = 0; i < C_PADDED; i=i+1) begin
            assign flat_w_c[(stage*C_PADDED)+i] = w_c[stage][i];
        end
    end
    // VCD dumping for simulation
    initial begin
        $dumpfile("dump.vcd");
        $dumpvars(0, math_adder_hierarchical);
    end
`endif
    // synopsys translate_on


endmodule : math_adder_hierarchical