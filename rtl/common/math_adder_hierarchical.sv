`timescale 1ns / 1ps

// Makes a tree of CLA's, C (the count of numbers) is padded to the next power of 2 with 0's
module math_adder_hierarchical #(
    parameter int N = 16,
    parameter int C = 10
) (
    input logic [N-1:0] i_numbers [0:C-1],  // verilog_lint: waive unpacked-dimensions-range-ordering
    output logic [N-1:0] ow_sum
);

    localparam int CPadded = 2 ** $clog2(C);
    localparam int Stages = $clog2(CPadded);

    logic [N-1:0] w_intermediate_sums [0:Stages+1][0:CPadded]; // verilog_lint: waive unpacked-dimensions-range-ordering
    logic w_c[0:Stages+1][0:CPadded];  // verilog_lint: waive unpacked-dimensions-range-ordering

    genvar i, stage;

    ////////////////////////////////////////////////////////////////////////////
    // Initialize first stage with input numbers, and pad with zeros if necessary
    generate
        for (genvar k = 0; k < CPadded; k++) begin : gen_loop
            assign w_intermediate_sums[0][k] = (k < C) ? i_numbers[k] : '0;
            assign w_c[0][k] = 1'b0;
        end
    endgenerate

    ////////////////////////////////////////////////////////////////////////////
    // Stages of addition
    generate
        for (stage = 0; stage < Stages; stage = stage + 1) begin : gen_cla_outer
            for (i = 0; i < CPadded >> stage; i = i + 2) begin : gen_cla_inner
                math_adder_carry_lookahead #(N) adder_inst (
                    .i_a(w_intermediate_sums[stage][i]),
                    .i_b(w_intermediate_sums[stage][i+1]),
                    .i_c((stage == 0) ? 1'b0 : (i == 0) ? 1'b0 : w_c[stage][i]),
                    .ow_sum(w_intermediate_sums[stage+1][i/2]),
                    .ow_carry(w_c[stage+1][i/2])
                );
            end
        end
    endgenerate

    assign ow_sum = w_intermediate_sums[Stages][0];

    // synopsys translate_off
`ifdef DEBUG
    // Debug signals
    logic [(N*C)-1:0] flat_i_numbers;
    for (i = 0; i < C; i++) begin : gen_flat_numbers
        assign flat_i_numbers[i*N+:N] = i_numbers[i];
    end

    logic [(N*(Stages+1)*CPadded)-1:0] flat_intermediate_sums;
    for (stage = 0; stage < Stages; stage = stage + 1) begin : gen_flat_sums_outer
        for (i = 0; i < CPadded; i++) begin : gen_flat_sums
            assign flat_intermediate_sums[(stage*CPadded+i)*N+:N] = w_intermediate_sums[stage][i];
        end
    end

    logic [((Stages+1)*CPadded)-1:0] flat_w_c;
    for (stage = 0; stage < Stages; stage = stage + 1) begin : gen_flat_carry_outer
        for (i = 0; i < CPadded; i++) begin : gen_flat_carry
            assign flat_w_c[(stage*CPadded)+i] = w_c[stage][i];
        end
    end
    // VCD dumping for simulation
`endif
    // synopsys translate_on


endmodule : math_adder_hierarchical
