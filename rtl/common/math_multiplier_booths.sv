`timescale 1ns / 1ps

module math_multiplier_booths #(
    parameter int N   = 16,
    parameter int Nd2 = N / 2
) (
    input  logic signed [  N-1:0] i_multiplier,
    input  logic signed [  N-1:0] i_multiplicand,
    output logic signed [2*N-1:0] ow_product
);

    logic [2:0] w_select[0:Nd2-1];  // verilog_lint: waive unpacked-dimensions-range-ordering
    logic [N:0] w_MxS[0:Nd2-1];  // verilog_lint: waive unpacked-dimensions-range-ordering
    logic [2*N-1:0] w_shift_MxS[0:Nd2-1];  // verilog_lint: waive unpacked-dimensions-range-ordering

    logic [N:0] inv_i_multiplier;
    integer i, j;

    assign inv_i_multiplier = ~i_multiplier + 1'b1;

    always_comb begin
        w_select[0] = {i_multiplicand[1], i_multiplicand[0], 1'b0};

        for (i = 1; i < Nd2; i = i + 1)
        w_select[i] = {i_multiplicand[2*i+1], i_multiplicand[2*i], i_multiplicand[2*i-1]};

        for (i = 0; i < Nd2; i = i + 1) begin
            case (w_select[i])
                3'b001, 3'b010: w_MxS[i] = {i_multiplier[N-1], i_multiplier};
                3'b011:         w_MxS[i] = {i_multiplier, 1'b0};
                3'b100:         w_MxS[i] = {inv_i_multiplier[N-1:0], 1'b0};
                3'b101, 3'b110: w_MxS[i] = inv_i_multiplier;
                default:        w_MxS[i] = 0;
            endcase
            w_shift_MxS[i] = w_MxS[i];

            for (j = 0; j < i; j = j + 1) begin
                w_shift_MxS[i] = {w_shift_MxS[i], 2'b00};
            end
        end
    end

    // Use CLA's to get the final product
    math_adder_hierarchical #(
        .N(2 * N),
        .C(Nd2)
    ) u_math_adder_hierarchical (
        .i_numbers(w_shift_MxS),
        .ow_sum   (ow_product)
    );

    // synopsys translate_off
    initial begin
        $dumpfile("waves.vcd");
        $dumpvars(0, math_multiplier_booths);
    end
    // synopsys translate_on

endmodule : math_multiplier_booths
