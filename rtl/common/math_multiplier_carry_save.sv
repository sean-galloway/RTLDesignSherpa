`timescale 1ns / 1ps

module math_multiplier_carry_save #(
    parameter N = 4
) (
    input  logic [  N-1:0] i_multiplier,
    input  logic [  N-1:0] i_multiplicand,
    output logic [2*N-1:0] ow_product
);
    logic [N:0]     w_cin  [0:N]; // verilog_lint: waive unpacked-dimensions-range-ordering
    logic [N:0]     w_pin  [0:N]; // verilog_lint: waive unpacked-dimensions-range-ordering
    logic [N:0]     w_cout [0:N]; // verilog_lint: waive unpacked-dimensions-range-ordering
    logic [N:0]     w_pout [0:N]; // verilog_lint: waive unpacked-dimensions-range-ordering
    logic [2*N-1:0] w_product;

    // Generate partial products
    genvar i, j;
    generate
        assign w_pin[0] = 'b0;
        assign w_cin[0] = 'b0;
        for (i = 0; i < N; i++) begin : gen_output
            for (j = 0; j < N; j++) begin : gen_inner
                math_multiplier_basic_cell basic_mul_cell (
                    .i_i  (i_multiplier[i]),
                    .i_j  (i_multiplicand[j]),
                    .i_c  (w_cin[i][j]),
                    .i_p  (w_pin[i][j]),
                    .ow_c (w_cout[i][j]),
                    .ow_p (w_pout[i][j])
                );
                assign w_cin[i+1][j] = w_cout[i][j];
                if (j == 0)
                    assign w_product[i] = w_pout[i][j];
                if (j > 0)
                    assign w_pin[i+1][j-1] = w_pout[i][j];
            end
            assign w_pin[i+1][N-1] = 0;
        end
    endgenerate

    // do the final addition
    assign ow_product[2*N-1:0] = {{w_pin[N][N-1:0] + w_cin[N][N-1:0]}, w_product[N-1:0]};

    // /////////////////////////////////////////////////////////////////////////
    // // error checking
    // // synopsys translate_off
    // // Generate a version of the memory for waveforms
    // logic [(N+1)*(N+1):0] flat_w_cin;
    // logic [(N+1)*(N+1):0] flat_w_pin;
    // logic [(N+1)*(N+1):0] flat_w_cout;
    // logic [(N+1)*(N+1):0] flat_w_pout;
    // genvar k;
    // generate
    //     for (k = 0; k <= N; k++) begin : gen_flatten_signals
    //         assign flat_w_cin[k*N+:N]  = w_cin[k];
    //         assign flat_w_pin[k*N+:N]  = w_pin[k];
    //         assign flat_w_cout[k*N+:N] = w_cout[k];
    //         assign flat_w_pout[k*N+:N] = w_pout[k];
    //     end
    // endgenerate

endmodule : math_multiplier_carry_save

