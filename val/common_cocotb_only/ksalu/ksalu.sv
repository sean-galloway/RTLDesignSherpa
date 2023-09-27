`timescale 1ns / 1ps

module ksalu
#(
  parameter int DW = 8  // Width of input and output data
) (
    input  logic            clk, rst_n,
    input  logic [DW-1:0]   a, b,
    input  logic [3:0]      op,
    input  logic [1:0]      op2,    // only used for the universal shift register
    input  logic            start,
    output logic            done,
    output logic [DW*2-1:0] result,
    output logic [DW-1:0]   remainder
);

    // Local Flops and Signals
    logic            counting;
    logic            clear, increment;
    logic [3:0]      count, count_end, count_end_d;
    logic            counting, done;

    // handle all of the combi logical operations
    assign clear = start;
    assign increment = counting;
    assign single_start = op[3]== 1'b0;
    assign count_end_d =    (op[3:2]==2'b10) ? 4'b0100:
                            (op[3:2]==2'b11) ? 4'b0110:
                            (op==4'b0011)    ? 4'b1000: 4'b0001;
    assign done = (counting && (count == count_end));
    assign increment = counting;

    // Do the count handling
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            counting <= 'b0;
            count_end <= 'b0;
        end
        else
            if (start) begin
                counting <= 1'b1;
                count_end <= count_end_d;
            end
            else if (done) begin
                counting <= 'b0;
                count_end <= 'b0;
            end
        end

    // Main counter to delay the done signal
    load_clear_counter
    #(
        .MAX  (15)
    )
    u_load_clear_counter(
        .clk       (clk),
        .rst_n     (rst_n),
        .clear     (clear),
        .increment (increment),
        .load      (1'b0),
        .loadval   ('b0),
        .count     (count),
        .done      ()
    );

    ripple_carry_adder
    #(
        .SIZE (SIZE )
    )
    u_ripple_carry_adder(
        .a     (a     ),
        .b     (b     ),
        .c_in  (c_in  ),
        .sum   (sum   ),
        .c_out (c_out )
    );

endmodule
