`timescale 1ns / 1ps

module count_leading_zeros #(
    parameter int WIDTH         = 32,
    parameter     INSTANCE_NAME = "CLZ"  // verilog_lint: waive explicit-parameter-storage-type
) (
    input  logic [      WIDTH-1:0] i_data,
    output logic [$clog2(WIDTH):0] ow_count_leading_zeros
);

    localparam int N = $clog2(WIDTH) + 1;

    function automatic [$clog2(WIDTH):0] count_leading_zeros_func;
        input [WIDTH-1:0] input_data;
        logic found;
        begin
            count_leading_zeros_func = 0;  // Initialize to zero
            found = 1'b0;
            for (int i = 0; i < WIDTH; i++) begin
                if (!input_data[i] && !found) begin
                    count_leading_zeros_func += 1;
                end else begin
                    found = 1'b1;  // Stop counting when the first '1' is found
                end
            end
        end
    endfunction


    always_comb begin
        ow_count_leading_zeros = count_leading_zeros_func(i_data);
        $display("CLZ: %h, %h, %t", i_data, ow_count_leading_zeros, $time);
    end

endmodule : count_leading_zeros
