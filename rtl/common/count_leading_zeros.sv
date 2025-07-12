`timescale 1ns / 1ps

module count_leading_zeros #(
    parameter int WIDTH         = 32,
    parameter     INSTANCE_NAME = "CLZ"  // verilog_lint: waive explicit-parameter-storage-type
) (
    input  logic [      WIDTH-1:0] data,
    output logic [$clog2(WIDTH):0] clz
);

    localparam int N = $clog2(WIDTH) + 1;

    function automatic [$clog2(WIDTH):0] clz_func;
        input [WIDTH-1:0] input_data;
        logic found;
        begin
            clz_func = 0;  // Initialize to zero
            found = 1'b0;
            for (int i = 0; i < WIDTH; i++) begin
                if (!input_data[i] && !found) begin
                    clz_func += 1;
                end else begin
                    found = 1'b1;  // Stop counting when the first '1' is found
                end
            end
        end
    endfunction


    always_comb begin
        clz = clz_func(data);
        $display("CLZ: %h, %h, %t", data, clz, $time);
    end

endmodule : count_leading_zeros
