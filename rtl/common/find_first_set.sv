`timescale 1ns / 1ps

module find_first_set #(
    parameter int WIDTH         = 32,
    parameter     INSTANCE_NAME = "FFS"  // verilog_lint: waive explicit-parameter-storage-type
) (
    input  logic [      WIDTH-1:0] i_data,
    output logic [$clog2(WIDTH):0] ow_index
);

    localparam int N = $clog2(WIDTH) + 1;

    function automatic [N-1:0] find_set_index;
        input [WIDTH-1:0] input_data;
        logic found;
        begin
            find_set_index = {N{1'b0}};  // Default value if no bit is set
            found = 1'b0;
            for (int i = 0; i < WIDTH && !found; i++) begin
                if (input_data[i]) begin
                    find_set_index = i;
                    found = 1'b1;
                end
            end
        end
    endfunction

    always_comb begin
        ow_index = find_set_index(i_data);
        // $display("FFS: %s, %h, %t", INSTANCE_NAME, data, $time);
    end

endmodule : find_first_set
