// `timescale 1ns / 1ps

// module find_last_set
// #(parameter      int WIDTH = 32, parameter INSTANCE_NAME="")
// (
//     input  logic [WIDTH-1:0]         data,
//     output logic [$clog2(WIDTH):0] index
// );

//     localparam int N = $clog2(WIDTH)+1;
    
//     logic found;

//     always_comb begin
//         index = {WIDTH{1'b0}}; // Default value if no bit is set
//         found = 1'b0;
//         $display("FLS: %s, %h, %t", INSTANCE_NAME, data, $time);
        
//         for (int i = WIDTH - 1; i >= 0; i--) begin
//             if (data[i] == 1'b1 && !found) begin
//                 index = i;
//                 found = 1'b1;
//             end
//         end
//     end    

// endmodule : find_last_set

`timescale 1ns / 1ps

module find_last_set
#(parameter      int WIDTH = 32, parameter INSTANCE_NAME="")
(
    input  logic [WIDTH-1:0]         i_data,
    output logic [$clog2(WIDTH):0]   ow_index
);

    localparam int N = $clog2(WIDTH)+1;

    function [$clog2(WIDTH):0] find_last_set_index;
        input [WIDTH-1:0] input_data;
        logic found;
        begin
            find_last_set_index = {$clog2(WIDTH)+1{1'b0}}; // Default value if no bit is set
            found = 1'b0;
            for (int i = WIDTH - 1; i >= 0 && !found; i--) begin
                if (input_data[i]) begin
                    find_last_set_index = i;
                    found = 1'b1;
                end
            end
        end
    endfunction

    always_comb begin
        ow_index = find_last_set_index(i_data);
        // $display("FLS: %s, %h, %t", INSTANCE_NAME, data, $time);
    end    

endmodule : find_last_set
