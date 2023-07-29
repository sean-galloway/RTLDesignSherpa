`timescale 1ns / 1ps

module find_first_set
#(parameter      int WIDTH = 32)
(
    input  logic [WIDTH-1:0]         data,
    output logic [$clog2(WIDTH):0] first_set_index
);

    localparam int N = $clog2(WIDTH)+1;

    function automatic logic [N-1:0] ffs(input logic [WIDTH-1:0] vector);
        logic [N-1:0] location;

        location = {{N{1'b1}}};

        for (int i = 0; i < WIDTH; i++)
            if (vector[i] == 1'b1)
                location = i[N-1:0];

        return {location};
    endfunction

    assign first_set_index = ffs(data);

endmodule : find_first_set