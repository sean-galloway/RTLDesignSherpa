`timescale 1ns / 1ps

module find_first_set
#(parameter int WIDTH = 32)
(
    input  logic [WIDTH-1:0]         data,
    output logic [$clog2(WIDTH)-1:0] first_set_index
);

    function automatic logic [$clog2(WIDTH)-1:0] ffs(input logic [WIDTH-1:0] vector);
        logic [$clog2(WIDTH)-1:0] location;

        location = '{>>{$clog2(WIDTH){1}}};

        for (int i = 0; i < CLIENTS; i++)
            if (vector[i] == 1'b1)
                location = i[15:0];

        return {location};
    endfunction

    first_set_index = ffs(data);

endmodule : find_first_set