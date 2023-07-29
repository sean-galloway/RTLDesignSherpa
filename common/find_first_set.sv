`timescale 1ns / 1ps

module find_first_set
#(parameter      int WIDTH = 32)
(
    input  logic [WIDTH-1:0]         data,
    output logic [$clog2(WIDTH):0]   index
);

    localparam int N = $clog2(WIDTH)+1;

    function automatic logic [N-1:0] ffs(input logic [WIDTH-1:0] vector);
        logic [N-1:0] location;

        location = {{N{1'b1}}};

        for (int i = WIDTH; i >= 0; i--)
            if (vector[i] == 1'b1)
                location = i[N-1:0];

        return {location};
    endfunction

    assign index = ffs(data);

    // always_comb begin
    //     index = N-1; // Default value if no bit is set

    //     for (int i = WIDTH - 1; i >= 0; i--) begin
    //         if (data[i] == 1'b1) begin
    //             index = i;
    //         end
    //     end
    // end

endmodule : find_first_set