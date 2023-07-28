`timescale 1ns / 1ps

module leading_one_trailing_one #(parameter N=8) (
    input  logic [N-1:0]       data,
    output logic [$clog2(N):0] leadingone,
    output logic [N-1:0]       leadingone_vector,
    output logic [$clog2(N):0] trailingone,
    output logic [N-1:0]       trailingone_vector,
    output logic               all_zeroes,
    output logic               valid
);

    function integer ffs(input logic [N-1:0] value);
        for (int i = 0; i < N; i++) begin
            if (value[i] == 1'b1)
                return i + 1; // Add 1 to get a 1-based index
        end
        return 0; // Return 0 if no set bit is found
    endfunction

    function integer clz(input logic [N-1:0] value);
        for (int i = N-1; i >= 0; i--) begin
            if (value[i] == 1'b1)
                return i;
        end
        return N; // Return N if all bits are zeros
    endfunction

    always_comb begin
        if (data === 0) begin
            leadingone = $clog2(N);
            trailingone = $clog2(N);
            all_zeroes = 1;
        end
        else begin
            leadingone = $clog2(N) - clz(data);     // TODO: replace with $clz when it is supported
            trailingone = ffs(data);                // TODO: replace with $ffs when it is supported
            all_zeroes = 0;
        end
    end

    always_comb begin
        leadingone_vector = '0;
        leadingone_vector[leadingone - 1] = 1'b1; // Subtract 1 to convert to 0-based index
        trailingone_vector = '0;
        trailingone_vector[trailingone - 1] = 1'b1; // Subtract 1 to convert to 0-based index
    end

    assign valid = !all_zeroes;

endmodule : leading_one_trailing_one

