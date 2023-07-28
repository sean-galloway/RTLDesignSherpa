// Parameterized CLA
module carry_lookahead_adder #(parameter N = 4) (
    input [N-1:0] a,
    input [N-1:0] b,
    input c_in,
    output [N-1:0] sum,
    output c_out
);

    wire [N-1:0] p, g;
    wire [N:0]   c;

    // Generate and propagate signals
    generate
        genvar i;
        for (i = 0; i < N; i++) begin
            assign g[i] = a[i] & b[i];
            assign p[i] = a[i] | b[i];
        end
    endgenerate

    // Calculate carry bits
    assign c[0] = c_in;
    generate
        for (i = 1; i <= N; i++) begin
            assign c[i] = g[i-1] | (p[i-1] & c[i-1]);
        end
    endgenerate

    // Calculate sum bits
    generate
        for (i = 0; i < N; i++) begin
            assign sum[i] = a[i] ^ b[i] ^ c[i];
        end
    endgenerate

    // assign carry-out
    assign c_out = c[N];

endmodule : carry_lookahead_adder