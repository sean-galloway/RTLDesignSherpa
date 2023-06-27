// Parameterized CLa
module carry_lookahead_adder #(parameter N = 4) (
    input [N-1:0] a,
    input [N-1:0] b,
    input c_in,
    output [N-1:0] sum,
    output c_out
);

    wire [N-1:0] p, g;
    wire [N:0] c;

    // Generate and propagate signals
    genvar i;
    generate
        generate_propagate_loop: for (i = 0; i < N; i = i + 1) begin
            assign g[i] = a[i] & b[i];
            assign p[i] = a[i] | b[i];
        end
    endgenerate

    // Calculate carry bits
    assign c[0] = c_in;
    generate_carry_loop: for (i = 1; i <= N; i = i + 1) begin
        assign c[i] = g[i-1] | (p[i-1] & c[i-1]);
    end

    // Calculate sum bits
    generate_sum_loop: for (i = 0; i < N; i = i + 1) begin
        assign sum[i] = a[i] ^ b[i] ^ c[i];
    end

    // assign carry-out
    assign c_out = c[N];

endmodule