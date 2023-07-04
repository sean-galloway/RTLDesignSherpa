`ifndef COMMON_MACROS
`define COMMON_MACROS

    // Glitch Free Flop with the number of flops as a parameter,
    // it uses FLOP_COUNT number of flops in the chain
    // instance sample:
    // `GLITCH_FREE_N_DFF_ARN( , , , ,N)
    `define GLITCH_FREE_N_DFF_ARN #(parameter WIDTH=1)           \
    module flop(q[WIDTH-1:0], d[WIDTH-1:0], clk, rst_n, FLOP_COUNT)\
    parameter FLOP_COUNT = FLOP_COUNT;                           \
    reg [FLOP_COUNT-1:0] flop_out_reg;                           \
    always @(posedge clk or negedge rst_n) begin              \
        if (!rst_n)                                              \
            flop_out_reg[0] <= 1'b0;                             \
        else                                                     \
            flop_out_reg[0] <= d;                                \
    end                                                          \
    generate                                                     \
        genvar i;                                                \
        for (i = 1; i < FLOP_COUNT; i = i + 1) begin : FLOP_LOOP \
            always @(posedge clk or negedge rst_n) begin      \
                if (!rst_n)                                      \
                    flop_out_reg[i] <= 1'b0;                     \
                else                                             \
                    flop_out_reg[i] <= flop_out_reg[i-1];        \
            end                                                  \
        end                                                      \
    endgenerate                                                  \
    always_comb begin                                            \
        assign q = flop_out_reg[FLOP_COUNT-1];                   \
    end                                                          \
    endmodule


    // D flip-flop w/ async reset_n
    // instance sample:
    // `DFF_ARN( , , , )
    `define DFF_ARN #(parameter WIDTH=1)          \
    module (q[WIDTH-1:0], d[WIDTH-1:0], clk, rst_n)             \
    always_ff @(posedge clk, negedge rst_n) begin \
        if (!rst_n) q <= '0;                      \
        else        q <= d;                       \
    end                                           \
    endmodule

    // D flip-flop w/ async reset_n, specify reset
    `define DFF_ARN_RSTVAL(q, en, d, clk, rst_n, RSTVAL)   \
    always_ff @(posedge clk, negedge rst_n) begin          \
        if (!rst_n)  q <= RSTVAL;                          \
        else         q <= d;                               \
    end

    // Enable D flip-flop w/ async reset_n
    `define EN_DFF_ARN(q, en, d, clk, rst_n)       \
    always_ff @(posedge clk, negedge rst_n) begin  \
        if (!rst_n)  q <= '0;                      \
        else if (en) q <= d;                       \
        else         q <= q;                       \
    end

    // Enable D flip-flop w/ async reset_n, specify reset
    `define EN_DFF_ARN_RSTVAL(q, en, d, clk, rst_n, RSTVAL)   \
    always_ff @(posedge clk, negedge rst_n) begin             \
        if (!rst_n)  q <= RSTVAL;                             \
        else if (en) q <= d;                                  \
        else         q <= q;                                  \
    end

    // zero vector
    `define VEC0(SIZE) {(SIZE) {1'B0}}

    // one's vector
    `define VEC1(SIZE) {(SIZE) {1'B1}}

    // Load and Clear Counter
    `define LD_CLR_COUNTER(count, load, clear, increment, clk, rst_n, SIZE, max, loadval) \
    always_ff @(posedge clk, negedge rst_n) begin                                         \
        if (!rst_n) count <= {SIZE{1'b0}};                                                \
        else if (clear) count <= {SIZE{1'b0}};                                            \
        else if (load)  count <= loadval;                                                 \
        else if (increment) begin                                                         \
            count <= (count == max) ? {SIZE{1'b0}} :                                      \
                                        count + {{(SIZE-1){1'b0}, 1'b1}};                 \
        end                                                                               \
    end

    // Reverse Vector
    `define REVERSE_VECTORD(in, out)                               \
    always_comb begin                                              \
        for (integer i=0; i<$bits(in); i++) begin                  \
            out[($bits(in)-1)-i] = in[i];                          \
        end                                                        \
    end

    // Priority Encoders
    `define PRIORITY_ENCODER(pri_in, vld_in, dis_out, pri_out)                  \
    always_comb begin                                                           \
        dis_out[$bits(vld_in)-1:0] = '0;                                        \
        pri_out[$bits(vld_in)-1:0] = '0;                                        \
        dis_out[pri_in[0]] = 1'b0;                                              \
        pri_out[pri_in[0]] = vld_in[pri_in[0]];                                 \
                                                                                \
        for (integer i=1; i<$bits(vld_in); i++) begin                           \
            dis_out[pri_in[i]] = dis_out[pri_in[i-1]] | pri_out[pri_in[i-1]];   \
            pri_out[pri_in[j]] = vld_in[pri_in[j]] & ~dis_out[pri_in[j]];       \
        end                                                                     \
    end

    // Priority Encoder with Enable
    `define PRIORITY_ENCODER_ENABLE(pri_in, enable, pri_out)                   \
    always_comb begin                                                          \
        pri_out = 'bx;                                                         \
        for (integer i=0; i<$bits(pri_in); i=i+1) begin                        \
            if (pri_in[i] && enable[i]) begin                                  \
                pri_out = i;                                                   \
                break;                                                         \
            end                                                                \
        end                                                                    \
    end
`endif

