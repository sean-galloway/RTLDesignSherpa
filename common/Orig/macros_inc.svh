`ifndef COMMON_MACROS
`define COMMON_MACROS
    // D flip-flop w/ async reset_n
    `define DFF_ARN(q, d, clk, rst_n)             \
    always_ff @(posedge clk, negedge rst_n) begin \
        if (!rst_n) q <= '0;                      \
        else        q <= d;                       \
    end

    // D flip-flop w/ async reset_n, specify reset
    `define DFF_ARN_RSTVAL(q, en, d, clk, rst_n, RSTVAL)   \
    always_ff @(posedge clk, negedge rst_n) begin          \
        if (!rst_n)  q <= RSTVAL;                          \
        else         q <= d;                               \
    end

    // Double D flip-flop w/ async reset_n
    `define GLITCHFRE_FF_ARN(qq, d, clk, rst_n)   \
    always_ff @(posedge clk, negedge rst_n) begin \
        if (!rst_n) begin                         \
            q <= '0;                              \
            qq <= '0;                             \
        end                                       \
        else begin                                \
            q <= d;                               \
            qq <= q;                              \
        end                                       \
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
`endif

