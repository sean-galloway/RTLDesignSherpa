`timescale 1ns / 1ps

module math_adder_brent_kung_grouppg_016 #(
    parameter int N = 16
) (
    input  logic [N:0] i_p,
    input  logic [N:0] i_g,
    output logic [N:0] ow_gg,
    output logic [N:0] ow_pp
);

    logic G_3_2;
    logic P_3_2;
    logic G_5_4;
    logic P_5_4;
    logic G_7_6;
    logic P_7_6;
    logic G_9_8;
    logic P_9_8;
    logic G_11_10;
    logic P_11_10;
    logic G_13_12;
    logic P_13_12;
    logic G_15_14;
    logic P_15_14;
    logic G_7_4;
    logic P_7_4;
    logic G_11_8;
    logic P_11_8;
    logic G_15_12;
    logic P_15_12;
    logic G_15_8;
    logic P_15_8;
    math_adder_brent_kung_gray gray_block_1_0 (
        .i_g(i_g[1]),
        .i_p(i_p[1]),
        .i_g_km1(i_g[0]),
        .ow_g(ow_gg[1])
    );
    math_adder_brent_kung_black black_block_3_2 (
        .i_g(i_g[3]),
        .i_p(i_p[3]),
        .i_g_km1(i_g[2]),
        .i_p_km1(i_p[2]),
        .ow_g(G_3_2),
        .ow_p(P_3_2)
    );
    math_adder_brent_kung_black black_block_5_4 (
        .i_g(i_g[5]),
        .i_p(i_p[5]),
        .i_g_km1(i_g[4]),
        .i_p_km1(i_p[4]),
        .ow_g(G_5_4),
        .ow_p(P_5_4)
    );
    math_adder_brent_kung_black black_block_7_6 (
        .i_g(i_g[7]),
        .i_p(i_p[7]),
        .i_g_km1(i_g[6]),
        .i_p_km1(i_p[6]),
        .ow_g(G_7_6),
        .ow_p(P_7_6)
    );
    math_adder_brent_kung_black black_block_9_8 (
        .i_g(i_g[9]),
        .i_p(i_p[9]),
        .i_g_km1(i_g[8]),
        .i_p_km1(i_p[8]),
        .ow_g(G_9_8),
        .ow_p(P_9_8)
    );
    math_adder_brent_kung_black black_block_11_10 (
        .i_g(i_g[11]),
        .i_p(i_p[11]),
        .i_g_km1(i_g[10]),
        .i_p_km1(i_p[10]),
        .ow_g(G_11_10),
        .ow_p(P_11_10)
    );
    math_adder_brent_kung_black black_block_13_12 (
        .i_g(i_g[13]),
        .i_p(i_p[13]),
        .i_g_km1(i_g[12]),
        .i_p_km1(i_p[12]),
        .ow_g(G_13_12),
        .ow_p(P_13_12)
    );
    math_adder_brent_kung_black black_block_15_14 (
        .i_g(i_g[15]),
        .i_p(i_p[15]),
        .i_g_km1(i_g[14]),
        .i_p_km1(i_p[14]),
        .ow_g(G_15_14),
        .ow_p(P_15_14)
    );
    math_adder_brent_kung_gray gray_block_3_0 (
        .i_g(G_3_2),
        .i_p(P_3_2),
        .i_g_km1(ow_gg[1]),
        .ow_g(ow_gg[3])
    );
    math_adder_brent_kung_black black_block_7_4 (
        .i_g(G_7_6),
        .i_p(P_7_6),
        .i_g_km1(G_5_4),
        .i_p_km1(P_5_4),
        .ow_g(G_7_4),
        .ow_p(P_7_4)
    );
    math_adder_brent_kung_black black_block_11_8 (
        .i_g(G_11_10),
        .i_p(P_11_10),
        .i_g_km1(G_9_8),
        .i_p_km1(P_9_8),
        .ow_g(G_11_8),
        .ow_p(P_11_8)
    );
    math_adder_brent_kung_black black_block_15_12 (
        .i_g(G_15_14),
        .i_p(P_15_14),
        .i_g_km1(G_13_12),
        .i_p_km1(P_13_12),
        .ow_g(G_15_12),
        .ow_p(P_15_12)
    );
    math_adder_brent_kung_gray gray_block_7_0 (
        .i_g(G_7_4),
        .i_p(P_7_4),
        .i_g_km1(ow_gg[3]),
        .ow_g(ow_gg[7])
    );
    math_adder_brent_kung_black black_block_15_8 (
        .i_g(G_15_12),
        .i_p(P_15_12),
        .i_g_km1(G_11_8),
        .i_p_km1(P_11_8),
        .ow_g(G_15_8),
        .ow_p(P_15_8)
    );
    math_adder_brent_kung_gray gray_block_15_0 (
        .i_g(G_15_8),
        .i_p(P_15_8),
        .i_g_km1(ow_gg[7]),
        .ow_g(ow_gg[15])
    );
    math_adder_brent_kung_gray gray_block_11_7 (
        .i_g(G_11_8),
        .i_p(P_11_8),
        .i_g_km1(ow_gg[7]),
        .ow_g(ow_gg[11])
    );
    math_adder_brent_kung_gray gray_block_5_3 (
        .i_g(G_5_4),
        .i_p(P_5_4),
        .i_g_km1(ow_gg[3]),
        .ow_g(ow_gg[5])
    );
    math_adder_brent_kung_gray gray_block_9_7 (
        .i_g(G_9_8),
        .i_p(P_9_8),
        .i_g_km1(ow_gg[7]),
        .ow_g(ow_gg[9])
    );
    math_adder_brent_kung_gray gray_block_13_11 (
        .i_g(G_13_12),
        .i_p(P_13_12),
        .i_g_km1(ow_gg[11]),
        .ow_g(ow_gg[13])
    );
    math_adder_brent_kung_gray gray_block_2_1 (
        .i_g(i_g[2]),
        .i_p(i_p[2]),
        .i_g_km1(ow_gg[1]),
        .ow_g(ow_gg[2])
    );
    math_adder_brent_kung_gray gray_block_4_3 (
        .i_g(i_g[4]),
        .i_p(i_p[4]),
        .i_g_km1(ow_gg[3]),
        .ow_g(ow_gg[4])
    );
    math_adder_brent_kung_gray gray_block_6_5 (
        .i_g(i_g[6]),
        .i_p(i_p[6]),
        .i_g_km1(ow_gg[5]),
        .ow_g(ow_gg[6])
    );
    math_adder_brent_kung_gray gray_block_8_7 (
        .i_g(i_g[8]),
        .i_p(i_p[8]),
        .i_g_km1(ow_gg[7]),
        .ow_g(ow_gg[8])
    );
    math_adder_brent_kung_gray gray_block_10_9 (
        .i_g(i_g[10]),
        .i_p(i_p[10]),
        .i_g_km1(ow_gg[9]),
        .ow_g(ow_gg[10])
    );
    math_adder_brent_kung_gray gray_block_12_11 (
        .i_g(i_g[12]),
        .i_p(i_p[12]),
        .i_g_km1(ow_gg[11]),
        .ow_g(ow_gg[12])
    );
    math_adder_brent_kung_gray gray_block_14_13 (
        .i_g(i_g[14]),
        .i_p(i_p[14]),
        .i_g_km1(ow_gg[13]),
        .ow_g(ow_gg[14])
    );
    math_adder_brent_kung_gray gray_block_16_15 (
        .i_g(i_g[16]),
        .i_p(i_p[16]),
        .i_g_km1(ow_gg[15]),
        .ow_g(ow_gg[16])
    );
    assign ow_gg[0] = i_g[0];
    assign ow_pp[0] = i_p[0];
endmodule
