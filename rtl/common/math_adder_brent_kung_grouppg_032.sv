`timescale 1ns / 1ps

module math_adder_brent_kung_grouppg_032 #(
    parameter int N = 32
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
    logic G_17_16;
    logic P_17_16;
    logic G_19_18;
    logic P_19_18;
    logic G_21_20;
    logic P_21_20;
    logic G_23_22;
    logic P_23_22;
    logic G_25_24;
    logic P_25_24;
    logic G_27_26;
    logic P_27_26;
    logic G_29_28;
    logic P_29_28;
    logic G_31_30;
    logic P_31_30;
    logic G_7_4;
    logic P_7_4;
    logic G_11_8;
    logic P_11_8;
    logic G_15_12;
    logic P_15_12;
    logic G_19_16;
    logic P_19_16;
    logic G_23_20;
    logic P_23_20;
    logic G_27_24;
    logic P_27_24;
    logic G_31_28;
    logic P_31_28;
    logic G_15_8;
    logic P_15_8;
    logic G_23_16;
    logic P_23_16;
    logic G_31_24;
    logic P_31_24;
    logic G_31_16;
    logic P_31_16;
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
    math_adder_brent_kung_black black_block_17_16 (
        .i_g(i_g[17]),
        .i_p(i_p[17]),
        .i_g_km1(i_g[16]),
        .i_p_km1(i_p[16]),
        .ow_g(G_17_16),
        .ow_p(P_17_16)
    );
    math_adder_brent_kung_black black_block_19_18 (
        .i_g(i_g[19]),
        .i_p(i_p[19]),
        .i_g_km1(i_g[18]),
        .i_p_km1(i_p[18]),
        .ow_g(G_19_18),
        .ow_p(P_19_18)
    );
    math_adder_brent_kung_black black_block_21_20 (
        .i_g(i_g[21]),
        .i_p(i_p[21]),
        .i_g_km1(i_g[20]),
        .i_p_km1(i_p[20]),
        .ow_g(G_21_20),
        .ow_p(P_21_20)
    );
    math_adder_brent_kung_black black_block_23_22 (
        .i_g(i_g[23]),
        .i_p(i_p[23]),
        .i_g_km1(i_g[22]),
        .i_p_km1(i_p[22]),
        .ow_g(G_23_22),
        .ow_p(P_23_22)
    );
    math_adder_brent_kung_black black_block_25_24 (
        .i_g(i_g[25]),
        .i_p(i_p[25]),
        .i_g_km1(i_g[24]),
        .i_p_km1(i_p[24]),
        .ow_g(G_25_24),
        .ow_p(P_25_24)
    );
    math_adder_brent_kung_black black_block_27_26 (
        .i_g(i_g[27]),
        .i_p(i_p[27]),
        .i_g_km1(i_g[26]),
        .i_p_km1(i_p[26]),
        .ow_g(G_27_26),
        .ow_p(P_27_26)
    );
    math_adder_brent_kung_black black_block_29_28 (
        .i_g(i_g[29]),
        .i_p(i_p[29]),
        .i_g_km1(i_g[28]),
        .i_p_km1(i_p[28]),
        .ow_g(G_29_28),
        .ow_p(P_29_28)
    );
    math_adder_brent_kung_black black_block_31_30 (
        .i_g(i_g[31]),
        .i_p(i_p[31]),
        .i_g_km1(i_g[30]),
        .i_p_km1(i_p[30]),
        .ow_g(G_31_30),
        .ow_p(P_31_30)
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
    math_adder_brent_kung_black black_block_19_16 (
        .i_g(G_19_18),
        .i_p(P_19_18),
        .i_g_km1(G_17_16),
        .i_p_km1(P_17_16),
        .ow_g(G_19_16),
        .ow_p(P_19_16)
    );
    math_adder_brent_kung_black black_block_23_20 (
        .i_g(G_23_22),
        .i_p(P_23_22),
        .i_g_km1(G_21_20),
        .i_p_km1(P_21_20),
        .ow_g(G_23_20),
        .ow_p(P_23_20)
    );
    math_adder_brent_kung_black black_block_27_24 (
        .i_g(G_27_26),
        .i_p(P_27_26),
        .i_g_km1(G_25_24),
        .i_p_km1(P_25_24),
        .ow_g(G_27_24),
        .ow_p(P_27_24)
    );
    math_adder_brent_kung_black black_block_31_28 (
        .i_g(G_31_30),
        .i_p(P_31_30),
        .i_g_km1(G_29_28),
        .i_p_km1(P_29_28),
        .ow_g(G_31_28),
        .ow_p(P_31_28)
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
    math_adder_brent_kung_black black_block_23_16 (
        .i_g(G_23_20),
        .i_p(P_23_20),
        .i_g_km1(G_19_16),
        .i_p_km1(P_19_16),
        .ow_g(G_23_16),
        .ow_p(P_23_16)
    );
    math_adder_brent_kung_black black_block_31_24 (
        .i_g(G_31_28),
        .i_p(P_31_28),
        .i_g_km1(G_27_24),
        .i_p_km1(P_27_24),
        .ow_g(G_31_24),
        .ow_p(P_31_24)
    );
    math_adder_brent_kung_gray gray_block_15_0 (
        .i_g(G_15_8),
        .i_p(P_15_8),
        .i_g_km1(ow_gg[7]),
        .ow_g(ow_gg[15])
    );
    math_adder_brent_kung_black black_block_31_16 (
        .i_g(G_31_24),
        .i_p(P_31_24),
        .i_g_km1(G_23_16),
        .i_p_km1(P_23_16),
        .ow_g(G_31_16),
        .ow_p(P_31_16)
    );
    math_adder_brent_kung_gray gray_block_31_0 (
        .i_g(G_31_16),
        .i_p(P_31_16),
        .i_g_km1(ow_gg[15]),
        .ow_g(ow_gg[31])
    );
    math_adder_brent_kung_gray gray_block_23_15 (
        .i_g(G_23_16),
        .i_p(P_23_16),
        .i_g_km1(ow_gg[15]),
        .ow_g(ow_gg[23])
    );
    math_adder_brent_kung_gray gray_block_11_7 (
        .i_g(G_11_8),
        .i_p(P_11_8),
        .i_g_km1(ow_gg[7]),
        .ow_g(ow_gg[11])
    );
    math_adder_brent_kung_gray gray_block_19_15 (
        .i_g(G_19_16),
        .i_p(P_19_16),
        .i_g_km1(ow_gg[15]),
        .ow_g(ow_gg[19])
    );
    math_adder_brent_kung_gray gray_block_27_23 (
        .i_g(G_27_24),
        .i_p(P_27_24),
        .i_g_km1(ow_gg[23]),
        .ow_g(ow_gg[27])
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
    math_adder_brent_kung_gray gray_block_17_15 (
        .i_g(G_17_16),
        .i_p(P_17_16),
        .i_g_km1(ow_gg[15]),
        .ow_g(ow_gg[17])
    );
    math_adder_brent_kung_gray gray_block_21_19 (
        .i_g(G_21_20),
        .i_p(P_21_20),
        .i_g_km1(ow_gg[19]),
        .ow_g(ow_gg[21])
    );
    math_adder_brent_kung_gray gray_block_25_23 (
        .i_g(G_25_24),
        .i_p(P_25_24),
        .i_g_km1(ow_gg[23]),
        .ow_g(ow_gg[25])
    );
    math_adder_brent_kung_gray gray_block_29_27 (
        .i_g(G_29_28),
        .i_p(P_29_28),
        .i_g_km1(ow_gg[27]),
        .ow_g(ow_gg[29])
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
    math_adder_brent_kung_gray gray_block_18_17 (
        .i_g(i_g[18]),
        .i_p(i_p[18]),
        .i_g_km1(ow_gg[17]),
        .ow_g(ow_gg[18])
    );
    math_adder_brent_kung_gray gray_block_20_19 (
        .i_g(i_g[20]),
        .i_p(i_p[20]),
        .i_g_km1(ow_gg[19]),
        .ow_g(ow_gg[20])
    );
    math_adder_brent_kung_gray gray_block_22_21 (
        .i_g(i_g[22]),
        .i_p(i_p[22]),
        .i_g_km1(ow_gg[21]),
        .ow_g(ow_gg[22])
    );
    math_adder_brent_kung_gray gray_block_24_23 (
        .i_g(i_g[24]),
        .i_p(i_p[24]),
        .i_g_km1(ow_gg[23]),
        .ow_g(ow_gg[24])
    );
    math_adder_brent_kung_gray gray_block_26_25 (
        .i_g(i_g[26]),
        .i_p(i_p[26]),
        .i_g_km1(ow_gg[25]),
        .ow_g(ow_gg[26])
    );
    math_adder_brent_kung_gray gray_block_28_27 (
        .i_g(i_g[28]),
        .i_p(i_p[28]),
        .i_g_km1(ow_gg[27]),
        .ow_g(ow_gg[28])
    );
    math_adder_brent_kung_gray gray_block_30_29 (
        .i_g(i_g[30]),
        .i_p(i_p[30]),
        .i_g_km1(ow_gg[29]),
        .ow_g(ow_gg[30])
    );
    math_adder_brent_kung_gray gray_block_32_31 (
        .i_g(i_g[32]),
        .i_p(i_p[32]),
        .i_g_km1(ow_gg[31]),
        .ow_g(ow_gg[32])
    );
    assign ow_gg[0] = i_g[0];
    assign ow_pp[0] = i_p[0];
endmodule
