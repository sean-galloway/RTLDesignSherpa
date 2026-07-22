// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: math_adder_brent_kung_grouppg_064
// Purpose: Math Adder Brent Kung Grouppg 064 module
//
// Documentation: rtl/common/PRD.md
// Subsystem: common
//
// Author: sean galloway
// Created: 2025-10-18

`timescale 1ns / 1ps

module math_adder_brent_kung_grouppg_064 #(
    parameter int N = 64
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
    logic G_33_32;
    logic P_33_32;
    logic G_35_34;
    logic P_35_34;
    logic G_37_36;
    logic P_37_36;
    logic G_39_38;
    logic P_39_38;
    logic G_41_40;
    logic P_41_40;
    logic G_43_42;
    logic P_43_42;
    logic G_45_44;
    logic P_45_44;
    logic G_47_46;
    logic P_47_46;
    logic G_49_48;
    logic P_49_48;
    logic G_51_50;
    logic P_51_50;
    logic G_53_52;
    logic P_53_52;
    logic G_55_54;
    logic P_55_54;
    logic G_57_56;
    logic P_57_56;
    logic G_59_58;
    logic P_59_58;
    logic G_61_60;
    logic P_61_60;
    logic G_63_62;
    logic P_63_62;
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
    logic G_35_32;
    logic P_35_32;
    logic G_39_36;
    logic P_39_36;
    logic G_43_40;
    logic P_43_40;
    logic G_47_44;
    logic P_47_44;
    logic G_51_48;
    logic P_51_48;
    logic G_55_52;
    logic P_55_52;
    logic G_59_56;
    logic P_59_56;
    logic G_63_60;
    logic P_63_60;
    logic G_15_8;
    logic P_15_8;
    logic G_23_16;
    logic P_23_16;
    logic G_31_24;
    logic P_31_24;
    logic G_39_32;
    logic P_39_32;
    logic G_47_40;
    logic P_47_40;
    logic G_55_48;
    logic P_55_48;
    logic G_63_56;
    logic P_63_56;
    logic G_31_16;
    logic P_31_16;
    logic G_47_32;
    logic P_47_32;
    logic G_63_48;
    logic P_63_48;
    logic G_63_32;
    logic P_63_32;
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
    math_adder_brent_kung_black black_block_33_32 (
        .i_g(i_g[33]),
        .i_p(i_p[33]),
        .i_g_km1(i_g[32]),
        .i_p_km1(i_p[32]),
        .ow_g(G_33_32),
        .ow_p(P_33_32)
    );
    math_adder_brent_kung_black black_block_35_34 (
        .i_g(i_g[35]),
        .i_p(i_p[35]),
        .i_g_km1(i_g[34]),
        .i_p_km1(i_p[34]),
        .ow_g(G_35_34),
        .ow_p(P_35_34)
    );
    math_adder_brent_kung_black black_block_37_36 (
        .i_g(i_g[37]),
        .i_p(i_p[37]),
        .i_g_km1(i_g[36]),
        .i_p_km1(i_p[36]),
        .ow_g(G_37_36),
        .ow_p(P_37_36)
    );
    math_adder_brent_kung_black black_block_39_38 (
        .i_g(i_g[39]),
        .i_p(i_p[39]),
        .i_g_km1(i_g[38]),
        .i_p_km1(i_p[38]),
        .ow_g(G_39_38),
        .ow_p(P_39_38)
    );
    math_adder_brent_kung_black black_block_41_40 (
        .i_g(i_g[41]),
        .i_p(i_p[41]),
        .i_g_km1(i_g[40]),
        .i_p_km1(i_p[40]),
        .ow_g(G_41_40),
        .ow_p(P_41_40)
    );
    math_adder_brent_kung_black black_block_43_42 (
        .i_g(i_g[43]),
        .i_p(i_p[43]),
        .i_g_km1(i_g[42]),
        .i_p_km1(i_p[42]),
        .ow_g(G_43_42),
        .ow_p(P_43_42)
    );
    math_adder_brent_kung_black black_block_45_44 (
        .i_g(i_g[45]),
        .i_p(i_p[45]),
        .i_g_km1(i_g[44]),
        .i_p_km1(i_p[44]),
        .ow_g(G_45_44),
        .ow_p(P_45_44)
    );
    math_adder_brent_kung_black black_block_47_46 (
        .i_g(i_g[47]),
        .i_p(i_p[47]),
        .i_g_km1(i_g[46]),
        .i_p_km1(i_p[46]),
        .ow_g(G_47_46),
        .ow_p(P_47_46)
    );
    math_adder_brent_kung_black black_block_49_48 (
        .i_g(i_g[49]),
        .i_p(i_p[49]),
        .i_g_km1(i_g[48]),
        .i_p_km1(i_p[48]),
        .ow_g(G_49_48),
        .ow_p(P_49_48)
    );
    math_adder_brent_kung_black black_block_51_50 (
        .i_g(i_g[51]),
        .i_p(i_p[51]),
        .i_g_km1(i_g[50]),
        .i_p_km1(i_p[50]),
        .ow_g(G_51_50),
        .ow_p(P_51_50)
    );
    math_adder_brent_kung_black black_block_53_52 (
        .i_g(i_g[53]),
        .i_p(i_p[53]),
        .i_g_km1(i_g[52]),
        .i_p_km1(i_p[52]),
        .ow_g(G_53_52),
        .ow_p(P_53_52)
    );
    math_adder_brent_kung_black black_block_55_54 (
        .i_g(i_g[55]),
        .i_p(i_p[55]),
        .i_g_km1(i_g[54]),
        .i_p_km1(i_p[54]),
        .ow_g(G_55_54),
        .ow_p(P_55_54)
    );
    math_adder_brent_kung_black black_block_57_56 (
        .i_g(i_g[57]),
        .i_p(i_p[57]),
        .i_g_km1(i_g[56]),
        .i_p_km1(i_p[56]),
        .ow_g(G_57_56),
        .ow_p(P_57_56)
    );
    math_adder_brent_kung_black black_block_59_58 (
        .i_g(i_g[59]),
        .i_p(i_p[59]),
        .i_g_km1(i_g[58]),
        .i_p_km1(i_p[58]),
        .ow_g(G_59_58),
        .ow_p(P_59_58)
    );
    math_adder_brent_kung_black black_block_61_60 (
        .i_g(i_g[61]),
        .i_p(i_p[61]),
        .i_g_km1(i_g[60]),
        .i_p_km1(i_p[60]),
        .ow_g(G_61_60),
        .ow_p(P_61_60)
    );
    math_adder_brent_kung_black black_block_63_62 (
        .i_g(i_g[63]),
        .i_p(i_p[63]),
        .i_g_km1(i_g[62]),
        .i_p_km1(i_p[62]),
        .ow_g(G_63_62),
        .ow_p(P_63_62)
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
    math_adder_brent_kung_black black_block_35_32 (
        .i_g(G_35_34),
        .i_p(P_35_34),
        .i_g_km1(G_33_32),
        .i_p_km1(P_33_32),
        .ow_g(G_35_32),
        .ow_p(P_35_32)
    );
    math_adder_brent_kung_black black_block_39_36 (
        .i_g(G_39_38),
        .i_p(P_39_38),
        .i_g_km1(G_37_36),
        .i_p_km1(P_37_36),
        .ow_g(G_39_36),
        .ow_p(P_39_36)
    );
    math_adder_brent_kung_black black_block_43_40 (
        .i_g(G_43_42),
        .i_p(P_43_42),
        .i_g_km1(G_41_40),
        .i_p_km1(P_41_40),
        .ow_g(G_43_40),
        .ow_p(P_43_40)
    );
    math_adder_brent_kung_black black_block_47_44 (
        .i_g(G_47_46),
        .i_p(P_47_46),
        .i_g_km1(G_45_44),
        .i_p_km1(P_45_44),
        .ow_g(G_47_44),
        .ow_p(P_47_44)
    );
    math_adder_brent_kung_black black_block_51_48 (
        .i_g(G_51_50),
        .i_p(P_51_50),
        .i_g_km1(G_49_48),
        .i_p_km1(P_49_48),
        .ow_g(G_51_48),
        .ow_p(P_51_48)
    );
    math_adder_brent_kung_black black_block_55_52 (
        .i_g(G_55_54),
        .i_p(P_55_54),
        .i_g_km1(G_53_52),
        .i_p_km1(P_53_52),
        .ow_g(G_55_52),
        .ow_p(P_55_52)
    );
    math_adder_brent_kung_black black_block_59_56 (
        .i_g(G_59_58),
        .i_p(P_59_58),
        .i_g_km1(G_57_56),
        .i_p_km1(P_57_56),
        .ow_g(G_59_56),
        .ow_p(P_59_56)
    );
    math_adder_brent_kung_black black_block_63_60 (
        .i_g(G_63_62),
        .i_p(P_63_62),
        .i_g_km1(G_61_60),
        .i_p_km1(P_61_60),
        .ow_g(G_63_60),
        .ow_p(P_63_60)
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
    math_adder_brent_kung_black black_block_39_32 (
        .i_g(G_39_36),
        .i_p(P_39_36),
        .i_g_km1(G_35_32),
        .i_p_km1(P_35_32),
        .ow_g(G_39_32),
        .ow_p(P_39_32)
    );
    math_adder_brent_kung_black black_block_47_40 (
        .i_g(G_47_44),
        .i_p(P_47_44),
        .i_g_km1(G_43_40),
        .i_p_km1(P_43_40),
        .ow_g(G_47_40),
        .ow_p(P_47_40)
    );
    math_adder_brent_kung_black black_block_55_48 (
        .i_g(G_55_52),
        .i_p(P_55_52),
        .i_g_km1(G_51_48),
        .i_p_km1(P_51_48),
        .ow_g(G_55_48),
        .ow_p(P_55_48)
    );
    math_adder_brent_kung_black black_block_63_56 (
        .i_g(G_63_60),
        .i_p(P_63_60),
        .i_g_km1(G_59_56),
        .i_p_km1(P_59_56),
        .ow_g(G_63_56),
        .ow_p(P_63_56)
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
    math_adder_brent_kung_black black_block_47_32 (
        .i_g(G_47_40),
        .i_p(P_47_40),
        .i_g_km1(G_39_32),
        .i_p_km1(P_39_32),
        .ow_g(G_47_32),
        .ow_p(P_47_32)
    );
    math_adder_brent_kung_black black_block_63_48 (
        .i_g(G_63_56),
        .i_p(P_63_56),
        .i_g_km1(G_55_48),
        .i_p_km1(P_55_48),
        .ow_g(G_63_48),
        .ow_p(P_63_48)
    );
    math_adder_brent_kung_gray gray_block_31_0 (
        .i_g(G_31_16),
        .i_p(P_31_16),
        .i_g_km1(ow_gg[15]),
        .ow_g(ow_gg[31])
    );
    math_adder_brent_kung_black black_block_63_32 (
        .i_g(G_63_48),
        .i_p(P_63_48),
        .i_g_km1(G_47_32),
        .i_p_km1(P_47_32),
        .ow_g(G_63_32),
        .ow_p(P_63_32)
    );
    math_adder_brent_kung_gray gray_block_63_0 (
        .i_g(G_63_32),
        .i_p(P_63_32),
        .i_g_km1(ow_gg[31]),
        .ow_g(ow_gg[63])
    );
    math_adder_brent_kung_gray gray_block_47_31 (
        .i_g(G_47_32),
        .i_p(P_47_32),
        .i_g_km1(ow_gg[31]),
        .ow_g(ow_gg[47])
    );
    math_adder_brent_kung_gray gray_block_23_15 (
        .i_g(G_23_16),
        .i_p(P_23_16),
        .i_g_km1(ow_gg[15]),
        .ow_g(ow_gg[23])
    );
    math_adder_brent_kung_gray gray_block_39_31 (
        .i_g(G_39_32),
        .i_p(P_39_32),
        .i_g_km1(ow_gg[31]),
        .ow_g(ow_gg[39])
    );
    math_adder_brent_kung_gray gray_block_55_47 (
        .i_g(G_55_48),
        .i_p(P_55_48),
        .i_g_km1(ow_gg[47]),
        .ow_g(ow_gg[55])
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
    math_adder_brent_kung_gray gray_block_35_31 (
        .i_g(G_35_32),
        .i_p(P_35_32),
        .i_g_km1(ow_gg[31]),
        .ow_g(ow_gg[35])
    );
    math_adder_brent_kung_gray gray_block_43_39 (
        .i_g(G_43_40),
        .i_p(P_43_40),
        .i_g_km1(ow_gg[39]),
        .ow_g(ow_gg[43])
    );
    math_adder_brent_kung_gray gray_block_51_47 (
        .i_g(G_51_48),
        .i_p(P_51_48),
        .i_g_km1(ow_gg[47]),
        .ow_g(ow_gg[51])
    );
    math_adder_brent_kung_gray gray_block_59_55 (
        .i_g(G_59_56),
        .i_p(P_59_56),
        .i_g_km1(ow_gg[55]),
        .ow_g(ow_gg[59])
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
    math_adder_brent_kung_gray gray_block_33_31 (
        .i_g(G_33_32),
        .i_p(P_33_32),
        .i_g_km1(ow_gg[31]),
        .ow_g(ow_gg[33])
    );
    math_adder_brent_kung_gray gray_block_37_35 (
        .i_g(G_37_36),
        .i_p(P_37_36),
        .i_g_km1(ow_gg[35]),
        .ow_g(ow_gg[37])
    );
    math_adder_brent_kung_gray gray_block_41_39 (
        .i_g(G_41_40),
        .i_p(P_41_40),
        .i_g_km1(ow_gg[39]),
        .ow_g(ow_gg[41])
    );
    math_adder_brent_kung_gray gray_block_45_43 (
        .i_g(G_45_44),
        .i_p(P_45_44),
        .i_g_km1(ow_gg[43]),
        .ow_g(ow_gg[45])
    );
    math_adder_brent_kung_gray gray_block_49_47 (
        .i_g(G_49_48),
        .i_p(P_49_48),
        .i_g_km1(ow_gg[47]),
        .ow_g(ow_gg[49])
    );
    math_adder_brent_kung_gray gray_block_53_51 (
        .i_g(G_53_52),
        .i_p(P_53_52),
        .i_g_km1(ow_gg[51]),
        .ow_g(ow_gg[53])
    );
    math_adder_brent_kung_gray gray_block_57_55 (
        .i_g(G_57_56),
        .i_p(P_57_56),
        .i_g_km1(ow_gg[55]),
        .ow_g(ow_gg[57])
    );
    math_adder_brent_kung_gray gray_block_61_59 (
        .i_g(G_61_60),
        .i_p(P_61_60),
        .i_g_km1(ow_gg[59]),
        .ow_g(ow_gg[61])
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
    math_adder_brent_kung_gray gray_block_34_33 (
        .i_g(i_g[34]),
        .i_p(i_p[34]),
        .i_g_km1(ow_gg[33]),
        .ow_g(ow_gg[34])
    );
    math_adder_brent_kung_gray gray_block_36_35 (
        .i_g(i_g[36]),
        .i_p(i_p[36]),
        .i_g_km1(ow_gg[35]),
        .ow_g(ow_gg[36])
    );
    math_adder_brent_kung_gray gray_block_38_37 (
        .i_g(i_g[38]),
        .i_p(i_p[38]),
        .i_g_km1(ow_gg[37]),
        .ow_g(ow_gg[38])
    );
    math_adder_brent_kung_gray gray_block_40_39 (
        .i_g(i_g[40]),
        .i_p(i_p[40]),
        .i_g_km1(ow_gg[39]),
        .ow_g(ow_gg[40])
    );
    math_adder_brent_kung_gray gray_block_42_41 (
        .i_g(i_g[42]),
        .i_p(i_p[42]),
        .i_g_km1(ow_gg[41]),
        .ow_g(ow_gg[42])
    );
    math_adder_brent_kung_gray gray_block_44_43 (
        .i_g(i_g[44]),
        .i_p(i_p[44]),
        .i_g_km1(ow_gg[43]),
        .ow_g(ow_gg[44])
    );
    math_adder_brent_kung_gray gray_block_46_45 (
        .i_g(i_g[46]),
        .i_p(i_p[46]),
        .i_g_km1(ow_gg[45]),
        .ow_g(ow_gg[46])
    );
    math_adder_brent_kung_gray gray_block_48_47 (
        .i_g(i_g[48]),
        .i_p(i_p[48]),
        .i_g_km1(ow_gg[47]),
        .ow_g(ow_gg[48])
    );
    math_adder_brent_kung_gray gray_block_50_49 (
        .i_g(i_g[50]),
        .i_p(i_p[50]),
        .i_g_km1(ow_gg[49]),
        .ow_g(ow_gg[50])
    );
    math_adder_brent_kung_gray gray_block_52_51 (
        .i_g(i_g[52]),
        .i_p(i_p[52]),
        .i_g_km1(ow_gg[51]),
        .ow_g(ow_gg[52])
    );
    math_adder_brent_kung_gray gray_block_54_53 (
        .i_g(i_g[54]),
        .i_p(i_p[54]),
        .i_g_km1(ow_gg[53]),
        .ow_g(ow_gg[54])
    );
    math_adder_brent_kung_gray gray_block_56_55 (
        .i_g(i_g[56]),
        .i_p(i_p[56]),
        .i_g_km1(ow_gg[55]),
        .ow_g(ow_gg[56])
    );
    math_adder_brent_kung_gray gray_block_58_57 (
        .i_g(i_g[58]),
        .i_p(i_p[58]),
        .i_g_km1(ow_gg[57]),
        .ow_g(ow_gg[58])
    );
    math_adder_brent_kung_gray gray_block_60_59 (
        .i_g(i_g[60]),
        .i_p(i_p[60]),
        .i_g_km1(ow_gg[59]),
        .ow_g(ow_gg[60])
    );
    math_adder_brent_kung_gray gray_block_62_61 (
        .i_g(i_g[62]),
        .i_p(i_p[62]),
        .i_g_km1(ow_gg[61]),
        .ow_g(ow_gg[62])
    );
    math_adder_brent_kung_gray gray_block_64_63 (
        .i_g(i_g[64]),
        .i_p(i_p[64]),
        .i_g_km1(ow_gg[63]),
        .ow_g(ow_gg[64])
    );
    assign ow_gg[0] = i_g[0];
    assign ow_pp[0] = i_p[0];
endmodule
