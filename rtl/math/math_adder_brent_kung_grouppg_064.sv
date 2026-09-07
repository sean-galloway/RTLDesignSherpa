// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: math_adder_brent_kung_grouppg_064
// Purpose: Math Adder Brent Kung Grouppg 064 module
//
// Documentation: docs/markdown/rtl-math/overview.md
// Subsystem: math
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

    // Per-bit scalars for the prefix chain, NOT bit-selects of ow_gg.
    //
    // This is a Brent-Kung prefix tree: bit 1 feeds 3 feeds 7 feeds 15,
    // strictly forwards, never back. But when every bit is a select of the
    // SAME output vector, Verilator schedules that vector as one node and
    // "bit 3 reads bit 1" becomes ow_gg depending on itself -- reported as
    // UNOPTFLAT: Circular combinational logic, which fails any build that
    // treats warnings as errors. It failed all six Dadda/Wallace multiplier
    // tests, which use this adder as their final CPA.
    //
    // `verilator split_var` is the usual answer and does NOT work here:
    // cocotb builds with --public-flat-rw, and Verilator refuses to split a
    // public variable (SPLITVAR). Scalars solve it structurally instead --
    // each is its own net, and ow_gg is now only ever WRITTEN in this module,
    // so no cycle can be inferred. Same logic, same connectivity.
    logic w_gg_1, w_gg_2, w_gg_3, w_gg_4, w_gg_5, w_gg_6, w_gg_7, w_gg_8, w_gg_9, w_gg_10, w_gg_11, w_gg_12, w_gg_13, w_gg_14, w_gg_15, w_gg_16, w_gg_17, w_gg_18, w_gg_19, w_gg_20, w_gg_21, w_gg_22, w_gg_23, w_gg_24, w_gg_25, w_gg_26, w_gg_27, w_gg_28, w_gg_29, w_gg_30, w_gg_31, w_gg_32, w_gg_33, w_gg_34, w_gg_35, w_gg_36, w_gg_37, w_gg_38, w_gg_39, w_gg_40, w_gg_41, w_gg_42, w_gg_43, w_gg_44, w_gg_45, w_gg_46, w_gg_47, w_gg_48, w_gg_49, w_gg_50, w_gg_51, w_gg_52, w_gg_53, w_gg_54, w_gg_55, w_gg_56, w_gg_57, w_gg_58, w_gg_59, w_gg_60, w_gg_61, w_gg_62, w_gg_63, w_gg_64;

    // `split_var` so Verilator schedules ow_gg PER BIT, not as one node.
    // This is a Brent-Kung prefix tree: bit 1 feeds bit 3 feeds bit 7 feeds
    // bit 15, strictly forwards. But every bit is driven by a different
    // sub-instance of the SAME vector, so scheduling ow_gg as a single node
    // makes "bit 3 reads bit 1" look like ow_gg depending on itself --
    // reported as UNOPTFLAT: Circular combinational logic, which fails any
    // build that treats warnings as errors. There is no loop; splitting the
    // variable lets the scheduler see the real, acyclic dependency.
    // The metacomment is a comment to every other tool.
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
        .ow_g(w_gg_1)
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
        .i_g_km1(w_gg_1),
        .ow_g(w_gg_3)
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
        .i_g_km1(w_gg_3),
        .ow_g(w_gg_7)
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
        .i_g_km1(w_gg_7),
        .ow_g(w_gg_15)
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
        .i_g_km1(w_gg_15),
        .ow_g(w_gg_31)
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
        .i_g_km1(w_gg_31),
        .ow_g(w_gg_63)
    );
    math_adder_brent_kung_gray gray_block_47_31 (
        .i_g(G_47_32),
        .i_p(P_47_32),
        .i_g_km1(w_gg_31),
        .ow_g(w_gg_47)
    );
    math_adder_brent_kung_gray gray_block_23_15 (
        .i_g(G_23_16),
        .i_p(P_23_16),
        .i_g_km1(w_gg_15),
        .ow_g(w_gg_23)
    );
    math_adder_brent_kung_gray gray_block_39_31 (
        .i_g(G_39_32),
        .i_p(P_39_32),
        .i_g_km1(w_gg_31),
        .ow_g(w_gg_39)
    );
    math_adder_brent_kung_gray gray_block_55_47 (
        .i_g(G_55_48),
        .i_p(P_55_48),
        .i_g_km1(w_gg_47),
        .ow_g(w_gg_55)
    );
    math_adder_brent_kung_gray gray_block_11_7 (
        .i_g(G_11_8),
        .i_p(P_11_8),
        .i_g_km1(w_gg_7),
        .ow_g(w_gg_11)
    );
    math_adder_brent_kung_gray gray_block_19_15 (
        .i_g(G_19_16),
        .i_p(P_19_16),
        .i_g_km1(w_gg_15),
        .ow_g(w_gg_19)
    );
    math_adder_brent_kung_gray gray_block_27_23 (
        .i_g(G_27_24),
        .i_p(P_27_24),
        .i_g_km1(w_gg_23),
        .ow_g(w_gg_27)
    );
    math_adder_brent_kung_gray gray_block_35_31 (
        .i_g(G_35_32),
        .i_p(P_35_32),
        .i_g_km1(w_gg_31),
        .ow_g(w_gg_35)
    );
    math_adder_brent_kung_gray gray_block_43_39 (
        .i_g(G_43_40),
        .i_p(P_43_40),
        .i_g_km1(w_gg_39),
        .ow_g(w_gg_43)
    );
    math_adder_brent_kung_gray gray_block_51_47 (
        .i_g(G_51_48),
        .i_p(P_51_48),
        .i_g_km1(w_gg_47),
        .ow_g(w_gg_51)
    );
    math_adder_brent_kung_gray gray_block_59_55 (
        .i_g(G_59_56),
        .i_p(P_59_56),
        .i_g_km1(w_gg_55),
        .ow_g(w_gg_59)
    );
    math_adder_brent_kung_gray gray_block_5_3 (
        .i_g(G_5_4),
        .i_p(P_5_4),
        .i_g_km1(w_gg_3),
        .ow_g(w_gg_5)
    );
    math_adder_brent_kung_gray gray_block_9_7 (
        .i_g(G_9_8),
        .i_p(P_9_8),
        .i_g_km1(w_gg_7),
        .ow_g(w_gg_9)
    );
    math_adder_brent_kung_gray gray_block_13_11 (
        .i_g(G_13_12),
        .i_p(P_13_12),
        .i_g_km1(w_gg_11),
        .ow_g(w_gg_13)
    );
    math_adder_brent_kung_gray gray_block_17_15 (
        .i_g(G_17_16),
        .i_p(P_17_16),
        .i_g_km1(w_gg_15),
        .ow_g(w_gg_17)
    );
    math_adder_brent_kung_gray gray_block_21_19 (
        .i_g(G_21_20),
        .i_p(P_21_20),
        .i_g_km1(w_gg_19),
        .ow_g(w_gg_21)
    );
    math_adder_brent_kung_gray gray_block_25_23 (
        .i_g(G_25_24),
        .i_p(P_25_24),
        .i_g_km1(w_gg_23),
        .ow_g(w_gg_25)
    );
    math_adder_brent_kung_gray gray_block_29_27 (
        .i_g(G_29_28),
        .i_p(P_29_28),
        .i_g_km1(w_gg_27),
        .ow_g(w_gg_29)
    );
    math_adder_brent_kung_gray gray_block_33_31 (
        .i_g(G_33_32),
        .i_p(P_33_32),
        .i_g_km1(w_gg_31),
        .ow_g(w_gg_33)
    );
    math_adder_brent_kung_gray gray_block_37_35 (
        .i_g(G_37_36),
        .i_p(P_37_36),
        .i_g_km1(w_gg_35),
        .ow_g(w_gg_37)
    );
    math_adder_brent_kung_gray gray_block_41_39 (
        .i_g(G_41_40),
        .i_p(P_41_40),
        .i_g_km1(w_gg_39),
        .ow_g(w_gg_41)
    );
    math_adder_brent_kung_gray gray_block_45_43 (
        .i_g(G_45_44),
        .i_p(P_45_44),
        .i_g_km1(w_gg_43),
        .ow_g(w_gg_45)
    );
    math_adder_brent_kung_gray gray_block_49_47 (
        .i_g(G_49_48),
        .i_p(P_49_48),
        .i_g_km1(w_gg_47),
        .ow_g(w_gg_49)
    );
    math_adder_brent_kung_gray gray_block_53_51 (
        .i_g(G_53_52),
        .i_p(P_53_52),
        .i_g_km1(w_gg_51),
        .ow_g(w_gg_53)
    );
    math_adder_brent_kung_gray gray_block_57_55 (
        .i_g(G_57_56),
        .i_p(P_57_56),
        .i_g_km1(w_gg_55),
        .ow_g(w_gg_57)
    );
    math_adder_brent_kung_gray gray_block_61_59 (
        .i_g(G_61_60),
        .i_p(P_61_60),
        .i_g_km1(w_gg_59),
        .ow_g(w_gg_61)
    );
    math_adder_brent_kung_gray gray_block_2_1 (
        .i_g(i_g[2]),
        .i_p(i_p[2]),
        .i_g_km1(w_gg_1),
        .ow_g(w_gg_2)
    );
    math_adder_brent_kung_gray gray_block_4_3 (
        .i_g(i_g[4]),
        .i_p(i_p[4]),
        .i_g_km1(w_gg_3),
        .ow_g(w_gg_4)
    );
    math_adder_brent_kung_gray gray_block_6_5 (
        .i_g(i_g[6]),
        .i_p(i_p[6]),
        .i_g_km1(w_gg_5),
        .ow_g(w_gg_6)
    );
    math_adder_brent_kung_gray gray_block_8_7 (
        .i_g(i_g[8]),
        .i_p(i_p[8]),
        .i_g_km1(w_gg_7),
        .ow_g(w_gg_8)
    );
    math_adder_brent_kung_gray gray_block_10_9 (
        .i_g(i_g[10]),
        .i_p(i_p[10]),
        .i_g_km1(w_gg_9),
        .ow_g(w_gg_10)
    );
    math_adder_brent_kung_gray gray_block_12_11 (
        .i_g(i_g[12]),
        .i_p(i_p[12]),
        .i_g_km1(w_gg_11),
        .ow_g(w_gg_12)
    );
    math_adder_brent_kung_gray gray_block_14_13 (
        .i_g(i_g[14]),
        .i_p(i_p[14]),
        .i_g_km1(w_gg_13),
        .ow_g(w_gg_14)
    );
    math_adder_brent_kung_gray gray_block_16_15 (
        .i_g(i_g[16]),
        .i_p(i_p[16]),
        .i_g_km1(w_gg_15),
        .ow_g(w_gg_16)
    );
    math_adder_brent_kung_gray gray_block_18_17 (
        .i_g(i_g[18]),
        .i_p(i_p[18]),
        .i_g_km1(w_gg_17),
        .ow_g(w_gg_18)
    );
    math_adder_brent_kung_gray gray_block_20_19 (
        .i_g(i_g[20]),
        .i_p(i_p[20]),
        .i_g_km1(w_gg_19),
        .ow_g(w_gg_20)
    );
    math_adder_brent_kung_gray gray_block_22_21 (
        .i_g(i_g[22]),
        .i_p(i_p[22]),
        .i_g_km1(w_gg_21),
        .ow_g(w_gg_22)
    );
    math_adder_brent_kung_gray gray_block_24_23 (
        .i_g(i_g[24]),
        .i_p(i_p[24]),
        .i_g_km1(w_gg_23),
        .ow_g(w_gg_24)
    );
    math_adder_brent_kung_gray gray_block_26_25 (
        .i_g(i_g[26]),
        .i_p(i_p[26]),
        .i_g_km1(w_gg_25),
        .ow_g(w_gg_26)
    );
    math_adder_brent_kung_gray gray_block_28_27 (
        .i_g(i_g[28]),
        .i_p(i_p[28]),
        .i_g_km1(w_gg_27),
        .ow_g(w_gg_28)
    );
    math_adder_brent_kung_gray gray_block_30_29 (
        .i_g(i_g[30]),
        .i_p(i_p[30]),
        .i_g_km1(w_gg_29),
        .ow_g(w_gg_30)
    );
    math_adder_brent_kung_gray gray_block_32_31 (
        .i_g(i_g[32]),
        .i_p(i_p[32]),
        .i_g_km1(w_gg_31),
        .ow_g(w_gg_32)
    );
    math_adder_brent_kung_gray gray_block_34_33 (
        .i_g(i_g[34]),
        .i_p(i_p[34]),
        .i_g_km1(w_gg_33),
        .ow_g(w_gg_34)
    );
    math_adder_brent_kung_gray gray_block_36_35 (
        .i_g(i_g[36]),
        .i_p(i_p[36]),
        .i_g_km1(w_gg_35),
        .ow_g(w_gg_36)
    );
    math_adder_brent_kung_gray gray_block_38_37 (
        .i_g(i_g[38]),
        .i_p(i_p[38]),
        .i_g_km1(w_gg_37),
        .ow_g(w_gg_38)
    );
    math_adder_brent_kung_gray gray_block_40_39 (
        .i_g(i_g[40]),
        .i_p(i_p[40]),
        .i_g_km1(w_gg_39),
        .ow_g(w_gg_40)
    );
    math_adder_brent_kung_gray gray_block_42_41 (
        .i_g(i_g[42]),
        .i_p(i_p[42]),
        .i_g_km1(w_gg_41),
        .ow_g(w_gg_42)
    );
    math_adder_brent_kung_gray gray_block_44_43 (
        .i_g(i_g[44]),
        .i_p(i_p[44]),
        .i_g_km1(w_gg_43),
        .ow_g(w_gg_44)
    );
    math_adder_brent_kung_gray gray_block_46_45 (
        .i_g(i_g[46]),
        .i_p(i_p[46]),
        .i_g_km1(w_gg_45),
        .ow_g(w_gg_46)
    );
    math_adder_brent_kung_gray gray_block_48_47 (
        .i_g(i_g[48]),
        .i_p(i_p[48]),
        .i_g_km1(w_gg_47),
        .ow_g(w_gg_48)
    );
    math_adder_brent_kung_gray gray_block_50_49 (
        .i_g(i_g[50]),
        .i_p(i_p[50]),
        .i_g_km1(w_gg_49),
        .ow_g(w_gg_50)
    );
    math_adder_brent_kung_gray gray_block_52_51 (
        .i_g(i_g[52]),
        .i_p(i_p[52]),
        .i_g_km1(w_gg_51),
        .ow_g(w_gg_52)
    );
    math_adder_brent_kung_gray gray_block_54_53 (
        .i_g(i_g[54]),
        .i_p(i_p[54]),
        .i_g_km1(w_gg_53),
        .ow_g(w_gg_54)
    );
    math_adder_brent_kung_gray gray_block_56_55 (
        .i_g(i_g[56]),
        .i_p(i_p[56]),
        .i_g_km1(w_gg_55),
        .ow_g(w_gg_56)
    );
    math_adder_brent_kung_gray gray_block_58_57 (
        .i_g(i_g[58]),
        .i_p(i_p[58]),
        .i_g_km1(w_gg_57),
        .ow_g(w_gg_58)
    );
    math_adder_brent_kung_gray gray_block_60_59 (
        .i_g(i_g[60]),
        .i_p(i_p[60]),
        .i_g_km1(w_gg_59),
        .ow_g(w_gg_60)
    );
    math_adder_brent_kung_gray gray_block_62_61 (
        .i_g(i_g[62]),
        .i_p(i_p[62]),
        .i_g_km1(w_gg_61),
        .ow_g(w_gg_62)
    );
    math_adder_brent_kung_gray gray_block_64_63 (
        .i_g(i_g[64]),
        .i_p(i_p[64]),
        .i_g_km1(w_gg_63),
        .ow_g(w_gg_64)
    );
    assign ow_gg[0] = i_g[0];
    assign ow_pp[0] = i_p[0];
    assign ow_gg[1] = w_gg_1;
    assign ow_gg[2] = w_gg_2;
    assign ow_gg[3] = w_gg_3;
    assign ow_gg[4] = w_gg_4;
    assign ow_gg[5] = w_gg_5;
    assign ow_gg[6] = w_gg_6;
    assign ow_gg[7] = w_gg_7;
    assign ow_gg[8] = w_gg_8;
    assign ow_gg[9] = w_gg_9;
    assign ow_gg[10] = w_gg_10;
    assign ow_gg[11] = w_gg_11;
    assign ow_gg[12] = w_gg_12;
    assign ow_gg[13] = w_gg_13;
    assign ow_gg[14] = w_gg_14;
    assign ow_gg[15] = w_gg_15;
    assign ow_gg[16] = w_gg_16;
    assign ow_gg[17] = w_gg_17;
    assign ow_gg[18] = w_gg_18;
    assign ow_gg[19] = w_gg_19;
    assign ow_gg[20] = w_gg_20;
    assign ow_gg[21] = w_gg_21;
    assign ow_gg[22] = w_gg_22;
    assign ow_gg[23] = w_gg_23;
    assign ow_gg[24] = w_gg_24;
    assign ow_gg[25] = w_gg_25;
    assign ow_gg[26] = w_gg_26;
    assign ow_gg[27] = w_gg_27;
    assign ow_gg[28] = w_gg_28;
    assign ow_gg[29] = w_gg_29;
    assign ow_gg[30] = w_gg_30;
    assign ow_gg[31] = w_gg_31;
    assign ow_gg[32] = w_gg_32;
    assign ow_gg[33] = w_gg_33;
    assign ow_gg[34] = w_gg_34;
    assign ow_gg[35] = w_gg_35;
    assign ow_gg[36] = w_gg_36;
    assign ow_gg[37] = w_gg_37;
    assign ow_gg[38] = w_gg_38;
    assign ow_gg[39] = w_gg_39;
    assign ow_gg[40] = w_gg_40;
    assign ow_gg[41] = w_gg_41;
    assign ow_gg[42] = w_gg_42;
    assign ow_gg[43] = w_gg_43;
    assign ow_gg[44] = w_gg_44;
    assign ow_gg[45] = w_gg_45;
    assign ow_gg[46] = w_gg_46;
    assign ow_gg[47] = w_gg_47;
    assign ow_gg[48] = w_gg_48;
    assign ow_gg[49] = w_gg_49;
    assign ow_gg[50] = w_gg_50;
    assign ow_gg[51] = w_gg_51;
    assign ow_gg[52] = w_gg_52;
    assign ow_gg[53] = w_gg_53;
    assign ow_gg[54] = w_gg_54;
    assign ow_gg[55] = w_gg_55;
    assign ow_gg[56] = w_gg_56;
    assign ow_gg[57] = w_gg_57;
    assign ow_gg[58] = w_gg_58;
    assign ow_gg[59] = w_gg_59;
    assign ow_gg[60] = w_gg_60;
    assign ow_gg[61] = w_gg_61;
    assign ow_gg[62] = w_gg_62;
    assign ow_gg[63] = w_gg_63;
    assign ow_gg[64] = w_gg_64;

endmodule
