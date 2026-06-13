// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2026 sean galloway
//
// Module: char_top_fpga_mmcm
// Purpose: MMCM clock-sweep variant of the FPGA characterization wrapper.
//
// Description:
//   Drives FOUR parallel char_top instances at MMCM-derived test clocks
//   (defaults 150 / 200 / 250 / 300 MHz). Each instance gets the same
//   LFSR seed from the board switches. Each instance's outputs are folded
//   into a 32-bit XOR signature in their own clock domain, then CDC'd to
//   the safe 100 MHz observation clock.
//
// On-board observation (8 user LEDs):
//   LED[3:0] - per-test-clock 'alive' bit: blinks while the signature in
//              that clock domain changes between consecutive snapshots.
//              A solid (stuck) bit means the chain in that domain stopped
//              updating - implicating that test clock as failing timing.
//   LED[7:4] - lower 4 bits of the selected test clock's signature; the
//              selector is the upper switch (SW[3:2]) so a user can scope
//              any of the four domains.
//
// Usage:
//   make bitstream FPGA_TOP=char_top_fpga_mmcm
//
// VCO geometry (Artix-7 -1 MMCME2_BASE):
//   CLKIN  = 100 MHz; CLKFBOUT_MULT_F * 100 must stay in [600, 1200] MHz.
//   We use CLKFBOUT_MULT_F = 12.0 -> VCO = 1200 MHz, then per-output
//   dividers pick the test frequencies:
//     CLKOUT0 = 1200/8 = 150 MHz
//     CLKOUT1 = 1200/6 = 200 MHz
//     CLKOUT2 = 1200/5 = 240 MHz   (effective "250 MHz" bucket)
//     CLKOUT3 = 1200/4 = 300 MHz
//
// Author: sean galloway
// Created: 2026-06-12

`timescale 1ns / 1ps

module char_top_fpga_mmcm (
    input  logic        CLK100MHZ,
    input  logic        CPU_RESETN,
    input  logic [3:0]  SW,
    output logic [7:0]  LED
);

    // ---- Observation domain (the safe 100 MHz reference) ------------------
    logic obs_clk;
    logic obs_rst_n;
    assign obs_clk   = CLK100MHZ;
    assign obs_rst_n = CPU_RESETN;

    // ---- MMCM: four test clocks from a 1200 MHz VCO ----------------------
    logic mmcm_fb;
    logic clk_test_raw [0:3];
    logic mmcm_locked;

    MMCME2_BASE #(
        .BANDWIDTH         ("OPTIMIZED"),
        .CLKIN1_PERIOD     (10.0),       // 100 MHz
        .CLKFBOUT_MULT_F   (12.0),       // VCO = 1200 MHz
        .CLKOUT0_DIVIDE_F  (8.0),        // 150 MHz
        .CLKOUT1_DIVIDE    (6),          // 200 MHz
        .CLKOUT2_DIVIDE    (5),          // 240 MHz ("250 MHz" bucket)
        .CLKOUT3_DIVIDE    (4),          // 300 MHz
        .DIVCLK_DIVIDE     (1),
        .CLKOUT0_PHASE     (0.0),
        .CLKOUT1_PHASE     (0.0),
        .CLKOUT2_PHASE     (0.0),
        .CLKOUT3_PHASE     (0.0),
        .CLKOUT0_DUTY_CYCLE(0.5),
        .CLKOUT1_DUTY_CYCLE(0.5),
        .CLKOUT2_DUTY_CYCLE(0.5),
        .CLKOUT3_DUTY_CYCLE(0.5),
        .REF_JITTER1       (0.010),
        .STARTUP_WAIT      ("FALSE")
    ) u_mmcm (
        .CLKIN1     (CLK100MHZ),
        .CLKFBIN    (mmcm_fb),
        .RST        (~CPU_RESETN),
        .PWRDWN     (1'b0),
        .CLKFBOUT   (mmcm_fb),
        .CLKFBOUTB  (),
        .CLKOUT0    (clk_test_raw[0]),
        .CLKOUT0B   (),
        .CLKOUT1    (clk_test_raw[1]),
        .CLKOUT1B   (),
        .CLKOUT2    (clk_test_raw[2]),
        .CLKOUT2B   (),
        .CLKOUT3    (clk_test_raw[3]),
        .CLKOUT4    (),
        .CLKOUT5    (),
        .CLKOUT6    (),
        .LOCKED     (mmcm_locked)
    );

    // Buffer the MMCM outputs onto the global clock network.
    logic clk_test [0:3];
    genvar gc;
    generate
        for (gc = 0; gc < 4; gc++) begin : gen_bufg
            BUFG u_bufg (.I(clk_test_raw[gc]), .O(clk_test[gc]));
        end
    endgenerate

    // Per-test-domain reset: held until MMCM locks AND the board reset
    // button is released. Synchronise the release to each test clock so
    // every char_top instance comes out of reset cleanly.
    logic [3:0] r_rst_meta;
    logic [3:0] r_rst_sync;
    logic [3:0] test_rst_n;
    genvar gr;
    generate
        for (gr = 0; gr < 4; gr++) begin : gen_rst_sync
            (* ASYNC_REG = "TRUE" *) logic r_meta;
            (* ASYNC_REG = "TRUE" *) logic r_sync;
            always_ff @(posedge clk_test[gr] or negedge CPU_RESETN) begin
                if (!CPU_RESETN) begin
                    r_meta <= 1'b0;
                    r_sync <= 1'b0;
                end else begin
                    r_meta <= mmcm_locked;
                    r_sync <= r_meta;
                end
            end
            assign test_rst_n[gr] = r_sync;
        end
    endgenerate

    // ---- Four char_top instances, one per test clock ----------------------
    logic        nand_d   [0:3];
    logic        inv_d    [0:3];
    logic        xor_d    [0:3];
    logic [64:0] carry_d  [0:3];
    logic [31:0] mult_d   [0:3];
    logic        mux_d    [0:3];
    logic [31:0] qdata_d  [0:3];
    logic        qvalid_d [0:3];
    logic [4:0]  qcount_d [0:3];
    logic [3:0]  clkdiv_d [0:3];
    logic [31:0] graybin_d[0:3];
    logic [31:0] graycode_d[0:3];

    // Seed pulse local to each test clock.
    logic r_seeded [0:3];

    genvar gi;
    generate
        for (gi = 0; gi < 4; gi++) begin : gen_char
            logic        seed_valid;
            logic [31:0] seed_data;
            assign seed_data  = {28'd0, SW};
            assign seed_valid = !r_seeded[gi];

            always_ff @(posedge clk_test[gi] or negedge test_rst_n[gi]) begin
                if (!test_rst_n[gi]) r_seeded[gi] <= 1'b0;
                else                 r_seeded[gi] <= 1'b1;
            end

            char_top #(
                .EN_NAND_TREE      (1),
                .EN_INVERTER_CHAIN (1),
                .EN_XOR_TREE       (1),
                .EN_CARRY_CHAIN    (1),
                .EN_MULTIPLIER     (1),
                .EN_MUX_TREE       (1),
                .EN_QUEUE_DEPTH    (1),
                .EN_CLK_DIVIDER    (1),
                .EN_GRAY_COUNTER   (1)
            ) u_char_top (
                .clk           (clk_test[gi]),
                .rst_n         (test_rst_n[gi]),
                .i_seed_valid  (seed_valid),
                .i_seed_data   (seed_data),
                .o_nand        (nand_d[gi]),
                .o_inverter    (inv_d[gi]),
                .o_xor         (xor_d[gi]),
                .o_carry       (carry_d[gi]),
                .o_mult        (mult_d[gi]),
                .o_mux         (mux_d[gi]),
                .o_queue_data  (qdata_d[gi]),
                .o_queue_valid (qvalid_d[gi]),
                .o_queue_count (qcount_d[gi]),
                .o_clk_div     (clkdiv_d[gi]),
                .o_gray_bin    (graybin_d[gi]),
                .o_gray_code   (graycode_d[gi])
            );
        end
    endgenerate

    // ---- Per-domain signature accumulator + CDC into obs_clk -------------
    // Pack each char_top's outputs into one wide bus for the fold.
    localparam int FAB_W = 1+1+1+65+32+1+32+1+5+4+32+32;  // = 207 bits
    logic [FAB_W-1:0] fab [0:3];
    logic [31:0]      sig_obs [0:3];
    logic             alive_obs [0:3];

    genvar gp;
    generate
        for (gp = 0; gp < 4; gp++) begin : gen_pack_sig
            assign fab[gp] = {
                nand_d[gp], inv_d[gp], xor_d[gp],
                carry_d[gp], mult_d[gp], mux_d[gp],
                qdata_d[gp], qvalid_d[gp], qcount_d[gp],
                clkdiv_d[gp], graybin_d[gp], graycode_d[gp]
            };

            sig_accum #(
                .IN_WIDTH (FAB_W),
                .SNAP_LOG2(16)
            ) u_sig (
                .src_clk   (clk_test[gp]),
                .src_rst_n (test_rst_n[gp]),
                .src_data  (fab[gp]),
                .obs_clk   (obs_clk),
                .obs_rst_n (obs_rst_n),
                .obs_sig   (sig_obs[gp]),
                .obs_alive (alive_obs[gp])
            );
        end
    endgenerate

    // ---- Selector mux: SW[3:2] picks which signature drives LED[7:4] -----
    logic [31:0] sel_sig;
    always_comb begin
        case (SW[3:2])
            2'b00:   sel_sig = sig_obs[0];
            2'b01:   sel_sig = sig_obs[1];
            2'b10:   sel_sig = sig_obs[2];
            default: sel_sig = sig_obs[3];
        endcase
    end

    // ---- LED map: low nibble = per-clock alive flag; high nibble = sig[3:0]
    assign LED[0] = alive_obs[0];
    assign LED[1] = alive_obs[1];
    assign LED[2] = alive_obs[2];
    assign LED[3] = alive_obs[3];
    assign LED[4] = sel_sig[0];
    assign LED[5] = sel_sig[1];
    assign LED[6] = sel_sig[2];
    assign LED[7] = sel_sig[3];

endmodule : char_top_fpga_mmcm
