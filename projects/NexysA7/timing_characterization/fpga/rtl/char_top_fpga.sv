// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: char_top_fpga
// Purpose: Thin Nexys A7-100T wrapper around char_top
//
// Description:
//   char_top has wide output ports (CARRY_WIDTH+1, 2*MULT_WIDTH, GRAY_WIDTH,
//   etc.) that the ASIC harness uses as STA observation points - several
//   hundred bits in total.  The FPGA can't pin-out that many signals and
//   we don't need them anyway: for an on-board run we just need synthesis
//   to keep every chain alive so timing analysis is honest.
//
//   This wrapper XOR-reduces each FUB's output bus to a single bit and
//   drives 8 LEDs (one bit per FUB; the 9th feeds back into LED[0] via XOR
//   so all nine paths reach an output port).  Inputs come from a single
//   100 MHz board clock, the CPU_RESETN button, and 4 board switches that
//   set the seed.
//
//   Documentation: projects/NexysA7/timing_characterization/README.md
//   Subsystem: timing_characterization (FPGA)
//
// Author: sean galloway
// Created: 2026-06-12

`timescale 1ns / 1ps

module char_top_fpga (
    // Nexys A7-100T board pins
    input  logic        CLK100MHZ,
    input  logic        CPU_RESETN,        // active-low button
    input  logic [3:0]  SW,                // 4 user switches (seed nibble)
    output logic [7:0]  LED                // 8 user LEDs (per-FUB XOR-reduce)
);

    // ---- Clock + reset ----
    logic clk;
    logic rst_n;
    assign clk   = CLK100MHZ;
    assign rst_n = CPU_RESETN;

    // ---- Seed source ----
    // The harness's LFSR is reseeded once at start-of-day. Pulse i_seed_valid
    // for one cycle after reset deassertion; pull the seed value from the
    // board switches so a flip of SW between runs perturbs the chain.
    logic        r_seeded;
    logic        seed_valid;
    logic [31:0] seed_data;
    assign seed_data  = {28'd0, SW};
    assign seed_valid = !r_seeded;

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n)        r_seeded <= 1'b0;
        else               r_seeded <= 1'b1;
    end

    // ---- Wide FUB outputs from the characterization harness ----
    logic                          o_nand;
    logic                          o_inverter;
    logic                          o_xor;
    logic [64:0]                   o_carry;        // CARRY_WIDTH=64 -> 65 bits
    logic [31:0]                   o_mult;         // MULT_WIDTH=16  -> 32 bits
    logic                          o_mux;
    // FIFO_DATA_WIDTH=32 / FIFO_DEPTH=16 -> count is clog2(16)+1 = 5 bits.
    logic [31:0]                   o_queue_data;
    logic                          o_queue_valid;
    logic [4:0]                    o_queue_count;
    logic [3:0]                    o_clk_div;
    logic [31:0]                   o_gray_bin;
    logic [31:0]                   o_gray_code;

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
        .clk               (clk),
        .rst_n             (rst_n),
        .i_seed_valid      (seed_valid),
        .i_seed_data       (seed_data),
        .o_nand            (o_nand),
        .o_inverter        (o_inverter),
        .o_xor             (o_xor),
        .o_carry           (o_carry),
        .o_mult            (o_mult),
        .o_mux             (o_mux),
        .o_queue_data      (o_queue_data),
        .o_queue_valid     (o_queue_valid),
        .o_queue_count     (o_queue_count),
        .o_clk_div         (o_clk_div),
        .o_gray_bin        (o_gray_bin),
        .o_gray_code       (o_gray_code)
    );

    // ---- One-bit reduce per FUB and drive LEDs ----
    // Every output bit shows up in at least one LED equation so Vivado
    // can't optimise any chain away.
    logic w_nand_bit;
    logic w_inv_bit;
    logic w_xor_bit;
    logic w_carry_bit;
    logic w_mult_bit;
    logic w_mux_bit;
    logic w_queue_bit;
    logic w_clkdiv_bit;
    logic w_gray_bit;

    assign w_nand_bit   = o_nand;
    assign w_inv_bit    = o_inverter;
    assign w_xor_bit    = o_xor;
    assign w_carry_bit  = ^o_carry;
    assign w_mult_bit   = ^o_mult;
    assign w_mux_bit    = o_mux;
    assign w_queue_bit  = o_queue_valid ^ (^o_queue_data) ^ (^o_queue_count);
    assign w_clkdiv_bit = ^o_clk_div;
    assign w_gray_bit   = (^o_gray_bin) ^ (^o_gray_code);

    // 8 LEDs for 9 FUBs: gray rolls into nand on LED[0] via XOR so both
    // chains reach a top-level port without losing a LED to a single bit.
    assign LED[0] = w_nand_bit   ^ w_gray_bit;
    assign LED[1] = w_inv_bit;
    assign LED[2] = w_xor_bit;
    assign LED[3] = w_carry_bit;
    assign LED[4] = w_mult_bit;
    assign LED[5] = w_mux_bit;
    assign LED[6] = w_queue_bit;
    assign LED[7] = w_clkdiv_bit;

endmodule : char_top_fpga
