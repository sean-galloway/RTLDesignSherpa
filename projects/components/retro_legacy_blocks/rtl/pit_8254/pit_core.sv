// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: pit_core
// Purpose: Core logic for 8254 PIT with 3 independent counters
//
// Instantiates 3 pit_counter modules and handles:
// - Control word decode (which counter to configure)
// - Counter data routing (read/write to selected counter)
// - Status byte generation for each counter
// - Clock enable generation from clock select
//
// Follows HPET pattern: array of timer instances with shared control

`timescale 1ns / 1ps

`include "reset_defs.svh"

module pit_core #(
    parameter int NUM_COUNTERS = 3
) (
    input wire clk,
    input wire rst,  // Active-high reset

    // Configuration from registers
    input wire        cfg_pit_enable,
    input wire        cfg_clock_select,

    // Control word inputs
    input wire        cfg_bcd,
    input wire [2:0]  cfg_mode,
    input wire [1:0]  cfg_rw_mode,
    input wire [1:0]  cfg_counter_select,
    input wire        cfg_control_wr,

    // Counter data interface (to/from registers)
    input  wire [15:0] counter0_reg_in,
    input  wire [15:0] counter1_reg_in,
    input  wire [15:0] counter2_reg_in,
    input  wire        counter0_reg_wr,      // Write strobe for counter 0
    input  wire        counter1_reg_wr,      // Write strobe for counter 1
    input  wire        counter2_reg_wr,      // Write strobe for counter 2
    output wire [15:0] counter0_reg_out,
    output wire [15:0] counter1_reg_out,
    output wire [15:0] counter2_reg_out,

    // Status outputs
    output wire [7:0] counter0_status,
    output wire [7:0] counter1_status,
    output wire [7:0] counter2_status,

    // Hardware interface
    input  wire [NUM_COUNTERS-1:0] i_gate,      // GATE inputs
    output wire [NUM_COUNTERS-1:0] o_out        // OUT/IRQ outputs
);

    //========================================================================
    // Clock Enable Generation
    //========================================================================

    // cfg_clock_select: 0 = external (GATE as clock), 1 = use clk
    // For now, assume using clk and GATE is just enable
    wire w_clk_en = cfg_pit_enable;

    //========================================================================
    // Control Word Decode
    //========================================================================

    // Control word is directed to specific counter based on counter_select
    logic [NUM_COUNTERS-1:0] w_control_wr_strobe;

    always_comb begin
        w_control_wr_strobe = '0;
        if (cfg_control_wr) begin
            case (cfg_counter_select)
                2'b00: w_control_wr_strobe[0] = 1'b1;  // Counter 0
                2'b01: w_control_wr_strobe[1] = 1'b1;  // Counter 1
                2'b10: w_control_wr_strobe[2] = 1'b1;  // Counter 2
                2'b11: w_control_wr_strobe = '0;       // Read-back command (future)
            endcase
        end
    end

    //========================================================================
    // Counter Data Write Strobes (from pit_config_regs)
    //========================================================================

    // Write strobes come directly from pit_config_regs edge detection
    logic [NUM_COUNTERS-1:0] w_count_reg_wr;

    assign w_count_reg_wr[0] = counter0_reg_wr;
    assign w_count_reg_wr[1] = counter1_reg_wr;
    assign w_count_reg_wr[2] = counter2_reg_wr;

    //========================================================================
    // Counter Instances
    //========================================================================

    // Counter 0
    wire        w_null_count0;
    wire [1:0]  w_status_rw_mode0;
    wire [2:0]  w_status_mode0;
    wire        w_status_bcd0;

    pit_counter u_counter0 (
        .clk                (clk),
        .rst                (rst),
        // Configuration
        .cfg_bcd            (cfg_bcd),
        .cfg_mode           (cfg_mode),
        .cfg_rw_mode        (cfg_rw_mode),
        .cfg_control_wr     (w_control_wr_strobe[0]),
        // Counter data
        .count_reg_in       (counter0_reg_in),
        .count_reg_wr       (w_count_reg_wr[0]),
        .count_reg_out      (counter0_reg_out),
        // Hardware interface
        .i_gate             (i_gate[0]),
        .i_clk_en           (w_clk_en),
        .o_out              (o_out[0]),
        // Status
        .o_null_count       (w_null_count0),
        .o_status_rw_mode   (w_status_rw_mode0),
        .o_status_mode      (w_status_mode0),
        .o_status_bcd       (w_status_bcd0)
    );

    // Counter 1
    wire        w_null_count1;
    wire [1:0]  w_status_rw_mode1;
    wire [2:0]  w_status_mode1;
    wire        w_status_bcd1;

    pit_counter u_counter1 (
        .clk                (clk),
        .rst                (rst),
        // Configuration
        .cfg_bcd            (cfg_bcd),
        .cfg_mode           (cfg_mode),
        .cfg_rw_mode        (cfg_rw_mode),
        .cfg_control_wr     (w_control_wr_strobe[1]),
        // Counter data
        .count_reg_in       (counter1_reg_in),
        .count_reg_wr       (w_count_reg_wr[1]),
        .count_reg_out      (counter1_reg_out),
        // Hardware interface
        .i_gate             (i_gate[1]),
        .i_clk_en           (w_clk_en),
        .o_out              (o_out[1]),
        // Status
        .o_null_count       (w_null_count1),
        .o_status_rw_mode   (w_status_rw_mode1),
        .o_status_mode      (w_status_mode1),
        .o_status_bcd       (w_status_bcd1)
    );

    // Counter 2
    wire        w_null_count2;
    wire [1:0]  w_status_rw_mode2;
    wire [2:0]  w_status_mode2;
    wire        w_status_bcd2;

    pit_counter u_counter2 (
        .clk                (clk),
        .rst                (rst),
        // Configuration
        .cfg_bcd            (cfg_bcd),
        .cfg_mode           (cfg_mode),
        .cfg_rw_mode        (cfg_rw_mode),
        .cfg_control_wr     (w_control_wr_strobe[2]),
        // Counter data
        .count_reg_in       (counter2_reg_in),
        .count_reg_wr       (w_count_reg_wr[2]),
        .count_reg_out      (counter2_reg_out),
        // Hardware interface
        .i_gate             (i_gate[2]),
        .i_clk_en           (w_clk_en),
        .o_out              (o_out[2]),
        // Status
        .o_null_count       (w_null_count2),
        .o_status_rw_mode   (w_status_rw_mode2),
        .o_status_mode      (w_status_mode2),
        .o_status_bcd       (w_status_bcd2)
    );

    //========================================================================
    // Status Byte Assembly
    //========================================================================

    // Status byte format (8254 read-back):
    // [7]    = OUT pin state
    // [6]    = NULL COUNT flag
    // [5:4]  = RW_MODE
    // [3:1]  = MODE
    // [0]    = BCD

    assign counter0_status = {
        o_out[0],           // [7] OUT
        w_null_count0,      // [6] NULL COUNT
        w_status_rw_mode0,  // [5:4] RW_MODE
        w_status_mode0,     // [3:1] MODE
        w_status_bcd0       // [0] BCD
    };

    assign counter1_status = {
        o_out[1],
        w_null_count1,
        w_status_rw_mode1,
        w_status_mode1,
        w_status_bcd1
    };

    assign counter2_status = {
        o_out[2],
        w_null_count2,
        w_status_rw_mode2,
        w_status_mode2,
        w_status_bcd2
    };

endmodule
