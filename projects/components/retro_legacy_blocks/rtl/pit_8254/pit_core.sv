// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: pit_core
// Purpose: 8254 PIT counter array - three independent counters plus the
//          control-word decode and the GATE input synchronizer
//
// Parameters:
//   - NUM_COUNTERS: fixed at 3 (the register map is generated for 3 counters;
//                   see the simulation-time guard below)
//   - SYNC_STAGES:  gate_in synchronizer depth, >= 2. Default 2.
//
// ============================================================================
// GATE IS SYNCHRONIZED HERE  (GitHub #52 qc round_3, item 3)
// ============================================================================
// gate_in is a device pin. It is asynchronous to the counting clock in BOTH
// configurations - with CDC_ENABLE = 1 the counters run on pit_clk, with
// CDC_ENABLE = 0 they run on pclk, and a pin is unrelated to either - so the
// synchronizer is UNCONDITIONAL rather than generate-gated on CDC_ENABLE. A
// "bypass when CDC_ENABLE = 0" would be asserting that the pin is synchronous
// to pclk, which nothing guarantees, and it would give the two configurations
// different GATE timing for no benefit.
//
// Cost: SYNC_STAGES counting-clock cycles of GATE latency, which mode 0
// pause/resume has ample margin for.
//
// ============================================================================
// CONTROL WORD DECODE
// ============================================================================
// A control word write is routed to the counter named by counter_select, and
// splits by the RW field:
//
//   RW != 00  -> PROGRAM   (cfg_control_wr): mode/RW/BCD shadow, OUT low,
//                          NULL COUNT set, count in progress aborted
//   RW == 00  -> LATCH     (cfg_latch_cmd): freeze the current count for an
//                          atomic read; programming is untouched
//
// counter_select = 11 is the 8254 read-back command. It is NOT implemented:
// this block exposes read-back through the PIT_STATUS register instead, so a
// control word with SC = 11 is accepted by the register file and does nothing
// here. Stated deviation, unchanged by GitHub #52.
//
// Documentation: projects/components/retro_legacy_blocks/rtl/pit_8254/README.md
// Subsystem: retro_legacy_blocks/pit_8254
//
// Updated: 2026-09-09 - GitHub #52: gate_in synchronizer, latch-vs-program
//                       control word decode, counter read strobes, active-low
//                       reset

`timescale 1ns / 1ps

`include "reset_defs.svh"

module pit_core #(
    parameter int NUM_COUNTERS = 3,
    parameter int SYNC_STAGES  = 2   // gate_in metastability filter depth, >= 2
) (
    input wire clk,
    input wire rst_n,  // Active-low asynchronous reset

    // Configuration from registers
    input wire        cfg_pit_enable,
    input wire        cfg_clock_select,

    // Control word inputs
    input wire        cfg_bcd,
    input wire [2:0]  cfg_mode,
    input wire [1:0]  cfg_rw_mode,
    input wire [1:0]  cfg_counter_select,
    input wire        cfg_control_wr,       // One cycle per control word write

    // Counter data interface (to/from registers)
    input  wire [15:0] counter0_reg_in,
    input  wire [15:0] counter1_reg_in,
    input  wire [15:0] counter2_reg_in,
    input  wire        counter0_reg_wr,     // Load strobe for counter 0
    input  wire        counter1_reg_wr,
    input  wire        counter2_reg_wr,
    input  wire        counter0_reg_rd,     // Data-read strobe for counter 0
    input  wire        counter1_reg_rd,
    input  wire        counter2_reg_rd,
    output wire [15:0] counter0_reg_out,
    output wire [15:0] counter1_reg_out,
    output wire [15:0] counter2_reg_out,

    // Status outputs
    output wire [7:0] counter0_status,
    output wire [7:0] counter1_status,
    output wire [7:0] counter2_status,

    // Hardware interface
    input  wire [NUM_COUNTERS-1:0] i_gate,      // GATE inputs (asynchronous)
    output wire [NUM_COUNTERS-1:0] o_out        // OUT / IRQ outputs
);

    //========================================================================
    // Local Parameters
    //========================================================================

    localparam logic [1:0] RW_LATCH = 2'b00;   // Control word latch opcode

    //========================================================================
    // Signals
    //========================================================================

    // GATE synchronizer
    logic [NUM_COUNTERS-1:0] r_gate_sync [SYNC_STAGES];
    logic [NUM_COUNTERS-1:0] w_gate;

    // Control word decode
    logic [NUM_COUNTERS-1:0] w_control_wr_strobe;   // PROGRAM, per counter
    logic [NUM_COUNTERS-1:0] w_latch_cmd_strobe;    // LATCH, per counter

    // Counter data strobes, gathered so the three instances index one vector
    logic [NUM_COUNTERS-1:0] w_count_reg_wr;
    logic [NUM_COUNTERS-1:0] w_count_reg_rd;

    // Counting clock enable. cfg_clock_select is software-visible storage with
    // no hardware effect: there is one counting clock and no prescaler to pick
    // between, so the only enable is the global PIT enable. Stated deviation.
    logic w_clk_en;

    // Per-counter status fields
    logic                    w_null_count [NUM_COUNTERS];
    logic [1:0]              w_status_rw_mode [NUM_COUNTERS];
    logic [2:0]              w_status_mode [NUM_COUNTERS];
    logic                    w_status_bcd [NUM_COUNTERS];

`ifndef SYNTHESIS
    // Simulation-time parameter guards (same shape as the gpio/hpet/pic
    // guards). The register map is generated from a fixed 3-counter RDL and
    // this file names counters 0-2 explicitly, so NUM_COUNTERS is not free.
    initial begin : param_check
        if (NUM_COUNTERS != 3) begin
            $error("pit_core: NUM_COUNTERS=%0d but pit_regs.rdl defines 3 counters",
                   NUM_COUNTERS);
        end
        if (SYNC_STAGES < 2) begin
            $error("pit_core: SYNC_STAGES=%0d but an input synchronizer needs >= 2",
                   SYNC_STAGES);
        end
    end
`endif

    //========================================================================
    // GATE Input Synchronizer
    //========================================================================

    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            for (int s = 0; s < SYNC_STAGES; s++) begin
                r_gate_sync[s] <= '0;
            end
        end else begin
            r_gate_sync[0] <= i_gate;
            for (int s = 1; s < SYNC_STAGES; s++) begin
                r_gate_sync[s] <= r_gate_sync[s-1];
            end
        end
    )

    assign w_gate = r_gate_sync[SYNC_STAGES-1];

    //========================================================================
    // Clock Enable
    //========================================================================

    assign w_clk_en = cfg_pit_enable;

    //========================================================================
    // Control Word Decode
    //========================================================================

    always_comb begin
        w_control_wr_strobe = '0;
        w_latch_cmd_strobe  = '0;
        for (int n = 0; n < NUM_COUNTERS; n++) begin
            if (cfg_control_wr && (cfg_counter_select == 2'(n))) begin
                if (cfg_rw_mode == RW_LATCH) begin
                    w_latch_cmd_strobe[n] = 1'b1;
                end else begin
                    w_control_wr_strobe[n] = 1'b1;
                end
            end
        end
        // counter_select = 11 (read-back command) matches no n and therefore
        // strobes nothing - see the header.
    end

    //========================================================================
    // Counter Data Strobes (from pit_config_regs, already one cycle wide)
    //========================================================================

    assign w_count_reg_wr[0] = counter0_reg_wr;
    assign w_count_reg_wr[1] = counter1_reg_wr;
    assign w_count_reg_wr[2] = counter2_reg_wr;

    assign w_count_reg_rd[0] = counter0_reg_rd;
    assign w_count_reg_rd[1] = counter1_reg_rd;
    assign w_count_reg_rd[2] = counter2_reg_rd;

    //========================================================================
    // Counter Instances
    //========================================================================
    // Kept as three named instances rather than a generate loop: u_counter0/1/2
    // are the hierarchical paths the white-box tests reach through
    // (dv/tbclasses/pit_8254/pit_tb.py counter_internal()), and a generate loop
    // would rename them to g_counters[N].u_counter.

    pit_counter u_counter0 (
        .clk                (clk),
        .rst_n              (rst_n),
        // Configuration
        .cfg_bcd            (cfg_bcd),
        .cfg_mode           (cfg_mode),
        .cfg_rw_mode        (cfg_rw_mode),
        .cfg_control_wr     (w_control_wr_strobe[0]),
        .cfg_latch_cmd      (w_latch_cmd_strobe[0]),
        // Counter data
        .count_reg_in       (counter0_reg_in),
        .count_reg_wr       (w_count_reg_wr[0]),
        .count_reg_rd       (w_count_reg_rd[0]),
        .count_reg_out      (counter0_reg_out),
        // Hardware interface
        .i_gate             (w_gate[0]),
        .i_clk_en           (w_clk_en),
        .o_out              (o_out[0]),
        // Status
        .o_null_count       (w_null_count[0]),
        .o_status_rw_mode   (w_status_rw_mode[0]),
        .o_status_mode      (w_status_mode[0]),
        .o_status_bcd       (w_status_bcd[0])
    );

    pit_counter u_counter1 (
        .clk                (clk),
        .rst_n              (rst_n),
        // Configuration
        .cfg_bcd            (cfg_bcd),
        .cfg_mode           (cfg_mode),
        .cfg_rw_mode        (cfg_rw_mode),
        .cfg_control_wr     (w_control_wr_strobe[1]),
        .cfg_latch_cmd      (w_latch_cmd_strobe[1]),
        // Counter data
        .count_reg_in       (counter1_reg_in),
        .count_reg_wr       (w_count_reg_wr[1]),
        .count_reg_rd       (w_count_reg_rd[1]),
        .count_reg_out      (counter1_reg_out),
        // Hardware interface
        .i_gate             (w_gate[1]),
        .i_clk_en           (w_clk_en),
        .o_out              (o_out[1]),
        // Status
        .o_null_count       (w_null_count[1]),
        .o_status_rw_mode   (w_status_rw_mode[1]),
        .o_status_mode      (w_status_mode[1]),
        .o_status_bcd       (w_status_bcd[1])
    );

    pit_counter u_counter2 (
        .clk                (clk),
        .rst_n              (rst_n),
        // Configuration
        .cfg_bcd            (cfg_bcd),
        .cfg_mode           (cfg_mode),
        .cfg_rw_mode        (cfg_rw_mode),
        .cfg_control_wr     (w_control_wr_strobe[2]),
        .cfg_latch_cmd      (w_latch_cmd_strobe[2]),
        // Counter data
        .count_reg_in       (counter2_reg_in),
        .count_reg_wr       (w_count_reg_wr[2]),
        .count_reg_rd       (w_count_reg_rd[2]),
        .count_reg_out      (counter2_reg_out),
        // Hardware interface
        .i_gate             (w_gate[2]),
        .i_clk_en           (w_clk_en),
        .o_out              (o_out[2]),
        // Status
        .o_null_count       (w_null_count[2]),
        .o_status_rw_mode   (w_status_rw_mode[2]),
        .o_status_mode      (w_status_mode[2]),
        .o_status_bcd       (w_status_bcd[2])
    );

    //========================================================================
    // Status Byte Assembly
    //========================================================================
    // 8254 read-back status byte:
    //   [7] OUT  [6] NULL COUNT  [5:4] RW_MODE  [3:1] MODE  [0] BCD

    assign counter0_status = {
        o_out[0],
        w_null_count[0],
        w_status_rw_mode[0],
        w_status_mode[0],
        w_status_bcd[0]
    };

    assign counter1_status = {
        o_out[1],
        w_null_count[1],
        w_status_rw_mode[1],
        w_status_mode[1],
        w_status_bcd[1]
    };

    assign counter2_status = {
        o_out[2],
        w_null_count[2],
        w_status_rw_mode[2],
        w_status_mode[2],
        w_status_bcd[2]
    };

endmodule
