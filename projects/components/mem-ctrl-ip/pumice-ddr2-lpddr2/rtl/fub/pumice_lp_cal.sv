// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: pumice_lp_cal
// Purpose: One-shot LPDDR2 DQ-calibration sequencer. Issues MRR reads to
//          MR32 (pattern A) and MR40 (pattern B), captures the first beat of
//          each return, and exposes the captured data to firmware. The actual
//          DQ-vs-tap sweep lives outside the core; this module only provides
//          the MRR engine and capture sideband.
//
//          Run condition: init_done_i && (memtype_i == MEMTYPE_LPDDR2).
//          DDR2 has no MRR, so the FUB is inert for DDR2 builds.
//
// Documentation:
//   projects/components/mem-ctrl-ip/pumice-ddr2-lpddr2/docs/uarch/PUMICE_TRAINING_LAYER_UARCH.md
//
// Author: sean galloway
// Created: 2026-10-07

`timescale 1ns / 1ps

`include "reset_defs.svh"

module pumice_lp_cal
    import pumice_pkg::*;
#(
    parameter int DFI_DATA_WIDTH = 128,
    parameter int MR32_INDEX     = 32,
    parameter int MR40_INDEX     = 40
) (
    input  logic                      mc_clk,
    input  logic                      mc_rst_n,

    // ----- run-time enable / build guard ------------------------------------
    input  logic                      cal_start_i,    // pulse to start one shot
    input  logic                      cal_abort_i,    // pulse to cancel
    input  logic                      init_done_i,
    input  memtype_e                  memtype_i,

    // ----- timing -----------------------------------------------------------
    input  logic [15:0]               t_mrr_i,        // MRR-to-MRR spacing
    input  logic [15:0]               t_readout_i,    // issue -> data timeout

    // ----- maintenance command channel to arbiter ---------------------------
    output logic                      cmd_req_o,
    input  logic                      cmd_grant_i,
    output dram_op_e                  cmd_op_o,       // OP_MRS
    output logic [2:0]                cmd_bank_o,     // 0
    output logic [17:0]               cmd_row_o,      // {MA[5:0], OP[7:0]}
    output logic                      cmd_mrr_o,      // formatter MRR select

    // ----- calibration capture handshake (mc_clk domain) --------------------
    // cal_expect_o arms the DFI-layer read-aligner sideband.
    // cal_data_i / cal_data_valid_i carry the synchronized-up captured beat.
    output logic                      cal_expect_o,
    input  logic [DFI_DATA_WIDTH-1:0] cal_data_i,
    input  logic                      cal_data_valid_i,

    output logic [DFI_DATA_WIDTH-1:0] mrr32_data_o,
    output logic [DFI_DATA_WIDTH-1:0] mrr40_data_o,
    output logic                      mrr32_valid_o,
    output logic                      mrr40_valid_o,

    // ----- status -----------------------------------------------------------
    output logic                      cal_busy_o,
    output logic                      cal_done_o,     // sticky
    output logic                      cal_err_o       // sticky
);

    //=========================================================================
    // State
    //=========================================================================
    typedef enum logic [2:0] {
        CAL_IDLE          = 3'd0,
        CAL_WAIT_GRANT32  = 3'd1,
        CAL_PULSE_EXPECT32= 3'd2,
        CAL_WAIT_DATA32   = 3'd3,
        CAL_WAIT_TMRR     = 3'd4,
        CAL_WAIT_GRANT40  = 3'd5,
        CAL_PULSE_EXPECT40= 3'd6,
        CAL_WAIT_DATA40   = 3'd7
    } cal_state_e;

    cal_state_e r_state;
    logic [15:0] r_timer;
    logic [15:0] r_timeout;
    logic        r_done;
    logic        r_err;
    logic [DFI_DATA_WIDTH-1:0] r_mrr32_data;
    logic [DFI_DATA_WIDTH-1:0] r_mrr40_data;
    logic        r_mrr32_valid;
    logic        r_mrr40_valid;

    logic w_run;
    assign w_run = init_done_i && (memtype_i == MEMTYPE_LPDDR2);

    // Command payload helpers.
    function automatic logic [17:0] mrr_row(input logic [5:0] ma);
        return {4'd0, ma, 8'd0};   // OP field = 0 for MRR
    endfunction

    //=========================================================================
    // Control FSM
    //=========================================================================
    `ALWAYS_FF_RST(mc_clk, mc_rst_n, begin
        if (`RST_ASSERTED(mc_rst_n)) begin
            r_state       <= CAL_IDLE;
            r_timer       <= 16'd0;
            r_timeout     <= 16'd0;
            r_done        <= 1'b0;
            r_err         <= 1'b0;
            r_mrr32_data  <= '0;
            r_mrr40_data  <= '0;
            r_mrr32_valid <= 1'b0;
            r_mrr40_valid <= 1'b0;
        end else if (cal_abort_i || !w_run) begin
            r_state       <= CAL_IDLE;
            r_timer       <= 16'd0;
            r_timeout     <= 16'd0;
            // sticky done/err are NOT cleared by abort; soft reset clears them
            r_mrr32_valid <= r_mrr32_valid && !cal_abort_i;
            r_mrr40_valid <= r_mrr40_valid && !cal_abort_i;
        end else begin
            unique case (r_state)
                CAL_IDLE: begin
                    if (cal_start_i) begin
                        r_state   <= CAL_WAIT_GRANT32;
                        r_done    <= 1'b0;
                        r_err     <= 1'b0;
                        r_mrr32_valid <= 1'b0;
                        r_mrr40_valid <= 1'b0;
                    end
                end

                CAL_WAIT_GRANT32: begin
                    if (cmd_grant_i) begin
                        r_state   <= CAL_PULSE_EXPECT32;
                        r_timeout <= t_readout_i;
                    end
                end

                CAL_PULSE_EXPECT32: begin
                    r_state <= CAL_WAIT_DATA32;
                end

                CAL_WAIT_DATA32: begin
                    if (cal_data_valid_i) begin
                        r_mrr32_data  <= cal_data_i;
                        r_mrr32_valid <= 1'b1;
                        r_state       <= CAL_WAIT_TMRR;
                        r_timer       <= t_mrr_i;
                    end else if (r_timeout == 16'd0) begin
                        r_err   <= 1'b1;
                        r_done  <= 1'b1;
                        r_state <= CAL_IDLE;
                    end else begin
                        r_timeout <= r_timeout - 16'd1;
                    end
                end

                CAL_WAIT_TMRR: begin
                    if (r_timer == 16'd0) begin
                        r_state <= CAL_WAIT_GRANT40;
                    end else begin
                        r_timer <= r_timer - 16'd1;
                    end
                end

                CAL_WAIT_GRANT40: begin
                    if (cmd_grant_i) begin
                        r_state   <= CAL_PULSE_EXPECT40;
                        r_timeout <= t_readout_i;
                    end
                end

                CAL_PULSE_EXPECT40: begin
                    r_state <= CAL_WAIT_DATA40;
                end

                CAL_WAIT_DATA40: begin
                    if (cal_data_valid_i) begin
                        r_mrr40_data  <= cal_data_i;
                        r_mrr40_valid <= 1'b1;
                        r_done        <= 1'b1;
                        r_state       <= CAL_IDLE;
                    end else if (r_timeout == 16'd0) begin
                        r_err   <= 1'b1;
                        r_done  <= 1'b1;
                        r_state <= CAL_IDLE;
                    end else begin
                        r_timeout <= r_timeout - 16'd1;
                    end
                end

                default: r_state <= CAL_IDLE;
            endcase
        end
    end)

    //=========================================================================
    // Output assignment
    //=========================================================================
    assign cmd_op_o   = OP_MRS;
    assign cmd_bank_o = 3'd0;
    assign cmd_mrr_o  = 1'b1;

    always_comb begin
        cmd_row_o   = 18'd0;
        cmd_req_o   = 1'b0;
        cal_expect_o= 1'b0;
        unique case (r_state)
            CAL_WAIT_GRANT32: begin
                cmd_req_o = 1'b1;
                cmd_row_o = mrr_row(MR32_INDEX[5:0]);
            end
            CAL_PULSE_EXPECT32: begin
                cal_expect_o = 1'b1;
                cmd_row_o    = mrr_row(MR32_INDEX[5:0]);
            end
            CAL_WAIT_GRANT40: begin
                cmd_req_o = 1'b1;
                cmd_row_o = mrr_row(MR40_INDEX[5:0]);
            end
            CAL_PULSE_EXPECT40: begin
                cal_expect_o = 1'b1;
                cmd_row_o    = mrr_row(MR40_INDEX[5:0]);
            end
            default: ;
        endcase
    end

    assign cal_busy_o    = (r_state != CAL_IDLE);
    assign cal_done_o    = r_done;
    assign cal_err_o     = r_err;
    assign mrr32_data_o  = r_mrr32_data;
    assign mrr40_data_o  = r_mrr40_data;
    assign mrr32_valid_o = r_mrr32_valid;
    assign mrr40_valid_o = r_mrr40_valid;

endmodule : pumice_lp_cal
