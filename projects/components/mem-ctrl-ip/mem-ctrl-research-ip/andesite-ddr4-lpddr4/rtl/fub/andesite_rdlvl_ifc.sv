// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: andesite_rdlvl_ifc
// Purpose: DDR4 MPR read-leveling interface
//
// Documentation:
//   projects/components/mem-ctrl-ip/mem-ctrl-research-ip/andesite-ddr4-lpddr4/docs/andesite_mas/
//
// New block per andesite_mas ch02_blocks/09_training.md: sequences MPR
// entry (MRW of the CSR MR3 image), the DFI read-leveling handshake,
// pattern capture per chip select, MPR exit, and the four-state telemetry
// the family page fences. No search states -- the host walks the delay
// line by re-asserting rdlvl_en_i with a new setting. The MR3 images are
// CSR inputs: the RTL makes no MPR-bit-position claim (HAS Q1).
//
// Author: sean galloway
// Created: 2026-10-04 (andesite, NEW)

`timescale 1ns / 1ps

`include "reset_defs.svh"

module andesite_rdlvl_ifc
    import andesite_pkg::*;
#(
    parameter int NUM_CS = 1,
    parameter int CSW    = (NUM_CS > 1) ? $clog2(NUM_CS) : 1
)(
    input  logic                 mc_clk,
    input  logic                 mc_rst_n,

    // host sweep: one assertion of enable = one delay setting
    input  logic                 rdlvl_en_i,
    input  logic [CSW-1:0]       cs_sel_i,

    // MR3 images (MPR enable + pattern select / MPR disable), CSR inputs
    input  logic [15:0]          csr_mr3_mpr_enter_i,
    input  logic [15:0]          csr_mr3_mpr_exit_i,

    // runtime CSRs, JESD79-4 speed-bin derived
    input  logic [15:0]          t_mpr_enter_i,    // MRW ack -> pattern valid
    input  logic [15:0]          t_mpr_exit_i,     // MRW ack -> MPR off
    input  logic [15:0]          t_mpr_readout_i,  // capture window
    input  logic [15:0]          tmod_i,           // post-MRW command gap
    input  logic [15:0]          t_rdlvl_timeout_i,// handshake window (0 = none)

    // observed pattern on DQ this sweep (datapath presents it)
    input  logic                 mpr_pattern_i,

    // MRW command path (same request/ack shape as the init sequencer)
    output logic                 cmd_req_o,
    input  logic                 cmd_ack_i,
    output dram_op_e             cmd_op_o,
    output logic [2:0]           cmd_bank_o,   // MR index (3 = MR3)
    output logic [15:0]          cmd_addr_o,   // the MR3 image

    // DFI read-leveling handshake, active-low per chip select
    input  logic [NUM_CS-1:0]    dfi_phylvl_req_cs_n_i,
    output logic [NUM_CS-1:0]    dfi_phylvl_ack_cs_n_o,
    output logic [NUM_CS-1:0]    dfi_phy_rdlvl_cs_n_o,

    // result + the family's four-state telemetry
    output logic                 result_valid_o,
    output logic [NUM_CS-1:0]    result_o,
    output logic [1:0]           status_o,
    output logic [15:0]          obs_attempts_o,
    output logic [15:0]          obs_results_o,
    output logic [15:0]          obs_timeouts_o,
    output logic [2:0]           obs_state_o
);

    // MAS 09 fence: IDLE -> MPR_ENTRY -> HANDSHAKE -> CAPTURE -> MPR_EXIT
    //               -> REPORT -> IDLE
    typedef enum logic [2:0] {
        ST_IDLE      = 3'd0,
        ST_MPR_ENTRY = 3'd1,
        ST_HANDSHAKE = 3'd2,
        ST_CAPTURE   = 3'd3,
        ST_MPR_EXIT  = 3'd4,
        ST_REPORT    = 3'd5
    } state_e;

    // three-state telemetry: 00 never, 01 converged, 10 timed out. The 2-bit
    // space keeps 11 reserved -- no live condition ever drives it (review M-3).
    typedef enum logic [1:0] {
        TELEM_NEVER   = 2'b00,
        TELEM_CONVERGED = 2'b01,
        TELEM_TIMEOUT = 2'b10
    } telemetry_e;

    state_e               r_state;
    logic [15:0]          r_cnt;
    logic [15:0]          r_timeout_cnt;
    logic                 r_mr_enter;   // 1: request the enter image
    logic [15:0]          r_attempts, r_results, r_timeouts;
    logic [NUM_CS-1:0]    r_result;
    telemetry_e           r_status;

    assign obs_state_o   = r_state;
    assign status_o      = r_status;
    assign obs_attempts_o  = r_attempts;
    assign obs_results_o   = r_results;
    assign obs_timeouts_o  = r_timeouts;
    assign result_o        = r_result;

    `ALWAYS_FF_RST(mc_clk, mc_rst_n, begin
        if (`RST_ASSERTED(mc_rst_n)) begin
            r_state        <= ST_IDLE;
            r_cnt          <= 16'd0;
            r_timeout_cnt  <= 16'd0;
            r_mr_enter     <= 1'b1;
            r_attempts     <= 16'd0;
            r_results      <= 16'd0;
            r_timeouts     <= 16'd0;
            r_result       <= '0;
            r_status       <= TELEM_NEVER;
            cmd_req_o      <= 1'b0;
            result_valid_o <= 1'b0;
        end else begin
            result_valid_o <= 1'b0;
            unique case (r_state)
                ST_IDLE: begin
                    if (rdlvl_en_i) begin
                        r_state    <= ST_MPR_ENTRY;
                        r_mr_enter <= 1'b1;
                        r_cnt      <= 16'd0;
                        if (r_attempts != 16'hFFFF) begin
                            r_attempts <= r_attempts + 16'd1;
                        end
                    end
                end

                // MPR_ENTRY / MPR_EXIT share the MRW request shape; the
                // r_mr_enter flag selects the image. tMOD counts after the
                // ack, then the entry/exit interval. (Written as two case
                // labels, not a comma pair: commas inside the reset-macro
                // argument list do not survive the preprocessor.)
                ST_MPR_ENTRY: begin
                    if (!cmd_req_o && (r_cnt == 16'd0)) begin
                        cmd_req_o <= 1'b1;   // request this cycle
                    end else if (cmd_req_o && cmd_ack_i) begin
                        cmd_req_o <= 1'b0;
                        r_cnt     <= tmod_i;
                    end else if (r_cnt != 16'd0) begin
                        r_cnt <= r_cnt - 16'd1;
                        if (r_cnt == 16'd1) begin
                            // tMOD expired: the entry interval runs next
                            r_cnt   <= t_mpr_enter_i;
                            r_state <= ST_HANDSHAKE;
                        end
                    end
                end

                ST_MPR_EXIT: begin
                    if (!cmd_req_o && (r_cnt == 16'd0)) begin
                        cmd_req_o <= 1'b1;   // request this cycle
                    end else if (cmd_req_o && cmd_ack_i) begin
                        cmd_req_o <= 1'b0;
                        r_cnt     <= tmod_i;
                    end else if (r_cnt != 16'd0) begin
                        r_cnt <= r_cnt - 16'd1;
                        if (r_cnt == 16'd1) begin
                            // tMOD expired: the exit interval runs next
                            r_cnt   <= t_mpr_exit_i;
                            r_state <= ST_REPORT;
                        end
                    end
                end

                ST_HANDSHAKE: begin
                    // drive ack + rdlvl for the selected CS while the PHY's
                    // active-low request is asserted; transition to CAPTURE on
                    // req assertion, bounded by the timeout CSR.
                    if (!dfi_phylvl_req_cs_n_i[cs_sel_i]) begin
                        r_state       <= ST_CAPTURE;
                        r_cnt         <= t_mpr_readout_i;
                        r_timeout_cnt <= 16'd0;
                    end else if ((t_rdlvl_timeout_i != 16'd0)
                                 && (r_timeout_cnt >= t_rdlvl_timeout_i)) begin
                        r_state       <= ST_REPORT;
                        r_status      <= TELEM_TIMEOUT;
                        r_timeout_cnt <= 16'd0;
                        if (r_timeouts != 16'hFFFF) begin
                            r_timeouts <= r_timeouts + 16'd1;
                        end
                    end else begin
                        r_timeout_cnt <= r_timeout_cnt + 16'd1;
                    end
                end

                ST_CAPTURE: begin
                    if (r_cnt == 16'd0) begin
                        r_result[cs_sel_i] <= mpr_pattern_i;
                        r_mr_enter         <= 1'b0;
                        r_state            <= ST_MPR_EXIT;
                        r_cnt              <= 16'd0;
                    end else begin
                        r_cnt <= r_cnt - 16'd1;
                    end
                end

                ST_REPORT: begin
                    // converged unless HANDSHAKE already set TIMEOUT; a
                    // result counts only on convergence.
                    if (r_status != TELEM_TIMEOUT) begin
                        r_status <= TELEM_CONVERGED;
                        if (r_results != 16'hFFFF) begin
                            r_results <= r_results + 16'd1;
                        end
                    end
                    result_valid_o <= 1'b1;
                    r_state        <= ST_IDLE;
                end

                default: r_state <= ST_IDLE;
            endcase
        end
    end)

    // command image: the MR3 index and the enter/exit image
    assign cmd_op_o   = OP_MRS;
    assign cmd_bank_o = 3'd3;
    assign cmd_addr_o = r_mr_enter ? csr_mr3_mpr_enter_i
                                   : csr_mr3_mpr_exit_i;

    // handshake drive: asserted only while in HANDSHAKE (the PHY samples
    // with its own req/grant cycle)
    assign dfi_phylvl_ack_cs_n_o = (r_state == ST_HANDSHAKE)
                                   ? ~(NUM_CS'(1'b1) << cs_sel_i) : '1;
    assign dfi_phy_rdlvl_cs_n_o  = (r_state == ST_HANDSHAKE)
                                   ? ~(NUM_CS'(1'b1) << cs_sel_i) : '1;

endmodule : andesite_rdlvl_ifc
