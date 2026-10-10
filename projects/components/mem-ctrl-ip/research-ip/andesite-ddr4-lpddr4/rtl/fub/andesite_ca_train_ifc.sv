// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: andesite_ca_train_ifc
// Purpose: LPDDR4 CA / WDQ training interface
//
// Documentation:
//   projects/components/mem-ctrl-ip/research-ip/andesite-ddr4-lpddr4/docs/andesite_mas/
//
// New block per andesite_mas ch02_blocks/09_training.md: both flows ride
// MPC opcodes through the formatter's LPDDR4 CA path; the issuer shape is
// reused with `zq_ctrl`'s MPC submodule. The opcode encodings are CSR
// images, TBC(JESD209-4) -- driven at the protocol level, never decoded;
// no MPC opcode encodings are invented anywhere in andesite. State is per
// channel; the four-state telemetry and three counters match the family
// page.
//
// Author: sean galloway
// Created: 2026-10-04 (andesite, NEW)

`timescale 1ns / 1ps

`include "reset_defs.svh"

module andesite_ca_train_ifc
    import andesite_pkg::*;
    import mc_common_pkg::*;   // Vivado: pkg export of the family symbols is not honored; import explicitly
(
    input  logic                 mc_clk,
    input  logic                 mc_rst_n,

    // one assertion = one host adjustment round, per flow
    input  logic                 ca_train_en_i,
    input  logic                 wdq_cal_en_i,
    input  logic                 chan_sel_i,   // LPDDR4 x16 channels train alone

    // MPC opcode images (CSR; encodings TBC(JESD209-4))
    input  logic [5:0]           csr_mpc_ca_enter_i,
    input  logic [5:0]           csr_mpc_ca_exit_i,
    input  logic [5:0]           csr_mpc_wdq_enter_i,
    input  logic [5:0]           csr_mpc_wdq_exit_i,

    // sample windows + handshake bound, runtime CSRs (JESD209-4 speed bin)
    input  logic [15:0]          t_ca_train_i,
    input  logic [15:0]          t_wdq_cal_i,
    input  logic [15:0]          t_ca_timeout_i,   // 0 = no bound

    // observations presented by the datapath
    input  logic                 ca_sample_i,
    input  logic                 wdq_sample_i,

    // MPC issue path (protocol-level: OP_MPC + the image)
    output logic                 cmd_req_o,
    input  logic                 cmd_ack_i,
    output dram_op_e             cmd_op_o,
    output logic [5:0]           mpc_op_o,

    // result + family telemetry
    output logic                 result_valid_o,
    output logic [1:0]           result_o,     // per channel
    output logic [1:0]           status_o,
    output logic [15:0]          obs_attempts_o,
    output logic [15:0]          obs_results_o,
    output logic [15:0]          obs_timeouts_o,
    output logic [2:0]           obs_state_o
);

    // MAS 09 shape: IDLE -> MPC_ENTER -> SAMPLE -> MPC_EXIT -> REPORT ->
    // IDLE, for each flow; the flow select picks the opcode images and the
    // sample window.
    typedef enum logic [2:0] {
        ST_IDLE      = 3'd0,
        ST_MPC_ENTER = 3'd1,
        ST_SAMPLE    = 3'd2,
        ST_MPC_EXIT  = 3'd3,
        ST_REPORT    = 3'd4
    } state_e;

    // three-state telemetry: 00 never, 01 converged, 10 timed out. The 2-bit
    // space keeps 11 reserved -- no live condition ever drives it (review M-3).
    typedef enum logic [1:0] {
        TELEM_NEVER    = 2'b00,
        TELEM_CONVERGED = 2'b01,
        TELEM_TIMEOUT  = 2'b10
    } telemetry_e;

    typedef enum logic [1:0] {
        FLOW_CA  = 2'd0,
        FLOW_WDQ = 2'd1
    } flow_e;

    state_e       r_state;
    flow_e        r_flow;
    logic         r_exit;          // 1: the exit image goes out next
    logic [15:0]  r_cnt;
    logic [15:0]  r_timeout_cnt;
    logic [15:0]  r_attempts, r_results, r_timeouts;
    logic [1:0]   r_result;
    telemetry_e   r_status;

    assign obs_state_o    = r_state;
    assign status_o       = r_status;
    assign obs_attempts_o = r_attempts;
    assign obs_results_o  = r_results;
    assign obs_timeouts_o = r_timeouts;
    assign result_o       = r_result;

    `ALWAYS_FF_RST(mc_clk, mc_rst_n, begin
        if (`RST_ASSERTED(mc_rst_n)) begin
            r_state        <= ST_IDLE;
            r_flow         <= FLOW_CA;
            r_exit         <= 1'b0;
            r_cnt          <= 16'd0;
            r_timeout_cnt  <= 16'd0;
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
                    if (ca_train_en_i || wdq_cal_en_i) begin
                        r_state       <= ST_MPC_ENTER;
                        r_flow        <= ca_train_en_i ? FLOW_CA : FLOW_WDQ;
                        r_exit        <= 1'b0;
                        r_cnt         <= 16'd0;
                        r_timeout_cnt <= 16'd0;
                        if (r_attempts != 16'hFFFF) begin
                            r_attempts <= r_attempts + 16'd1;
                        end
                    end
                end

                // MPC_ENTER / MPC_EXIT share the request shape; r_exit
                // selects the image. Timeout bounds the enter handshake.
                ST_MPC_ENTER: begin
                    if (!cmd_req_o && (r_cnt == 16'd0)) begin
                        cmd_req_o <= 1'b1;
                    end else if (cmd_req_o && cmd_ack_i) begin
                        cmd_req_o <= 1'b0;
                        r_cnt     <= r_flow == FLOW_CA ? t_ca_train_i
                                                       : t_wdq_cal_i;
                    end else if (r_cnt != 16'd0) begin
                        r_cnt <= r_cnt - 16'd1;
                        if (r_cnt == 16'd1) begin
                            r_cnt   <= 16'd0;
                            if (r_exit) begin
                                r_state <= ST_REPORT;
                            end else begin
                                r_state <= ST_SAMPLE;
                            end
                        end
                    end else if ((t_ca_timeout_i != 16'd0)
                                 && (r_timeout_cnt >= t_ca_timeout_i)) begin
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

                ST_SAMPLE: begin
                    if (r_flow == FLOW_CA) begin
                        r_result[chan_sel_i] <= ca_sample_i;
                    end else begin
                        r_result[chan_sel_i] <= wdq_sample_i;
                    end
                    r_exit        <= 1'b1;
                    r_state       <= ST_MPC_ENTER;   // second pass drives the exit
                    r_cnt         <= 16'd0;
                    // M-4: the exit pass gets its own timeout budget instead
                    // of inheriting the enter pass's accumulated count.
                    r_timeout_cnt <= 16'd0;
                end

                ST_REPORT: begin
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

    assign cmd_op_o = OP_MPC;
    assign mpc_op_o = !r_exit ? ((r_flow == FLOW_CA) ? csr_mpc_ca_enter_i
                                                     : csr_mpc_wdq_enter_i)
                              : ((r_flow == FLOW_CA) ? csr_mpc_ca_exit_i
                                                     : csr_mpc_wdq_exit_i);

endmodule : andesite_ca_train_ifc
