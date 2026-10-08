// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: pumice_zq_ctrl
// Purpose: Periodic ZQ calibration (ZQCS/ZQCL) as maintenance traffic for
//          LPDDR2. LPDDR2 has no dedicated ZQCS/ZQCL command; both are MRW
//          writes to MR10 (OP = 0x56 for ZQCS, 0xAB for ZQCL). This FUB only
//          raises requests and holds the post-grant bus-quiet window; the
//          arbiter emits the actual MRW command with the row packed as
//          {MR10_index, OP}.
//
//          Run condition: zq_en_i && init_done_i && memtype_i==MEMTYPE_LPDDR2.
//          DDR2 has no ZQ pin, so the FUB is inert for DDR2 builds.
//
// Documentation:
//   projects/components/mem-ctrl-ip/pumice-ddr2-lpddr2/docs/uarch/PUMICE_TRAINING_LAYER_UARCH.md
//
// Author: sean galloway
// Created: 2026-10-07

`timescale 1ns / 1ps

`include "reset_defs.svh"

module pumice_zq_ctrl
    import pumice_pkg::*;
#(
    parameter int MR10_INDEX = 10
) (
    input  logic        mc_clk,
    input  logic        mc_rst_n,

    // ----- run-time enable / build guard ------------------------------------
    input  logic        zq_en_i,          // CSR CAL_CTRL.zq_en
    input  logic        init_done_i,      // scheduler init complete
    input  memtype_e    memtype_i,        // MEMTYPE_LPDDR2 required

    // ----- configuration ----------------------------------------------------
    input  logic [31:0] t_zqcs_interval_i,// MC cycles between calibrations, 0=off
    input  logic [15:0] t_zqcs_i,         // post-grant hold for ZQCS
    input  logic [15:0] t_zqcl_i,         // post-grant hold for ZQCL

    // Mode-C placement policy
    input  logic        zq_defer_en_i,    // 1 = defer under sustained demand
    input  logic [12:0] overdue_max_i,    // max deferral cycles (0 = no cap)

    // ----- arbiter interface (identical shape to refresh_ctrl) -------------
    input  logic        demand_i,         // scheduler has read/write work
    output logic        zq_req_o,
    input  logic        zq_grant_i,

    // ----- command payload selected on grant --------------------------------
    output dram_op_e    zq_op_o,          // always OP_MRS
    output logic [2:0]  zq_bank_o,        // 0 (MR index lives in row field)
    output logic [17:0] zq_row_o,         // {MR10_index[5:0], OP[7:0]}
    output logic        zq_is_zqcl_o,     // 1 = this grant is a ZQCL

    // ----- post-grant hold / telemetry --------------------------------------
    output logic        cal_busy_o,       // bus must be quiet
    output logic [15:0] obs_zqcs_total_o, // calibrations issued since reset
    output logic        obs_overdue_o     // interval expired, still no grant
);

    localparam logic [7:0] ZQCS_OP = 8'h56;
    localparam logic [7:0] ZQCL_OP = 8'hAB;

    //=========================================================================
    // State
    //=========================================================================
    typedef enum logic [1:0] {
        ZQ_IDLE  = 2'd0,
        ZQ_REQ   = 2'd1,
        ZQ_HOLD  = 2'd2,
        ZQ_DEFER = 2'd3
    } zq_state_e;

    zq_state_e   r_state;
    logic [31:0] r_interval;
    logic [15:0] r_hold;
    logic [15:0] r_total;
    logic        r_overdue;
    logic [12:0] r_defer_cnt;
    logic        r_is_zqcl;   // selected op for the current request

    logic w_interval_valid;
    assign w_interval_valid = (t_zqcs_interval_i != 32'd0);

    logic w_run;
    assign w_run = zq_en_i && init_done_i && (memtype_i == MEMTYPE_LPDDR2) && w_interval_valid;

    `ALWAYS_FF_RST(mc_clk, mc_rst_n, begin
        if (`RST_ASSERTED(mc_rst_n)) begin
            r_state     <= ZQ_IDLE;
            r_interval  <= t_zqcs_interval_i;
            r_hold      <= 16'd0;
            r_total     <= 16'd0;
            r_overdue   <= 1'b0;
            r_defer_cnt <= 13'd0;
            r_is_zqcl   <= 1'b0;
        end else if (!w_run) begin
            r_state     <= ZQ_IDLE;
            r_interval  <= t_zqcs_interval_i;
            r_overdue   <= 1'b0;
            r_defer_cnt <= 13'd0;
            r_is_zqcl   <= 1'b0;
        end else begin
            unique case (r_state)
                ZQ_IDLE: begin
                    if (r_interval == 32'd0) begin
                        if (zq_defer_en_i && demand_i) begin
                            r_state     <= ZQ_DEFER;
                            r_defer_cnt <= 13'd0;
                            r_overdue   <= 1'b0;
                            r_is_zqcl   <= 1'b0;
                        end else begin
                            r_state   <= ZQ_REQ;
                            r_overdue <= 1'b0;
                            r_is_zqcl <= 1'b0;
                        end
                    end else begin
                        r_interval <= r_interval - 32'd1;
                    end
                end

                ZQ_REQ: begin
                    if (zq_grant_i) begin
                        r_state   <= ZQ_HOLD;
                        r_hold    <= r_is_zqcl ? t_zqcl_i : t_zqcs_i;
                        r_total   <= r_total + 16'd1;
                        r_overdue <= 1'b0;
                    end else if (demand_i) begin
                        r_overdue <= 1'b1;
                    end
                end

                ZQ_HOLD: begin
                    if (r_hold == 16'd0) begin
                        r_state    <= ZQ_IDLE;
                        r_interval <= t_zqcs_interval_i;
                    end else begin
                        r_hold <= r_hold - 16'd1;
                    end
                end

                ZQ_DEFER: begin
                    // Hold under demand. Exit on loss of demand, policy change,
                    // or overdue limit. An overdue deferral requests ZQCL.
                    if (!zq_defer_en_i || !demand_i) begin
                        r_state     <= ZQ_REQ;
                        r_defer_cnt <= 13'd0;
                        r_is_zqcl   <= (r_defer_cnt != 13'd0);
                    end else if (overdue_max_i != 13'd0 &&
                                 r_defer_cnt >= overdue_max_i) begin
                        r_state     <= ZQ_REQ;
                        r_defer_cnt <= 13'd0;
                        r_is_zqcl   <= 1'b1;
                    end else begin
                        r_defer_cnt <= r_defer_cnt + 13'd1;
                        r_is_zqcl   <= 1'b0;
                    end
                    r_overdue <= 1'b1;
                end

                default: r_state <= ZQ_IDLE;
            endcase
        end
    end)

    //=========================================================================
    // Outputs
    //=========================================================================
    `ALWAYS_FF_RST(mc_clk, mc_rst_n, begin
        if (`RST_ASSERTED(mc_rst_n)) begin
            zq_req_o         <= 1'b0;
            cal_busy_o       <= 1'b0;
            obs_zqcs_total_o <= 16'd0;
            obs_overdue_o    <= 1'b0;
            zq_op_o          <= OP_NOP;
            zq_bank_o        <= 3'd0;
            zq_row_o         <= 18'd0;
            zq_is_zqcl_o     <= 1'b0;
        end else begin
            zq_req_o         <= (r_state == ZQ_REQ);
            cal_busy_o       <= (r_state == ZQ_HOLD);
            obs_zqcs_total_o <= r_total;
            obs_overdue_o    <= r_overdue;
            zq_op_o          <= OP_MRS;
            zq_bank_o        <= 3'd0;
            // MRW row packing: {MA[5:0], OP[7:0]}; MA[7:6]=0.
            zq_row_o         <= {4'd0, MR10_INDEX[5:0], r_is_zqcl ? ZQCL_OP : ZQCS_OP};
            zq_is_zqcl_o     <= r_is_zqcl;
        end
    end)

endmodule : pumice_zq_ctrl
