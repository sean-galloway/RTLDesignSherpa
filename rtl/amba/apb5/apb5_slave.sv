// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: apb5_slave
// Purpose: APB5 Slave with AMBA5 extensions
//
// APB5 Extensions:
// - PAUSER: User-defined request attributes (from master)
// - PWUSER: User-defined write data attributes (from master)
// - PRUSER: User-defined read data attributes (to master)
// - PBUSER: User-defined response attributes (to master)
// - PWAKEUP: Wake-up signal (to master)
// - Optional parity support for data integrity
//
// Documentation: rtl/amba/PRD.md
// Subsystem: amba
//
// Author: sean galloway
// Created: 2025-12-21

`timescale 1ns / 1ps

`include "reset_defs.svh"

module apb5_slave #(
    parameter int ADDR_WIDTH      = 32,
    parameter int DATA_WIDTH      = 32,
    parameter int STRB_WIDTH      = DATA_WIDTH / 8,
    parameter int PROT_WIDTH      = 3,
    parameter int AUSER_WIDTH     = 4,
    parameter int WUSER_WIDTH     = 4,
    parameter int RUSER_WIDTH     = 4,
    parameter int BUSER_WIDTH     = 4,
    parameter int DEPTH           = 2,
    parameter bit ENABLE_PARITY   = 0,
    // Short Parameters
    parameter int DW  = DATA_WIDTH,
    parameter int AW  = ADDR_WIDTH,
    parameter int SW  = STRB_WIDTH,
    parameter int PW  = PROT_WIDTH,
    parameter int AUW = AUSER_WIDTH,
    parameter int WUW = WUSER_WIDTH,
    parameter int RUW = RUSER_WIDTH,
    parameter int BUW = BUSER_WIDTH,
    // Computed widths
    parameter int CPW = AW + DW + SW + PW + AUW + WUW + 1,  // Command packet width
    parameter int RPW = DW + RUW + BUW + 1                   // Response packet width (data + user + error)
) (
    // Clock and Reset
    input  logic              pclk,
    input  logic              presetn,

    // APB5 interface (slave side)
    input  logic              s_apb_PSEL,
    input  logic              s_apb_PENABLE,
    output logic              s_apb_PREADY,
    input  logic [AW-1:0]     s_apb_PADDR,
    input  logic              s_apb_PWRITE,
    input  logic [DW-1:0]     s_apb_PWDATA,
    input  logic [SW-1:0]     s_apb_PSTRB,
    input  logic [PW-1:0]     s_apb_PPROT,
    input  logic [AUW-1:0]    s_apb_PAUSER,
    input  logic [WUW-1:0]    s_apb_PWUSER,
    output logic [DW-1:0]     s_apb_PRDATA,
    output logic              s_apb_PSLVERR,
    output logic              s_apb_PWAKEUP,
    output logic [RUW-1:0]    s_apb_PRUSER,
    output logic [BUW-1:0]    s_apb_PBUSER,

    // Optional parity signals (active when ENABLE_PARITY=1)
    input  logic [SW-1:0]     s_apb_PWDATAPARITY,
    input  logic              s_apb_PADDRPARITY,
    input  logic              s_apb_PCTRLPARITY,
    output logic [SW-1:0]     s_apb_PRDATAPARITY,
    output logic              s_apb_PREADYPARITY,
    output logic              s_apb_PSLVERRPARITY,

    // Command Interface
    output logic              cmd_valid,
    input  logic              cmd_ready,
    output logic              cmd_pwrite,
    output logic [AW-1:0]     cmd_paddr,
    output logic [DW-1:0]     cmd_pwdata,
    output logic [SW-1:0]     cmd_pstrb,
    output logic [PW-1:0]     cmd_pprot,
    output logic [AUW-1:0]    cmd_pauser,
    output logic [WUW-1:0]    cmd_pwuser,

    // Response Interface
    input  logic              rsp_valid,
    output logic              rsp_ready,
    input  logic [DW-1:0]     rsp_prdata,
    input  logic              rsp_pslverr,
    input  logic [RUW-1:0]    rsp_pruser,
    input  logic [BUW-1:0]    rsp_pbuser,

    // Wake-up control
    input  logic              wakeup_request,

    // Parity error flags (active when ENABLE_PARITY=1)
    output logic              parity_error_wdata,
    output logic              parity_error_ctrl
);

    // Load command packet signals
    logic                r_cmd_valid;
    logic                r_cmd_ready;
    logic [CPW-1:0]      r_cmd_data_in;
    logic [CPW-1:0]      r_cmd_data_out;
    logic [3:0]          r_cmd_count;

    assign r_cmd_data_in = {s_apb_PWRITE, s_apb_PPROT, s_apb_PSTRB, s_apb_PADDR, s_apb_PWDATA,
                            s_apb_PAUSER, s_apb_PWUSER};
    assign {cmd_pwrite, cmd_pprot, cmd_pstrb, cmd_paddr, cmd_pwdata,
            cmd_pauser, cmd_pwuser} = r_cmd_data_out;

    gaxi_skid_buffer #(
        .DEPTH(DEPTH),
        .DATA_WIDTH(CPW)
    ) cmd_skid_buffer_inst (
        .axi_aclk     (pclk),
        .axi_aresetn  (presetn),
        .wr_valid     (r_cmd_valid),
        .wr_ready     (r_cmd_ready),
        .wr_data      (r_cmd_data_in),
        .rd_valid     (cmd_valid),
        .rd_ready     (cmd_ready),
        .rd_data      (r_cmd_data_out),
        .count        (r_cmd_count),
        /* verilator lint_off PINCONNECTEMPTY */
        .rd_count     ()
        /* verilator lint_on PINCONNECTEMPTY */
    );

    // Response packet signals
    logic                r_rsp_valid;
    logic                r_rsp_ready;
    logic [RPW-1:0]      r_rsp_data_in;
    logic [RPW-1:0]      r_rsp_data_out;
    logic [DW-1:0]       r_rsp_prdata;
    logic                r_rsp_pslverr;
    logic [RUW-1:0]      r_rsp_pruser;
    logic [BUW-1:0]      r_rsp_pbuser;
    logic [3:0]          r_rsp_count;

    assign {r_rsp_pslverr, r_rsp_prdata, r_rsp_pruser, r_rsp_pbuser} = r_rsp_data_out;
    assign r_rsp_data_in = {rsp_pslverr, rsp_prdata, rsp_pruser, rsp_pbuser};

    gaxi_skid_buffer #(
        .DEPTH(DEPTH),
        .DATA_WIDTH(RPW)
    ) resp_skid_buffer_inst (
        .axi_aclk     (pclk),
        .axi_aresetn  (presetn),
        .wr_valid     (rsp_valid),
        .wr_ready     (rsp_ready),
        .wr_data      (r_rsp_data_in),
        .rd_valid     (r_rsp_valid),
        .rd_ready     (r_rsp_ready),
        .rd_data      (r_rsp_data_out),
        .count        (r_rsp_count),
        /* verilator lint_off PINCONNECTEMPTY */
        .rd_count     ()
        /* verilator lint_on PINCONNECTEMPTY */
    );

    // APB5 FSM
    typedef enum logic [2:0] {
        IDLE = 3'b001,
        BUSY = 3'b010,
        WAIT = 3'b100
    } apb_state_t;

    apb_state_t r_apb_state;
    logic r_penable_prev;

    // Wake-up signal handling
    logic r_wakeup;

    `ALWAYS_FF_RST(pclk, presetn,
        if (`RST_ASSERTED(presetn)) begin
            r_wakeup <= 1'b0;
        end else begin
            r_wakeup <= wakeup_request;
        end
    )

    assign s_apb_PWAKEUP = r_wakeup;

    // Parity generation and checking
    generate
        if (ENABLE_PARITY) begin : gen_parity
            // Write data parity check
            logic [SW-1:0] w_expected_wdata_parity;
            for (genvar i = 0; i < SW; i++) begin : gen_wdata_parity_check
                assign w_expected_wdata_parity[i] = ^s_apb_PWDATA[i*8 +: 8];
            end

            assign parity_error_wdata = (s_apb_PSEL && s_apb_PENABLE) ?
                                        (w_expected_wdata_parity != s_apb_PWDATAPARITY) : 1'b0;

            // Control parity check (address, control signals)
            logic w_expected_addr_parity;
            logic w_expected_ctrl_parity;
            assign w_expected_addr_parity = ^s_apb_PADDR;
            assign w_expected_ctrl_parity = ^{s_apb_PWRITE, s_apb_PSTRB, s_apb_PPROT};

            assign parity_error_ctrl = (s_apb_PSEL && s_apb_PENABLE) ?
                                       ((w_expected_addr_parity != s_apb_PADDRPARITY) ||
                                        (w_expected_ctrl_parity != s_apb_PCTRLPARITY)) : 1'b0;

            // Read data parity generation
            for (genvar i = 0; i < SW; i++) begin : gen_rdata_parity
                assign s_apb_PRDATAPARITY[i] = ^s_apb_PRDATA[i*8 +: 8];
            end

            // Control signal parity generation
            assign s_apb_PREADYPARITY = ^s_apb_PREADY;
            assign s_apb_PSLVERRPARITY = ^s_apb_PSLVERR;
        end else begin : gen_no_parity
            assign parity_error_wdata = 1'b0;
            assign parity_error_ctrl = 1'b0;
            assign s_apb_PRDATAPARITY = '0;
            assign s_apb_PREADYPARITY = 1'b0;
            assign s_apb_PSLVERRPARITY = 1'b0;
        end
    endgenerate

    // Main APB5 state machine
    `ALWAYS_FF_RST(pclk, presetn,
        if (`RST_ASSERTED(presetn)) begin
            r_apb_state    <= IDLE;
            s_apb_PREADY   <= 1'b0;
            s_apb_PSLVERR  <= 1'b0;
            s_apb_PRDATA   <= '0;
            s_apb_PRUSER   <= '0;
            s_apb_PBUSER   <= '0;
            r_cmd_valid    <= 1'b0;
            r_rsp_ready    <= 1'b0;
            r_penable_prev <= 1'b0;
        end else begin
            // Default states
            r_apb_state    <= r_apb_state;
            s_apb_PREADY   <= 1'b0;
            s_apb_PSLVERR  <= 1'b0;
            r_cmd_valid    <= 1'b0;
            r_rsp_ready    <= 1'b0;
            r_penable_prev <= s_apb_PENABLE;

            casez (r_apb_state)

                IDLE: begin
                    // Only capture on rising edge of PENABLE (SETUP->ACCESS transition)
                    if (s_apb_PSEL && s_apb_PENABLE && !r_penable_prev && r_cmd_ready) begin
                        r_cmd_valid <= 1'b1;
                        r_apb_state <= BUSY;
                    end
                end

                BUSY: begin
                    if (r_rsp_valid) begin
                        s_apb_PREADY  <= 1'b1;
                        s_apb_PRDATA  <= r_rsp_prdata;
                        s_apb_PSLVERR <= r_rsp_pslverr;
                        s_apb_PRUSER  <= r_rsp_pruser;
                        s_apb_PBUSER  <= r_rsp_pbuser;
                        r_rsp_ready   <= 1'b1;
                        r_apb_state   <= WAIT;
                    end
                end

                WAIT: r_apb_state <= IDLE;

                default: r_apb_state <= IDLE;

            endcase
        end
    )

endmodule : apb5_slave
