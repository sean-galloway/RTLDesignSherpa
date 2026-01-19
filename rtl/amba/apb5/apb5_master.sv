// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: apb5_master
// Purpose: APB5 Master with AMBA5 extensions
//
// APB5 Extensions:
// - PAUSER: User-defined request attributes
// - PWUSER: User-defined write data attributes
// - PWAKEUP: Wake-up signal handling (input from slave)
// - Optional parity support for data integrity
//
// Documentation: rtl/amba/PRD.md
// Subsystem: amba
//
// Author: sean galloway
// Created: 2025-12-21

`timescale 1ns / 1ps

`include "reset_defs.svh"

module apb5_master #(
    parameter int ADDR_WIDTH      = 32,
    parameter int DATA_WIDTH      = 32,
    parameter int PROT_WIDTH      = 3,
    parameter int AUSER_WIDTH     = 4,
    parameter int WUSER_WIDTH     = 4,
    parameter int RUSER_WIDTH     = 4,
    parameter int BUSER_WIDTH     = 4,
    parameter int CMD_DEPTH       = 6,
    parameter int RSP_DEPTH       = 6,
    parameter bit ENABLE_PARITY   = 0,
    parameter int STRB_WIDTH      = DATA_WIDTH / 8,
    // Short Parameters
    parameter int AW  = ADDR_WIDTH,
    parameter int DW  = DATA_WIDTH,
    parameter int SW  = STRB_WIDTH,
    parameter int PW  = PROT_WIDTH,
    parameter int AUW = AUSER_WIDTH,
    parameter int WUW = WUSER_WIDTH,
    parameter int RUW = RUSER_WIDTH,
    parameter int BUW = BUSER_WIDTH,
    // Computed widths
    parameter int CPW = AW + DW + SW + PW + AUW + WUW + 1,  // Command packet width
    parameter int RPW = DW + RUW + BUW + 2                   // Response packet width (data + user + wakeup + error)
) (
    // Clock and Reset
    input  logic              pclk,
    input  logic              presetn,

    // APB5 interface (master side)
    output logic              m_apb_PSEL,
    output logic              m_apb_PENABLE,
    output logic [AW-1:0]     m_apb_PADDR,
    output logic              m_apb_PWRITE,
    output logic [DW-1:0]     m_apb_PWDATA,
    output logic [SW-1:0]     m_apb_PSTRB,
    output logic [PW-1:0]     m_apb_PPROT,
    output logic [AUW-1:0]    m_apb_PAUSER,
    output logic [WUW-1:0]    m_apb_PWUSER,
    input  logic [DW-1:0]     m_apb_PRDATA,
    input  logic              m_apb_PSLVERR,
    input  logic              m_apb_PREADY,
    input  logic              m_apb_PWAKEUP,
    input  logic [RUW-1:0]    m_apb_PRUSER,
    input  logic [BUW-1:0]    m_apb_PBUSER,

    // Optional parity signals (active when ENABLE_PARITY=1)
    output logic [SW-1:0]     m_apb_PWDATAPARITY,
    output logic              m_apb_PADDRPARITY,
    output logic              m_apb_PCTRLPARITY,
    input  logic [SW-1:0]     m_apb_PRDATAPARITY,
    input  logic              m_apb_PREADYPARITY,
    input  logic              m_apb_PSLVERRPARITY,

    // Command Packet interface
    input  logic              cmd_valid,
    output logic              cmd_ready,
    input  logic              cmd_pwrite,
    input  logic [AW-1:0]     cmd_paddr,
    input  logic [DW-1:0]     cmd_pwdata,
    input  logic [SW-1:0]     cmd_pstrb,
    input  logic [PW-1:0]     cmd_pprot,
    input  logic [AUW-1:0]    cmd_pauser,
    input  logic [WUW-1:0]    cmd_pwuser,

    // Response interface
    output logic              rsp_valid,
    input  logic              rsp_ready,
    output logic [DW-1:0]     rsp_prdata,
    output logic              rsp_pslverr,
    output logic              rsp_pwakeup,
    output logic [RUW-1:0]    rsp_pruser,
    output logic [BUW-1:0]    rsp_pbuser,

    // Parity error flags (active when ENABLE_PARITY=1)
    output logic              parity_error_rdata,
    output logic              parity_error_ctrl,

    // Wake-up status
    output logic              wakeup_pending
);

    // Command FIFO signals
    logic                r_cmd_valid;
    logic                w_cmd_ready;
    logic [CPW-1:0]      r_cmd_data_in;
    logic [CPW-1:0]      r_cmd_data_out;
    logic [3:0]          w_cmd_count;

    // Unpacked command signals
    logic [DW-1:0]       r_cmd_pwdata;
    logic [AW-1:0]       r_cmd_paddr;
    logic [SW-1:0]       r_cmd_pstrb;
    logic [PW-1:0]       r_cmd_pprot;
    logic [AUW-1:0]      r_cmd_pauser;
    logic [WUW-1:0]      r_cmd_pwuser;
    logic                r_cmd_pwrite;

    // Pack command inputs into a single data word
    assign r_cmd_data_in = {cmd_pwrite, cmd_pprot, cmd_pstrb, cmd_paddr, cmd_pwdata,
                            cmd_pauser, cmd_pwuser};

    // Unpack command data for use in the APB interface
    assign {r_cmd_pwrite, r_cmd_pprot, r_cmd_pstrb, r_cmd_paddr, r_cmd_pwdata,
            r_cmd_pauser, r_cmd_pwuser} = r_cmd_data_out;

    // Command FIFO instance
    gaxi_skid_buffer #(
        .DATA_WIDTH   (CPW),
        .DEPTH        (CMD_DEPTH)
    ) cmd_fifo_inst (
        .axi_aclk     (pclk),
        .axi_aresetn  (presetn),
        .wr_valid     (cmd_valid),
        .wr_ready     (cmd_ready),
        .wr_data      (r_cmd_data_in),
        .count        (w_cmd_count),
        .rd_valid     (r_cmd_valid),
        .rd_ready     (w_cmd_ready),
        .rd_data      (r_cmd_data_out),
        /* verilator lint_off PINCONNECTEMPTY */
        .rd_count     ()
        /* verilator lint_on PINCONNECTEMPTY */
    );

    // Response FIFO signals
    logic                w_rsp_valid;
    logic                r_rsp_ready;
    logic [RPW-1:0]      r_rsp_data_in;
    logic [RPW-1:0]      r_rsp_data_out;

    // Pack response data for the FIFO
    assign r_rsp_data_in = {m_apb_PSLVERR, m_apb_PWAKEUP, m_apb_PRDATA, m_apb_PRUSER, m_apb_PBUSER};

    // Response FIFO instance
    gaxi_skid_buffer #(
        .DATA_WIDTH   (RPW),
        .DEPTH        (RSP_DEPTH)
    ) resp_fifo_inst (
        .axi_aclk     (pclk),
        .axi_aresetn  (presetn),
        .wr_valid     (w_rsp_valid),
        .wr_ready     (r_rsp_ready),
        .wr_data      (r_rsp_data_in),
        /* verilator lint_off PINCONNECTEMPTY */
        .count        (),
        /* verilator lint_on PINCONNECTEMPTY */
        .rd_valid     (rsp_valid),
        .rd_ready     (rsp_ready),
        .rd_data      (r_rsp_data_out),
        /* verilator lint_off PINCONNECTEMPTY */
        .rd_count     ()
        /* verilator lint_on PINCONNECTEMPTY */
    );

    // Unpack response data
    assign {rsp_pslverr, rsp_pwakeup, rsp_prdata, rsp_pruser, rsp_pbuser} = r_rsp_data_out;

    // APB5 FSM
    typedef enum logic [2:0] {
        IDLE   = 3'b001,
        SETUP  = 3'b010,
        ACCESS = 3'b100
    } apb_state_t;

    apb_state_t r_apb_state, w_apb_next_state;

    `ALWAYS_FF_RST(pclk, presetn,
        if (`RST_ASSERTED(presetn)) begin
            r_apb_state <= IDLE;
        end else begin
            r_apb_state <= w_apb_next_state;
        end
    )

    // Wake-up tracking
    logic r_wakeup_pending;

    `ALWAYS_FF_RST(pclk, presetn,
        if (`RST_ASSERTED(presetn)) begin
            r_wakeup_pending <= 1'b0;
        end else begin
            if (m_apb_PWAKEUP) begin
                r_wakeup_pending <= 1'b1;
            end else if (r_apb_state != IDLE) begin
                // Clear wakeup pending when we start a transaction
                r_wakeup_pending <= 1'b0;
            end
        end
    )

    assign wakeup_pending = r_wakeup_pending;

    // Parity generation (when enabled)
    generate
        if (ENABLE_PARITY) begin : gen_parity
            // Write data parity (odd parity per byte)
            for (genvar i = 0; i < SW; i++) begin : gen_wdata_parity
                assign m_apb_PWDATAPARITY[i] = ^r_cmd_pwdata[i*8 +: 8];
            end

            // Address parity
            assign m_apb_PADDRPARITY = ^r_cmd_paddr;

            // Control parity (pwrite, pstrb, pprot)
            assign m_apb_PCTRLPARITY = ^{r_cmd_pwrite, r_cmd_pstrb, r_cmd_pprot};

            // Read data parity check
            logic [SW-1:0] w_expected_rdata_parity;
            for (genvar i = 0; i < SW; i++) begin : gen_rdata_parity_check
                assign w_expected_rdata_parity[i] = ^m_apb_PRDATA[i*8 +: 8];
            end

            assign parity_error_rdata = (m_apb_PREADY && m_apb_PSEL && m_apb_PENABLE) ?
                                        (w_expected_rdata_parity != m_apb_PRDATAPARITY) : 1'b0;

            // Control parity check (PREADY, PSLVERR)
            assign parity_error_ctrl = (m_apb_PREADY && m_apb_PSEL && m_apb_PENABLE) ?
                                       ((^m_apb_PREADY != m_apb_PREADYPARITY) ||
                                        (^m_apb_PSLVERR != m_apb_PSLVERRPARITY)) : 1'b0;
        end else begin : gen_no_parity
            assign m_apb_PWDATAPARITY = '0;
            assign m_apb_PADDRPARITY = 1'b0;
            assign m_apb_PCTRLPARITY = 1'b0;
            assign parity_error_rdata = 1'b0;
            assign parity_error_ctrl = 1'b0;
        end
    endgenerate

    // Main APB5 state machine
    always_comb begin
        // Default assignments
        w_apb_next_state = r_apb_state;
        m_apb_PSEL = 1'b0;
        m_apb_PENABLE = 1'b0;
        m_apb_PADDR = r_cmd_paddr;
        m_apb_PWRITE = r_cmd_pwrite;
        m_apb_PWDATA = r_cmd_pwdata;
        m_apb_PSTRB = r_cmd_pstrb;
        m_apb_PPROT = r_cmd_pprot;
        m_apb_PAUSER = r_cmd_pauser;
        m_apb_PWUSER = r_cmd_pwuser;
        w_cmd_ready = 1'b0;
        w_rsp_valid = 1'b0;

        casez (r_apb_state)
            IDLE: begin
                // Start transaction if there's a valid command
                if (r_cmd_valid) begin
                    m_apb_PSEL = 1'b1;
                    w_apb_next_state = SETUP;
                end
            end

            SETUP: begin
                // Setup phase - assert PSEL without PENABLE
                m_apb_PSEL = 1'b1;

                // Always move to ACCESS phase
                w_apb_next_state = ACCESS;
            end

            ACCESS: begin
                // Access phase - assert both PSEL and PENABLE
                m_apb_PSEL = 1'b1;
                m_apb_PENABLE = 1'b1;

                // Wait for slave to respond with PREADY
                if (m_apb_PREADY) begin
                    // Only proceed if response FIFO is ready
                    if (r_rsp_ready) begin
                        w_rsp_valid = 1'b1;
                        w_cmd_ready = 1'b1;

                        // Go back to IDLE or directly start a new transaction
                        if (w_cmd_count > 1)
                            w_apb_next_state = SETUP;
                        else
                            w_apb_next_state = IDLE;
                    end else begin
                        // Response FIFO not ready, stay in ACCESS state
                        w_apb_next_state = ACCESS;
                    end
                end
            end

            // verilator coverage_off
            // DEFENSIVE: Illegal FSM state recovery
            default: w_apb_next_state = IDLE;
            // verilator coverage_on
        endcase
    end

endmodule : apb5_master
