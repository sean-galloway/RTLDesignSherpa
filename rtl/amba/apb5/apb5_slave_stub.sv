// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: apb5_slave_stub
// Purpose: APB5 Slave Stub for packed command/response interface testing
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
// Created: 2025-12-23

`timescale 1ns / 1ps

`include "reset_defs.svh"

module apb5_slave_stub #(
    parameter int DEPTH             = 4,
    parameter int DATA_WIDTH        = 32,
    parameter int ADDR_WIDTH        = 32,
    parameter int PROT_WIDTH        = 3,
    parameter int AUSER_WIDTH       = 4,
    parameter int WUSER_WIDTH       = 4,
    parameter int RUSER_WIDTH       = 4,
    parameter int BUSER_WIDTH       = 4,
    parameter bit ENABLE_PARITY     = 0,
    parameter int STRB_WIDTH        = DATA_WIDTH / 8,
    // Command packet: addr, data, strb, prot, pwrite, pauser, pwuser
    parameter int CMD_PACKET_WIDTH  = ADDR_WIDTH + DATA_WIDTH + STRB_WIDTH + PROT_WIDTH +
                                      AUSER_WIDTH + WUSER_WIDTH + 1,
    // Response packet: data, ruser, buser, pslverr
    parameter int RESP_PACKET_WIDTH = DATA_WIDTH + RUSER_WIDTH + BUSER_WIDTH + 1,
    // Short Parameters
    parameter int DW  = DATA_WIDTH,
    parameter int AW  = ADDR_WIDTH,
    parameter int SW  = STRB_WIDTH,
    parameter int PW  = PROT_WIDTH,
    parameter int AUW = AUSER_WIDTH,
    parameter int WUW = WUSER_WIDTH,
    parameter int RUW = RUSER_WIDTH,
    parameter int BUW = BUSER_WIDTH,
    parameter int CPW = CMD_PACKET_WIDTH,
    parameter int RPW = RESP_PACKET_WIDTH
) (
    // Clock and Reset
    input  logic                        pclk,
    input  logic                        presetn,

    // APB5 interface
    input  logic                        s_apb_PSEL,
    input  logic                        s_apb_PENABLE,
    input  logic [AW-1:0]               s_apb_PADDR,
    input  logic                        s_apb_PWRITE,
    input  logic [DW-1:0]               s_apb_PWDATA,
    input  logic [SW-1:0]               s_apb_PSTRB,
    input  logic [PW-1:0]               s_apb_PPROT,
    input  logic [AUW-1:0]              s_apb_PAUSER,
    input  logic [WUW-1:0]              s_apb_PWUSER,
    output logic [DW-1:0]               s_apb_PRDATA,
    output logic                        s_apb_PSLVERR,
    output logic                        s_apb_PREADY,
    output logic                        s_apb_PWAKEUP,
    output logic [RUW-1:0]              s_apb_PRUSER,
    output logic [BUW-1:0]              s_apb_PBUSER,

    // Optional parity signals (active when ENABLE_PARITY=1)
    input  logic [SW-1:0]               s_apb_PWDATAPARITY,
    input  logic                        s_apb_PADDRPARITY,
    input  logic                        s_apb_PCTRLPARITY,
    output logic [SW-1:0]               s_apb_PRDATAPARITY,
    output logic                        s_apb_PREADYPARITY,
    output logic                        s_apb_PSLVERRPARITY,

    // Command Packet (packed)
    output logic                        cmd_valid,
    input  logic                        cmd_ready,
    output logic [CPW-1:0]              cmd_data,

    // Response Packet (packed)
    input  logic                        rsp_valid,
    output logic                        rsp_ready,
    input  logic [RPW-1:0]              rsp_data,

    // Wake-up control
    input  logic                        wakeup_request,

    // Parity error flags (active when ENABLE_PARITY=1)
    output logic                        parity_error_wdata,
    output logic                        parity_error_ctrl
);

    // Load command packet signals
    logic                r_cmd_valid;
    logic                r_cmd_ready;
    logic [CPW-1:0]      r_cmd_data;
    logic [DW-1:0]       r_cmd_pwdata;
    logic [AW-1:0]       r_cmd_paddr;
    logic [SW-1:0]       r_cmd_pstrb;
    logic [PW-1:0]       r_cmd_pprot;
    logic [AUW-1:0]      r_cmd_pauser;
    logic [WUW-1:0]      r_cmd_pwuser;
    logic                r_cmd_pwrite;

    assign r_cmd_data = {r_cmd_pwrite, r_cmd_pprot, r_cmd_pstrb, r_cmd_paddr, r_cmd_pwdata,
                         r_cmd_pauser, r_cmd_pwuser};

    gaxi_skid_buffer #(
        .DEPTH(DEPTH),
        .DATA_WIDTH(CPW)
    ) cmd_skid_buffer_inst (
        .axi_aclk     (pclk),
        .axi_aresetn  (presetn),
        .wr_valid     (r_cmd_valid),
        .wr_ready     (r_cmd_ready),
        .wr_data      (r_cmd_data),
        /* verilator lint_off PINCONNECTEMPTY */
        .count        (),
        /* verilator lint_on PINCONNECTEMPTY */
        .rd_valid     (cmd_valid),
        .rd_ready     (cmd_ready),
        /* verilator lint_off PINCONNECTEMPTY */
        .rd_count     (),
        /* verilator lint_on PINCONNECTEMPTY */
        .rd_data      (cmd_data)
    );

    // Extract response packet signals
    logic                r_rsp_valid;
    logic                r_rsp_ready;
    logic [RPW-1:0]      r_rsp_data;
    logic [DW-1:0]       r_rsp_prdata;
    logic                r_rsp_pslverr;
    logic [RUW-1:0]      r_rsp_pruser;
    logic [BUW-1:0]      r_rsp_pbuser;

    assign {r_rsp_pslverr, r_rsp_prdata, r_rsp_pruser, r_rsp_pbuser} = r_rsp_data;

    gaxi_skid_buffer #(
        .DEPTH(DEPTH),
        .DATA_WIDTH(RPW)
    ) resp_skid_buffer_inst (
        .axi_aclk     (pclk),
        .axi_aresetn  (presetn),
        .wr_valid     (rsp_valid),
        .wr_ready     (rsp_ready),
        .wr_data      (rsp_data),
        /* verilator lint_off PINCONNECTEMPTY */
        .count        (),
        /* verilator lint_on PINCONNECTEMPTY */
        .rd_valid     (r_rsp_valid),
        .rd_ready     (r_rsp_ready),
        /* verilator lint_off PINCONNECTEMPTY */
        .rd_count     (),
        /* verilator lint_on PINCONNECTEMPTY */
        .rd_data      (r_rsp_data)
    );

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

    // APB5 FSM
    typedef enum logic [1:0] {
        IDLE      = 2'b01,
        XFER_DATA = 2'b10
    } apb_state_t;

    apb_state_t r_apb_state, w_apb_next_state;

    `ALWAYS_FF_RST(pclk, presetn,
        if (`RST_ASSERTED(presetn)) begin
            r_apb_state <= IDLE;
        end else begin
            r_apb_state <= w_apb_next_state;
        end
    )

    always_comb begin
        w_apb_next_state   = r_apb_state;
        s_apb_PREADY       = 1'b0;
        s_apb_PSLVERR      = 1'b0;
        s_apb_PRDATA       = '0;
        s_apb_PRUSER       = '0;
        s_apb_PBUSER       = '0;
        r_cmd_paddr        = s_apb_PADDR;
        r_cmd_pwrite       = s_apb_PWRITE;
        r_cmd_pwdata       = s_apb_PWDATA;
        r_cmd_pstrb        = s_apb_PSTRB;
        r_cmd_pprot        = s_apb_PPROT;
        r_cmd_pauser       = s_apb_PAUSER;
        r_cmd_pwuser       = s_apb_PWUSER;
        r_cmd_valid        = 1'b0;
        r_rsp_ready        = 1'b0;

        case (r_apb_state)
            IDLE: begin
                if (s_apb_PSEL && s_apb_PENABLE && r_cmd_ready) begin
                    r_cmd_valid      = 1'b1;
                    w_apb_next_state = XFER_DATA;
                end
            end

            XFER_DATA: begin
                if (r_rsp_valid) begin
                    s_apb_PREADY     = 1'b1;
                    s_apb_PRDATA     = r_rsp_prdata;
                    s_apb_PSLVERR    = r_rsp_pslverr;
                    s_apb_PRUSER     = r_rsp_pruser;
                    s_apb_PBUSER     = r_rsp_pbuser;
                    r_rsp_ready      = 1'b1;
                    w_apb_next_state = IDLE;
                end
            end

            default: w_apb_next_state = r_apb_state;
        endcase
    end

endmodule : apb5_slave_stub
