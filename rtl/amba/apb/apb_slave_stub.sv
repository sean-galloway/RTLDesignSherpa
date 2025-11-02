// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: apb_slave_stub
// Purpose: Apb Slave Stub module
//
// Documentation: rtl/amba/PRD.md
// Subsystem: amba
//
// Author: sean galloway
// Created: 2025-10-18

`timescale 1ns / 1ps

`include "reset_defs.svh"

module apb_slave_stub #(
    parameter int DEPTH    = 4,
    parameter int DATA_WIDTH    = 32,
    parameter int ADDR_WIDTH    = 32,
    parameter int STRB_WIDTH    = DATA_WIDTH / 8,
    parameter int CMD_PACKET_WIDTH = ADDR_WIDTH + DATA_WIDTH + STRB_WIDTH + 4, // addr, data, strb, prot, pwrite
    parameter int RESP_PACKET_WIDTH = DATA_WIDTH + 1, // data, resp
    // Short Parameters
    parameter int DW  = DATA_WIDTH,
    parameter int AW  = ADDR_WIDTH,
    parameter int SW  = STRB_WIDTH,
    parameter int CPW = CMD_PACKET_WIDTH,
    parameter int RPW = RESP_PACKET_WIDTH
) (
    // Clock and Reset
    input  logic                        pclk,
    input  logic                        presetn,

    // APB interface
    input  logic                        s_apb_PSEL,
    input  logic                        s_apb_PENABLE,
    input  logic [AW-1:0]               s_apb_PADDR,
    input  logic                        s_apb_PWRITE,
    input  logic [DW-1:0]               s_apb_PWDATA,
    input  logic [SW-1:0]               s_apb_PSTRB,
    input  logic [2:0]                  s_apb_PPROT,
    output logic [DW-1:0]               s_apb_PRDATA,
    output logic                        s_apb_PSLVERR,
    output logic                        s_apb_PREADY,

    // Command Packet
    output logic                        cmd_valid,
    input  logic                        cmd_ready,
    output logic [CPW-1:0]              cmd_data,

    // AXI read interface
    input  logic                        rsp_valid,
    output logic                        rsp_ready,
    input  logic [RPW-1:0]              rsp_data
);

    // Load command packet signals
    logic                r_cmd_valid;
    logic                r_cmd_ready;
    logic [CPW-1:0]      r_cmd_data;
    logic [DW-1:0]       r_cmd_pwdata;
    logic [AW-1:0]       r_cmd_paddr;
    logic [SW-1:0]       r_cmd_pstrb;
    logic [2:0]          r_cmd_pprot;
    logic                r_cmd_pwrite;

    assign r_cmd_data = {r_cmd_pwrite, r_cmd_pprot, r_cmd_pstrb, r_cmd_paddr, r_cmd_pwdata};

    gaxi_skid_buffer #(
        .DEPTH(DEPTH),
        .DATA_WIDTH(CPW)
    ) cmd_skid_buffer_inst (
        .axi_aclk     (pclk),
        .axi_aresetn  (presetn),
        .wr_valid     (r_cmd_valid),
        .wr_ready     (r_cmd_ready),
        .wr_data      (r_cmd_data),
        .count        (),  // Unused monitoring output
        .rd_valid     (cmd_valid),
        .rd_ready     (cmd_ready),
        .rd_count     (),  // Unused monitoring output
        .rd_data      (cmd_data)
    );


    // Extract response packet signals
    logic                r_rsp_valid;
    logic                r_rsp_ready;
    logic [RPW-1:0]      r_rsp_data;
    logic [DW-1:0]       r_rsp_prdata;
    logic                r_rsp_pslverr;

    assign {r_rsp_pslverr, r_rsp_prdata} = r_rsp_data;

    gaxi_skid_buffer #(
        .DEPTH(DEPTH),
        .DATA_WIDTH(RPW)
    ) resp_skid_buffer_inst (
        .axi_aclk     (pclk),
        .axi_aresetn  (presetn),
        .wr_valid     (rsp_valid),
        .wr_ready     (rsp_ready),
        .wr_data      (rsp_data),
        .count        (),  // Unused monitoring output
        .rd_valid     (r_rsp_valid),
        .rd_ready     (r_rsp_ready),
        .rd_count     (),  // Unused monitoring output
        .rd_data      (r_rsp_data)
    );

    // APB FSM
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
        s_apb_PRDATA       = 'b0;
        r_cmd_paddr        = s_apb_PADDR;
        r_cmd_pwrite       = s_apb_PWRITE;
        r_cmd_pwdata       = s_apb_PWDATA;
        r_cmd_pstrb        = s_apb_PSTRB;
        r_cmd_pprot        = s_apb_PPROT;
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
                    r_rsp_ready      = 1'b1;
                    w_apb_next_state = IDLE;
                end
            end

            default: w_apb_next_state = r_apb_state;
        endcase
    end

endmodule : apb_slave_stub
