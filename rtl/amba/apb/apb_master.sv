// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: apb_master
// Purpose: Apb Master module
//
// Documentation: rtl/amba/PRD.md
// Subsystem: amba
//
// Author: sean galloway
// Created: 2025-10-18

`timescale 1ns / 1ps

`include "reset_defs.svh"

module apb_master #(
    parameter int ADDR_WIDTH      = 32,
    parameter int DATA_WIDTH      = 32,
    parameter int PROT_WIDTH      = 3,
    parameter int CMD_DEPTH       = 6,
    parameter int RSP_DEPTH       = 6,
    parameter int STRB_WIDTH      = DATA_WIDTH / 8,
    // Short Parameters
    parameter int AW  = ADDR_WIDTH,
    parameter int DW  = DATA_WIDTH,
    parameter int SW  = STRB_WIDTH,
    parameter int PW  = PROT_WIDTH,
    parameter int CPW = AW + DW + SW + PW + 1, // verilog_lint: waive line-length
    parameter int RPW = DW + 1
) (
    // Clock and Reset
    input  logic              pclk,
    input  logic              presetn,

    // APB interface
    output logic              m_apb_PSEL,
    output logic              m_apb_PENABLE,
    output logic [AW-1:0]     m_apb_PADDR,
    output logic              m_apb_PWRITE,
    output logic [DW-1:0]     m_apb_PWDATA,
    output logic [SW-1:0]     m_apb_PSTRB,
    output logic [PW-1:0]     m_apb_PPROT,
    input  logic [DW-1:0]     m_apb_PRDATA,
    input  logic              m_apb_PSLVERR,
    input  logic              m_apb_PREADY,

    // Command Packet
    input  logic              cmd_valid,
    output logic              cmd_ready,
    input  logic              cmd_pwrite,
    input  logic [AW-1:0]     cmd_paddr,
    input  logic [DW-1:0]     cmd_pwdata,
    input  logic [SW-1:0]     cmd_pstrb,
    input  logic [PW-1:0]     cmd_pprot,

    // Read Return interface
    output logic              rsp_valid,
    input  logic              rsp_ready,
    output logic [DW-1:0]     rsp_prdata,
    output logic              rsp_pslverr
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
    logic [2:0]          r_cmd_pprot;
    logic                r_cmd_pwrite;

    // Pack command inputs into a single data word
    assign r_cmd_data_in = {cmd_pwrite, cmd_pprot, cmd_pstrb, cmd_paddr, cmd_pwdata};

    // Unpack command data for use in the APB interface
    assign {r_cmd_pwrite, r_cmd_pprot, r_cmd_pstrb, r_cmd_paddr, r_cmd_pwdata} = r_cmd_data_out;

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
        .count       (w_cmd_count),
        .rd_valid     (r_cmd_valid),
        .rd_ready     (w_cmd_ready),
        .rd_data      (r_cmd_data_out),
        .rd_count     ()
    );

    // Response FIFO signals
    logic                w_rsp_valid;
    logic                r_rsp_ready;
    logic [RPW-1:0]      r_rsp_data_in;

    // Pack response data for the FIFO
    assign r_rsp_data_in = {m_apb_PSLVERR, m_apb_PRDATA};

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
        .count       (),
        .rd_valid     (rsp_valid),
        .rd_ready     (rsp_ready),
        .rd_data      ({rsp_pslverr, rsp_prdata}),
        .rd_count     ()
    );

    // APB FSM
    typedef enum logic [2:0] {
        IDLE = 3'b001,
        SETUP = 3'b010,
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
                    // Both reads and writes need to send response back
                    // Only proceed if response FIFO is ready
                    if (r_rsp_ready) begin
                        w_rsp_valid = 1'b1;
                        w_cmd_ready = 1'b1;

                        // Go back to IDLE or directly start a new transaction
                        // Check if there are more commands AFTER popping this one
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

endmodule : apb_master
