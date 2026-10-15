// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// Module: fb_axi4_rd_stub
// Purpose: AXI4 read responder for a write-only window: every burst is
//          answered with arlen+1 beats of zero data, OKAY, on the request's ID.
//          The configuration bridge still routes a host READ of the
//          descriptor-RAM window here (the RAM's only read port belongs to the
//          data fabric); without an answer that read would hang the UART link.
//
// Author: sean galloway
// Created: 2026-10-15

`timescale 1ns / 1ps

`include "reset_defs.svh"

module fb_axi4_rd_stub #(
    parameter int IW = 1,
    parameter int AW = 32,
    parameter int DW = 128
) (
    input  logic          aclk,
    input  logic          aresetn,
    input  logic [IW-1:0] s_arid,
    input  logic [AW-1:0] s_araddr,
    input  logic [7:0]    s_arlen,
    input  logic          s_arvalid,
    output logic          s_arready,
    output logic [IW-1:0] s_rid,
    output logic [DW-1:0] s_rdata,
    output logic [1:0]    s_rresp,
    output logic          s_rlast,
    output logic          s_rvalid,
    input  logic          s_rready
);
    logic [7:0] r_left;
    assign s_arready = !s_rvalid;
    assign s_rdata   = '0;
    assign s_rresp   = 2'b00;
    assign s_rlast   = s_rvalid && (r_left == 8'd0);
    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            s_rvalid <= 1'b0;
            s_rid    <= '0;
            r_left   <= '0;
        end else if (s_arvalid && s_arready) begin
            s_rvalid <= 1'b1;
            s_rid    <= s_arid;
            r_left   <= s_arlen;
        end else if (s_rvalid && s_rready) begin
            if (r_left == 8'd0) s_rvalid <= 1'b0;
            else                r_left   <= r_left - 8'd1;
        end
    )
    wire unused = ^s_araddr;
endmodule : fb_axi4_rd_stub
