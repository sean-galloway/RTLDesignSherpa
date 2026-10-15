// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// Module: fb_axil_wr_sink
// Purpose: AXI4-Lite write sink: accepts every write and answers OKAY. Ends an
//          AXI4-Lite write master the fabric benchmark does not use (STREAM's
//          MonBus egress with its monitors compiled out, writes to the
//          read-only error FIFO window) so it can never stall.
//
//          One write at a time; nothing is stored.
//
// Author: sean galloway
// Created: 2026-10-15

`timescale 1ns / 1ps

`include "reset_defs.svh"

module fb_axil_wr_sink #(
    parameter int AW = 32,
    parameter int DW = 32
) (
    input  logic            aclk,
    input  logic            aresetn,
    input  logic [AW-1:0]   s_awaddr,
    input  logic [2:0]      s_awprot,
    input  logic            s_awvalid,
    output logic            s_awready,
    input  logic [DW-1:0]   s_wdata,
    input  logic [DW/8-1:0] s_wstrb,
    input  logic            s_wvalid,
    output logic            s_wready,
    output logic [1:0]      s_bresp,
    output logic            s_bvalid,
    input  logic            s_bready
);
    // AW and W are accepted independently (ready never depends on valid);
    // B is issued once both halves of a write have arrived, and held until
    // taken. One write in flight at a time.
    logic r_aw, r_w;
    assign s_awready = !r_aw && !s_bvalid;
    assign s_wready  = !r_w  && !s_bvalid;
    assign s_bresp   = 2'b00;
    wire w_aw = r_aw || (s_awvalid && s_awready);
    wire w_w  = r_w  || (s_wvalid  && s_wready);
    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_aw     <= 1'b0;
            r_w      <= 1'b0;
            s_bvalid <= 1'b0;
        end else if (s_bvalid) begin
            if (s_bready) s_bvalid <= 1'b0;
        end else if (w_aw && w_w) begin
            r_aw     <= 1'b0;
            r_w      <= 1'b0;
            s_bvalid <= 1'b1;
        end else begin
            r_aw <= w_aw;
            r_w  <= w_w;
        end
    )
    wire unused = ^{s_awaddr, s_awprot, s_wdata, s_wstrb};
endmodule : fb_axil_wr_sink
