// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// Module: fb_apb_stub
// Purpose: An APB window with nothing behind it yet: every access completes in
//          one wait-free cycle, writes are dropped, reads return 0, no error.
//          Holds the observers' windows of the configuration map (0x18_0000,
//          0x19_0000) until the observers are built in, so the map -- and the
//          host tools that resolve it -- do not move when they arrive. A read
//          of 0 is what obs_addrs treats as "observer not present".
//
// Author: sean galloway
// Created: 2026-10-15

`timescale 1ns / 1ps

module fb_apb_stub #(
    parameter int AW = 32,
    parameter int DW = 32
) (
    input  logic            psel,
    input  logic            penable,
    input  logic            pwrite,
    input  logic [AW-1:0]   paddr,
    input  logic [DW-1:0]   pwdata,
    input  logic [DW/8-1:0] pstrb,
    input  logic [2:0]      pprot,
    output logic [DW-1:0]   prdata,
    output logic            pready,
    output logic            pslverr
);
    assign prdata  = '0;
    assign pready  = 1'b1;
    assign pslverr = 1'b0;
    wire unused = ^{psel, penable, pwrite, paddr, pwdata, pstrb, pprot};
endmodule : fb_apb_stub
