// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// Module: ref_axil_stub
// Purpose:
//   An AXI4-Lite slave that accepts every write (OKAY) and answers every
//   read with zero. The reference rig (cache-ip common-ip TASK-003) reuses
//   the jet pair rig's generated AXIL bridge so the jet host stack runs
//   unchanged; the three MonBus tally apertures have no tally behind them
//   and land here. One transaction of each direction at a time.
//
// Author: sean galloway
// Created: 2026-11-11
`timescale 1ns / 1ps

module ref_axil_stub #(
    parameter int ADDR_WIDTH = 32,
    parameter int DATA_WIDTH = 32
) (
    input  logic                    aclk,
    input  logic                    aresetn,
    input  logic [ADDR_WIDTH-1:0]   s_axil_awaddr,
    input  logic [2:0]              s_axil_awprot,
    input  logic                    s_axil_awvalid,
    output logic                    s_axil_awready,
    input  logic [DATA_WIDTH-1:0]   s_axil_wdata,
    input  logic [DATA_WIDTH/8-1:0] s_axil_wstrb,
    input  logic                    s_axil_wvalid,
    output logic                    s_axil_wready,
    output logic [1:0]              s_axil_bresp,
    output logic                    s_axil_bvalid,
    input  logic                    s_axil_bready,
    input  logic [ADDR_WIDTH-1:0]   s_axil_araddr,
    input  logic [2:0]              s_axil_arprot,
    input  logic                    s_axil_arvalid,
    output logic                    s_axil_arready,
    output logic [DATA_WIDTH-1:0]   s_axil_rdata,
    output logic [1:0]              s_axil_rresp,
    output logic                    s_axil_rvalid,
    input  logic                    s_axil_rready
);
    /* verilator lint_off UNUSEDSIGNAL */
    logic [ADDR_WIDTH+3+DATA_WIDTH+DATA_WIDTH/8+ADDR_WIDTH+3-1:0] w_unused;
    assign w_unused = {s_axil_awaddr, s_axil_awprot, s_axil_wdata, s_axil_wstrb,
                       s_axil_araddr, s_axil_arprot};
    /* verilator lint_on UNUSEDSIGNAL */

    // write: take AW and W (in either order), then raise B until accepted
    logic r_aw_got, r_w_got, r_bvalid;
    assign s_axil_awready = ~r_aw_got & ~r_bvalid;
    assign s_axil_wready  = ~r_w_got  & ~r_bvalid;
    assign s_axil_bvalid  = r_bvalid;
    assign s_axil_bresp   = 2'b00;
    always_ff @(posedge aclk or negedge aresetn) begin
        if (!aresetn) begin
            r_aw_got <= 1'b0; r_w_got <= 1'b0; r_bvalid <= 1'b0;
        end else begin
            if (s_axil_awvalid & s_axil_awready) r_aw_got <= 1'b1;
            if (s_axil_wvalid  & s_axil_wready)  r_w_got  <= 1'b1;
            if (r_aw_got & r_w_got & ~r_bvalid) begin
                r_bvalid <= 1'b1; r_aw_got <= 1'b0; r_w_got <= 1'b0;
            end else if (r_bvalid & s_axil_bready) begin
                r_bvalid <= 1'b0;
            end
        end
    end

    // read: accept AR, answer zero
    logic r_rvalid;
    assign s_axil_arready = ~r_rvalid;
    assign s_axil_rvalid  = r_rvalid;
    assign s_axil_rdata   = '0;
    assign s_axil_rresp   = 2'b00;
    always_ff @(posedge aclk or negedge aresetn) begin
        if (!aresetn) r_rvalid <= 1'b0;
        else if (s_axil_arvalid & s_axil_arready) r_rvalid <= 1'b1;
        else if (r_rvalid & s_axil_rready) r_rvalid <= 1'b0;
    end
endmodule : ref_axil_stub
