// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
// Module: fb_mig (lint/sim stand-in)
// Purpose: Port-for-port stand-in for the MIG 7-series core so Verilator can
//          lint fb_genesys2_top. The real fb_mig is a Vivado IP the board build
//          creates (fpga/tcl/fb_mig_ip.tcl). Wrapped in `ifdef VERILATOR (as the
//          shared Xilinx primitive stubs are), so no other tool ever sees it.
`ifdef VERILATOR
`timescale 1ns / 1ps
/* verilator lint_off UNUSEDSIGNAL */
/* verilator lint_off UNDRIVEN */
module fb_mig (
    output logic [14:0]  ddr3_addr,
    output logic [2:0]   ddr3_ba,
    output logic         ddr3_cas_n,
    output logic [0:0]   ddr3_ck_n,
    output logic [0:0]   ddr3_ck_p,
    output logic [0:0]   ddr3_cke,
    output logic         ddr3_ras_n,
    output logic         ddr3_reset_n,
    output logic         ddr3_we_n,
    inout  wire  [31:0]  ddr3_dq,
    inout  wire  [3:0]   ddr3_dqs_n,
    inout  wire  [3:0]   ddr3_dqs_p,
    output logic         init_calib_complete,
    output logic [0:0]   ddr3_cs_n,
    output logic [3:0]   ddr3_dm,
    output logic [0:0]   ddr3_odt,
    output logic         ui_clk,
    output logic         ui_clk_sync_rst,
    output logic         mmcm_locked,
    input  logic         aresetn,
    input  logic         app_sr_req,
    input  logic         app_ref_req,
    input  logic         app_zq_req,
    output logic         app_sr_active,
    output logic         app_ref_ack,
    output logic         app_zq_ack,
    input  logic [9:0]   s_axi_awid,
    input  logic [29:0]  s_axi_awaddr,
    input  logic [7:0]   s_axi_awlen,
    input  logic [2:0]   s_axi_awsize,
    input  logic [1:0]   s_axi_awburst,
    input  logic [0:0]   s_axi_awlock,
    input  logic [3:0]   s_axi_awcache,
    input  logic [2:0]   s_axi_awprot,
    input  logic [3:0]   s_axi_awqos,
    input  logic         s_axi_awvalid,
    output logic         s_axi_awready,
    input  logic [127:0] s_axi_wdata,
    input  logic [15:0]  s_axi_wstrb,
    input  logic         s_axi_wlast,
    input  logic         s_axi_wvalid,
    output logic         s_axi_wready,
    output logic [9:0]   s_axi_bid,
    output logic [1:0]   s_axi_bresp,
    output logic         s_axi_bvalid,
    input  logic         s_axi_bready,
    input  logic [9:0]   s_axi_arid,
    input  logic [29:0]  s_axi_araddr,
    input  logic [7:0]   s_axi_arlen,
    input  logic [2:0]   s_axi_arsize,
    input  logic [1:0]   s_axi_arburst,
    input  logic [0:0]   s_axi_arlock,
    input  logic [3:0]   s_axi_arcache,
    input  logic [2:0]   s_axi_arprot,
    input  logic [3:0]   s_axi_arqos,
    input  logic         s_axi_arvalid,
    output logic         s_axi_arready,
    output logic [9:0]   s_axi_rid,
    output logic [127:0] s_axi_rdata,
    output logic [1:0]   s_axi_rresp,
    output logic         s_axi_rlast,
    output logic         s_axi_rvalid,
    input  logic         s_axi_rready,
    input  logic         sys_clk_p,
    input  logic         sys_clk_n,
    input  logic         sys_rst
);
endmodule
/* verilator lint_on UNDRIVEN */
/* verilator lint_on UNUSEDSIGNAL */
`endif
