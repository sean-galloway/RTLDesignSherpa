// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// Module: ref_cache_tb
// Purpose: One reference cache (REF_CACHE_SEL: 0 HPDcache wrapper, 1 CVA6
//   write-back dcache wrapper) on the pair rig's 512 KB AXI4 block-RAM memory,
//   with the GAXI CPU port on the testbench boundary for the house GAXI BFMs
//   (cache-ip common-ip TASK-003: the read-after-write check the rig's cycle
//   injector cannot make, because its reads never land on a word it wrote).
`timescale 1ns / 1ps

module ref_cache_tb #(
    parameter int REF_CACHE_SEL = 0,
    parameter int ADDR_WIDTH    = 32,
    parameter int BUS_WIDTH     = 64,
    parameter int AXI_ID_WIDTH  = 8,
    parameter int MEM_DEPTH     = 131072
) (
    input  logic clk,
    input  logic rst_n,
    input  logic                                   cpu_req_wr_valid,
    output logic                                   cpu_req_wr_ready,
    input  logic [ADDR_WIDTH+1+BUS_WIDTH/8+BUS_WIDTH-1:0] cpu_req_wr_data,
    output logic                                   cpu_rsp_rd_valid,
    input  logic                                   cpu_rsp_rd_ready,
    output logic [BUS_WIDTH-1:0]                   cpu_rsp_rd_data,
    output logic                                   o_rsp_error
);
    localparam int IW = AXI_ID_WIDTH, UW = 1, STRB_W = BUS_WIDTH / 8;

    logic [IW-1:0]        m_arid, m_awid, m_rid, m_bid;
    logic [ADDR_WIDTH-1:0] m_araddr, m_awaddr;
    logic [7:0]           m_arlen, m_awlen;
    logic [2:0]           m_arsize, m_awsize;
    logic [1:0]           m_arburst, m_awburst;
    logic                 m_arlock, m_awlock;
    logic [3:0]           m_arcache, m_awcache;
    logic [2:0]           m_arprot, m_awprot;
    logic [3:0]           m_arqos, m_awqos;
    logic [3:0]           m_arregion, m_awregion;
    logic [UW-1:0]        m_aruser, m_awuser, m_wuser, m_ruser, m_buser;
    logic                 m_arvalid, m_arready, m_rvalid, m_rready, m_rlast;
    logic [BUS_WIDTH-1:0] m_rdata, m_wdata;
    logic [1:0]           m_rresp, m_bresp;
    logic                 m_awvalid, m_awready, m_wvalid, m_wready, m_wlast, m_bvalid, m_bready;
    logic [STRB_W-1:0]    m_wstrb;
    /* verilator lint_off UNUSEDSIGNAL */
    logic evt_a, evt_b;
    /* verilator lint_on UNUSEDSIGNAL */

`define REF_AXI_PORTS \
        .m_axi_arid(m_arid), .m_axi_araddr(m_araddr), .m_axi_arlen(m_arlen), .m_axi_arsize(m_arsize), \
        .m_axi_arburst(m_arburst), .m_axi_arlock(m_arlock), .m_axi_arcache(m_arcache), .m_axi_arprot(m_arprot), \
        .m_axi_arqos(m_arqos), .m_axi_arregion(m_arregion), .m_axi_aruser(m_aruser), .m_axi_arvalid(m_arvalid), \
        .m_axi_arready(m_arready), .m_axi_rid(m_rid), .m_axi_rdata(m_rdata), .m_axi_rresp(m_rresp), \
        .m_axi_rlast(m_rlast), .m_axi_ruser(m_ruser), .m_axi_rvalid(m_rvalid), .m_axi_rready(m_rready), \
        .m_axi_awid(m_awid), .m_axi_awaddr(m_awaddr), .m_axi_awlen(m_awlen), .m_axi_awsize(m_awsize), \
        .m_axi_awburst(m_awburst), .m_axi_awlock(m_awlock), .m_axi_awcache(m_awcache), .m_axi_awprot(m_awprot), \
        .m_axi_awqos(m_awqos), .m_axi_awregion(m_awregion), .m_axi_awuser(m_awuser), .m_axi_awvalid(m_awvalid), \
        .m_axi_awready(m_awready), .m_axi_wdata(m_wdata), .m_axi_wstrb(m_wstrb), .m_axi_wlast(m_wlast), \
        .m_axi_wuser(m_wuser), .m_axi_wvalid(m_wvalid), .m_axi_wready(m_wready), .m_axi_bid(m_bid), \
        .m_axi_bresp(m_bresp), .m_axi_buser(m_buser), .m_axi_bvalid(m_bvalid), .m_axi_bready(m_bready)

    generate
        if (REF_CACHE_SEL == 1) begin : gen_cva6
            ref_cva6_dcache_top #(
                .ADDR_WIDTH(ADDR_WIDTH), .BUS_WIDTH(BUS_WIDTH),
                .AXI_ID_WIDTH(AXI_ID_WIDTH), .AXI_USER_WIDTH(UW)
            ) u_ref (
                .aclk(clk), .aresetn(rst_n),
                .cpu_req_wr_valid(cpu_req_wr_valid), .cpu_req_wr_ready(cpu_req_wr_ready),
                .cpu_req_wr_data(cpu_req_wr_data), .cpu_rsp_rd_valid(cpu_rsp_rd_valid),
                .cpu_rsp_rd_ready(cpu_rsp_rd_ready), .cpu_rsp_rd_data(cpu_rsp_rd_data),
                `REF_AXI_PORTS,
                .o_miss(evt_a), .o_rsp_error(o_rsp_error)
            );
            assign evt_b = 1'b0;
        end else begin : gen_hpd
            ref_hpdcache_top #(
                .ADDR_WIDTH(ADDR_WIDTH), .SETS(128), .WAYS(4), .LINE_BYTES(64), .BUS_WIDTH(BUS_WIDTH),
                .AXI_ID_WIDTH(AXI_ID_WIDTH), .AXI_USER_WIDTH(UW)
            ) u_ref (
                .aclk(clk), .aresetn(rst_n),
                .cpu_req_wr_valid(cpu_req_wr_valid), .cpu_req_wr_ready(cpu_req_wr_ready),
                .cpu_req_wr_data(cpu_req_wr_data), .cpu_rsp_rd_valid(cpu_rsp_rd_valid),
                .cpu_rsp_rd_ready(cpu_rsp_rd_ready), .cpu_rsp_rd_data(cpu_rsp_rd_data),
                `REF_AXI_PORTS,
                .o_evt_read_miss(evt_a), .o_evt_write_miss(evt_b), .o_rsp_error(o_rsp_error)
            );
        end
    endgenerate
`undef REF_AXI_PORTS

    sdpram_slave_axi4_axi4 #(
        .AXI_ID_WIDTH(AXI_ID_WIDTH), .ADDR_WIDTH(ADDR_WIDTH), .DATA_WIDTH(BUS_WIDTH),
        .USER_WIDTH(UW), .MEM_DEPTH(MEM_DEPTH), .USE_WSTRB(1'b0)
    ) u_mem (
        .aclk(clk), .aresetn(rst_n),
        .s_axi_awid(m_awid), .s_axi_awaddr(m_awaddr), .s_axi_awlen(m_awlen), .s_axi_awsize(m_awsize),
        .s_axi_awburst(m_awburst), .s_axi_awlock(m_awlock), .s_axi_awcache(m_awcache), .s_axi_awprot(m_awprot),
        .s_axi_awqos(m_awqos), .s_axi_awregion(m_awregion), .s_axi_awuser(m_awuser), .s_axi_awvalid(m_awvalid),
        .s_axi_awready(m_awready), .s_axi_wdata(m_wdata), .s_axi_wstrb(m_wstrb), .s_axi_wlast(m_wlast),
        .s_axi_wuser(m_wuser), .s_axi_wvalid(m_wvalid), .s_axi_wready(m_wready), .s_axi_bid(m_bid),
        .s_axi_bresp(m_bresp), .s_axi_buser(m_buser), .s_axi_bvalid(m_bvalid), .s_axi_bready(m_bready),
        .s_axi_arid(m_arid), .s_axi_araddr(m_araddr), .s_axi_arlen(m_arlen), .s_axi_arsize(m_arsize),
        .s_axi_arburst(m_arburst), .s_axi_arlock(m_arlock), .s_axi_arcache(m_arcache), .s_axi_arprot(m_arprot),
        .s_axi_arqos(m_arqos), .s_axi_arregion(m_arregion), .s_axi_aruser(m_aruser), .s_axi_arvalid(m_arvalid),
        .s_axi_arready(m_arready), .s_axi_rid(m_rid), .s_axi_rdata(m_rdata), .s_axi_rresp(m_rresp),
        .s_axi_rlast(m_rlast), .s_axi_ruser(m_ruser), .s_axi_rvalid(m_rvalid), .s_axi_rready(m_rready),
        .i_cfg_start_clear(1'b0), .o_cfg_done_clear(), .o_dbg_vr(), .o_dbg_fub_vr(), .o_dbg_bram_wr(),
        .o_dbg_bram_rd(), .o_dbg_busy_wr(), .o_dbg_busy_rd()
    );
endmodule : ref_cache_tb
