// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// Module: rs_axi4_engines_tb_top
// Description: Loopback fixture for the Reed-Solomon AXI4 job engines.
//
//   One sdpram_slave_axi4_axi4 memory, with rs_axi4_write_engine on its WRITE
//   channels and rs_axi4_read_engine on its READ channels. AXI4's write and
//   read channel sets are independent, so the two engines share the one slave
//   port without any arbitration between them.
//
//   The test writes a known pattern into the memory through the write engine,
//   reads it back through the read engine, and compares. That covers both
//   engines and the memory in the combination the harness will actually use,
//   and it needs BFMs only on the two simple valid/ready stream ports -- no
//   AXI4 BFM, because the real memory is the far end.
//
//   USE_WSTRB is 0 here, which is the point of having plumbed it: the write
//   engine only ever writes whole words, and at the default the memory cannot
//   infer block RAM. This fixture is where that combination gets exercised.
`timescale 1ns / 1ps

module rs_axi4_engines_tb_top #(
    parameter int ADDR_WIDTH      = 32,
    parameter int DATA_WIDTH      = 32,
    parameter int ID_WIDTH        = 4,
    parameter int MEM_DEPTH       = 1024,
    parameter int MAX_OUTSTANDING = 4
) (
    input  logic                    aclk,
    input  logic                    aresetn,

    // -- write engine job + stream in -------------------------------------
    input  logic                    wr_start,
    input  logic [ADDR_WIDTH-1:0]   wr_addr,
    input  logic [31:0]             wr_beats,
    input  logic [7:0]              wr_burst_len,
    output logic                    wr_done,
    output logic                    wr_resp_err,
    input  logic                    in_valid,
    output logic                    in_ready,
    input  logic [DATA_WIDTH-1:0]   in_data,
    input  logic                    in_last,

    // -- read engine job + stream out -------------------------------------
    input  logic                    rd_start,
    input  logic [ADDR_WIDTH-1:0]   rd_addr,
    input  logic [31:0]             rd_beats,
    input  logic [7:0]              rd_burst_len,
    input  logic [15:0]             rd_beats_per_block,
    output logic                    rd_done,
    output logic                    rd_resp_err,
    output logic                    out_valid,
    input  logic                    out_ready,
    output logic [DATA_WIDTH-1:0]   out_data,
    output logic                    out_last
);

    localparam int SIZE_BYTES = $clog2(DATA_WIDTH / 8);   // AXI axsize

    // -- write channels ----------------------------------------------------
    logic [ID_WIDTH-1:0]     awid;
    logic [ADDR_WIDTH-1:0]   awaddr;
    logic [7:0]              awlen;
    logic [2:0]              awsize;
    logic [1:0]              awburst;
    logic                    awlock;
    logic [3:0]              awcache;
    logic [2:0]              awprot;
    logic [3:0]              awqos, awregion;
    logic [0:0]              awuser, wuser, buser, aruser, ruser;
    logic                    awvalid, awready;
    logic [DATA_WIDTH-1:0]   wdata;
    logic [DATA_WIDTH/8-1:0] wstrb;
    logic                    wlast, wvalid, wready;
    logic [ID_WIDTH-1:0]     bid;
    logic [1:0]              bresp;
    logic                    bvalid, bready;

    // -- read channels -----------------------------------------------------
    logic [ID_WIDTH-1:0]     arid;
    logic [ADDR_WIDTH-1:0]   araddr;
    logic [7:0]              arlen;
    logic [2:0]              arsize;
    logic [1:0]              arburst;
    logic                    arlock;
    logic [3:0]              arcache;
    logic [2:0]              arprot;
    logic [3:0]              arqos, arregion;
    logic                    arvalid, arready;
    logic [ID_WIDTH-1:0]     rid;
    logic [DATA_WIDTH-1:0]   rdata;
    logic [1:0]              rresp;
    logic                    rlast, rvalid, rready;

    rs_axi4_write_engine #(
        .ADDR_WIDTH(ADDR_WIDTH), .DATA_WIDTH(DATA_WIDTH), .ID_WIDTH(ID_WIDTH),
        .MAX_OUTSTANDING(MAX_OUTSTANDING), .USER_WIDTH(1)
    ) u_wr (
        .aclk(aclk), .aresetn(aresetn),
        .cfg_start(wr_start), .cfg_dst_addr(wr_addr), .cfg_beats(wr_beats),
        .cfg_burst_len(wr_burst_len), .cfg_axi_id(ID_WIDTH'(1)),
        .cfg_axi_size(3'(SIZE_BYTES)),
        .cfg_done(wr_done), .resp_err(wr_resp_err),
        .in_valid(in_valid), .in_ready(in_ready), .in_data(in_data), .in_last(in_last),
        .m_axi_awid(awid), .m_axi_awaddr(awaddr), .m_axi_awlen(awlen),
        .m_axi_awsize(awsize), .m_axi_awburst(awburst), .m_axi_awlock(awlock),
        .m_axi_awcache(awcache), .m_axi_awprot(awprot), .m_axi_awqos(awqos),
        .m_axi_awregion(awregion), .m_axi_awuser(awuser),
        .m_axi_awvalid(awvalid), .m_axi_awready(awready),
        .m_axi_wdata(wdata), .m_axi_wstrb(wstrb), .m_axi_wlast(wlast),
        .m_axi_wuser(wuser), .m_axi_wvalid(wvalid), .m_axi_wready(wready),
        .m_axi_bid(bid), .m_axi_bresp(bresp), .m_axi_buser(buser),
        .m_axi_bvalid(bvalid), .m_axi_bready(bready));

    rs_axi4_read_engine #(
        .ADDR_WIDTH(ADDR_WIDTH), .DATA_WIDTH(DATA_WIDTH), .ID_WIDTH(ID_WIDTH),
        .MAX_OUTSTANDING(MAX_OUTSTANDING), .USER_WIDTH(1)
    ) u_rd (
        .aclk(aclk), .aresetn(aresetn),
        .cfg_start(rd_start), .cfg_src_addr(rd_addr), .cfg_beats(rd_beats),
        .cfg_burst_len(rd_burst_len), .cfg_beats_per_block(rd_beats_per_block),
        .cfg_axi_id(ID_WIDTH'(2)), .cfg_axi_size(3'(SIZE_BYTES)),
        .cfg_done(rd_done), .resp_err(rd_resp_err),
        .out_valid(out_valid), .out_ready(out_ready), .out_data(out_data),
        .out_last(out_last),
        .m_axi_arid(arid), .m_axi_araddr(araddr), .m_axi_arlen(arlen),
        .m_axi_arsize(arsize), .m_axi_arburst(arburst), .m_axi_arlock(arlock),
        .m_axi_arcache(arcache), .m_axi_arprot(arprot), .m_axi_arqos(arqos),
        .m_axi_arregion(arregion), .m_axi_aruser(aruser),
        .m_axi_arvalid(arvalid), .m_axi_arready(arready),
        .m_axi_rid(rid), .m_axi_rdata(rdata), .m_axi_rresp(rresp),
        .m_axi_rlast(rlast), .m_axi_ruser(ruser),
        .m_axi_rvalid(rvalid), .m_axi_rready(rready));

    // USE_WSTRB = 0: the write engine writes whole words only, and at the
    // default this memory drops out of block RAM into distributed RAM.
    /* verilator lint_off PINCONNECTEMPTY */
    sdpram_slave_axi4_axi4 #(
        .AXI_ID_WIDTH(ID_WIDTH), .ADDR_WIDTH(ADDR_WIDTH), .DATA_WIDTH(DATA_WIDTH),
        .USER_WIDTH(1), .MEM_DEPTH(MEM_DEPTH), .USE_WSTRB(1'b0)
    ) u_mem (
        .aclk(aclk), .aresetn(aresetn),
        .s_axi_awid(awid), .s_axi_awaddr(awaddr), .s_axi_awlen(awlen),
        .s_axi_awsize(awsize), .s_axi_awburst(awburst), .s_axi_awlock(awlock),
        .s_axi_awcache(awcache), .s_axi_awprot(awprot), .s_axi_awqos(awqos),
        .s_axi_awregion(awregion), .s_axi_awuser(awuser),
        .s_axi_awvalid(awvalid), .s_axi_awready(awready),
        .s_axi_wdata(wdata), .s_axi_wstrb(wstrb), .s_axi_wlast(wlast),
        .s_axi_wuser(wuser), .s_axi_wvalid(wvalid), .s_axi_wready(wready),
        .s_axi_bid(bid), .s_axi_bresp(bresp), .s_axi_buser(buser),
        .s_axi_bvalid(bvalid), .s_axi_bready(bready),
        .s_axi_arid(arid), .s_axi_araddr(araddr), .s_axi_arlen(arlen),
        .s_axi_arsize(arsize), .s_axi_arburst(arburst), .s_axi_arlock(arlock),
        .s_axi_arcache(arcache), .s_axi_arprot(arprot), .s_axi_arqos(arqos),
        .s_axi_arregion(arregion), .s_axi_aruser(aruser),
        .s_axi_arvalid(arvalid), .s_axi_arready(arready),
        .s_axi_rid(rid), .s_axi_rdata(rdata), .s_axi_rresp(rresp),
        .s_axi_rlast(rlast), .s_axi_ruser(ruser),
        .s_axi_rvalid(rvalid), .s_axi_rready(rready),
        .i_cfg_start_clear(1'b0), .o_cfg_done_clear(),
        .o_dbg_vr(), .o_dbg_fub_vr(), .o_dbg_bram_wr(), .o_dbg_bram_rd(),
        .o_dbg_busy_wr(), .o_dbg_busy_rd());
    /* verilator lint_on PINCONNECTEMPTY */

endmodule
