// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// Module: bch_axi4_loop_tb_top
// Description: Full memory-to-memory loop for the BCH AXI4 codec tops.
//
//   messages -> [seed write engine] -> M1 -> [bch_encoder_axi4] -> M2
//            -> [bch_decoder_axi4]   -> M3 -> [drain read engine] -> messages
//
//   Three sdpram memories, each with exactly one writer on its write channels
//   and one reader on its read channels. AXI4's write and read channel sets
//   are independent, so nothing in the chain needs arbitration.
`timescale 1ns / 1ps

module bch_axi4_loop_tb_top #(
    parameter int FIELD_DIM     = bch_pkg::FIELD_DIM,
    parameter int PRIM_POLY     = bch_pkg::PRIM_POLY,
    parameter int T_BITS        = bch_pkg::T_BITS,
    parameter int N_BITS        = bch_pkg::N_BITS,
    parameter int FIRST_ROOT    = bch_pkg::FIRST_ROOT,
    parameter int DATA_WIDTH    = bch_pkg::BITS_PER_BEAT,
    parameter int ADDR_WIDTH    = 32,
    parameter int ID_WIDTH      = 4,
    parameter int MEM_DEPTH     = 2048,
    parameter int MAX_OUTSTANDING = 4
) (
    input  logic                    aclk,
    input  logic                    aresetn,

    // -- seed: push messages into M1 -----------------------------------------
    input  logic                    seed_start,
    input  logic [31:0]             seed_beats,
    input  logic [7:0]              burst_len,
    output logic                    seed_done,
    input  logic                    in_valid,
    output logic                    in_ready,
    input  logic [DATA_WIDTH-1:0]   in_data,
    input  logic                    in_last,

    // -- encode job: M1 -> M2 ------------------------------------------------
    input  logic                    enc_start,
    input  logic [15:0]             blocks,
    output logic                    enc_done,
    output logic                    enc_resp_err,
    output logic                    enc_frame_err,

    // -- decode job: M2 -> M3 ------------------------------------------------
    input  logic                    dec_start,
    output logic                    dec_done,
    output logic                    dec_resp_err,
    output logic [31:0]             dec_blocks_ok,
    output logic [31:0]             dec_blocks_corrected,
    output logic [31:0]             dec_blocks_uncorrectable,
    output logic [31:0]             dec_blocks_frame_err,
    output logic [31:0]             dec_bits_corrected,

    // -- drain: read the recovered messages out of M3 ------------------------
    input  logic                    drain_start,
    input  logic [31:0]             drain_beats,
    input  logic [15:0]             drain_per_block,
    output logic                    drain_done,
    output logic                    out_valid,
    input  logic                    out_ready,
    output logic [DATA_WIDTH-1:0]   out_data,
    output logic                    out_last
);

    localparam int SIZE_B = $clog2(DATA_WIDTH / 8);

    // ---- memory 1: messages in, encoder reads ----
    logic [ID_WIDTH-1:0]     m1_awid, m1_bid, m1_arid, m1_rid;
    logic [ADDR_WIDTH-1:0]   m1_awaddr, m1_araddr;
    logic [7:0]              m1_awlen, m1_arlen;
    logic [2:0]              m1_awsize, m1_awprot, m1_arsize, m1_arprot;
    logic [1:0]              m1_awburst, m1_bresp, m1_arburst, m1_rresp;
    logic                    m1_awlock, m1_arlock;
    logic [3:0]              m1_awcache, m1_awqos, m1_awregion;
    logic [3:0]              m1_arcache, m1_arqos, m1_arregion;
    logic [0:0]              m1_awuser, m1_wuser, m1_buser, m1_aruser, m1_ruser;
    logic                    m1_awvalid, m1_awready, m1_wvalid, m1_wready;
    logic                    m1_wlast, m1_bvalid, m1_bready;
    logic                    m1_arvalid, m1_arready, m1_rvalid, m1_rready, m1_rlast;
    logic [DATA_WIDTH-1:0]   m1_wdata, m1_rdata;
    logic [DATA_WIDTH/8-1:0] m1_wstrb;

    /* verilator lint_off PINCONNECTEMPTY */
    sdpram_slave_axi4_axi4 #(
        .AXI_ID_WIDTH(ID_WIDTH), .ADDR_WIDTH(ADDR_WIDTH), .DATA_WIDTH(DATA_WIDTH),
        .USER_WIDTH(1), .MEM_DEPTH(MEM_DEPTH), .USE_WSTRB(1'b0)
    ) u_mem1 (
        .aclk(aclk), .aresetn(aresetn),
        .s_axi_awid(m1_awid), .s_axi_awaddr(m1_awaddr), .s_axi_awlen(m1_awlen),
        .s_axi_awsize(m1_awsize), .s_axi_awburst(m1_awburst), .s_axi_awlock(m1_awlock),
        .s_axi_awcache(m1_awcache), .s_axi_awprot(m1_awprot), .s_axi_awqos(m1_awqos),
        .s_axi_awregion(m1_awregion), .s_axi_awuser(m1_awuser),
        .s_axi_awvalid(m1_awvalid), .s_axi_awready(m1_awready),
        .s_axi_wdata(m1_wdata), .s_axi_wstrb(m1_wstrb), .s_axi_wlast(m1_wlast),
        .s_axi_wuser(m1_wuser), .s_axi_wvalid(m1_wvalid), .s_axi_wready(m1_wready),
        .s_axi_bid(m1_bid), .s_axi_bresp(m1_bresp), .s_axi_buser(m1_buser),
        .s_axi_bvalid(m1_bvalid), .s_axi_bready(m1_bready),
        .s_axi_arid(m1_arid), .s_axi_araddr(m1_araddr), .s_axi_arlen(m1_arlen),
        .s_axi_arsize(m1_arsize), .s_axi_arburst(m1_arburst), .s_axi_arlock(m1_arlock),
        .s_axi_arcache(m1_arcache), .s_axi_arprot(m1_arprot), .s_axi_arqos(m1_arqos),
        .s_axi_arregion(m1_arregion), .s_axi_aruser(m1_aruser),
        .s_axi_arvalid(m1_arvalid), .s_axi_arready(m1_arready),
        .s_axi_rid(m1_rid), .s_axi_rdata(m1_rdata), .s_axi_rresp(m1_rresp),
        .s_axi_rlast(m1_rlast), .s_axi_ruser(m1_ruser),
        .s_axi_rvalid(m1_rvalid), .s_axi_rready(m1_rready),
        .i_cfg_start_clear(1'b0), .o_cfg_done_clear(),
        .o_dbg_vr(), .o_dbg_fub_vr(), .o_dbg_bram_wr(), .o_dbg_bram_rd(),
        .o_dbg_busy_wr(), .o_dbg_busy_rd());
    /* verilator lint_on PINCONNECTEMPTY */


    // ---- memory 2: codewords: encoder writes, decoder reads ----
    logic [ID_WIDTH-1:0]     m2_awid, m2_bid, m2_arid, m2_rid;
    logic [ADDR_WIDTH-1:0]   m2_awaddr, m2_araddr;
    logic [7:0]              m2_awlen, m2_arlen;
    logic [2:0]              m2_awsize, m2_awprot, m2_arsize, m2_arprot;
    logic [1:0]              m2_awburst, m2_bresp, m2_arburst, m2_rresp;
    logic                    m2_awlock, m2_arlock;
    logic [3:0]              m2_awcache, m2_awqos, m2_awregion;
    logic [3:0]              m2_arcache, m2_arqos, m2_arregion;
    logic [0:0]              m2_awuser, m2_wuser, m2_buser, m2_aruser, m2_ruser;
    logic                    m2_awvalid, m2_awready, m2_wvalid, m2_wready;
    logic                    m2_wlast, m2_bvalid, m2_bready;
    logic                    m2_arvalid, m2_arready, m2_rvalid, m2_rready, m2_rlast;
    logic [DATA_WIDTH-1:0]   m2_wdata, m2_rdata;
    logic [DATA_WIDTH/8-1:0] m2_wstrb;

    /* verilator lint_off PINCONNECTEMPTY */
    sdpram_slave_axi4_axi4 #(
        .AXI_ID_WIDTH(ID_WIDTH), .ADDR_WIDTH(ADDR_WIDTH), .DATA_WIDTH(DATA_WIDTH),
        .USER_WIDTH(1), .MEM_DEPTH(MEM_DEPTH), .USE_WSTRB(1'b0)
    ) u_mem2 (
        .aclk(aclk), .aresetn(aresetn),
        .s_axi_awid(m2_awid), .s_axi_awaddr(m2_awaddr), .s_axi_awlen(m2_awlen),
        .s_axi_awsize(m2_awsize), .s_axi_awburst(m2_awburst), .s_axi_awlock(m2_awlock),
        .s_axi_awcache(m2_awcache), .s_axi_awprot(m2_awprot), .s_axi_awqos(m2_awqos),
        .s_axi_awregion(m2_awregion), .s_axi_awuser(m2_awuser),
        .s_axi_awvalid(m2_awvalid), .s_axi_awready(m2_awready),
        .s_axi_wdata(m2_wdata), .s_axi_wstrb(m2_wstrb), .s_axi_wlast(m2_wlast),
        .s_axi_wuser(m2_wuser), .s_axi_wvalid(m2_wvalid), .s_axi_wready(m2_wready),
        .s_axi_bid(m2_bid), .s_axi_bresp(m2_bresp), .s_axi_buser(m2_buser),
        .s_axi_bvalid(m2_bvalid), .s_axi_bready(m2_bready),
        .s_axi_arid(m2_arid), .s_axi_araddr(m2_araddr), .s_axi_arlen(m2_arlen),
        .s_axi_arsize(m2_arsize), .s_axi_arburst(m2_arburst), .s_axi_arlock(m2_arlock),
        .s_axi_arcache(m2_arcache), .s_axi_arprot(m2_arprot), .s_axi_arqos(m2_arqos),
        .s_axi_arregion(m2_arregion), .s_axi_aruser(m2_aruser),
        .s_axi_arvalid(m2_arvalid), .s_axi_arready(m2_arready),
        .s_axi_rid(m2_rid), .s_axi_rdata(m2_rdata), .s_axi_rresp(m2_rresp),
        .s_axi_rlast(m2_rlast), .s_axi_ruser(m2_ruser),
        .s_axi_rvalid(m2_rvalid), .s_axi_rready(m2_rready),
        .i_cfg_start_clear(1'b0), .o_cfg_done_clear(),
        .o_dbg_vr(), .o_dbg_fub_vr(), .o_dbg_bram_wr(), .o_dbg_bram_rd(),
        .o_dbg_busy_wr(), .o_dbg_busy_rd());
    /* verilator lint_on PINCONNECTEMPTY */


    // ---- memory 3: recovered messages: decoder writes, drain reads ----
    logic [ID_WIDTH-1:0]     m3_awid, m3_bid, m3_arid, m3_rid;
    logic [ADDR_WIDTH-1:0]   m3_awaddr, m3_araddr;
    logic [7:0]              m3_awlen, m3_arlen;
    logic [2:0]              m3_awsize, m3_awprot, m3_arsize, m3_arprot;
    logic [1:0]              m3_awburst, m3_bresp, m3_arburst, m3_rresp;
    logic                    m3_awlock, m3_arlock;
    logic [3:0]              m3_awcache, m3_awqos, m3_awregion;
    logic [3:0]              m3_arcache, m3_arqos, m3_arregion;
    logic [0:0]              m3_awuser, m3_wuser, m3_buser, m3_aruser, m3_ruser;
    logic                    m3_awvalid, m3_awready, m3_wvalid, m3_wready;
    logic                    m3_wlast, m3_bvalid, m3_bready;
    logic                    m3_arvalid, m3_arready, m3_rvalid, m3_rready, m3_rlast;
    logic [DATA_WIDTH-1:0]   m3_wdata, m3_rdata;
    logic [DATA_WIDTH/8-1:0] m3_wstrb;

    /* verilator lint_off PINCONNECTEMPTY */
    sdpram_slave_axi4_axi4 #(
        .AXI_ID_WIDTH(ID_WIDTH), .ADDR_WIDTH(ADDR_WIDTH), .DATA_WIDTH(DATA_WIDTH),
        .USER_WIDTH(1), .MEM_DEPTH(MEM_DEPTH), .USE_WSTRB(1'b0)
    ) u_mem3 (
        .aclk(aclk), .aresetn(aresetn),
        .s_axi_awid(m3_awid), .s_axi_awaddr(m3_awaddr), .s_axi_awlen(m3_awlen),
        .s_axi_awsize(m3_awsize), .s_axi_awburst(m3_awburst), .s_axi_awlock(m3_awlock),
        .s_axi_awcache(m3_awcache), .s_axi_awprot(m3_awprot), .s_axi_awqos(m3_awqos),
        .s_axi_awregion(m3_awregion), .s_axi_awuser(m3_awuser),
        .s_axi_awvalid(m3_awvalid), .s_axi_awready(m3_awready),
        .s_axi_wdata(m3_wdata), .s_axi_wstrb(m3_wstrb), .s_axi_wlast(m3_wlast),
        .s_axi_wuser(m3_wuser), .s_axi_wvalid(m3_wvalid), .s_axi_wready(m3_wready),
        .s_axi_bid(m3_bid), .s_axi_bresp(m3_bresp), .s_axi_buser(m3_buser),
        .s_axi_bvalid(m3_bvalid), .s_axi_bready(m3_bready),
        .s_axi_arid(m3_arid), .s_axi_araddr(m3_araddr), .s_axi_arlen(m3_arlen),
        .s_axi_arsize(m3_arsize), .s_axi_arburst(m3_arburst), .s_axi_arlock(m3_arlock),
        .s_axi_arcache(m3_arcache), .s_axi_arprot(m3_arprot), .s_axi_arqos(m3_arqos),
        .s_axi_arregion(m3_arregion), .s_axi_aruser(m3_aruser),
        .s_axi_arvalid(m3_arvalid), .s_axi_arready(m3_arready),
        .s_axi_rid(m3_rid), .s_axi_rdata(m3_rdata), .s_axi_rresp(m3_rresp),
        .s_axi_rlast(m3_rlast), .s_axi_ruser(m3_ruser),
        .s_axi_rvalid(m3_rvalid), .s_axi_rready(m3_rready),
        .i_cfg_start_clear(1'b0), .o_cfg_done_clear(),
        .o_dbg_vr(), .o_dbg_fub_vr(), .o_dbg_bram_wr(), .o_dbg_bram_rd(),
        .o_dbg_busy_wr(), .o_dbg_busy_rd());
    /* verilator lint_on PINCONNECTEMPTY */


    // ---- seed write engine -> M1 ----
    rs_axi4_write_engine #(
        .ADDR_WIDTH(ADDR_WIDTH), .DATA_WIDTH(DATA_WIDTH), .ID_WIDTH(ID_WIDTH),
        .MAX_OUTSTANDING(MAX_OUTSTANDING), .USER_WIDTH(1)
    ) u_seed (
        .aclk(aclk), .aresetn(aresetn),
        .cfg_start(seed_start), .cfg_dst_addr('0), .cfg_beats(seed_beats),
        .cfg_burst_len(burst_len), .cfg_axi_id(ID_WIDTH'(1)), .cfg_axi_size(3'(SIZE_B)),
        .cfg_done(seed_done), .resp_err(),
        .in_valid(in_valid), .in_ready(in_ready), .in_data(in_data), .in_last(in_last),
        .m_axi_awid(m1_awid), .m_axi_awaddr(m1_awaddr), .m_axi_awlen(m1_awlen),
        .m_axi_awsize(m1_awsize), .m_axi_awburst(m1_awburst), .m_axi_awlock(m1_awlock),
        .m_axi_awcache(m1_awcache), .m_axi_awprot(m1_awprot), .m_axi_awqos(m1_awqos),
        .m_axi_awregion(m1_awregion), .m_axi_awuser(m1_awuser),
        .m_axi_awvalid(m1_awvalid), .m_axi_awready(m1_awready),
        .m_axi_wdata(m1_wdata), .m_axi_wstrb(m1_wstrb), .m_axi_wlast(m1_wlast),
        .m_axi_wuser(m1_wuser), .m_axi_wvalid(m1_wvalid), .m_axi_wready(m1_wready),
        .m_axi_bid(m1_bid), .m_axi_bresp(m1_bresp), .m_axi_buser(m1_buser),
        .m_axi_bvalid(m1_bvalid), .m_axi_bready(m1_bready));

    // ---- encoder: M1 -> M2 ----
    bch_encoder_axi4 #(
        .FIELD_DIM(FIELD_DIM), .PRIM_POLY(PRIM_POLY), .T_BITS(T_BITS),
        .N_BITS(N_BITS), .FIRST_ROOT(FIRST_ROOT), .DATA_WIDTH(DATA_WIDTH),
        .ADDR_WIDTH(ADDR_WIDTH), .ID_WIDTH(ID_WIDTH),
        .MAX_OUTSTANDING(MAX_OUTSTANDING), .USER_WIDTH(1)
    ) u_enc (
        .aclk(aclk), .aresetn(aresetn),
        .cfg_start(enc_start), .cfg_src_addr('0), .cfg_dst_addr('0),
        .cfg_blocks(blocks), .cfg_burst_len(burst_len), .cfg_axi_id(ID_WIDTH'(2)),
        .cfg_done(enc_done), .resp_err(enc_resp_err), .frame_err(enc_frame_err),
        .m_axi_arid(m1_arid), .m_axi_araddr(m1_araddr), .m_axi_arlen(m1_arlen),
        .m_axi_arsize(m1_arsize), .m_axi_arburst(m1_arburst), .m_axi_arlock(m1_arlock),
        .m_axi_arcache(m1_arcache), .m_axi_arprot(m1_arprot), .m_axi_arqos(m1_arqos),
        .m_axi_arregion(m1_arregion), .m_axi_aruser(m1_aruser),
        .m_axi_arvalid(m1_arvalid), .m_axi_arready(m1_arready),
        .m_axi_rid(m1_rid), .m_axi_rdata(m1_rdata), .m_axi_rresp(m1_rresp),
        .m_axi_rlast(m1_rlast), .m_axi_ruser(m1_ruser),
        .m_axi_rvalid(m1_rvalid), .m_axi_rready(m1_rready),
        .m_axi_awid(m2_awid), .m_axi_awaddr(m2_awaddr), .m_axi_awlen(m2_awlen),
        .m_axi_awsize(m2_awsize), .m_axi_awburst(m2_awburst), .m_axi_awlock(m2_awlock),
        .m_axi_awcache(m2_awcache), .m_axi_awprot(m2_awprot), .m_axi_awqos(m2_awqos),
        .m_axi_awregion(m2_awregion), .m_axi_awuser(m2_awuser),
        .m_axi_awvalid(m2_awvalid), .m_axi_awready(m2_awready),
        .m_axi_wdata(m2_wdata), .m_axi_wstrb(m2_wstrb), .m_axi_wlast(m2_wlast),
        .m_axi_wuser(m2_wuser), .m_axi_wvalid(m2_wvalid), .m_axi_wready(m2_wready),
        .m_axi_bid(m2_bid), .m_axi_bresp(m2_bresp), .m_axi_buser(m2_buser),
        .m_axi_bvalid(m2_bvalid), .m_axi_bready(m2_bready));

    // ---- decoder: M2 -> M3 ----
    bch_decoder_axi4 #(
        .FIELD_DIM(FIELD_DIM), .PRIM_POLY(PRIM_POLY), .T_BITS(T_BITS),
        .N_BITS(N_BITS), .FIRST_ROOT(FIRST_ROOT), .DATA_WIDTH(DATA_WIDTH),
        .ADDR_WIDTH(ADDR_WIDTH), .ID_WIDTH(ID_WIDTH),
        .MAX_OUTSTANDING(MAX_OUTSTANDING), .USER_WIDTH(1)
    ) u_dec (
        .aclk(aclk), .aresetn(aresetn),
        .cfg_start(dec_start), .cfg_src_addr('0), .cfg_dst_addr('0),
        .cfg_blocks(blocks), .cfg_burst_len(burst_len), .cfg_axi_id(ID_WIDTH'(3)),
        .cfg_done(dec_done), .resp_err(dec_resp_err),
        .out_status_ok(), .out_status_corrected(), .out_status_uncorrectable(),
        .out_status_frame_err(),
        .stat_blocks_ok(dec_blocks_ok), .stat_blocks_corrected(dec_blocks_corrected),
        .stat_blocks_uncorrectable(dec_blocks_uncorrectable),
        .stat_blocks_frame_err(dec_blocks_frame_err),
        .stat_bits_corrected(dec_bits_corrected),
        .m_axi_arid(m2_arid), .m_axi_araddr(m2_araddr), .m_axi_arlen(m2_arlen),
        .m_axi_arsize(m2_arsize), .m_axi_arburst(m2_arburst), .m_axi_arlock(m2_arlock),
        .m_axi_arcache(m2_arcache), .m_axi_arprot(m2_arprot), .m_axi_arqos(m2_arqos),
        .m_axi_arregion(m2_arregion), .m_axi_aruser(m2_aruser),
        .m_axi_arvalid(m2_arvalid), .m_axi_arready(m2_arready),
        .m_axi_rid(m2_rid), .m_axi_rdata(m2_rdata), .m_axi_rresp(m2_rresp),
        .m_axi_rlast(m2_rlast), .m_axi_ruser(m2_ruser),
        .m_axi_rvalid(m2_rvalid), .m_axi_rready(m2_rready),
        .m_axi_awid(m3_awid), .m_axi_awaddr(m3_awaddr), .m_axi_awlen(m3_awlen),
        .m_axi_awsize(m3_awsize), .m_axi_awburst(m3_awburst), .m_axi_awlock(m3_awlock),
        .m_axi_awcache(m3_awcache), .m_axi_awprot(m3_awprot), .m_axi_awqos(m3_awqos),
        .m_axi_awregion(m3_awregion), .m_axi_awuser(m3_awuser),
        .m_axi_awvalid(m3_awvalid), .m_axi_awready(m3_awready),
        .m_axi_wdata(m3_wdata), .m_axi_wstrb(m3_wstrb), .m_axi_wlast(m3_wlast),
        .m_axi_wuser(m3_wuser), .m_axi_wvalid(m3_wvalid), .m_axi_wready(m3_wready),
        .m_axi_bid(m3_bid), .m_axi_bresp(m3_bresp), .m_axi_buser(m3_buser),
        .m_axi_bvalid(m3_bvalid), .m_axi_bready(m3_bready));

    // ---- drain read engine <- M3 ----
    rs_axi4_read_engine #(
        .ADDR_WIDTH(ADDR_WIDTH), .DATA_WIDTH(DATA_WIDTH), .ID_WIDTH(ID_WIDTH),
        .MAX_OUTSTANDING(MAX_OUTSTANDING), .USER_WIDTH(1)
    ) u_drain (
        .aclk(aclk), .aresetn(aresetn),
        .cfg_start(drain_start), .cfg_src_addr('0), .cfg_beats(drain_beats),
        .cfg_burst_len(burst_len), .cfg_beats_per_block(drain_per_block),
        .cfg_axi_id(ID_WIDTH'(4)), .cfg_axi_size(3'(SIZE_B)),
        .cfg_done(drain_done), .resp_err(),
        .out_valid(out_valid), .out_ready(out_ready), .out_data(out_data),
        .out_last(out_last),
        .m_axi_arid(m3_arid), .m_axi_araddr(m3_araddr), .m_axi_arlen(m3_arlen),
        .m_axi_arsize(m3_arsize), .m_axi_arburst(m3_arburst), .m_axi_arlock(m3_arlock),
        .m_axi_arcache(m3_arcache), .m_axi_arprot(m3_arprot), .m_axi_arqos(m3_arqos),
        .m_axi_arregion(m3_arregion), .m_axi_aruser(m3_aruser),
        .m_axi_arvalid(m3_arvalid), .m_axi_arready(m3_arready),
        .m_axi_rid(m3_rid), .m_axi_rdata(m3_rdata), .m_axi_rresp(m3_rresp),
        .m_axi_rlast(m3_rlast), .m_axi_ruser(m3_ruser),
        .m_axi_rvalid(m3_rvalid), .m_axi_rready(m3_rready));

endmodule
