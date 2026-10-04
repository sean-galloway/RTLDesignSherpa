// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// Module: bch_axi4_pipeline
// Description: The BCH loop harness's AXI4 datapath -- a memory-to-memory
//              codec chain with the same stream in, stream out and status
//              surface the stream datapath presents.
//
//   The stream flavour is one flowing pipe. The AXI4 flavour is four sequential
//   jobs over three memories:
//
//     generator -> [seed write]  -> M1
//     M1        -> [ENCODER]     -> M2      packed codewords
//     M2        -> [DECODER]     -> M4      recovered messages
//                   ^-- INJECT sits on the decoder's R channel
//     M4        -> [drain read]  -> checker
//
//   The BCH encoder writes packed codewords (bch_encoder_axi4 includes the
//   beat packer when K % B != 0), and the decoder expects packed input, so the
//   injector sees the same packed stream the decoder does.
//
`timescale 1ns / 1ps
`include "reset_defs.svh"

module bch_axi4_pipeline #(
    parameter int    FIELD_DIM = 13,
    parameter int    PRIM_POLY = 'h201B,
    parameter int    T_BITS    = 8,
    parameter int    N_BITS    = 4224,
    parameter int    FIRST_ROOT = 1,
    parameter int    DATA_WIDTH = 32,
    parameter int    ADDR_WIDTH = 32,
    parameter int    ID_WIDTH   = 4,
    parameter int    MEM_DEPTH  = 4096,
    parameter int    MAX_OUTSTANDING = 4,
    // derived
    parameter int    K_BITS         = N_BITS - bch_pkg::bch_degree_g(FIELD_DIM, PRIM_POLY, T_BITS, FIRST_ROOT),
    parameter int    BITS_PER_BEAT  = DATA_WIDTH,
    parameter int    SYMBOLS_PER_BEAT = DATA_WIDTH / 8
) (
    input  logic                        aclk,
    input  logic                        aresetn,

    input  logic                        start,
    input  logic [15:0]                 cfg_blocks,
    input  logic [7:0]                  cfg_burst_len,
    output logic                        busy,
    output logic                        done,

    input  logic                        in_valid,
    output logic                        in_ready,
    input  logic [DATA_WIDTH-1:0]       in_data,
    input  logic                        in_last,

    output logic                        out_valid,
    input  logic                        out_ready,
    output logic [DATA_WIDTH-1:0]       out_data,
    output logic [SYMBOLS_PER_BEAT-1:0] out_keep,
    output logic                        out_last,

    input  logic [1:0]                  inj_mode,
    input  logic [7:0]                  inj_count,
    input  logic [15:0]                 inj_rate,
    input  logic [31:0]                 inj_seed,
    input  logic                        inj_seed_load,
    input  logic                        inj_clear,

    output logic                        obs_cw_out_valid,
    output logic                        obs_cw_out_ready,
    output logic                        obs_cw_in_valid,
    output logic                        obs_cw_in_ready,
    input  logic                        obs_meter_clear,
    input  logic                        obs_apb_psel,
    input  logic                        obs_apb_penable,
    output logic                        obs_apb_pready,
    input  logic [11:0]                 obs_apb_paddr,
    input  logic                        obs_apb_pwrite,
    input  logic [31:0]                 obs_apb_pwdata,
    input  logic [3:0]                  obs_apb_pstrb,
    output logic [31:0]                 obs_apb_prdata,
    output logic                        obs_apb_pslverr,

    output logic                        obs_enc_active,
    output logic                        obs_dec_active,

    output logic                        resp_err,
    output logic                        enc_frame_err,
    output logic [31:0]                 blk_ok,
    output logic [31:0]                 blk_corr,
    output logic [31:0]                 blk_unc,
    output logic [31:0]                 blk_frame,
    output logic [31:0]                 sym_corr,
    output logic [31:0]                 inj_bits,
    output logic [31:0]                 inj_blocks,
    output logic [31:0]                 inj_over_t,
    output logic [7:0]                  inj_last,
    output logic [4:0]                  stage_done
);

    import bch_pkg::bch_beats;

    localparam int AW  = ADDR_WIDTH;
    localparam int DW  = DATA_WIDTH;
    localparam int IDW = ID_WIDTH;
    localparam int S   = SYMBOLS_PER_BEAT;
    localparam int SIZE_B  = $clog2(DW / 8);
    localparam int K_BEATS = bch_beats(K_BITS, DW);
    localparam int CW_BEATS = bch_beats(N_BITS, DW);

    // ---- memory 1: messages
    logic [IDW-1:0]          m1_awid, m1_bid, m1_arid, m1_rid;
    logic [AW-1:0]           m1_awaddr, m1_araddr;
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
    logic [DW-1:0]           m1_wdata, m1_rdata;
    logic [DW/8-1:0]         m1_wstrb;

    /* verilator lint_off PINCONNECTEMPTY */
    sdpram_slave_axi4_axi4 #(
        .AXI_ID_WIDTH(IDW), .ADDR_WIDTH(AW), .DATA_WIDTH(DW),
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

    // ---- memory 2: codewords
    logic [IDW-1:0]          m2_awid, m2_bid, m2_arid, m2_rid;
    logic [AW-1:0]           m2_awaddr, m2_araddr;
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
    logic [DW-1:0]           m2_wdata, m2_rdata;
    logic [DW/8-1:0]         m2_wstrb;

    /* verilator lint_off PINCONNECTEMPTY */
    sdpram_slave_axi4_axi4 #(
        .AXI_ID_WIDTH(IDW), .ADDR_WIDTH(AW), .DATA_WIDTH(DW),
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

    // ---- memory 4: recovered messages
    logic [IDW-1:0]          m4_awid, m4_bid, m4_arid, m4_rid;
    logic [AW-1:0]           m4_awaddr, m4_araddr;
    logic [7:0]              m4_awlen, m4_arlen;
    logic [2:0]              m4_awsize, m4_awprot, m4_arsize, m4_arprot;
    logic [1:0]              m4_awburst, m4_bresp, m4_arburst, m4_rresp;
    logic                    m4_awlock, m4_arlock;
    logic [3:0]              m4_awcache, m4_awqos, m4_awregion;
    logic [3:0]              m4_arcache, m4_arqos, m4_arregion;
    logic [0:0]              m4_awuser, m4_wuser, m4_buser, m4_aruser, m4_ruser;
    logic                    m4_awvalid, m4_awready, m4_wvalid, m4_wready;
    logic                    m4_wlast, m4_bvalid, m4_bready;
    logic                    m4_arvalid, m4_arready, m4_rvalid, m4_rready, m4_rlast;
    logic [DW-1:0]           m4_wdata, m4_rdata;
    logic [DW/8-1:0]         m4_wstrb;

    /* verilator lint_off PINCONNECTEMPTY */
    sdpram_slave_axi4_axi4 #(
        .AXI_ID_WIDTH(IDW), .ADDR_WIDTH(AW), .DATA_WIDTH(DW),
        .USER_WIDTH(1), .MEM_DEPTH(MEM_DEPTH), .USE_WSTRB(1'b0)
    ) u_mem4 (
        .aclk(aclk), .aresetn(aresetn),
        .s_axi_awid(m4_awid), .s_axi_awaddr(m4_awaddr), .s_axi_awlen(m4_awlen),
        .s_axi_awsize(m4_awsize), .s_axi_awburst(m4_awburst), .s_axi_awlock(m4_awlock),
        .s_axi_awcache(m4_awcache), .s_axi_awprot(m4_awprot), .s_axi_awqos(m4_awqos),
        .s_axi_awregion(m4_awregion), .s_axi_awuser(m4_awuser),
        .s_axi_awvalid(m4_awvalid), .s_axi_awready(m4_awready),
        .s_axi_wdata(m4_wdata), .s_axi_wstrb(m4_wstrb), .s_axi_wlast(m4_wlast),
        .s_axi_wuser(m4_wuser), .s_axi_wvalid(m4_wvalid), .s_axi_wready(m4_wready),
        .s_axi_bid(m4_bid), .s_axi_bresp(m4_bresp), .s_axi_buser(m4_buser),
        .s_axi_bvalid(m4_bvalid), .s_axi_bready(m4_bready),
        .s_axi_arid(m4_arid), .s_axi_araddr(m4_araddr), .s_axi_arlen(m4_arlen),
        .s_axi_arsize(m4_arsize), .s_axi_arburst(m4_arburst), .s_axi_arlock(m4_arlock),
        .s_axi_arcache(m4_arcache), .s_axi_arprot(m4_arprot), .s_axi_arqos(m4_arqos),
        .s_axi_arregion(m4_arregion), .s_axi_aruser(m4_aruser),
        .s_axi_arvalid(m4_arvalid), .s_axi_arready(m4_arready),
        .s_axi_rid(m4_rid), .s_axi_rdata(m4_rdata), .s_axi_rresp(m4_rresp),
        .s_axi_rlast(m4_rlast), .s_axi_ruser(m4_ruser),
        .s_axi_rvalid(m4_rvalid), .s_axi_rready(m4_rready),
        .i_cfg_start_clear(1'b0), .o_cfg_done_clear(),
        .o_dbg_vr(), .o_dbg_fub_vr(), .o_dbg_bram_wr(), .o_dbg_bram_rd(),
        .o_dbg_busy_wr(), .o_dbg_busy_rd());
    /* verilator lint_on PINCONNECTEMPTY */

    // =========================================================================
    // stage starts: each on the RISING edge of the previous stage's done
    // =========================================================================
    logic seed_done, enc_done, dec_done, drain_done;
    logic r_seed_d, r_enc_d, r_dec_d;
    logic dec_start, enc_start, drain_start;

    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_seed_d <= 1'b0; r_enc_d <= 1'b0; r_dec_d <= 1'b0;
        end else if (start) begin
            r_seed_d <= 1'b1; r_enc_d <= 1'b1; r_dec_d <= 1'b1;
        end else begin
            r_seed_d <= seed_done; r_enc_d <= enc_done;
            r_dec_d  <= dec_done;
        end
    )

    assign enc_start   = seed_done  && !r_seed_d;
    assign dec_start   = enc_done   && !r_enc_d;
    assign drain_start = dec_done   && !r_dec_d;

    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn))      busy <= 1'b0;
        else if (start)                  busy <= 1'b1;
        else if (drain_done && busy)     busy <= 1'b0;
    )
    assign done       = drain_done;
    assign stage_done = {drain_done, dec_done, 1'b0, enc_done, seed_done};

    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            obs_enc_active <= 1'b0;
            obs_dec_active <= 1'b0;
        end else if (start) begin
            obs_enc_active <= 1'b0;
            obs_dec_active <= 1'b0;
        end else begin
            if      (enc_start) obs_enc_active <= 1'b1;
            else if (enc_done)  obs_enc_active <= 1'b0;
            if      (dec_start) obs_dec_active <= 1'b1;
            else if (dec_done)  obs_dec_active <= 1'b0;
        end
    )

    // =========================================================================
    // 1. seed: the generator's message stream into M1
    // =========================================================================
    logic seed_err;
    rs_axi4_write_engine #(
        .ADDR_WIDTH(AW), .DATA_WIDTH(DW), .ID_WIDTH(IDW),
        .MAX_OUTSTANDING(MAX_OUTSTANDING), .USER_WIDTH(1)
    ) u_seed (
        .aclk(aclk), .aresetn(aresetn),
        .cfg_start(start), .cfg_dst_addr('0),
        .cfg_beats(32'(cfg_blocks) * 32'(K_BEATS)),
        .cfg_burst_len(cfg_burst_len), .cfg_axi_id(IDW'(1)), .cfg_axi_size(3'(SIZE_B)),
        .cfg_done(seed_done), .resp_err(seed_err),
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

    // =========================================================================
    // 2. encode: M1 -> M2
    // =========================================================================
    assign obs_cw_out_valid = m2_wvalid;
    assign obs_cw_out_ready = m2_wready;

    logic enc_err;
    bch_encoder_axi4 #(
        .FIELD_DIM(FIELD_DIM), .PRIM_POLY(PRIM_POLY), .T_BITS(T_BITS),
        .N_BITS(N_BITS), .FIRST_ROOT(FIRST_ROOT), .DATA_WIDTH(DW),
        .ADDR_WIDTH(AW), .ID_WIDTH(IDW), .MAX_OUTSTANDING(MAX_OUTSTANDING),
        .USER_WIDTH(1)
    ) u_enc (
        .aclk(aclk), .aresetn(aresetn),
        .cfg_start(enc_start), .cfg_src_addr('0), .cfg_dst_addr('0),
        .cfg_blocks(cfg_blocks), .cfg_burst_len(cfg_burst_len), .cfg_axi_id(IDW'(2)),
        .cfg_done(enc_done), .resp_err(enc_err), .frame_err(enc_frame_err),
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

    // =========================================================================
    // 3. inject: on the DECODER'S READ CHANNEL
    // =========================================================================
    logic          w_inj_in_fire, w_inj_out_fire;
    logic          w_inj_out_valid, w_inj_out_ready, w_inj_out_last;
    logic [DW-1:0] w_inj_out_data;
    logic [S-1:0]  w_inj_out_keep;
    logic          w_inj_in_ready;

    localparam int N_TAIL = N_BITS % DW;
    logic [15:0] r_inj_beat;
    logic        w_inj_blk_last;
    assign w_inj_blk_last = (r_inj_beat == 16'(CW_BEATS - 1));
    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn))   r_inj_beat <= '0;
        else if (dec_start)           r_inj_beat <= '0;
        else if (w_inj_in_fire)       r_inj_beat <= w_inj_blk_last ? 16'd0
                                                                  : r_inj_beat + 16'd1;
    )

    logic [DW-1:0] w_inj_in_keep;
    assign w_inj_in_keep = (w_inj_blk_last && (N_TAIL != 0))
                         ? DW'((1 << N_TAIL) - 1) : {DW{1'b1}};

    localparam int SB_W = 1 + IDW + 2;
    logic            w_sb_wr_ready, w_sb_rd_valid;
    logic [SB_W-1:0] w_sb_rd_data;
    logic            w_dec_rlast;
    logic [IDW-1:0]  w_dec_rid;
    logic [1:0]      w_dec_rresp;

    /* verilator lint_off PINCONNECTEMPTY */
    gaxi_fifo_sync #(.DATA_WIDTH(SB_W), .DEPTH(8), .REGISTERED(0)) u_inj_sb (
        .axi_aclk(aclk), .axi_aresetn(aresetn),
        .wr_valid(w_inj_in_fire), .wr_ready(w_sb_wr_ready),
        .wr_data({m2_rlast, m2_rid, m2_rresp}),
        .rd_ready(w_inj_out_fire), .count(),
        .rd_valid(w_sb_rd_valid), .rd_data(w_sb_rd_data));
    /* verilator lint_on PINCONNECTEMPTY */

    assign {w_dec_rlast, w_dec_rid, w_dec_rresp} = w_sb_rd_data;

    assign m2_rready     = w_inj_in_ready && w_sb_wr_ready;
    assign w_inj_in_fire = m2_rvalid && m2_rready;

    bch_error_injector #(
        .FIELD_DIM(FIELD_DIM), .PRIM_POLY(PRIM_POLY), .T_BITS(T_BITS), .N_BITS(N_BITS),
        .BITS_PER_BEAT(DW)
    ) u_inj (
        .aclk(aclk), .aresetn(aresetn),
        .in_valid(m2_rvalid && w_sb_wr_ready), .in_ready(w_inj_in_ready),
        .in_data(m2_rdata), .in_keep(w_inj_in_keep), .in_last(w_inj_blk_last),
        .out_valid(w_inj_out_valid), .out_ready(w_inj_out_ready),
        .out_data(w_inj_out_data), .out_keep(w_inj_out_keep),
        .out_last(w_inj_out_last),
        .cfg_mode(inj_mode), .cfg_count(inj_count), .cfg_rate(inj_rate),
        .cfg_seed(inj_seed), .cfg_seed_load(inj_seed_load), .cfg_clear(inj_clear),
        .cfg_mark(1'b0),
        .o_inj_bits(inj_bits), .o_inj_blocks(inj_blocks),
        .o_inj_over_t(inj_over_t), .o_last_block_errors(inj_last));

    assign w_inj_out_fire = w_inj_out_valid && w_inj_out_ready;

    assign obs_cw_in_valid  = w_inj_out_valid;
    assign obs_cw_in_ready  = w_inj_out_ready;

    // =========================================================================
    // 4. decode: M2 (corrupted in flight) -> M4
    // =========================================================================
    logic dec_err;
    bch_decoder_axi4 #(
        .FIELD_DIM(FIELD_DIM), .PRIM_POLY(PRIM_POLY), .T_BITS(T_BITS),
        .N_BITS(N_BITS), .FIRST_ROOT(FIRST_ROOT), .DATA_WIDTH(DW),
        .ADDR_WIDTH(AW), .ID_WIDTH(IDW), .MAX_OUTSTANDING(MAX_OUTSTANDING),
        .USER_WIDTH(1)
    ) u_dec (
        .aclk(aclk), .aresetn(aresetn),
        .cfg_start(dec_start), .cfg_src_addr('0), .cfg_dst_addr('0),
        .cfg_blocks(cfg_blocks), .cfg_burst_len(cfg_burst_len), .cfg_axi_id(IDW'(5)),
        .cfg_done(dec_done), .resp_err(dec_err),
        .out_status_ok(), .out_status_corrected(), .out_status_uncorrectable(),
        .out_status_frame_err(),
        .stat_blocks_ok(blk_ok), .stat_blocks_corrected(blk_corr),
        .stat_blocks_uncorrectable(blk_unc), .stat_blocks_frame_err(blk_frame),
        .stat_bits_corrected(sym_corr),
        .m_axi_arid(m2_arid), .m_axi_araddr(m2_araddr), .m_axi_arlen(m2_arlen),
        .m_axi_arsize(m2_arsize), .m_axi_arburst(m2_arburst), .m_axi_arlock(m2_arlock),
        .m_axi_arcache(m2_arcache), .m_axi_arprot(m2_arprot), .m_axi_arqos(m2_arqos),
        .m_axi_arregion(m2_arregion), .m_axi_aruser(m2_aruser),
        .m_axi_arvalid(m2_arvalid), .m_axi_arready(m2_arready),
        .m_axi_rid(w_dec_rid), .m_axi_rdata(w_inj_out_data), .m_axi_rresp(w_dec_rresp),
        .m_axi_rlast(w_dec_rlast), .m_axi_ruser(m2_ruser),
        .m_axi_rvalid(w_inj_out_valid), .m_axi_rready(w_inj_out_ready),
        .m_axi_awid(m4_awid), .m_axi_awaddr(m4_awaddr), .m_axi_awlen(m4_awlen),
        .m_axi_awsize(m4_awsize), .m_axi_awburst(m4_awburst), .m_axi_awlock(m4_awlock),
        .m_axi_awcache(m4_awcache), .m_axi_awprot(m4_awprot), .m_axi_awqos(m4_awqos),
        .m_axi_awregion(m4_awregion), .m_axi_awuser(m4_awuser),
        .m_axi_awvalid(m4_awvalid), .m_axi_awready(m4_awready),
        .m_axi_wdata(m4_wdata), .m_axi_wstrb(m4_wstrb), .m_axi_wlast(m4_wlast),
        .m_axi_wuser(m4_wuser), .m_axi_wvalid(m4_wvalid), .m_axi_wready(m4_wready),
        .m_axi_bid(m4_bid), .m_axi_bresp(m4_bresp), .m_axi_buser(m4_buser),
        .m_axi_bvalid(m4_bvalid), .m_axi_bready(m4_bready));

    // =========================================================================
    // 5. drain: M4 -> the checker
    // =========================================================================
    logic drain_err;
    rs_axi4_read_engine #(
        .ADDR_WIDTH(AW), .DATA_WIDTH(DW), .ID_WIDTH(IDW),
        .MAX_OUTSTANDING(MAX_OUTSTANDING), .USER_WIDTH(1)
    ) u_drain (
        .aclk(aclk), .aresetn(aresetn),
        .cfg_start(drain_start), .cfg_src_addr('0),
        .cfg_beats(32'(cfg_blocks) * 32'(K_BEATS)),
        .cfg_burst_len(cfg_burst_len), .cfg_beats_per_block(16'(K_BEATS)),
        .cfg_axi_id(IDW'(6)), .cfg_axi_size(3'(SIZE_B)),
        .cfg_done(drain_done), .resp_err(drain_err),
        .out_valid(out_valid), .out_ready(out_ready), .out_data(out_data),
        .out_last(out_last),
        .m_axi_arid(m4_arid), .m_axi_araddr(m4_araddr), .m_axi_arlen(m4_arlen),
        .m_axi_arsize(m4_arsize), .m_axi_arburst(m4_arburst), .m_axi_arlock(m4_arlock),
        .m_axi_arcache(m4_arcache), .m_axi_arprot(m4_arprot), .m_axi_arqos(m4_arqos),
        .m_axi_arregion(m4_arregion), .m_axi_aruser(m4_aruser),
        .m_axi_arvalid(m4_arvalid), .m_axi_arready(m4_arready),
        .m_axi_rid(m4_rid), .m_axi_rdata(m4_rdata), .m_axi_rresp(m4_rresp),
        .m_axi_rlast(m4_rlast), .m_axi_ruser(m4_ruser),
        .m_axi_rvalid(m4_rvalid), .m_axi_rready(m4_rready));

    localparam int K_TAIL_BITS  = K_BITS % DW;
    localparam int K_TAIL_BYTES = K_TAIL_BITS / 8;
    assign out_keep = (out_last && (K_TAIL_BYTES != 0))
                    ? S'((1 << K_TAIL_BYTES) - 1) : {S{1'b1}};

    // =========================================================================
    // Interface observer on the codec's own AXI4 master ports
    // =========================================================================
    /* verilator lint_off PINCONNECTEMPTY */
    axi4_intf_master_observer #(
        .NUM_RD_PORTS      (2),
        .NUM_WR_PORTS      (2),
        .ADDR_WIDTH        (AW),
        .DATA_WIDTH        (DW),
        .AXI_ID_WIDTH      (IDW),
        .AXI_USER_WIDTH    (1),
        .APB_ADDR_WIDTH    (12),
        .ENABLE_BUS_METER  (1'b1),
        .ENABLE_LATENCY_HIST(1'b1),
        .ENABLE_MON_TAPS   (1'b0),
        .WR_CH_FROM_AWID   (1'b1),
        .NUM_CHANNELS      (1)
    ) u_obs_axi4 (
        .aclk(aclk), .aresetn(aresetn),
        .s_apb_psel   (obs_apb_psel),
        .s_apb_penable(obs_apb_penable),
        .s_apb_pready (obs_apb_pready),
        .s_apb_paddr  (obs_apb_paddr),
        .s_apb_pwrite (obs_apb_pwrite),
        .s_apb_pwdata (obs_apb_pwdata),
        .s_apb_pstrb  (obs_apb_pstrb),
        .s_apb_prdata (obs_apb_prdata),
        .s_apb_pslverr(obs_apb_pslverr),
        .obs_rd_arid({m2_arid, m1_arid}),
        .obs_rd_araddr({m2_araddr, m1_araddr}),
        .obs_rd_arlen({m2_arlen, m1_arlen}),
        .obs_rd_arsize({m2_arsize, m1_arsize}),
        .obs_rd_arburst({m2_arburst, m1_arburst}),
        .obs_rd_arlock({m2_arlock, m1_arlock}),
        .obs_rd_arcache({m2_arcache, m1_arcache}),
        .obs_rd_arprot({m2_arprot, m1_arprot}),
        .obs_rd_arqos({m2_arqos, m1_arqos}),
        .obs_rd_arregion({m2_arregion, m1_arregion}),
        .obs_rd_aruser({m2_aruser, m1_aruser}),
        .obs_rd_arvalid({m2_arvalid, m1_arvalid}),
        .obs_rd_arready({m2_arready, m1_arready}),
        .obs_rd_rid({w_dec_rid, m1_rid}),
        .obs_rd_rdata({w_inj_out_data, m1_rdata}),
        .obs_rd_rresp({w_dec_rresp, m1_rresp}),
        .obs_rd_rlast({w_dec_rlast, m1_rlast}),
        .obs_rd_ruser({m2_ruser, m1_ruser}),
        .obs_rd_rvalid({w_inj_out_valid, m1_rvalid}),
        .obs_rd_rready({w_inj_out_ready, m1_rready}),
        .obs_wr_awid({m4_awid, m2_awid}),
        .obs_wr_awaddr({m4_awaddr, m2_awaddr}),
        .obs_wr_awlen({m4_awlen, m2_awlen}),
        .obs_wr_awsize({m4_awsize, m2_awsize}),
        .obs_wr_awburst({m4_awburst, m2_awburst}),
        .obs_wr_awlock({m4_awlock, m2_awlock}),
        .obs_wr_awcache({m4_awcache, m2_awcache}),
        .obs_wr_awprot({m4_awprot, m2_awprot}),
        .obs_wr_awqos({m4_awqos, m2_awqos}),
        .obs_wr_awregion({m4_awregion, m2_awregion}),
        .obs_wr_awuser({m4_awuser, m2_awuser}),
        .obs_wr_awvalid({m4_awvalid, m2_awvalid}),
        .obs_wr_awready({m4_awready, m2_awready}),
        .obs_wr_wdata({m4_wdata, m2_wdata}),
        .obs_wr_wstrb({m4_wstrb, m2_wstrb}),
        .obs_wr_wlast({m4_wlast, m2_wlast}),
        .obs_wr_wuser({m4_wuser, m2_wuser}),
        .obs_wr_wvalid({m4_wvalid, m2_wvalid}),
        .obs_wr_wready({m4_wready, m2_wready}),
        .obs_wr_bid({m4_bid, m2_bid}),
        .obs_wr_bresp({m4_bresp, m2_bresp}),
        .obs_wr_buser({m4_buser, m2_buser}),
        .obs_wr_bvalid({m4_bvalid, m2_bvalid}),
        .obs_wr_bready({m4_bready, m2_bready}),
        .obs_wr_active_ch_id('{default: '0}),
        .obs_wr_active_ch_valid('{default: '0}),
        .cfg_rd_rid_per_channel('{default: '{default: '0}}),
        .cfg_rd_rid_per_channel_valid('{default: '{default: '0}}),
        .i_meter_clear (obs_meter_clear),
        .i_meter_freeze(!busy),
        .cam_clear(1'b0),
        .s_axil_arvalid(1'b0), .s_axil_araddr('0), .s_axil_arprot('0),
        .s_axil_rready(1'b0),
        .s_axil_arready(), .s_axil_rvalid(), .s_axil_rdata(), .s_axil_rresp(),
        .m_axi_awready(1'b0), .m_axi_wready(1'b0),
        .m_axi_bid('0), .m_axi_bresp('0), .m_axi_buser('0), .m_axi_bvalid(1'b0),
        .m_axi_awid(), .m_axi_awaddr(), .m_axi_awlen(), .m_axi_awsize(),
        .m_axi_awburst(), .m_axi_awlock(), .m_axi_awcache(), .m_axi_awprot(),
        .m_axi_awqos(), .m_axi_awregion(), .m_axi_awuser(), .m_axi_awvalid(),
        .m_axi_wdata(), .m_axi_wstrb(), .m_axi_wlast(), .m_axi_wuser(),
        .m_axi_wvalid(), .m_axi_bready(),
        .m_axil_awready(1'b0), .m_axil_wready(1'b0),
        .m_axil_bvalid(1'b0), .m_axil_bresp('0),
        .m_axil_awvalid(), .m_axil_awaddr(), .m_axil_awprot(),
        .m_axil_wvalid(), .m_axil_wdata(), .m_axil_wstrb(), .m_axil_bready(),
        .irq_out());
    /* verilator lint_on PINCONNECTEMPTY */

    assign resp_err = seed_err || enc_err || dec_err || drain_err;

endmodule
