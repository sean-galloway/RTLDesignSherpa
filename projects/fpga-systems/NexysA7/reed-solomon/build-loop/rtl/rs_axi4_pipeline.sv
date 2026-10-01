// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// Module: rs_axi4_pipeline
// Description: The loop harness's AXI4 datapath -- a memory-to-memory codec
//              chain with the same stream in, stream out and status surface
//              the stream datapath presents.
//
//   The stream flavour of this harness is one flowing pipe: generator into
//   encoder into injector into decoder into checker. The AXI4 flavour cannot
//   be, because rs_encoder_axi4 and rs_decoder_axi4 are JOB engines -- each
//   reads a region, transforms it, and writes another region. So the chain is
//   five sequential jobs over four memories:
//
//     generator -> [seed write]  -> M1
//     M1        -> [ENCODER]     -> M2      codewords
//     M2        -> [read, INJECT, write] -> M3   corrupted codewords
//     M3        -> [DECODER]     -> M4      recovered messages
//     M4        -> [drain read]  -> checker
//
//   Every memory has exactly ONE writer on its write channels and ONE reader
//   on its read channels. AXI4's two channel sets are independent, so nothing
//   here arbitrates -- which is the whole reason four memories is cheaper than
//   sharing two. They are block RAM (USE_WSTRB = 0, every writer here writes
//   whole words), and the part has 135 tiles with none otherwise used.
//
//   Why the injector needs its own read/transform/write hop rather than
//   sitting inside the chain: the codeword only exists in memory between the
//   two codecs, and corrupting it means reading it out, flipping symbols, and
//   writing it back. Putting the injector inside either codec top would make
//   the corruption part of the codec, which is exactly backwards -- the
//   channel corrupts data, not the encoder.
//
//   Stage sequencing is a done-to-start chain, not a state machine: each
//   stage starts on the RISING EDGE of the previous stage's done. The rising
//   edge matters because cfg_done is held from one job until the next
//   cfg_start, so a level would re-trigger instantly off the previous run.
//
// Parameters mirror the harness's; MEM_DEPTH sizes every memory in words.
`timescale 1ns / 1ps
`include "reset_defs.svh"

module rs_axi4_pipeline #(
    parameter int    SYMBOL_WIDTH = 8,
    parameter int    PRIM_POLY    = 'h11D,
    parameter int    T_SYMBOLS    = 8,
    parameter int    N_SYMBOLS    = 252,
    parameter int    FIRST_ROOT   = 0,
    parameter int    DATA_WIDTH   = 32,
    parameter int    ADDR_WIDTH   = 32,
    parameter int    ID_WIDTH     = 4,
    parameter int    MEM_DEPTH    = 4096,
    parameter int    MAX_OUTSTANDING = 4,
    parameter string KES_ALGO     = "RIBM",
    // derived
    parameter int    K_SYMBOLS        = N_SYMBOLS - 2 * T_SYMBOLS,
    parameter int    SYMBOLS_PER_BEAT = DATA_WIDTH / SYMBOL_WIDTH
) (
    input  logic                        aclk,
    input  logic                        aresetn,

    // -- run control -------------------------------------------------------
    input  logic                        start,          // one-cycle pulse
    input  logic [15:0]                 cfg_blocks,
    input  logic [7:0]                  cfg_burst_len,
    output logic                        busy,
    output logic                        done,

    // -- message stream in, from the generator -----------------------------
    input  logic                        in_valid,
    output logic                        in_ready,
    input  logic [DATA_WIDTH-1:0]       in_data,
    input  logic                        in_last,

    // -- message stream out, to the checker --------------------------------
    output logic                        out_valid,
    input  logic                        out_ready,
    output logic [DATA_WIDTH-1:0]       out_data,
    output logic [SYMBOLS_PER_BEAT-1:0] out_keep,
    output logic                        out_last,

    // -- injector configuration, same fields the stream flavour takes ------
    input  logic [1:0]                  inj_mode,
    input  logic [7:0]                  inj_count,
    input  logic [15:0]                 inj_rate,
    input  logic [31:0]                 inj_seed,
    input  logic                        inj_seed_load,
    input  logic                        inj_clear,

    // -- status ------------------------------------------------------------
    output logic                        resp_err,       // any stage, sticky
    output logic                        enc_frame_err,
    output logic [31:0]                 blk_ok,
    output logic [31:0]                 blk_corr,
    output logic [31:0]                 blk_unc,
    output logic [31:0]                 blk_frame,
    output logic [31:0]                 sym_corr,
    output logic [31:0]                 inj_symbols,
    output logic [31:0]                 inj_blocks,
    output logic [31:0]                 inj_over_t,
    output logic [7:0]                  inj_last,
    output logic [4:0]                  stage_done      // seed, enc, inj, dec, drain
);

    localparam int AW  = ADDR_WIDTH;
    localparam int DW  = DATA_WIDTH;
    localparam int IDW = ID_WIDTH;
    localparam int S   = SYMBOLS_PER_BEAT;
    localparam int SIZE_B  = $clog2(DW / 8);
    localparam int K_BEATS = (K_SYMBOLS + S - 1) / S;
    localparam int CW_BEATS = (N_SYMBOLS + S - 1) / S;   // packed by the encoder top

    // ---- memory 1: messages: the generator writes, the encoder reads
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


    // ---- memory 2: codewords: the encoder writes, the inject hop reads
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


    // ---- memory 3: corrupted codewords: the inject hop writes, the decoder reads
    logic [IDW-1:0]          m3_awid, m3_bid, m3_arid, m3_rid;
    logic [AW-1:0]           m3_awaddr, m3_araddr;
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
    logic [DW-1:0]           m3_wdata, m3_rdata;
    logic [DW/8-1:0]         m3_wstrb;

    /* verilator lint_off PINCONNECTEMPTY */
    sdpram_slave_axi4_axi4 #(
        .AXI_ID_WIDTH(IDW), .ADDR_WIDTH(AW), .DATA_WIDTH(DW),
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


    // ---- memory 4: recovered messages: the decoder writes, the drain reads
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
    logic seed_done, enc_done, inj_done, dec_done, drain_done;
    logic r_seed_d, r_enc_d, r_inj_d, r_dec_d;
    logic enc_start, inj_start, dec_start, drain_start;

    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_seed_d <= 1'b0; r_enc_d <= 1'b0; r_inj_d <= 1'b0; r_dec_d <= 1'b0;
        end else if (start) begin
            // every stage's done is still high from the LAST run at this
            // point; arming the edge detectors low would fire all four
            // immediately, so they are armed HIGH and the real 0->1 that
            // follows each stage's own cfg_start is what gets seen
            r_seed_d <= 1'b1; r_enc_d <= 1'b1; r_inj_d <= 1'b1; r_dec_d <= 1'b1;
        end else begin
            r_seed_d <= seed_done; r_enc_d <= enc_done;
            r_inj_d  <= inj_done;  r_dec_d <= dec_done;
        end
    )

    assign enc_start   = seed_done  && !r_seed_d;
    assign inj_start   = enc_done   && !r_enc_d;
    assign dec_start   = inj_done   && !r_inj_d;
    assign drain_start = dec_done   && !r_dec_d;

    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn))      busy <= 1'b0;
        else if (start)                  busy <= 1'b1;
        else if (drain_done && busy)     busy <= 1'b0;
    )
    assign done       = drain_done;
    assign stage_done = {drain_done, dec_done, inj_done, enc_done, seed_done};

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
    logic enc_err;
    rs_encoder_axi4 #(
        .SYMBOL_WIDTH(SYMBOL_WIDTH), .PRIM_POLY(PRIM_POLY), .T_SYMBOLS(T_SYMBOLS),
        .N_SYMBOLS(N_SYMBOLS), .FIRST_ROOT(FIRST_ROOT), .DATA_WIDTH(DW),
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
    // 3. inject: M2 -> corrupt -> M3
    // =========================================================================
    logic                  ird_valid, ird_ready, ird_last, ird_done, ird_err;
    logic [DW-1:0]         ird_data;
    logic                  iwr_valid, iwr_ready, iwr_last, iwr_err;
    logic [DW-1:0]         iwr_data;
    logic [S-1:0]          iwr_keep;

    rs_axi4_read_engine #(
        .ADDR_WIDTH(AW), .DATA_WIDTH(DW), .ID_WIDTH(IDW),
        .MAX_OUTSTANDING(MAX_OUTSTANDING), .USER_WIDTH(1)
    ) u_inj_rd (
        .aclk(aclk), .aresetn(aresetn),
        .cfg_start(inj_start), .cfg_src_addr('0),
        .cfg_beats(32'(cfg_blocks) * 32'(CW_BEATS)),
        .cfg_burst_len(cfg_burst_len), .cfg_beats_per_block(16'(CW_BEATS)),
        .cfg_axi_id(IDW'(3)), .cfg_axi_size(3'(SIZE_B)),
        .cfg_done(ird_done), .resp_err(ird_err),
        .out_valid(ird_valid), .out_ready(ird_ready), .out_data(ird_data),
        .out_last(ird_last),
        .m_axi_arid(m2_arid), .m_axi_araddr(m2_araddr), .m_axi_arlen(m2_arlen),
        .m_axi_arsize(m2_arsize), .m_axi_arburst(m2_arburst), .m_axi_arlock(m2_arlock),
        .m_axi_arcache(m2_arcache), .m_axi_arprot(m2_arprot), .m_axi_arqos(m2_arqos),
        .m_axi_arregion(m2_arregion), .m_axi_aruser(m2_aruser),
        .m_axi_arvalid(m2_arvalid), .m_axi_arready(m2_arready),
        .m_axi_rid(m2_rid), .m_axi_rdata(m2_rdata), .m_axi_rresp(m2_rresp),
        .m_axi_rlast(m2_rlast), .m_axi_ruser(m2_ruser),
        .m_axi_rvalid(m2_rvalid), .m_axi_rready(m2_rready));

    // The codeword in memory is packed, so every beat is full except a block's
    // last, which carries N % S symbols when that is not zero.
    localparam int N_TAIL = N_SYMBOLS % S;
    logic [S-1:0] w_ird_keep;
    assign w_ird_keep = (ird_last && (N_TAIL != 0)) ? S'((1 << N_TAIL) - 1) : {S{1'b1}};

    rs_error_injector #(
        .SYMBOL_WIDTH(SYMBOL_WIDTH), .T_SYMBOLS(T_SYMBOLS), .N_SYMBOLS(N_SYMBOLS),
        .SYMBOLS_PER_BEAT(S)
    ) u_inj (
        .aclk(aclk), .aresetn(aresetn),
        .in_valid(ird_valid), .in_ready(ird_ready), .in_data(ird_data),
        .in_keep(w_ird_keep), .in_last(ird_last),
        .out_valid(iwr_valid), .out_ready(iwr_ready), .out_data(iwr_data),
        .out_keep(iwr_keep), .out_last(iwr_last),
        .cfg_mode(inj_mode), .cfg_count(inj_count), .cfg_rate(inj_rate),
        .cfg_seed(inj_seed), .cfg_seed_load(inj_seed_load), .cfg_clear(inj_clear),
        .o_inj_symbols(inj_symbols), .o_inj_blocks(inj_blocks),
        .o_inj_over_t(inj_over_t), .o_last_block_errors(inj_last));

    rs_axi4_write_engine #(
        .ADDR_WIDTH(AW), .DATA_WIDTH(DW), .ID_WIDTH(IDW),
        .MAX_OUTSTANDING(MAX_OUTSTANDING), .USER_WIDTH(1)
    ) u_inj_wr (
        .aclk(aclk), .aresetn(aresetn),
        .cfg_start(inj_start), .cfg_dst_addr('0),
        .cfg_beats(32'(cfg_blocks) * 32'(CW_BEATS)),
        .cfg_burst_len(cfg_burst_len), .cfg_axi_id(IDW'(4)), .cfg_axi_size(3'(SIZE_B)),
        .cfg_done(inj_done), .resp_err(iwr_err),
        .in_valid(iwr_valid), .in_ready(iwr_ready), .in_data(iwr_data), .in_last(iwr_last),
        .m_axi_awid(m3_awid), .m_axi_awaddr(m3_awaddr), .m_axi_awlen(m3_awlen),
        .m_axi_awsize(m3_awsize), .m_axi_awburst(m3_awburst), .m_axi_awlock(m3_awlock),
        .m_axi_awcache(m3_awcache), .m_axi_awprot(m3_awprot), .m_axi_awqos(m3_awqos),
        .m_axi_awregion(m3_awregion), .m_axi_awuser(m3_awuser),
        .m_axi_awvalid(m3_awvalid), .m_axi_awready(m3_awready),
        .m_axi_wdata(m3_wdata), .m_axi_wstrb(m3_wstrb), .m_axi_wlast(m3_wlast),
        .m_axi_wuser(m3_wuser), .m_axi_wvalid(m3_wvalid), .m_axi_wready(m3_wready),
        .m_axi_bid(m3_bid), .m_axi_bresp(m3_bresp), .m_axi_buser(m3_buser),
        .m_axi_bvalid(m3_bvalid), .m_axi_bready(m3_bready));

    // =========================================================================
    // 4. decode: M3 -> M4
    // =========================================================================
    logic dec_err;
    rs_decoder_axi4 #(
        .SYMBOL_WIDTH(SYMBOL_WIDTH), .PRIM_POLY(PRIM_POLY), .T_SYMBOLS(T_SYMBOLS),
        .N_SYMBOLS(N_SYMBOLS), .FIRST_ROOT(FIRST_ROOT), .DATA_WIDTH(DW),
        .ADDR_WIDTH(AW), .ID_WIDTH(IDW), .MAX_OUTSTANDING(MAX_OUTSTANDING),
        .USER_WIDTH(1), .KES_ALGO(KES_ALGO)
    ) u_dec (
        .aclk(aclk), .aresetn(aresetn),
        .cfg_start(dec_start), .cfg_src_addr('0), .cfg_dst_addr('0),
        .cfg_blocks(cfg_blocks), .cfg_burst_len(cfg_burst_len), .cfg_axi_id(IDW'(5)),
        .cfg_done(dec_done), .resp_err(dec_err),
        .out_status_ok(), .out_status_corrected(), .out_status_uncorrectable(),
        .out_status_frame_err(),
        .stat_blocks_ok(blk_ok), .stat_blocks_corrected(blk_corr),
        .stat_blocks_uncorrectable(blk_unc), .stat_blocks_frame_err(blk_frame),
        .stat_symbols_corrected(sym_corr),
        .m_axi_arid(m3_arid), .m_axi_araddr(m3_araddr), .m_axi_arlen(m3_arlen),
        .m_axi_arsize(m3_arsize), .m_axi_arburst(m3_arburst), .m_axi_arlock(m3_arlock),
        .m_axi_arcache(m3_arcache), .m_axi_arprot(m3_arprot), .m_axi_arqos(m3_arqos),
        .m_axi_arregion(m3_arregion), .m_axi_aruser(m3_aruser),
        .m_axi_arvalid(m3_arvalid), .m_axi_arready(m3_arready),
        .m_axi_rid(m3_rid), .m_axi_rdata(m3_rdata), .m_axi_rresp(m3_rresp),
        .m_axi_rlast(m3_rlast), .m_axi_ruser(m3_ruser),
        .m_axi_rvalid(m3_rvalid), .m_axi_rready(m3_rready),
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

    // the recovered message is packed too: full beats except a block's last
    localparam int K_TAIL = K_SYMBOLS % S;
    assign out_keep = (out_last && (K_TAIL != 0)) ? S'((1 << K_TAIL) - 1) : {S{1'b1}};

    assign resp_err = seed_err || enc_err || ird_err || iwr_err || dec_err || drain_err;

endmodule
