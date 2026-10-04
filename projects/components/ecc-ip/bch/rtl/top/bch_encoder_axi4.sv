// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// Module: bch_encoder_axi4
// Description: Binary BCH encoder as an AXI4 memory-to-memory job engine.
//
//   The AXI4 counterpart to bch_encoder_axis4: a job names a source address,
//   a destination address and a BLOCK COUNT, and the block reads k data bits
//   per block, encodes, and writes the n-bit codewords out.
//
//   bch_axi4_read_engine feeds the core and bch_axi4_write_engine drains it,
//   both on the one AXI4 master port -- the read and write channel sets are
//   independent, so nothing arbitrates between them.
//
//   The job is in BLOCKS, not bytes. A codec's unit of work is a block; the
//   source and destination beat counts differ by construction (k in, n out).
//
// Parameters:
//   FIELD_DIM / PRIM_POLY / T_BITS / N_BITS / FIRST_ROOT
//                    the code, exactly as bch_encoder_core takes them
//   DATA_WIDTH       AXI and stream width; also the BCH bits per beat
//   ADDR_WIDTH       AXI address width
//   ID_WIDTH         AXI id width
//   MAX_OUTSTANDING  requests in flight per direction
//
// Notes:
//   - A codeword is written PACKED: exactly ceil(N/B) beats with any partial
//     one last, which is bch_decoder_core's in_keep contract. The core starts
//     parity on a fresh beat, so at K % B != 0 its output carries a partial
//     beat mid-codeword that a decoder flags as mis-framed. bch_beat_packer
//     closes that up, and is omitted when there is nothing to pack.
//   - in_keep is generated here, because the read engine deals in beats and
//     knows nothing about bits. Full on every beat except a block's last,
//     which carries K_TAIL bits when k does not fill its final beat.
//   - The write side writes whole beats. A partial final beat's unused lanes
//     carry whatever the core emitted; the consumer knows the bit count from
//     the profile and the block count.
//   - cfg_done is the WRITE engine's done ANDed with the read's.
module bch_encoder_axi4
    import bch_pkg::bch_beats;
    import bch_pkg::bch_degree_g;
#(
    parameter int FIELD_DIM     = bch_pkg::FIELD_DIM,
    parameter int PRIM_POLY     = bch_pkg::PRIM_POLY,
    parameter int T_BITS        = bch_pkg::T_BITS,
    parameter int N_BITS        = bch_pkg::N_BITS,
    parameter int FIRST_ROOT    = bch_pkg::FIRST_ROOT,
    parameter int DATA_WIDTH    = bch_pkg::BITS_PER_BEAT,
    parameter int ADDR_WIDTH    = 32,
    parameter int ID_WIDTH      = 4,
    parameter int MAX_OUTSTANDING = 4,
    parameter int USER_WIDTH    = 1,
    // derived, exposed for the consumer's convenience
    parameter int K_BITS        = N_BITS - bch_degree_g(FIELD_DIM, PRIM_POLY, T_BITS, FIRST_ROOT),
    parameter int BITS_PER_BEAT = DATA_WIDTH
) (
    input  logic                    aclk,
    input  logic                    aresetn,

    // -- job -----------------------------------------------------------------
    input  logic                    cfg_start,          // one-cycle pulse
    input  logic [ADDR_WIDTH-1:0]   cfg_src_addr,
    input  logic [ADDR_WIDTH-1:0]   cfg_dst_addr,
    input  logic [15:0]             cfg_blocks,
    input  logic [7:0]              cfg_burst_len,
    input  logic [ID_WIDTH-1:0]     cfg_axi_id,
    output logic                    cfg_done,
    output logic                    resp_err,           // sticky, either direction
    output logic                    frame_err,          // sticky: a short/long block

    // -- AXI4 master: read channels ------------------------------------------
    output logic [ID_WIDTH-1:0]     m_axi_arid,
    output logic [ADDR_WIDTH-1:0]   m_axi_araddr,
    output logic [7:0]              m_axi_arlen,
    output logic [2:0]              m_axi_arsize,
    output logic [1:0]              m_axi_arburst,
    output logic                    m_axi_arlock,
    output logic [3:0]              m_axi_arcache,
    output logic [2:0]              m_axi_arprot,
    output logic [3:0]              m_axi_arqos,
    output logic [3:0]              m_axi_arregion,
    output logic [USER_WIDTH-1:0]   m_axi_aruser,
    output logic                    m_axi_arvalid,
    input  logic                    m_axi_arready,
    input  logic [ID_WIDTH-1:0]     m_axi_rid,
    input  logic [DATA_WIDTH-1:0]   m_axi_rdata,
    input  logic [1:0]              m_axi_rresp,
    input  logic                    m_axi_rlast,
    input  logic [USER_WIDTH-1:0]   m_axi_ruser,
    input  logic                    m_axi_rvalid,
    output logic                    m_axi_rready,

    // -- AXI4 master: write channels -----------------------------------------
    output logic [ID_WIDTH-1:0]     m_axi_awid,
    output logic [ADDR_WIDTH-1:0]   m_axi_awaddr,
    output logic [7:0]              m_axi_awlen,
    output logic [2:0]              m_axi_awsize,
    output logic [1:0]              m_axi_awburst,
    output logic                    m_axi_awlock,
    output logic [3:0]              m_axi_awcache,
    output logic [2:0]              m_axi_awprot,
    output logic [3:0]              m_axi_awqos,
    output logic [3:0]              m_axi_awregion,
    output logic [USER_WIDTH-1:0]   m_axi_awuser,
    output logic                    m_axi_awvalid,
    input  logic                    m_axi_awready,
    output logic [DATA_WIDTH-1:0]   m_axi_wdata,
    output logic [DATA_WIDTH/8-1:0] m_axi_wstrb,
    output logic                    m_axi_wlast,
    output logic [USER_WIDTH-1:0]   m_axi_wuser,
    output logic                    m_axi_wvalid,
    input  logic                    m_axi_wready,
    input  logic [ID_WIDTH-1:0]     m_axi_bid,
    input  logic [1:0]              m_axi_bresp,
    input  logic [USER_WIDTH-1:0]   m_axi_buser,
    input  logic                    m_axi_bvalid,
    output logic                    m_axi_bready
);

    localparam int B        = BITS_PER_BEAT;
    localparam int K_BEATS  = bch_beats(K_BITS, B);
    localparam int K_TAIL   = K_BITS % B;             // 0 = the last data beat is full
    localparam int SIZE_B   = $clog2(DATA_WIDTH / 8); // AXI axsize

    // A codeword leaves this module PACKED: exactly ceil(N/B) beats, with any
    // partial one last. That is bch_decoder_core's in_keep contract.
    localparam int CW_BEATS = bch_beats(N_BITS, B);

    // The core emits its data phase then starts parity on a FRESH beat, so at
    // K % B != 0 its output carries a partial beat MID-codeword, which a
    // decoder rejects. bch_beat_packer closes that up.
    localparam bit NEED_PACK = (K_TAIL != 0);

    if (B < 1 || B > K_BITS) begin : g_check_b
        $fatal(1, "bch_encoder_axi4: BITS_PER_BEAT %0d out of range 1..K (%0d)", B, K_BITS);
    end

    if (DATA_WIDTH != B) begin : g_check_dw
        $fatal(1, "bch_encoder_axi4: DATA_WIDTH %0d must equal BITS_PER_BEAT %0d", DATA_WIDTH, B);
    end


    // =========================================================================
    // source: k data beats per block
    // =========================================================================
    logic                  rd_valid, rd_ready, rd_last, rd_done, rd_err;
    logic [DATA_WIDTH-1:0] rd_data;

    rs_axi4_read_engine #(
        .ADDR_WIDTH(ADDR_WIDTH), .DATA_WIDTH(DATA_WIDTH), .ID_WIDTH(ID_WIDTH),
        .MAX_OUTSTANDING(MAX_OUTSTANDING), .USER_WIDTH(USER_WIDTH)
    ) u_rd (
        .aclk(aclk), .aresetn(aresetn),
        .cfg_start(cfg_start), .cfg_src_addr(cfg_src_addr),
        .cfg_beats(32'(cfg_blocks) * 32'(K_BEATS)),
        .cfg_burst_len(cfg_burst_len), .cfg_beats_per_block(16'(K_BEATS)),
        .cfg_axi_id(cfg_axi_id), .cfg_axi_size(3'(SIZE_B)),
        .cfg_done(rd_done), .resp_err(rd_err),
        .out_valid(rd_valid), .out_ready(rd_ready), .out_data(rd_data), .out_last(rd_last),
        .m_axi_arid(m_axi_arid), .m_axi_araddr(m_axi_araddr), .m_axi_arlen(m_axi_arlen),
        .m_axi_arsize(m_axi_arsize), .m_axi_arburst(m_axi_arburst),
        .m_axi_arlock(m_axi_arlock), .m_axi_arcache(m_axi_arcache),
        .m_axi_arprot(m_axi_arprot), .m_axi_arqos(m_axi_arqos),
        .m_axi_arregion(m_axi_arregion), .m_axi_aruser(m_axi_aruser),
        .m_axi_arvalid(m_axi_arvalid), .m_axi_arready(m_axi_arready),
        .m_axi_rid(m_axi_rid), .m_axi_rdata(m_axi_rdata), .m_axi_rresp(m_axi_rresp),
        .m_axi_rlast(m_axi_rlast), .m_axi_ruser(m_axi_ruser),
        .m_axi_rvalid(m_axi_rvalid), .m_axi_rready(m_axi_rready));

    // The read engine counts beats; bits are this module's business. Only a
    // block's LAST data beat can be partial, and only when k does not fill it.
    logic [B-1:0] w_in_keep;
    assign w_in_keep = (rd_last && (K_TAIL != 0)) ? B'((1 << K_TAIL) - 1) : {B{1'b1}};

    // =========================================================================
    // the codec
    // =========================================================================
    logic                  enc_valid, enc_ready, enc_last, w_frame_err;
    logic [DATA_WIDTH-1:0] enc_data;
    logic [B-1:0]          enc_keep;

    bch_encoder_core #(
        .FIELD_DIM(FIELD_DIM), .PRIM_POLY(PRIM_POLY), .T_BITS(T_BITS),
        .N_BITS(N_BITS), .BITS_PER_BEAT(B), .FIRST_ROOT(FIRST_ROOT),
        .K_BITS(K_BITS)
    ) u_core (
        .aclk(aclk), .aresetn(aresetn),
        .in_valid(rd_valid), .in_ready(rd_ready), .in_data(rd_data),
        .in_keep(w_in_keep), .in_last(rd_last),
        .out_valid(enc_valid), .out_ready(enc_ready), .out_data(enc_data),
        .out_keep(enc_keep), .out_last(enc_last),
        .frame_err(w_frame_err));

    // =========================================================================
    // repack, when the core's layout is not already decoder-legal
    // =========================================================================
    logic                  pk_valid, pk_ready, pk_last;
    logic [DATA_WIDTH-1:0] pk_data;
    logic [B-1:0]          pk_keep;

    if (NEED_PACK) begin : g_pack
        bch_beat_packer #(
            .BITS_PER_BEAT(B)
        ) u_pack (
            .aclk(aclk), .aresetn(aresetn),
            .in_valid(enc_valid), .in_ready(enc_ready), .in_data(enc_data),
            .in_keep(enc_keep), .in_last(enc_last),
            .out_valid(pk_valid), .out_ready(pk_ready), .out_data(pk_data),
            .out_keep(pk_keep), .out_last(pk_last));
    end else begin : g_no_pack
        assign pk_valid  = enc_valid;
        assign enc_ready = pk_ready;
        assign pk_data   = enc_data;
        assign pk_keep   = enc_keep;
        assign pk_last   = enc_last;
    end

    // =========================================================================
    // destination: a codeword per block
    // =========================================================================
    logic wr_done, wr_err;

    rs_axi4_write_engine #(
        .ADDR_WIDTH(ADDR_WIDTH), .DATA_WIDTH(DATA_WIDTH), .ID_WIDTH(ID_WIDTH),
        .MAX_OUTSTANDING(MAX_OUTSTANDING), .USER_WIDTH(USER_WIDTH)
    ) u_wr (
        .aclk(aclk), .aresetn(aresetn),
        .cfg_start(cfg_start), .cfg_dst_addr(cfg_dst_addr),
        .cfg_beats(32'(cfg_blocks) * 32'(CW_BEATS)),
        .cfg_burst_len(cfg_burst_len), .cfg_axi_id(cfg_axi_id),
        .cfg_axi_size(3'(SIZE_B)),
        .cfg_done(wr_done), .resp_err(wr_err),
        .in_valid(pk_valid), .in_ready(pk_ready), .in_data(pk_data), .in_last(pk_last),
        .m_axi_awid(m_axi_awid), .m_axi_awaddr(m_axi_awaddr), .m_axi_awlen(m_axi_awlen),
        .m_axi_awsize(m_axi_awsize), .m_axi_awburst(m_axi_awburst),
        .m_axi_awlock(m_axi_awlock), .m_axi_awcache(m_axi_awcache),
        .m_axi_awprot(m_axi_awprot), .m_axi_awqos(m_axi_awqos),
        .m_axi_awregion(m_axi_awregion), .m_axi_awuser(m_axi_awuser),
        .m_axi_awvalid(m_axi_awvalid), .m_axi_awready(m_axi_awready),
        .m_axi_wdata(m_axi_wdata), .m_axi_wstrb(m_axi_wstrb), .m_axi_wlast(m_axi_wlast),
        .m_axi_wuser(m_axi_wuser), .m_axi_wvalid(m_axi_wvalid), .m_axi_wready(m_axi_wready),
        .m_axi_bid(m_axi_bid), .m_axi_bresp(m_axi_bresp), .m_axi_buser(m_axi_buser),
        .m_axi_bvalid(m_axi_bvalid), .m_axi_bready(m_axi_bready));

    // =========================================================================
    // job status
    // =========================================================================
    assign cfg_done = rd_done && wr_done;
    assign resp_err = rd_err || wr_err;

    // frame_err is a pulse from the core; hold it for the job so a host that
    // polls after cfg_done still sees it
    always_ff @(posedge aclk or negedge aresetn) begin
        if (!aresetn)            frame_err <= 1'b0;
        else if (cfg_start)      frame_err <= 1'b0;
        else if (w_frame_err)    frame_err <= 1'b1;
    end

    // the packed stream reports keep; the write side writes whole beats
    logic unused_e;
    assign unused_e = ^pk_keep;

endmodule
