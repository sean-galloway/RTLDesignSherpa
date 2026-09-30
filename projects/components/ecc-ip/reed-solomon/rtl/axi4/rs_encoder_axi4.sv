// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// Module: rs_encoder_axi4
// Description: Reed-Solomon encoder as an AXI4 memory-to-memory job engine.
//
//   The AXI4 counterpart to rs_encoder_axis4 (PRD D9): a job names a source
//   address, a destination address and a BLOCK COUNT, and the block reads k
//   data symbols per block, encodes, and writes the n-symbol codewords out.
//   rs_axi4_read_engine feeds the core and rs_axi4_write_engine drains it,
//   both on the one AXI4 master port -- the read and write channel sets are
//   independent, so nothing arbitrates between them.
//
//   The job is in BLOCKS, not bytes. A codec's unit of work is a block, the
//   source and destination beat counts differ by construction (k in, n out),
//   and making the caller compute both from a byte count is how an off-by-one
//   becomes a framing error. The block count is the one number a caller has.
//
// Parameters:
//   SYMBOL_WIDTH / PRIM_POLY / T_SYMBOLS / N_SYMBOLS / FIRST_ROOT
//                    the code, exactly as rs_encoder_core takes them
//   DATA_WIDTH       AXI and stream width; a whole number of symbols
//   ADDR_WIDTH       AXI address width
//   ID_WIDTH         AXI id width
//   MAX_OUTSTANDING  requests in flight per direction
//
// Notes:
//   - A codeword occupies K_BEATS + P_BEATS beats, NOT ceil(N/S). The core
//     does not pack parity onto a partial final data beat: it finishes the
//     data phase and starts parity on a fresh beat. Those differ whenever k
//     and 2t BOTH end mid-beat -- 124 profiles in a small sweep of m and S --
//     and using ceil(N/S) there would truncate every codeword.
//   - in_keep is generated here, because the read engine deals in beats and
//     knows nothing about symbols. Full on every beat except a block's last,
//     which carries K_TAIL symbols when k does not fill its final beat.
//   - The write side writes whole beats. A partial final beat's unused lanes
//     carry whatever the core emitted; the consumer knows the symbol count
//     from the profile and the block count. That is what lets the memory run
//     sdpram_core with USE_WSTRB = 0 and infer block RAM.
//   - cfg_done is the WRITE engine's done ANDed with the read's: the job is
//     finished when the codewords have been acknowledged by the destination,
//     not when the last source beat was fetched.
module rs_encoder_axi4 #(
    parameter int SYMBOL_WIDTH     = 8,
    parameter int PRIM_POLY        = 'h11D,
    parameter int T_SYMBOLS        = 8,
    parameter int N_SYMBOLS        = (1 << SYMBOL_WIDTH) - 1,
    parameter int FIRST_ROOT       = 0,
    parameter int DATA_WIDTH       = 32,
    parameter int ADDR_WIDTH       = 32,
    parameter int ID_WIDTH         = 4,
    parameter int MAX_OUTSTANDING  = 4,
    parameter int USER_WIDTH       = 1,
    // derived, exposed for the consumer's convenience
    parameter int K_SYMBOLS        = N_SYMBOLS - 2 * T_SYMBOLS,
    parameter int SYMBOLS_PER_BEAT = DATA_WIDTH / SYMBOL_WIDTH
) (
    input  logic                    aclk,
    input  logic                    aresetn,

    // -- job ---------------------------------------------------------------
    input  logic                    cfg_start,          // one-cycle pulse
    input  logic [ADDR_WIDTH-1:0]   cfg_src_addr,
    input  logic [ADDR_WIDTH-1:0]   cfg_dst_addr,
    input  logic [15:0]             cfg_blocks,
    input  logic [7:0]              cfg_burst_len,
    input  logic [ID_WIDTH-1:0]     cfg_axi_id,
    output logic                    cfg_done,
    output logic                    resp_err,           // sticky, either direction
    output logic                    frame_err,          // sticky: a short/long block

    // -- AXI4 master: read channels ----------------------------------------
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

    // -- AXI4 master: write channels ---------------------------------------
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

    localparam int S        = SYMBOLS_PER_BEAT;
    localparam int K_BEATS  = (K_SYMBOLS      + S - 1) / S;
    localparam int P_BEATS  = (2 * T_SYMBOLS  + S - 1) / S;
    localparam int CW_BEATS = K_BEATS + P_BEATS;      // beats a codeword occupies
    localparam int K_TAIL   = K_SYMBOLS % S;          // 0 = the last data beat is full
    localparam int SIZE_B   = $clog2(DATA_WIDTH / 8); // AXI axsize

    if (DATA_WIDTH % SYMBOL_WIDTH != 0)
        $fatal(1, "rs_encoder_axi4: DATA_WIDTH %0d is not a whole number of %0d-bit symbols",
               DATA_WIDTH, SYMBOL_WIDTH);

    // The chain is only valid when k fills a whole number of beats.
    //
    // rs_encoder_core emits its data phase then starts parity on a FRESH beat,
    // so when K % S != 0 its data phase ends on a partial beat that is NOT the
    // codeword's last. rs_decoder_core's contract is the opposite: in_keep may
    // be partial ONLY on a block's last beat, and it flags a mis-framed block
    // otherwise. So an encoder output cannot be fed to a decoder at those
    // profiles without a repacker between them, which does not exist yet.
    //
    // With K % S == 0 there is no mid-stream partial, the codeword occupies
    // exactly ceil(N/S) beats, and any partial beat is the parity tail -- which
    // IS the last beat, so the decoder accepts it. Measured: RS(252,236),
    // RS(204,188) and RS(30,24) chain; RS(255,239) and RS(15,9) do not.
    //
    // This is an elaboration error rather than a silent mis-frame because the
    // failure is a framing error on every block, and a reader would look at
    // the decoder before the interface.
    if (K_SYMBOLS % S != 0)
        $fatal(1, "rs_encoder_axi4: K_SYMBOLS %0d is not a whole number of %0d-symbol beats. rs_encoder_core would emit a partial beat mid-codeword and rs_decoder_core rejects one; chaining them needs a beat packer, which is not built. Pick a profile whose K_SYMBOLS divides evenly by SYMBOLS_PER_BEAT.", K_SYMBOLS, S);


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

    // The read engine counts beats; symbols are this module's business. Only a
    // block's LAST data beat can be partial, and only when k does not fill it.
    logic [S-1:0] w_in_keep;
    assign w_in_keep = (rd_last && (K_TAIL != 0)) ? S'((1 << K_TAIL) - 1) : {S{1'b1}};

    // =========================================================================
    // the codec
    // =========================================================================
    logic                  enc_valid, enc_ready, enc_last, w_frame_err;
    logic [DATA_WIDTH-1:0] enc_data;
    logic [S-1:0]          enc_keep;

    rs_encoder_core #(
        .SYMBOL_WIDTH(SYMBOL_WIDTH), .PRIM_POLY(PRIM_POLY), .T_SYMBOLS(T_SYMBOLS),
        .N_SYMBOLS(N_SYMBOLS), .FIRST_ROOT(FIRST_ROOT), .DATA_WIDTH(DATA_WIDTH)
    ) u_core (
        .aclk(aclk), .aresetn(aresetn),
        .in_valid(rd_valid), .in_ready(rd_ready), .in_data(rd_data),
        .in_keep(w_in_keep), .in_last(rd_last),
        .out_valid(enc_valid), .out_ready(enc_ready), .out_data(enc_data),
        .out_keep(enc_keep), .out_last(enc_last),
        .frame_err(w_frame_err));

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
        .in_valid(enc_valid), .in_ready(enc_ready), .in_data(enc_data), .in_last(enc_last),
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

    // the core reports keep on its output; the write side writes whole beats
    logic unused_e;
    assign unused_e = ^enc_keep;

endmodule
