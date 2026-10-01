// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// Module: rs_decoder_axi4
// Description: Reed-Solomon decoder as an AXI4 memory-to-memory job engine.
//
//   The AXI4 counterpart to rs_decoder_axis4 and the mirror of
//   rs_encoder_axi4: a job names a source address, a destination address and a
//   BLOCK COUNT, and the block reads one codeword per block, corrects it, and
//   writes the k recovered message symbols out.
//
//   Per-block verdicts are accumulated into counters rather than only exposed
//   as a sideband pulse. A job covers many blocks and a host reads the result
//   once at the end, so a pulse it has to catch in flight is the wrong shape
//   -- the counters are what a CSR wants. The per-block sideband is brought
//   out too, for a consumer that wants to act on each block.
//
// Parameters:
//   SYMBOL_WIDTH / PRIM_POLY / T_SYMBOLS / N_SYMBOLS / FIRST_ROOT / KES_ALGO
//                    the code and the solver, as rs_decoder_core takes them
//   DATA_WIDTH       AXI and stream width; a whole number of symbols
//   ADDR_WIDTH       AXI address width
//   ID_WIDTH         AXI id width
//   MAX_OUTSTANDING  requests in flight per direction
//
// Notes:
//   - A codeword is read as ceil(N/S) PACKED beats with any partial one last,
//     which is what rs_encoder_axi4 writes (it generates rs_beat_packer in its
//     output path when the core's own layout would put a partial beat
//     mid-codeword). This module reconstructs that keep from the beat index,
//     since the read engine deals in beats and knows nothing about symbols.
//   - The output is k symbols per block and the write side writes whole beats;
//     a partial final beat's unused lanes carry whatever the core emitted.
//   - out_status_* are valid with the block's last output beat, which is the
//     core's release-on-verdict contract: nothing leaves until the
//     post-correction syndrome re-check has passed judgement.
module rs_decoder_axi4 #(
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
    parameter string KES_ALGO      = "RIBM",
    // derived, exposed for the consumer's convenience
    parameter int K_SYMBOLS        = N_SYMBOLS - 2 * T_SYMBOLS,
    parameter int SYMBOLS_PER_BEAT = DATA_WIDTH / SYMBOL_WIDTH,
    parameter int STATUS_CNT_WIDTH = $clog2(T_SYMBOLS + 1)
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

    // -- per-block verdict, valid with the block's last output beat ---------
    output logic                    out_status_ok,
    output logic [STATUS_CNT_WIDTH-1:0] out_status_corrected,
    output logic                    out_status_uncorrectable,
    output logic                    out_status_frame_err,

    // -- accumulated over the job, cleared by cfg_start --------------------
    output logic [31:0]             stat_blocks_ok,
    output logic [31:0]             stat_blocks_corrected,
    output logic [31:0]             stat_blocks_uncorrectable,
    output logic [31:0]             stat_blocks_frame_err,
    output logic [31:0]             stat_symbols_corrected,

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
    localparam int K_BEATS  = (K_SYMBOLS + S - 1) / S;
    // The codeword in memory is PACKED by rs_encoder_axi4: ceil(N/S) beats
    // with any partial one last. That is this core's in_keep contract, so the
    // tail is N % S and it lands on the block's final beat.
    localparam int CW_BEATS = (N_SYMBOLS + S - 1) / S;
    localparam int N_TAIL   = N_SYMBOLS % S;
    localparam int SIZE_B   = $clog2(DATA_WIDTH / 8);
    localparam int IBW      = (CW_BEATS > 1) ? $clog2(CW_BEATS) : 1;

    if (DATA_WIDTH % SYMBOL_WIDTH != 0)
        $fatal(1, "rs_decoder_axi4: DATA_WIDTH %0d is not a whole number of %0d-bit symbols",
               DATA_WIDTH, SYMBOL_WIDTH);


    // =========================================================================
    // source: one codeword per block
    // =========================================================================
    logic                  rd_valid, rd_ready, rd_last, rd_done, rd_err;
    logic [DATA_WIDTH-1:0] rd_data;

    rs_axi4_read_engine #(
        .ADDR_WIDTH(ADDR_WIDTH), .DATA_WIDTH(DATA_WIDTH), .ID_WIDTH(ID_WIDTH),
        .MAX_OUTSTANDING(MAX_OUTSTANDING), .USER_WIDTH(USER_WIDTH)
    ) u_rd (
        .aclk(aclk), .aresetn(aresetn),
        .cfg_start(cfg_start), .cfg_src_addr(cfg_src_addr),
        .cfg_beats(32'(cfg_blocks) * 32'(CW_BEATS)),
        .cfg_burst_len(cfg_burst_len), .cfg_beats_per_block(16'(CW_BEATS)),
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

    // Reconstruct the keep pattern the encoder produced. The read engine
    // counts beats and knows nothing about symbols, so the beat INDEX within
    // the block is what says whether this beat is the data phase's partial
    // tail, the parity phase's partial tail, or a full beat.
    logic [IBW-1:0] r_ibeat;
    logic [S-1:0]   w_in_keep;

    // Partial ONLY on the block's last beat, which is the core's contract. The
    // guard above means k fills its beats, so the only partial that can arise
    // is the parity tail -- and that IS the last beat.
    always_comb begin
        w_in_keep = {S{1'b1}};
        if ((N_TAIL != 0) && (r_ibeat == IBW'(CW_BEATS - 1)))
            w_in_keep = S'((1 << N_TAIL) - 1);
    end

    always_ff @(posedge aclk or negedge aresetn) begin
        if (!aresetn)                       r_ibeat <= '0;
        else if (cfg_start)                 r_ibeat <= '0;
        else if (rd_valid && rd_ready)      r_ibeat <= rd_last ? '0 : r_ibeat + IBW'(1);
    end

    // =========================================================================
    // the codec
    // =========================================================================
    logic                  dec_valid, dec_ready, dec_last;
    logic [DATA_WIDTH-1:0] dec_data;
    logic [S-1:0]          dec_keep;

    rs_decoder_core #(
        .SYMBOL_WIDTH(SYMBOL_WIDTH), .PRIM_POLY(PRIM_POLY), .T_SYMBOLS(T_SYMBOLS),
        .N_SYMBOLS(N_SYMBOLS), .FIRST_ROOT(FIRST_ROOT), .DATA_WIDTH(DATA_WIDTH),
        .KES_ALGO(KES_ALGO)
    ) u_core (
        .aclk(aclk), .aresetn(aresetn),
        .in_valid(rd_valid), .in_ready(rd_ready), .in_data(rd_data),
        .in_keep(w_in_keep), .in_last(rd_last),
        .out_valid(dec_valid), .out_ready(dec_ready), .out_data(dec_data),
        .out_keep(dec_keep), .out_last(dec_last),
        .out_status_ok(out_status_ok), .out_status_corrected(out_status_corrected),
        .out_status_uncorrectable(out_status_uncorrectable),
        .out_status_frame_err(out_status_frame_err));

    // =========================================================================
    // destination: k message beats per block
    // =========================================================================
    logic wr_done, wr_err;

    rs_axi4_write_engine #(
        .ADDR_WIDTH(ADDR_WIDTH), .DATA_WIDTH(DATA_WIDTH), .ID_WIDTH(ID_WIDTH),
        .MAX_OUTSTANDING(MAX_OUTSTANDING), .USER_WIDTH(USER_WIDTH)
    ) u_wr (
        .aclk(aclk), .aresetn(aresetn),
        .cfg_start(cfg_start), .cfg_dst_addr(cfg_dst_addr),
        .cfg_beats(32'(cfg_blocks) * 32'(K_BEATS)),
        .cfg_burst_len(cfg_burst_len), .cfg_axi_id(cfg_axi_id),
        .cfg_axi_size(3'(SIZE_B)),
        .cfg_done(wr_done), .resp_err(wr_err),
        .in_valid(dec_valid), .in_ready(dec_ready), .in_data(dec_data), .in_last(dec_last),
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

    // One verdict per block, taken on the block's last output beat -- which is
    // where the core's contract says the status is valid.
    logic w_verdict;
    assign w_verdict = dec_valid && dec_ready && dec_last;

    always_ff @(posedge aclk or negedge aresetn) begin
        if (!aresetn || cfg_start) begin
            stat_blocks_ok            <= '0;
            stat_blocks_corrected     <= '0;
            stat_blocks_uncorrectable <= '0;
            stat_blocks_frame_err     <= '0;
            stat_symbols_corrected    <= '0;
        end else if (w_verdict) begin
            if (out_status_frame_err)          stat_blocks_frame_err     <= stat_blocks_frame_err + 32'd1;
            else if (out_status_uncorrectable) stat_blocks_uncorrectable <= stat_blocks_uncorrectable + 32'd1;
            else if (out_status_ok)            stat_blocks_ok            <= stat_blocks_ok + 32'd1;
            else begin
                stat_blocks_corrected  <= stat_blocks_corrected + 32'd1;
                stat_symbols_corrected <= stat_symbols_corrected + 32'(out_status_corrected);
            end
        end
    end

    // the core reports keep on its output; the write side writes whole beats
    logic unused_d;
    assign unused_d = ^dec_keep;

endmodule
