// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// Module: rs_encoder_axis4
// Description: Reed-Solomon systematic encoder with AXI4-Stream interfaces.
//
//   This is the component's integration top (PRD D9). `rs_encoder_core` speaks
//   a bare valid/ready/last handshake, which is the right interface for the
//   algorithm but the wrong one for a fabric. This wraps it in the house
//   `axis4_slave` / `axis4_master` skid wrappers so a consumer connects a
//   stream, not eleven renamed wires.
//
//   Why this module exists at all: the Nexys A7 loop harness used to rename
//   the core's handshake onto its generator and checker signals inline, in the
//   BOARD area. That put an interface decision that belongs to the component
//   in a project that merely instantiates it, and every future consumer would
//   have had to repeat it. The adapter lives here now, once.
//
// Parameters:
//   SYMBOL_WIDTH      GF(2^m) symbol width, m. 8 is the common case.
//   PRIM_POLY         field polynomial, degree m, as an integer
//   T_SYMBOLS         correctable symbols per block; parity is 2t symbols
//   N_SYMBOLS         codeword length in symbols, <= 2^m - 1
//   FIRST_ROOT        b in g(x) = prod (x - alpha^(b+i))
//   DATA_WIDTH        stream width; must be a whole number of symbols
//   SKID_DEPTH        depth of the two AXIS skid buffers, 2..8
//   AXIS_*_WIDTH      tid / tdest / tuser widths, forwarded beat for beat
//
// Notes:
//   - tstrb vs keep. The core's `keep` is PER SYMBOL; AXI4-Stream's tstrb is
//     PER BYTE. At SYMBOL_WIDTH == 8 the two coincide and tstrb carries keep
//     directly. At any other m they do not, so keep rides the low
//     SYMBOLS_PER_BEAT bits of tuser and tstrb is driven all ones. The
//     elaboration guard below enforces a wide enough tuser for that case
//     rather than silently truncating the strobe.
//   - keep is low-aligned and may be partial only on a block's last beat,
//     which is the core's contract, not something this wrapper relaxes.
//   - tid and tdest are forwarded from the beat that ENTERS the encoder to the
//     beats that leave it, held for the whole codeword. Parity beats carry the
//     same id and dest as the block's data beats.
module rs_encoder_axis4 #(
    parameter int SYMBOL_WIDTH     = 8,
    parameter int PRIM_POLY        = 'h11D,
    parameter int T_SYMBOLS        = 8,
    parameter int N_SYMBOLS        = (1 << SYMBOL_WIDTH) - 1,
    parameter int FIRST_ROOT       = 0,
    parameter int DATA_WIDTH       = SYMBOL_WIDTH,
    parameter int SKID_DEPTH       = 2,
    parameter int AXIS_ID_WIDTH    = 0,
    parameter int AXIS_DEST_WIDTH  = 0,
    parameter int AXIS_USER_WIDTH  = 0,
    // derived, exposed for the consumer's convenience
    parameter int K_SYMBOLS        = N_SYMBOLS - 2 * T_SYMBOLS,
    parameter int SYMBOLS_PER_BEAT = DATA_WIDTH / SYMBOL_WIDTH,
    // zero-width AXIS sidebands still need a 1-bit wire; these are in the
    // parameter list rather than the body because the PORTS below use them
    parameter int IW               = (AXIS_ID_WIDTH   > 0) ? AXIS_ID_WIDTH   : 1,
    parameter int DESTW            = (AXIS_DEST_WIDTH > 0) ? AXIS_DEST_WIDTH : 1,
    parameter int UW               = (AXIS_USER_WIDTH > 0) ? AXIS_USER_WIDTH : 1
) (
    input  logic                       aclk,
    input  logic                       aresetn,

    // data symbols in
    input  logic [DATA_WIDTH-1:0]      s_axis_tdata,
    input  logic [DATA_WIDTH/8-1:0]    s_axis_tstrb,
    input  logic                       s_axis_tlast,
    input  logic [IW-1:0]              s_axis_tid,
    input  logic [DESTW-1:0]           s_axis_tdest,
    input  logic [UW-1:0]              s_axis_tuser,
    input  logic                       s_axis_tvalid,
    output logic                       s_axis_tready,

    // codeword symbols out: k data beats then the parity beats
    output logic [DATA_WIDTH-1:0]      m_axis_tdata,
    output logic [DATA_WIDTH/8-1:0]    m_axis_tstrb,
    output logic                       m_axis_tlast,
    output logic [IW-1:0]              m_axis_tid,
    output logic [DESTW-1:0]           m_axis_tdest,
    output logic [UW-1:0]              m_axis_tuser,
    output logic                       m_axis_tvalid,
    input  logic                       m_axis_tready,

    // one-cycle pulse: a block ended with other than k data symbols
    output logic                       frame_err
);

    // -------------------------------------------------------------------------
    // widths
    // -------------------------------------------------------------------------
    localparam int S     = SYMBOLS_PER_BEAT;
    localparam int SW    = DATA_WIDTH / 8;

    // At m == 8 a byte IS a symbol, so tstrb and keep are the same vector.
    // Anywhere else they are not, and guessing would corrupt partial beats.
    localparam bit KEEP_ON_USER = (SYMBOL_WIDTH != 8);

    // rs_encoder_core finishes its data phase and starts parity on a FRESH
    // beat, so at K % S != 0 its output carries a partial beat MID-codeword.
    // That is poor AXI-Stream citizenship -- a partial TSTRB is expected on
    // TLAST and almost nowhere else, and an rs_decoder_core downstream flags
    // it as a mis-framed block outright (PRD D9b). rs_beat_packer closes it
    // up so a codeword leaves as ceil(N/S) beats with any partial one last.
    // At K % S == 0 there is nothing to pack and it is not built.
    localparam bit NEED_PACK = (K_SYMBOLS % S != 0);

    if (DATA_WIDTH % SYMBOL_WIDTH != 0)
        $fatal(1, "rs_encoder_axis4: DATA_WIDTH %0d is not a whole number of %0d-bit symbols",
               DATA_WIDTH, SYMBOL_WIDTH);
    if (KEEP_ON_USER && AXIS_USER_WIDTH < S)
        // SV has no adjacent string-literal concatenation; keep it one literal
        $fatal(1, "rs_encoder_axis4: SYMBOL_WIDTH %0d != 8 so keep rides tuser, needing AXIS_USER_WIDTH >= SYMBOLS_PER_BEAT (%0d), got %0d",
               SYMBOL_WIDTH, S, AXIS_USER_WIDTH);

    // -------------------------------------------------------------------------
    // intake skid
    // -------------------------------------------------------------------------
    logic [DATA_WIDTH-1:0] in_tdata;
    logic [SW-1:0]         in_tstrb;
    logic                  in_tlast, in_tvalid, in_tready;
    logic [IW-1:0]         in_tid;
    logic [DESTW-1:0]      in_tdest;
    logic [UW-1:0]         in_tuser;

    /* verilator lint_off PINCONNECTEMPTY */
    axis4_slave #(
        .SKID_DEPTH(SKID_DEPTH), .AXIS_DATA_WIDTH(DATA_WIDTH),
        .AXIS_ID_WIDTH(AXIS_ID_WIDTH), .AXIS_DEST_WIDTH(AXIS_DEST_WIDTH),
        .AXIS_USER_WIDTH(AXIS_USER_WIDTH)
    ) u_in (
        .aclk(aclk), .aresetn(aresetn),
        .s_axis_tdata(s_axis_tdata), .s_axis_tstrb(s_axis_tstrb),
        .s_axis_tlast(s_axis_tlast), .s_axis_tid(s_axis_tid),
        .s_axis_tdest(s_axis_tdest), .s_axis_tuser(s_axis_tuser),
        .s_axis_tvalid(s_axis_tvalid), .s_axis_tready(s_axis_tready),
        .fub_axis_tdata(in_tdata), .fub_axis_tstrb(in_tstrb),
        .fub_axis_tlast(in_tlast), .fub_axis_tid(in_tid),
        .fub_axis_tdest(in_tdest), .fub_axis_tuser(in_tuser),
        .fub_axis_tvalid(in_tvalid), .fub_axis_tready(in_tready),
        .busy());
    /* verilator lint_on PINCONNECTEMPTY */

    // -------------------------------------------------------------------------
    // the codec
    // -------------------------------------------------------------------------
    logic [S-1:0]          w_in_keep;
    logic [DATA_WIDTH-1:0] core_data;
    logic [S-1:0]          core_keep;
    logic                  core_last, core_valid, core_ready;

    // A ternary will not do here: both arms ELABORATE, so in_tuser[S-1:0]
    // is range-checked even when KEEP_ON_USER is constant 0 -- and tuser is
    // 1 bit wide in that configuration, which is the normal one. It has to be
    // a generate so only the live arm exists.
    if (KEEP_ON_USER) begin : g_keep_in_user
        assign w_in_keep = in_tuser[S-1:0];
    end else begin : g_keep_in_strb
        assign w_in_keep = in_tstrb[S-1:0];
    end

    rs_encoder_core #(
        .SYMBOL_WIDTH(SYMBOL_WIDTH), .PRIM_POLY(PRIM_POLY), .T_SYMBOLS(T_SYMBOLS),
        .N_SYMBOLS(N_SYMBOLS), .FIRST_ROOT(FIRST_ROOT), .DATA_WIDTH(DATA_WIDTH),
        .SKID_DEPTH(SKID_DEPTH)
    ) u_core (
        .aclk(aclk), .aresetn(aresetn),
        .in_valid(in_tvalid), .in_ready(in_tready), .in_data(in_tdata),
        .in_keep(w_in_keep), .in_last(in_tlast),
        .out_valid(core_valid), .out_ready(core_ready), .out_data(core_data),
        .out_keep(core_keep), .out_last(core_last),
        .frame_err(frame_err));

    // -------------------------------------------------------------------------
    // repack, when the core's layout would put a partial beat mid-codeword
    // -------------------------------------------------------------------------
    logic [DATA_WIDTH-1:0] pk_data;
    logic [S-1:0]          pk_keep;
    logic                  pk_last, pk_valid, pk_ready;

    if (NEED_PACK) begin : g_pack
        rs_beat_packer #(
            .SYMBOL_WIDTH(SYMBOL_WIDTH), .SYMBOLS_PER_BEAT(S)
        ) u_pack (
            .aclk(aclk), .aresetn(aresetn),
            .in_valid(core_valid), .in_ready(core_ready), .in_data(core_data),
            .in_keep(core_keep), .in_last(core_last),
            .out_valid(pk_valid), .out_ready(pk_ready), .out_data(pk_data),
            .out_keep(pk_keep), .out_last(pk_last));
    end else begin : g_no_pack
        assign pk_valid   = core_valid;
        assign core_ready = pk_ready;
        assign pk_data    = core_data;
        assign pk_keep    = core_keep;
        assign pk_last    = core_last;
    end

    // -------------------------------------------------------------------------
    // id / dest passthrough
    //
    // A codeword leaves as more beats than it entered as, so the id and dest
    // cannot ride the datapath -- they are captured from the block's FIRST
    // accepted beat and held until its last beat leaves.
    // -------------------------------------------------------------------------
    logic [IW-1:0]    r_tid;
    logic [DESTW-1:0] r_tdest;
    logic             r_have;

    always_ff @(posedge aclk or negedge aresetn) begin
        if (!aresetn) begin
            r_tid <= '0; r_tdest <= '0; r_have <= 1'b0;
        end else begin
            if (in_tvalid && in_tready && !r_have) begin
                r_tid <= in_tid; r_tdest <= in_tdest; r_have <= 1'b1;
            end
            if (pk_valid && pk_ready && pk_last) r_have <= 1'b0;
        end
    end

    // -------------------------------------------------------------------------
    // outlet skid
    // -------------------------------------------------------------------------
    logic [SW-1:0] w_out_tstrb;
    logic [UW-1:0] w_out_tuser;

    // Same reason as above: a generate, not a runtime branch.
    if (KEEP_ON_USER) begin : g_keep_out_user
        always_comb begin
            w_out_tstrb = {SW{1'b1}};
            w_out_tuser = '0;
            w_out_tuser[S-1:0] = pk_keep;
        end
    end else begin : g_keep_out_strb
        always_comb begin
            w_out_tuser = '0;
            w_out_tstrb = {SW{1'b1}};
            w_out_tstrb[S-1:0] = pk_keep;
        end
    end

    /* verilator lint_off PINCONNECTEMPTY */
    axis4_master #(
        .SKID_DEPTH(SKID_DEPTH), .AXIS_DATA_WIDTH(DATA_WIDTH),
        .AXIS_ID_WIDTH(AXIS_ID_WIDTH), .AXIS_DEST_WIDTH(AXIS_DEST_WIDTH),
        .AXIS_USER_WIDTH(AXIS_USER_WIDTH)
    ) u_out (
        .aclk(aclk), .aresetn(aresetn),
        .fub_axis_tdata(pk_data), .fub_axis_tstrb(w_out_tstrb),
        .fub_axis_tlast(pk_last), .fub_axis_tid(r_tid),
        .fub_axis_tdest(r_tdest), .fub_axis_tuser(w_out_tuser),
        .fub_axis_tvalid(pk_valid), .fub_axis_tready(pk_ready),
        .m_axis_tdata(m_axis_tdata), .m_axis_tstrb(m_axis_tstrb),
        .m_axis_tlast(m_axis_tlast), .m_axis_tid(m_axis_tid),
        .m_axis_tdest(m_axis_tdest), .m_axis_tuser(m_axis_tuser),
        .m_axis_tvalid(m_axis_tvalid), .m_axis_tready(m_axis_tready),
        .busy());
    /* verilator lint_on PINCONNECTEMPTY */

endmodule
