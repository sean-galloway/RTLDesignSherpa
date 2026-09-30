// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// Module: rs_decoder
// Description: Reed-Solomon decoder with AXI4-Stream interfaces.
//
//   The component's integration top (PRD D9), the counterpart to `rs_encoder`.
//   `rs_decoder_core` speaks a bare valid/ready/last handshake plus a
//   per-block verdict; this wraps the stream halves in the house `axis4_slave`
//   / `axis4_master` skid wrappers and leaves the verdict as sideband.
//
//   Why the verdict stays sideband rather than riding tuser: it is per BLOCK,
//   not per beat, and it is only meaningful on the block's last beat. Encoding
//   it into tuser would either widen every beat to carry three mostly-idle
//   fields or define a "valid only when tlast" rule that a downstream AXIS
//   component has no way to honour generically. A consumer that wants it in
//   the stream can map it itself; a consumer that wants to count verdicts --
//   which is what every consumer so far does -- reads the sideband.
//
// Parameters:
//   SYMBOL_WIDTH      GF(2^m) symbol width, m. 8 is the common case.
//   PRIM_POLY         field polynomial, degree m, as an integer
//   T_SYMBOLS         correctable symbols per block
//   N_SYMBOLS         codeword length in symbols, <= 2^m - 1
//   FIRST_ROOT        b in g(x) = prod (x - alpha^(b+i)); must match the encoder
//   DATA_WIDTH        stream width; must be a whole number of symbols
//   SKID_DEPTH        depth of the two AXIS skid buffers, 2..8
//   BLOCK_FIFO_DEPTH  received-block buffer, in beats
//   KES_ALGO          "RIBM" or "EUCLID" -- which key-equation solver is built
//   AXIS_*_WIDTH      tid / tdest / tuser widths, forwarded beat for beat
//
// Notes:
//   - tstrb vs keep: identical rule to `rs_encoder`. At SYMBOL_WIDTH == 8 a
//     byte is a symbol and tstrb carries keep; at any other m keep rides the
//     low SYMBOLS_PER_BEAT bits of tuser and tstrb is all ones.
//   - The decoder emits k beats per n-beat block: parity is consumed, not
//     forwarded. tid and tdest are captured from the block's first accepted
//     beat and held across the beats it produces.
//   - out_status_* are valid with the block's LAST output beat, which is the
//     core's contract (release-on-verdict: nothing leaves until the
//     post-correction syndrome re-check has passed judgement).
module rs_decoder #(
    parameter int SYMBOL_WIDTH     = 8,
    parameter int PRIM_POLY        = 'h11D,
    parameter int T_SYMBOLS        = 8,
    parameter int N_SYMBOLS        = (1 << SYMBOL_WIDTH) - 1,
    parameter int FIRST_ROOT       = 0,
    parameter int DATA_WIDTH       = SYMBOL_WIDTH,
    parameter int SKID_DEPTH       = 2,
    parameter int BLOCK_FIFO_DEPTH = 1 << $clog2((N_SYMBOLS + 2 * T_SYMBOLS) / (DATA_WIDTH / SYMBOL_WIDTH) + 8),
    parameter string KES_ALGO      = "RIBM",
    // PRD D9 names these on the tops so a consumer selects its boundaries
    // rather than picking a module. Only "AXIS" is built today; "AXI4" needs
    // the read/write job engines, which do not exist yet, and "NONE" is just
    // the bare core -- instantiate rs_decoder_core directly for that.
    parameter string INTAKE_IF     = "AXIS",
    parameter string OUTLET_IF     = "AXIS",
    parameter int AXIS_ID_WIDTH    = 0,
    parameter int AXIS_DEST_WIDTH  = 0,
    parameter int AXIS_USER_WIDTH  = 0,
    // derived, exposed for the consumer's convenience
    parameter int K_SYMBOLS        = N_SYMBOLS - 2 * T_SYMBOLS,
    parameter int SYMBOLS_PER_BEAT = DATA_WIDTH / SYMBOL_WIDTH,
    parameter int STATUS_CNT_WIDTH = $clog2(T_SYMBOLS + 1),
    // zero-width AXIS sidebands still need a 1-bit wire; these are in the
    // parameter list rather than the body because the PORTS below use them
    parameter int IW               = (AXIS_ID_WIDTH   > 0) ? AXIS_ID_WIDTH   : 1,
    parameter int DESTW            = (AXIS_DEST_WIDTH > 0) ? AXIS_DEST_WIDTH : 1,
    parameter int UW               = (AXIS_USER_WIDTH > 0) ? AXIS_USER_WIDTH : 1
) (
    input  logic                        aclk,
    input  logic                        aresetn,

    // received codeword symbols in
    input  logic [DATA_WIDTH-1:0]       s_axis_tdata,
    input  logic [DATA_WIDTH/8-1:0]     s_axis_tstrb,
    input  logic                        s_axis_tlast,
    input  logic [IW-1:0]               s_axis_tid,
    input  logic [DESTW-1:0]            s_axis_tdest,
    input  logic [UW-1:0]               s_axis_tuser,
    input  logic                        s_axis_tvalid,
    output logic                        s_axis_tready,

    // corrected message symbols out: k beats per block
    output logic [DATA_WIDTH-1:0]       m_axis_tdata,
    output logic [DATA_WIDTH/8-1:0]     m_axis_tstrb,
    output logic                        m_axis_tlast,
    output logic [IW-1:0]               m_axis_tid,
    output logic [DESTW-1:0]            m_axis_tdest,
    output logic [UW-1:0]               m_axis_tuser,
    output logic                        m_axis_tvalid,
    input  logic                        m_axis_tready,

    // per-block verdict, valid with the block's last output beat
    output logic                        out_status_ok,
    output logic [STATUS_CNT_WIDTH-1:0] out_status_corrected,
    output logic                        out_status_uncorrectable,
    output logic                        out_status_frame_err
);

    localparam int S  = SYMBOLS_PER_BEAT;
    localparam int SW = DATA_WIDTH / 8;

    localparam bit KEEP_ON_USER = (SYMBOL_WIDTH != 8);

    if (INTAKE_IF != "AXIS")
        $fatal(1, "rs_decoder: INTAKE_IF=%s is not built; only \"AXIS\" exists today (AXI4 needs the job engines, NONE is rs_decoder_core)", INTAKE_IF);
    if (OUTLET_IF != "AXIS")
        $fatal(1, "rs_decoder: OUTLET_IF=%s is not built; only \"AXIS\" exists today (AXI4 needs the job engines, NONE is rs_decoder_core)", OUTLET_IF);

    if (DATA_WIDTH % SYMBOL_WIDTH != 0)
        $fatal(1, "rs_decoder: DATA_WIDTH %0d is not a whole number of %0d-bit symbols",
               DATA_WIDTH, SYMBOL_WIDTH);
    if (KEEP_ON_USER && AXIS_USER_WIDTH < S)
        // SV has no adjacent string-literal concatenation; keep it one literal
        $fatal(1, "rs_decoder: SYMBOL_WIDTH %0d != 8 so keep rides tuser, needing AXIS_USER_WIDTH >= SYMBOLS_PER_BEAT (%0d), got %0d",
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

    rs_decoder_core #(
        .SYMBOL_WIDTH(SYMBOL_WIDTH), .PRIM_POLY(PRIM_POLY), .T_SYMBOLS(T_SYMBOLS),
        .N_SYMBOLS(N_SYMBOLS), .FIRST_ROOT(FIRST_ROOT), .DATA_WIDTH(DATA_WIDTH),
        .SKID_DEPTH(SKID_DEPTH), .BLOCK_FIFO_DEPTH(BLOCK_FIFO_DEPTH),
        .KES_ALGO(KES_ALGO)
    ) u_core (
        .aclk(aclk), .aresetn(aresetn),
        .in_valid(in_tvalid), .in_ready(in_tready), .in_data(in_tdata),
        .in_keep(w_in_keep), .in_last(in_tlast),
        .out_valid(core_valid), .out_ready(core_ready), .out_data(core_data),
        .out_keep(core_keep), .out_last(core_last),
        .out_status_ok(out_status_ok), .out_status_corrected(out_status_corrected),
        .out_status_uncorrectable(out_status_uncorrectable),
        .out_status_frame_err(out_status_frame_err));

    // -------------------------------------------------------------------------
    // id / dest passthrough: captured on the block's first accepted beat and
    // held until its last corrected beat leaves. A block enters as n beats and
    // leaves as k, so these cannot ride the datapath.
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
            if (core_valid && core_ready && core_last) r_have <= 1'b0;
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
            w_out_tuser[S-1:0] = core_keep;
        end
    end else begin : g_keep_out_strb
        always_comb begin
            w_out_tuser = '0;
            w_out_tstrb = {SW{1'b1}};
            w_out_tstrb[S-1:0] = core_keep;
        end
    end

    /* verilator lint_off PINCONNECTEMPTY */
    axis4_master #(
        .SKID_DEPTH(SKID_DEPTH), .AXIS_DATA_WIDTH(DATA_WIDTH),
        .AXIS_ID_WIDTH(AXIS_ID_WIDTH), .AXIS_DEST_WIDTH(AXIS_DEST_WIDTH),
        .AXIS_USER_WIDTH(AXIS_USER_WIDTH)
    ) u_out (
        .aclk(aclk), .aresetn(aresetn),
        .fub_axis_tdata(core_data), .fub_axis_tstrb(w_out_tstrb),
        .fub_axis_tlast(core_last), .fub_axis_tid(r_tid),
        .fub_axis_tdest(r_tdest), .fub_axis_tuser(w_out_tuser),
        .fub_axis_tvalid(core_valid), .fub_axis_tready(core_ready),
        .m_axis_tdata(m_axis_tdata), .m_axis_tstrb(m_axis_tstrb),
        .m_axis_tlast(m_axis_tlast), .m_axis_tid(m_axis_tid),
        .m_axis_tdest(m_axis_tdest), .m_axis_tuser(m_axis_tuser),
        .m_axis_tvalid(m_axis_tvalid), .m_axis_tready(m_axis_tready),
        .busy());
    /* verilator lint_on PINCONNECTEMPTY */

endmodule
