`timescale 1ns / 1ps
`include "reset_defs.svh"
//==============================================================================
// Module: bridge_wr_rate_buf
// Description: Write rate-matching buffer for a bridge master's upsized path.
//
// Purpose:
//   A narrow master writing a wider slave through an upsize converter makes
//   one wide W beat per R narrow beats. Once its AW is picked, a shared slave's
//   W channel is that master's for the whole burst, so the slave sits idle
//   (R-1) cycles in R for the burst's length -- every other master waits on a
//   channel running at the narrow rate (bridge W2: 0.80 of a 64-bit slave
//   shared with a 32-bit master).
//
//   This buffer sits between the converter's wide side and the crossbar. It
//   holds each AW until its burst's W beats are all buffered, so when the AW
//   is picked the burst streams at the slave's full rate. A burst longer than
//   DEPTH cannot be held whole: its AW is released at once and the burst runs
//   as it did without the buffer (its W can only drain after its AW is picked,
//   so holding it would deadlock).
//
//   Holding an AW here cannot cross another master's W: the burst's W has
//   already left the master's single W stream (it is in this buffer), and the
//   path's later AWs queue behind it in order.
//
// Parameters:
//   AW_WIDTH - AW payload bits (the whole request; AWLEN is also given
//              separately as s_awlen)
//   W_WIDTH  - W payload bits (the whole beat; WLAST is also given as s_wlast)
//   DEPTH    - W buffer in wide beats, 2..256. A burst of AWLEN+1 <= DEPTH
//              beats is released whole; longer ones pass through
//   AW_DEPTH - AWs held, 2..16
//   MAX_OUTSTANDING - the path's outstanding-write bound (the master
//              adapter's max_outstanding): long bursts can be released that
//              far ahead of their W, and the release count must not wrap
//
// Notes:
//   - Order is preserved on both channels: AWs leave in arrival order, W beats
//     likewise. W may arrive ahead of its AW (legal AXI); its completion is
//     counted all the same.
//   - Latency: a short burst's AW is offered the cycle its last W beat is
//     buffered -- the write latency grows by the burst's arrival time.
//   - Properties are proven in formal/bridge/bridge_wr_rate_buf.
//==============================================================================

module bridge_wr_rate_buf #(
    parameter int AW_WIDTH = 64,
    parameter int W_WIDTH  = 72,
    parameter int DEPTH    = 16,
    parameter int AW_DEPTH = 4,
    parameter int MAX_OUTSTANDING = 64
) (
    input  logic                aclk,
    input  logic                aresetn,

    // From the width converter's wide side
    input  logic [AW_WIDTH-1:0] s_aw,
    input  logic [7:0]          s_awlen,
    input  logic                s_awvalid,
    output logic                s_awready,
    input  logic [W_WIDTH-1:0]  s_w,
    input  logic                s_wlast,
    input  logic                s_wvalid,
    output logic                s_wready,

    // To the crossbar
    output logic [AW_WIDTH-1:0] m_aw,
    output logic                m_awvalid,
    input  logic                m_awready,
    output logic [W_WIDTH-1:0]  m_w,
    output logic                m_wvalid,
    input  logic                m_wready
);

    // d ranges -MAX_OUTSTANDING..+DEPTH: signed, one bit of headroom.
    localparam int DW_D = $clog2(MAX_OUTSTANDING + DEPTH + 1) + 1;

    // ---- AW queue: {long, payload} -------------------------------------------
    logic                q_aw_valid, q_aw_ready;
    logic [AW_WIDTH:0]   q_aw;
    logic                w_in_long;
    logic                w_head_long;

    assign w_in_long = (9'({1'b0, s_awlen}) + 9'd1) > 9'(DEPTH);

    gaxi_fifo_sync #(
        .DATA_WIDTH (AW_WIDTH + 1),
        .DEPTH      (AW_DEPTH)
    ) u_aw_q (
        .axi_aclk    (aclk),
        .axi_aresetn (aresetn),
        .wr_valid    (s_awvalid),
        .wr_ready    (s_awready),
        .wr_data     ({w_in_long, s_aw}),
        .rd_ready    (q_aw_ready),
        /* verilator lint_off PINCONNECTEMPTY */
        .count       (),
        /* verilator lint_on PINCONNECTEMPTY */
        .rd_valid    (q_aw_valid),
        .rd_data     (q_aw)
    );

    assign w_head_long = q_aw[AW_WIDTH];
    assign m_aw        = q_aw[AW_WIDTH-1:0];

    // ---- W buffer --------------------------------------------------------------
    logic w_in_hs, w_in_last_hs;

    gaxi_fifo_sync #(
        .DATA_WIDTH (W_WIDTH),
        .DEPTH      (DEPTH)
    ) u_w_q (
        .axi_aclk    (aclk),
        .axi_aresetn (aresetn),
        .wr_valid    (s_wvalid),
        .wr_ready    (s_wready),
        .wr_data     (s_w),
        .rd_ready    (m_wready),
        /* verilator lint_off PINCONNECTEMPTY */
        .count       (),
        /* verilator lint_on PINCONNECTEMPTY */
        .rd_valid    (m_wvalid),
        .rd_data     (m_w)
    );

    assign w_in_hs      = s_wvalid && s_wready;
    assign w_in_last_hs = w_in_hs && s_wlast;

    // ---- Release -----------------------------------------------------------------
    // r_d = (WLASTs buffered) - (AWs released). W arrives in burst order and
    // AWs leave in burst order, so r_d > 0 exactly when the oldest unreleased
    // burst -- the head -- has its WLAST in the buffer. A long burst cannot
    // complete before its AW leaves (more than DEPTH beats cannot fit until
    // some drain, and none drain before the AW is picked), so releasing one
    // takes r_d below zero and its own WLAST brings it back: one counter, no
    // per-burst bookkeeping. (A separate skip count bounded by AW_DEPTH was
    // wrong: released AWs leave the queue, so as many long bursts as the
    // path has outstanding can be ahead of their W -- the proof found 8.)
    logic signed [DW_D-1:0] r_d;
    logic signed [DW_D-1:0] w_d_now;
    logic                   w_release;

    // Count the WLAST entering this cycle too: the AW leaves the cycle its
    // last beat is buffered, not the cycle after (one cycle less write
    // latency). AWVALID then follows the incoming W handshake -- valid and
    // this buffer's own not-full -- never the crossbar's ready.
    assign w_d_now    = r_d + DW_D'(w_in_last_hs);
    assign m_awvalid  = q_aw_valid && (w_head_long || (w_d_now > 0));
    assign w_release  = m_awvalid && m_awready;
    assign q_aw_ready = w_release;

    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_d <= '0;
        end else begin
            r_d <= r_d + DW_D'(w_in_last_hs) - DW_D'(w_release);
        end
    )

endmodule : bridge_wr_rate_buf
