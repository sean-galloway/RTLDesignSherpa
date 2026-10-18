// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// Formal proof for bridge_wr_rate_buf (projects/components/fabric-gen-ip/bridge/rtl):
// the write rate-matching buffer between an upsize converter's wide side and
// the crossbar.
//
// Configuration: DEPTH=2 wide beats, AW_DEPTH=2, bursts of 1..4 beats (so
// both short bursts, held whole, and long ones, passed through, occur). Small
// on purpose: every mechanism -- hold, pass-through, W ahead of AW, long
// bursts released ahead of their W -- shows up within a few beats.
//
// Environment:
//   source -- up to 6 bursts with fixed but arbitrary lengths; the AW stream
//             and the W stream advance independently (W may run ahead of its
//             AW, as AXI allows); valid is held until taken.
//   sink   -- the crossbar: takes an AW whenever it likes, and a W beat only
//             once that beat's burst's AW has been taken (the W owner rule).
//
// Proven:
//   ap_aw_order   AWs leave in arrival order
//   ap_w_order    W beats leave in arrival order
//   ap_hold       a short burst's AW leaves only once all its beats are in
//                 (the last one may be entering on that same cycle)
//   ap_aw_stable  an offered AW stays offered and unchanged until taken
//   ap_release    a complete short head, or any long head, is offered -- so
//                 the buffer never sits on a burst it could send
// Covered:
//   cp_mix        a long and a short burst both through, every beat out

`timescale 1ns / 1ps

module formal_bridge_wr_rate_buf (
    input logic aclk,
    input logic aresetn
);

    localparam int DEPTH    = 2;
    localparam int AW_DEPTH = 2;
    localparam int NB       = 6;      // bursts per run

    (* anyconst *) logic [2*NB-1:0] c_lens;   // AWLEN of burst k: c_lens[2k +: 2]
    (* anyseq *)   logic            f_aw_go, f_w_go, f_awready, f_wready;

    function automatic logic [3:0] len_of(input logic [3:0] k);
        len_of = (k < 4'(NB)) ? {2'b00, c_lens[2*k +: 2]} : 4'd0;
    endfunction

    reg [7:0] f_past_valid = 0;
    always @(posedge aclk) f_past_valid <= f_past_valid + (f_past_valid < 8'hFF);
    initial assume (!aresetn);
    always @(posedge aclk) if (f_past_valid >= 2) assume (aresetn);

    // ---- source ---------------------------------------------------------------
    reg  [3:0] aw_in_n;                 // next burst whose AW enters
    reg  [3:0] w_in_burst;              // burst of the next W beat in
    reg  [3:0] w_in_beat;               // its beat index
    reg  [7:0] w_in_total;              // beats accepted at the input
    reg        aw_pend, w_pend;

    logic s_awvalid, s_awready, s_wvalid, s_wready;
    logic [3:0] s_aw, s_w;
    logic [7:0] s_awlen;
    logic       s_wlast;

    assign s_awvalid = (aw_in_n < 4'(NB)) && (aw_pend || f_aw_go);
    assign s_aw      = aw_in_n;
    assign s_awlen   = 8'(len_of(aw_in_n));
    assign s_wvalid  = (w_in_burst < 4'(NB)) && (w_pend || f_w_go);
    assign s_w       = w_in_total[3:0];
    assign s_wlast   = (w_in_beat == len_of(w_in_burst));

    always @(posedge aclk) begin
        if (!aresetn) begin
            aw_in_n <= '0; w_in_burst <= '0; w_in_beat <= '0; w_in_total <= '0;
            aw_pend <= 1'b0; w_pend <= 1'b0;
        end else begin
            aw_pend <= s_awvalid && !s_awready;
            w_pend  <= s_wvalid && !s_wready;
            if (s_awvalid && s_awready) aw_in_n <= aw_in_n + 4'd1;
            if (s_wvalid && s_wready) begin
                w_in_total <= w_in_total + 8'd1;
                if (s_wlast) begin
                    w_in_burst <= w_in_burst + 4'd1;
                    w_in_beat  <= '0;
                end else begin
                    w_in_beat <= w_in_beat + 4'd1;
                end
            end
        end
    end

    // ---- DUT --------------------------------------------------------------------
    logic m_awvalid, m_awready, m_wvalid, m_wready;
    logic [3:0] m_aw, m_w;

    bridge_wr_rate_buf #(
        .AW_WIDTH (4),
        .W_WIDTH  (4),
        .DEPTH    (DEPTH),
        .AW_DEPTH (AW_DEPTH),
        .MAX_OUTSTANDING (8)
    ) dut (
        .aclk      (aclk),
        .aresetn   (aresetn),
        .s_aw      (s_aw),
        .s_awlen   (s_awlen),
        .s_awvalid (s_awvalid),
        .s_awready (s_awready),
        .s_w       (s_w),
        .s_wlast   (s_wlast),
        .s_wvalid  (s_wvalid),
        .s_wready  (s_wready),
        .m_aw      (m_aw),
        .m_awvalid (m_awvalid),
        .m_awready (m_awready),
        .m_w       (m_w),
        .m_wvalid  (m_wvalid),
        .m_wready  (m_wready)
    );

    // ---- sink -------------------------------------------------------------------
    reg  [3:0] aw_out_n;                // bursts whose AW has left
    reg  [7:0] cum_before;              // beats in bursts 0..aw_out_n-1
    reg  [3:0] w_out_burst, w_out_beat;
    reg  [7:0] w_out_total;

    assign m_awready = f_awready;
    // A W beat only once its burst's AW has been taken.
    assign m_wready  = f_wready && (w_out_burst < aw_out_n);

    always @(posedge aclk) begin
        if (!aresetn) begin
            aw_out_n <= '0; w_out_burst <= '0; w_out_beat <= '0; w_out_total <= '0;
            cum_before <= '0;
        end else begin
            if (m_awvalid && m_awready) begin
                aw_out_n   <= aw_out_n + 4'd1;
                cum_before <= cum_before + 8'(len_of(aw_out_n)) + 8'd1;
            end
            if (m_wvalid && m_wready) begin
                w_out_total <= w_out_total + 8'd1;
                if (w_out_beat == len_of(w_out_burst)) begin
                    w_out_burst <= w_out_burst + 4'd1;
                    w_out_beat  <= '0;
                end else begin
                    w_out_beat <= w_out_beat + 4'd1;
                end
            end
        end
    end

    // ---- properties ---------------------------------------------------------------
    logic head_short, head_complete, head_present;
    assign head_short    = (len_of(aw_out_n) + 4'd1) <= 4'(DEPTH);
    // Beats accepted so far, counting one accepted this very cycle: the AW
    // may leave on the cycle its last beat enters.
    assign head_complete = (w_in_total + 8'(s_wvalid && s_wready))
                           >= (cum_before + 8'(len_of(aw_out_n)) + 8'd1);
    assign head_present  = (aw_in_n > aw_out_n);

    always @(posedge aclk) begin
        if (aresetn && f_past_valid >= 3) begin
            if (m_awvalid) begin
                ap_aw_order: assert (m_aw == aw_out_n);
                ap_hold:     assert (!head_short || head_complete);
            end
            if (m_wvalid)
                ap_w_order:  assert (m_w == w_out_total[3:0]);
            if ($past(aresetn) && $past(m_awvalid && !m_awready))
                ap_aw_stable: assert (m_awvalid && (m_aw == $past(m_aw)));
            // The head has been in the queue a cycle (the FIFO's read
            // latency): complete-and-short, or long, means it is offered.
            if ($past(aresetn) && head_present && $past(head_present) &&
                $past(aw_out_n) == aw_out_n &&
                (!head_short || (head_complete && $past(head_complete))))
                ap_release:  assert (m_awvalid);
        end
    end

    always @(posedge aclk) begin
        if (aresetn && f_past_valid >= 3) begin
            cp_mix: cover (aw_out_n >= 4'd3 && w_out_total == cum_before &&
                           (c_lens[1:0] >= 2'd2) && (c_lens[3:2] <= 2'd1));
        end
    end

endmodule
