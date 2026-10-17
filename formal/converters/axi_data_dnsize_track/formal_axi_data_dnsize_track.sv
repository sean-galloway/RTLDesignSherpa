// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// Formal proof for axi_data_dnsize in TRACK_BURSTS=1 mode -- the mode the
// read width converter uses on an upsize path (wide slave R sliced into
// narrow master beats). The untracked mode has its own proof
// (../axi_data_dnsize); this one did not exist, so the burst framing this
// primitive does -- narrow_last from burst_len, the first beat from
// start_lane -- was covered by simulation only.
//
// Configuration: WIDE_WIDTH=8, NARROW_WIDTH=4 (ratio 2), BURST_LEN_WIDTH=3
// (bursts of 1..8 narrow beats), start lane 0 or 1, no sideband.
//
// Environment: a source that issues bursts back to back, any length and
// start lane, presents each burst's first wide beat with burst_start held
// (as axi4_dwidth_converter_rd drives it), holds a presented beat until it
// is taken, and may start the next burst on the cycle the previous one's last
// wide beat is taken. Every narrow lane of the stream carries its sequence
// number, so the checker sees exactly which beat came out.
//
// Proven:
//   ap_seq          narrow beats leave in stream order, none lost or repeated
//   ap_last_framing narrow_last on exactly the (burst_len+1)-th beat of each burst
//   ap_no_orphan    no narrow beat without a burst having been opened
// Covered:
//   cp_back_to_back a burst's last narrow beat and the next burst's first on
//                   consecutive cycles -- no dead cycle at the boundary

`timescale 1ns / 1ps

module formal_axi_data_dnsize_track (
    input logic aclk,
    input logic aresetn
);

    localparam int WIDE_WIDTH      = 8;
    localparam int NARROW_WIDTH    = 4;
    localparam int BURST_LEN_WIDTH = 3;

    // =========================================================================
    // Free inputs
    // =========================================================================
    (* anyseq *) logic                       f_go;        // source offers its beat
    (* anyseq *) logic                       f_chain;     // next burst starts at once
    (* anyseq *) logic [BURST_LEN_WIDTH-1:0] f_new_len;
    (* anyseq *) logic                       f_new_lane;
    (* anyseq *) logic                       narrow_ready;

    // =========================================================================
    // Formal infrastructure
    // =========================================================================
    reg [7:0] f_past_valid = 0;
    always @(posedge aclk)
        f_past_valid <= f_past_valid + (f_past_valid < 8'hFF);

    initial assume (!aresetn);
    always @(posedge aclk) if (f_past_valid >= 2) assume (aresetn);

    // =========================================================================
    // Source: back-to-back bursts, stream-numbered lanes
    // =========================================================================
    reg                       src_active;
    reg                       src_first;     // next beat is the burst's first
    reg                       src_pending;   // a beat is presented, not yet taken
    reg [BURST_LEN_WIDTH-1:0] cur_len;
    reg                       cur_lane;
    reg [3:0]                 src_left;      // narrow beats of this burst still to place
    reg [3:0]                 src_seq;       // sequence number of the next narrow beat
    reg [2:0]                 q_count;       // bursts opened, not yet fully out

    logic                     wide_valid, wide_ready_o;
    logic [WIDE_WIDTH-1:0]    wide_data;
    logic                     w_wide_hs;
    logic [1:0]               w_lanes;       // narrow beats this wide beat carries

    assign wide_valid = src_active && (src_pending || f_go);
    assign w_wide_hs  = wide_valid && wide_ready_o;
    assign w_lanes    = (src_first && cur_lane) ? 2'd1 : 2'd2;
    // A lane outside the burst carries 4'hF; the checker never expects it.
    assign wide_data  = (src_first && cur_lane)
                      ? {src_seq, 4'hF}
                      : {(src_left >= 4'd2) ? 4'(src_seq + 4'd1) : 4'hF, src_seq};

    logic [3:0] w_used;
    assign w_used = ({2'b00, w_lanes} < src_left) ? {2'b00, w_lanes} : src_left;

    logic w_open_now;   // a new burst is loaded this cycle
    assign w_open_now = (!src_active || (w_wide_hs && (w_used == src_left))) &&
                        f_chain && (q_count < 3'd3);

    always @(posedge aclk) begin
        if (!aresetn) begin
            src_active  <= 1'b0;
            src_first   <= 1'b0;
            src_pending <= 1'b0;
            cur_len     <= '0;
            cur_lane    <= 1'b0;
            src_left    <= '0;
            src_seq     <= '0;
        end else begin
            src_pending <= wide_valid && !wide_ready_o;
            if (w_wide_hs) begin
                src_seq   <= src_seq + w_used;
                src_left  <= src_left - w_used;
                src_first <= 1'b0;
                if (w_used == src_left)
                    src_active <= 1'b0;
            end
            if (w_open_now) begin
                src_active <= 1'b1;
                src_first  <= 1'b1;
                cur_len    <= f_new_len;
                cur_lane   <= f_new_lane;
                src_left   <= 4'({1'b0, f_new_len}) + 4'd1;
            end
        end
    end

    // =========================================================================
    // DUT
    // =========================================================================
    logic                    narrow_valid_o, narrow_last_o;
    logic [NARROW_WIDTH-1:0] narrow_data_o;
    logic                    narrow_sideband_o;

    axi_data_dnsize #(
        .WIDE_WIDTH      (WIDE_WIDTH),
        .NARROW_WIDTH    (NARROW_WIDTH),
        .WIDE_SB_WIDTH   (0),
        .NARROW_SB_WIDTH (0),
        .SB_BROADCAST    (1),
        .TRACK_BURSTS    (1),
        .BURST_LEN_WIDTH (BURST_LEN_WIDTH)
    ) dut (
        .aclk            (aclk),
        .aresetn         (aresetn),
        .burst_len       (cur_len),
        .burst_start     (wide_valid && src_first),
        .start_lane      (cur_lane),
        .wide_valid      (wide_valid),
        .wide_ready      (wide_ready_o),
        .wide_data       (wide_data),
        .wide_sideband   (1'b0),
        .wide_last       (1'b0),
        .narrow_valid    (narrow_valid_o),
        .narrow_ready    (narrow_ready),
        .narrow_data     (narrow_data_o),
        .narrow_sideband (narrow_sideband_o),
        .narrow_last     (narrow_last_o)
    );

    // =========================================================================
    // Checker: per-burst lengths in order, expected sequence number
    // =========================================================================
    reg [BURST_LEN_WIDTH-1:0] q_len [4];
    reg [1:0]                 q_rd, q_wr;
    reg [3:0]                 exp_seq;
    reg [BURST_LEN_WIDTH:0]   out_cnt;     // beats of the head burst already out

    logic w_narrow_hs;
    assign w_narrow_hs = narrow_valid_o && narrow_ready;

    always @(posedge aclk) begin
        if (!aresetn) begin
            q_rd    <= '0;
            q_wr    <= '0;
            q_count <= '0;
            exp_seq <= '0;
            out_cnt <= '0;
        end else begin
            if (w_wide_hs && src_first) begin
                q_len[q_wr] <= cur_len;
                q_wr        <= q_wr + 2'd1;
            end
            if (w_narrow_hs) begin
                exp_seq <= exp_seq + 4'd1;
                if (narrow_last_o) begin
                    out_cnt <= '0;
                    q_rd    <= q_rd + 2'd1;
                end else begin
                    out_cnt <= out_cnt + 1'b1;
                end
            end
            q_count <= q_count + 3'(w_wide_hs && src_first) - 3'(w_narrow_hs && narrow_last_o);
        end
    end

    always @(posedge aclk) begin
        if (aresetn && f_past_valid >= 3 && w_narrow_hs) begin
            ap_seq:          assert (narrow_data_o == exp_seq);
            ap_no_orphan:    assert (q_count != 3'd0);
            ap_last_framing: assert (narrow_last_o == (out_cnt == {1'b0, q_len[q_rd]}));
        end
    end

    // =========================================================================
    // Covers
    // =========================================================================
    always @(posedge aclk) begin
        if (aresetn && f_past_valid >= 3) begin
            cp_burst_done:   cover (w_narrow_hs && narrow_last_o);
            cp_lane1_burst:  cover (w_wide_hs && src_first && cur_lane);
            cp_back_to_back: cover ($past(w_narrow_hs && narrow_last_o) && w_narrow_hs &&
                                    $past(aresetn));
            cp_three_bursts: cover (w_narrow_hs && narrow_last_o && q_rd == 2'd2);
        end
    end

endmodule
