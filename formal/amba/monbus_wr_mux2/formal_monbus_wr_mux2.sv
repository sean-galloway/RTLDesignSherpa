// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// Formal harness for monbus_wr_mux2: two AXI4-shaped write FUBs merged onto
// one. Everything is checked at the PORTS against a harness-side AW-order
// queue built from the port handshakes (which s*_aw handshake fired), so the
// proof does not depend on the DUT's internal queues:
//   - AW: an m_aw handshake is exactly one s_aw handshake, port 0 first when
//     both are valid, and m_aw* carries that port's fields; while m_awvalid
//     is stalled the fields hold (the grant is locked), given sources that
//     hold their own AW as AXI requires (assumed)
//   - W: while bursts are queued, m_w* is the oldest-AW port's W channel
//     (valid/data/strb/last pass through, its wready is m_wready, the other
//     port's wready is 0); with nothing queued no W moves on either side
//   - B: m_b is handed to the oldest-AW port only; m_bready is that port's
//     bready; with nothing queued no B moves
//   - the mux never accepts more AWs than its order depth (no handshake
//     while the harness queue is full)
//   - covers: the two ports interleaved AW/W/B, a port-1 burst completing
//     behind a port-0 burst, a B returned to port 1
`default_nettype none
module formal_monbus_wr_mux2 (
    input logic clk,
    input logic rst_n
);
    localparam int ADDR_WIDTH  = 32;
    localparam int ORDER_DEPTH = 4;    // small: the full condition is reachable at depth 12

    // ---- free inputs -----------------------------------------------------
    (* anyseq *) reg [ADDR_WIDTH-1:0] s0_awaddr, s1_awaddr;
    (* anyseq *) reg [7:0]  s0_awlen, s1_awlen;
    (* anyseq *) reg        s0_awvalid, s1_awvalid;
    (* anyseq *) reg [63:0] s0_wdata, s1_wdata;
    (* anyseq *) reg [7:0]  s0_wstrb, s1_wstrb;
    (* anyseq *) reg        s0_wlast, s1_wlast, s0_wvalid, s1_wvalid;
    (* anyseq *) reg        s0_bready, s1_bready;
    (* anyseq *) reg        m_awready, m_wready, m_bvalid;
    (* anyseq *) reg [1:0]  m_bresp;

    // ---- DUT outputs -----------------------------------------------------
    wire        s0_awready, s1_awready, s0_wready, s1_wready, s0_bvalid, s1_bvalid;
    wire [0:0]  s0_bid, s1_bid, m_awid;
    wire [1:0]  s0_bresp, s1_bresp;
    wire [ADDR_WIDTH-1:0] m_awaddr;
    wire [7:0]  m_awlen, m_wstrb;
    wire [2:0]  m_awsize;
    wire [1:0]  m_awburst;
    wire        m_awvalid, m_wvalid, m_wlast, m_bready;
    wire [63:0] m_wdata;

    monbus_wr_mux2 #(
        .ADDR_WIDTH   (ADDR_WIDTH),
        .AXI_ID_WIDTH (1),
        .ORDER_DEPTH  (ORDER_DEPTH)
    ) dut (
        .axi_aclk (clk), .axi_aresetn (rst_n),
        .s0_awid (1'b0), .s0_awaddr (s0_awaddr), .s0_awlen (s0_awlen), .s0_awsize (3'd3),
        .s0_awburst (2'b01), .s0_awvalid (s0_awvalid), .s0_awready (s0_awready),
        .s0_wdata (s0_wdata), .s0_wstrb (s0_wstrb), .s0_wlast (s0_wlast),
        .s0_wvalid (s0_wvalid), .s0_wready (s0_wready),
        .s0_bid (s0_bid), .s0_bresp (s0_bresp), .s0_bvalid (s0_bvalid), .s0_bready (s0_bready),
        .s1_awid (1'b0), .s1_awaddr (s1_awaddr), .s1_awlen (s1_awlen), .s1_awsize (3'd3),
        .s1_awburst (2'b01), .s1_awvalid (s1_awvalid), .s1_awready (s1_awready),
        .s1_wdata (s1_wdata), .s1_wstrb (s1_wstrb), .s1_wlast (s1_wlast),
        .s1_wvalid (s1_wvalid), .s1_wready (s1_wready),
        .s1_bid (s1_bid), .s1_bresp (s1_bresp), .s1_bvalid (s1_bvalid), .s1_bready (s1_bready),
        .m_awid (m_awid), .m_awaddr (m_awaddr), .m_awlen (m_awlen), .m_awsize (m_awsize),
        .m_awburst (m_awburst), .m_awvalid (m_awvalid), .m_awready (m_awready),
        .m_wdata (m_wdata), .m_wstrb (m_wstrb), .m_wlast (m_wlast),
        .m_wvalid (m_wvalid), .m_wready (m_wready),
        .m_bid (1'b0), .m_bresp (m_bresp), .m_bvalid (m_bvalid), .m_bready (m_bready)
    );

    // ---- reset discipline ------------------------------------------------
    reg [7:0] f_past_valid = 0;
    always @(posedge clk) f_past_valid <= f_past_valid + (f_past_valid < 8'hFF);
    initial assume (!rst_n);
    always @(posedge clk) assume (rst_n == (f_past_valid >= 2));
    wire live = rst_n && f_past_valid > 2;

    // ---- port handshakes ---------------------------------------------------
    wire s0_aw_hs = s0_awvalid && s0_awready;
    wire s1_aw_hs = s1_awvalid && s1_awready;
    wire m_aw_hs  = m_awvalid  && m_awready;
    wire m_w_hs   = m_wvalid   && m_wready;
    wire m_b_hs   = m_bvalid   && m_bready;

    // ---- harness AW-order queue (one tag bit per entry) --------------------
    // Pushed with the port that handshook; the W head pops on an m_w wlast
    // handshake, the B head on an m_b handshake. Two read pointers over one
    // tag store: W consumes in AW order and B consumes in AW order, both
    // behind the AW writer.
    reg [ORDER_DEPTH-1:0] q_tag;
    reg [1:0] q_wr, q_wrd, q_brd;       // ORDER_DEPTH == 4
    reg [2:0] q_wcnt, q_bcnt;
    wire q_w_nonempty = (q_wcnt != 3'd0);
    wire q_b_nonempty = (q_bcnt != 3'd0);
    wire q_full       = (q_wcnt == 3'(ORDER_DEPTH)) || (q_bcnt == 3'(ORDER_DEPTH));
    wire w_head = q_tag[q_wrd];
    wire b_head = q_tag[q_brd];
    wire w_pop  = m_w_hs && m_wlast;

    always @(posedge clk) begin
        if (!rst_n) begin
            q_tag <= '0; q_wr <= '0; q_wrd <= '0; q_brd <= '0; q_wcnt <= '0; q_bcnt <= '0;
        end else begin
            if (m_aw_hs) begin q_tag[q_wr] <= s1_aw_hs; q_wr <= q_wr + 1'b1; end
            if (w_pop)   q_wrd <= q_wrd + 1'b1;
            if (m_b_hs)  q_brd <= q_brd + 1'b1;
            case ({m_aw_hs, w_pop})
                2'b10: q_wcnt <= q_wcnt + 1'b1;
                2'b01: q_wcnt <= q_wcnt - 1'b1;
                default: ;
            endcase
            case ({m_aw_hs, m_b_hs})
                2'b10: q_bcnt <= q_bcnt + 1'b1;
                2'b01: q_bcnt <= q_bcnt - 1'b1;
                default: ;
            endcase
        end
    end

    // ---- AXI source discipline: an offered AW holds until accepted -------
    always @(posedge clk) if (live) begin
        if ($past(s0_awvalid && !s0_awready)) begin
            assume (s0_awvalid);
            assume (s0_awaddr == $past(s0_awaddr));
            assume (s0_awlen  == $past(s0_awlen));
        end
        if ($past(s1_awvalid && !s1_awready)) begin
            assume (s1_awvalid);
            assume (s1_awaddr == $past(s1_awaddr));
            assume (s1_awlen  == $past(s1_awlen));
        end
    end

    // ---- properties ---------------------------------------------------------
    always @(posedge clk) if (live) begin
        // AW stability: a stalled AW keeps its valid and its fields
        if ($past(m_awvalid && !m_awready)) begin
            assert (m_awvalid);
            assert (m_awaddr == $past(m_awaddr));
            assert (m_awlen  == $past(m_awlen));
        end
        // AW: one port per m_aw handshake, port 0 first, fields pass through
        assert (m_aw_hs == (s0_aw_hs || s1_aw_hs));
        assert (!(s0_aw_hs && s1_aw_hs));
        // port 0 first -- when the grant is decided fresh; a grant locked on a
        // stalled port-1 AW completes even if port 0 turned up meanwhile
        if (s0_awvalid && !$past(m_awvalid && !m_awready)) assert (!s1_aw_hs);
        if (s0_aw_hs) begin assert (m_awaddr == s0_awaddr); assert (m_awlen == s0_awlen); end
        if (s1_aw_hs) begin assert (m_awaddr == s1_awaddr); assert (m_awlen == s1_awlen); end
        assert (m_awsize == 3'd3 && m_awburst == 2'b01);
        // never more AWs than the order depth
        if (q_full) assert (!m_aw_hs);
        assert (q_wcnt <= 3'(ORDER_DEPTH) && q_bcnt <= 3'(ORDER_DEPTH));

        // W: the oldest-AW port owns the W channel
        if (q_w_nonempty) begin
            if (w_head == 1'b0) begin
                assert (m_wvalid == s0_wvalid);
                assert (s0_wready == m_wready);
                assert (s1_wready == 1'b0);
                if (m_wvalid) begin
                    assert (m_wdata == s0_wdata); assert (m_wstrb == s0_wstrb);
                    assert (m_wlast == s0_wlast);
                end
            end else begin
                assert (m_wvalid == s1_wvalid);
                assert (s1_wready == m_wready);
                assert (s0_wready == 1'b0);
                if (m_wvalid) begin
                    assert (m_wdata == s1_wdata); assert (m_wstrb == s1_wstrb);
                    assert (m_wlast == s1_wlast);
                end
            end
        end else begin
            assert (!m_wvalid && !s0_wready && !s1_wready);
        end

        // B: handed to the oldest-AW port only
        if (q_b_nonempty) begin
            if (b_head == 1'b0) begin
                assert (s0_bvalid == m_bvalid); assert (s1_bvalid == 1'b0);
                assert (m_bready == s0_bready);
                if (m_bvalid) assert (s0_bresp == m_bresp);
            end else begin
                assert (s1_bvalid == m_bvalid); assert (s0_bvalid == 1'b0);
                assert (m_bready == s1_bready);
                if (m_bvalid) assert (s1_bresp == m_bresp);
            end
        end else begin
            assert (!m_bready && !s0_bvalid && !s1_bvalid);
        end
    end

    // ---- covers --------------------------------------------------------------
    reg [3:0] c_s0_aw, c_s1_aw, c_s1_b, c_s1_wlast_after_s0;
    reg       seen_s0_wlast;
    always @(posedge clk) begin
        if (!rst_n) begin
            c_s0_aw <= 0; c_s1_aw <= 0; c_s1_b <= 0; c_s1_wlast_after_s0 <= 0; seen_s0_wlast <= 0;
        end else begin
            if (s0_aw_hs) c_s0_aw <= c_s0_aw + 1'b1;
            if (s1_aw_hs) c_s1_aw <= c_s1_aw + 1'b1;
            if (m_b_hs && b_head) c_s1_b <= c_s1_b + 1'b1;
            if (w_pop && !w_head) seen_s0_wlast <= 1'b1;
            if (w_pop && w_head && seen_s0_wlast) c_s1_wlast_after_s0 <= c_s1_wlast_after_s0 + 1'b1;
        end
    end
    always @(posedge clk) if (live) begin
        cover (c_s0_aw >= 2 && c_s1_aw >= 2 && c_s1_b >= 1);   // interleaved, B back to port 1
        cover (c_s1_wlast_after_s0 >= 1);                        // port-1 burst behind port-0's
        cover (q_wcnt == 3'(ORDER_DEPTH));                       // order queue full
    end

endmodule
`default_nettype wire
