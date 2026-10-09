// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// Formal harness for monbus_group_core (amba TASK-041). Raw record mode
// (USE_COMPRESSION=0), small FIFOs. Everything is checked at the PORTS
// against a harness-side reference model of the routing decision and the
// 3-beat expander, so the proof does not depend on internal names:
//   - routing: drop / error-FIFO / write-path is exactly the per-protocol
//     pkt_mask, err_select and event-mask rule (1 = drop; an unknown
//     protocol is dropped; a masked event never reaches either FIFO)
//   - monbus_ready is asserted iff the packet is dropped or its target can
//     take it this cycle (error FIFO not full; expander idle and write FIFO
//     not full) -- so the group never withholds ready from a packet the
//     FIFOs could take, and never takes one it has no room for
//   - FIFO accounting: err_fifo_count moves by exactly the records written
//     minus the records read out (a record is three fub_s R beats);
//     write_fifo_count by the beats the expander pushes minus the fub_m W
//     handshakes; both bounded by their depth; irq_out == (error records
//     pending)
//   - the flush burst is a legal AXI write: awvalid/addr/len hold until
//     awready, 8-byte INCR beats, wstrb all ones, awlen+1 <= MAX_BURST_BEATS,
//     exactly awlen+1 W beats with wlast on the last, bready only after the
//     last beat, the address inside [base, limit] and never across 4 KB, and
//     a burst is only ever planned from beats already in the FIFO
//   - covers: each routing outcome, a record read back through fub_s, a
//     watermark flush and a timeout flush each carried through AW/W/B
`default_nettype none
module formal_monbus_group_core (
    input logic clk,
    input logic rst_n
);
    localparam int FIFO_DEPTH_ERR   = 4;
    localparam int FIFO_DEPTH_WRITE = 8;
    localparam int ADDR_WIDTH       = 32;
    localparam int MAX_BURST_BEATS  = 8;
    localparam int FLUSH_TIMEOUT    = 8;    // short so the timeout-flush cover is reachable at depth 40

    // packet field positions (monitor_common_pkg)
    localparam [3:0] PROTOCOL_AXI = 4'h0, PROTOCOL_AXIS = 4'h1, PROTOCOL_CORE = 4'h4;
    localparam [3:0] T_ERROR = 4'h0, T_COMPL = 4'h1, T_THRESH = 4'h2, T_TIMEOUT = 4'h3,
                     T_PERF = 4'h4, T_CREDIT = 4'h5, T_CHANNEL = 4'h6, T_STREAM = 4'h7,
                     T_ADDRM = 4'h8, T_DEBUG = 4'hF;

    // ---- free inputs -----------------------------------------------------
    (* anyseq *) reg          monbus_valid;
    (* anyseq *) reg [127:0]  monbus_packet;
    (* anyseq *) reg [63:0]   monbus_timestamp;
    (* anyseq *) reg [ADDR_WIDTH-1:0] cfg_base_addr, cfg_limit_addr;
    (* anyseq *) reg [15:0]   cfg_flush_watermark;
    (* anyseq *) reg [15:0]   cfg_axi_pkt_mask, cfg_axi_err_select, cfg_axi_error_mask,
                              cfg_axi_timeout_mask, cfg_axi_compl_mask, cfg_axi_thresh_mask,
                              cfg_axi_perf_mask, cfg_axi_addr_mask, cfg_axi_debug_mask;
    (* anyseq *) reg [15:0]   cfg_axis_pkt_mask, cfg_axis_err_select, cfg_axis_error_mask,
                              cfg_axis_timeout_mask, cfg_axis_compl_mask, cfg_axis_credit_mask,
                              cfg_axis_channel_mask, cfg_axis_stream_mask;
    (* anyseq *) reg [15:0]   cfg_core_pkt_mask, cfg_core_err_select, cfg_core_error_mask,
                              cfg_core_timeout_mask, cfg_core_compl_mask, cfg_core_thresh_mask,
                              cfg_core_perf_mask, cfg_core_debug_mask;
    (* anyseq *) reg          m_awready, m_wready, m_bvalid;
    (* anyseq *) reg [1:0]    m_bresp;
    (* anyseq *) reg          s_arvalid, s_rready;
    (* anyseq *) reg [ADDR_WIDTH-1:0] s_araddr;
    (* anyseq *) reg [7:0]    s_arlen;

    // ---- DUT outputs -----------------------------------------------------
    wire         monbus_ready;
    wire [63:0]  mon_time_out;
    wire         irq_out, err_fifo_full, write_fifo_full;
    wire [15:0]  err_fifo_count, write_fifo_count;
    wire [31:0]  stat_a, stat_b, stat_c, stat_0, stat_miss, stat_ts, stat_ed, stat_edd;
    wire [0:0]   m_awid;
    wire [ADDR_WIDTH-1:0] m_awaddr;
    wire [7:0]   m_awlen;
    wire [2:0]   m_awsize;
    wire [1:0]   m_awburst;
    wire         m_awvalid, m_wvalid, m_wlast, m_bready;
    wire [63:0]  m_wdata;
    wire [7:0]   m_wstrb;
    wire         s_arready, s_rvalid, s_rlast;
    wire [0:0]   s_rid;
    wire [63:0]  s_rdata;
    wire [1:0]   s_rresp;

    // Formal-only probes of the pipelined write-burst writer.
    wire [1:0]                    f_r_wr_state;
    wire [ADDR_WIDTH-1:0]         f_r_wr_addr;
    wire [15:0]                   f_r_cyc_total;
    wire [16:0]                   f_r_aw_cov_beats;
    wire [16:0]                   f_r_b_beats;
    wire [8:0]                    f_r_aw_subs;
    wire [8:0]                    f_r_b_subs;
    wire [2:0]                    f_r_os_count;
    wire [2:0]                    f_r_ws_count;
    wire [9:0]                    f_r_w_rem_in_sub;
    wire                          f_w_aw_issue;

    monbus_group_core #(
        .FIFO_DEPTH_ERR       (FIFO_DEPTH_ERR),
        .FIFO_DEPTH_WRITE     (FIFO_DEPTH_WRITE),
        .ADDR_WIDTH           (ADDR_WIDTH),
        .AXI_ID_WIDTH_M       (1),
        .AXI_ID_WIDTH_S       (1),
        .MAX_BURST_BEATS      (MAX_BURST_BEATS),
        .FLUSH_TIMEOUT_CYCLES (FLUSH_TIMEOUT),
        .NUM_PROTOCOLS        (3),
        .USE_COMPRESSION      (0),
        .HALF_BEAT_EN         (0)
    ) dut (
        .axi_aclk (clk), .axi_aresetn (rst_n),
        .cam_clear (1'b0),
        .monbus_valid (monbus_valid), .monbus_ready (monbus_ready),
        .monbus_packet (monbus_packet), .monbus_timestamp (monbus_timestamp),
        .mon_time_out (mon_time_out),
        .irq_out (irq_out), .err_fifo_full (err_fifo_full), .write_fifo_full (write_fifo_full),
        .err_fifo_count (err_fifo_count), .write_fifo_count (write_fifo_count),
        .cfg_base_addr (cfg_base_addr), .cfg_limit_addr (cfg_limit_addr),
        .cfg_flush_watermark (cfg_flush_watermark),
        .cfg_compress_en (1'b0),
        .cfg_axi_pkt_mask (cfg_axi_pkt_mask), .cfg_axi_err_select (cfg_axi_err_select),
        .cfg_axi_error_mask (cfg_axi_error_mask), .cfg_axi_timeout_mask (cfg_axi_timeout_mask),
        .cfg_axi_compl_mask (cfg_axi_compl_mask), .cfg_axi_thresh_mask (cfg_axi_thresh_mask),
        .cfg_axi_perf_mask (cfg_axi_perf_mask), .cfg_axi_addr_mask (cfg_axi_addr_mask),
        .cfg_axi_debug_mask (cfg_axi_debug_mask),
        .cfg_axis_pkt_mask (cfg_axis_pkt_mask), .cfg_axis_err_select (cfg_axis_err_select),
        .cfg_axis_error_mask (cfg_axis_error_mask), .cfg_axis_timeout_mask (cfg_axis_timeout_mask),
        .cfg_axis_compl_mask (cfg_axis_compl_mask), .cfg_axis_credit_mask (cfg_axis_credit_mask),
        .cfg_axis_channel_mask (cfg_axis_channel_mask), .cfg_axis_stream_mask (cfg_axis_stream_mask),
        .cfg_core_pkt_mask (cfg_core_pkt_mask), .cfg_core_err_select (cfg_core_err_select),
        .cfg_core_error_mask (cfg_core_error_mask), .cfg_core_timeout_mask (cfg_core_timeout_mask),
        .cfg_core_compl_mask (cfg_core_compl_mask), .cfg_core_thresh_mask (cfg_core_thresh_mask),
        .cfg_core_perf_mask (cfg_core_perf_mask), .cfg_core_debug_mask (cfg_core_debug_mask),
        .mon_compressor_stat_tier1_a (stat_a), .mon_compressor_stat_tier1_b (stat_b),
        .mon_compressor_stat_tier1_c (stat_c), .mon_compressor_stat_tier0 (stat_0),
        .mon_compressor_stat_cam_miss (stat_miss), .mon_compressor_stat_delta_ts_ovf (stat_ts),
        .mon_compressor_stat_event_data_ovf (stat_ed), .mon_compressor_stat_ed_delta_ovf (stat_edd),
        .fub_m_awid (m_awid), .fub_m_awaddr (m_awaddr), .fub_m_awlen (m_awlen),
        .fub_m_awsize (m_awsize), .fub_m_awburst (m_awburst),
        .fub_m_awvalid (m_awvalid), .fub_m_awready (m_awready),
        .fub_m_wdata (m_wdata), .fub_m_wstrb (m_wstrb), .fub_m_wlast (m_wlast),
        .fub_m_wvalid (m_wvalid), .fub_m_wready (m_wready),
        .fub_m_bid (1'b0), .fub_m_bresp (m_bresp), .fub_m_bvalid (m_bvalid), .fub_m_bready (m_bready),
        .fub_s_arid (1'b0), .fub_s_araddr (s_araddr), .fub_s_arlen (s_arlen),
        .fub_s_arsize (3'd3), .fub_s_arburst (2'b01),
        .fub_s_arvalid (s_arvalid), .fub_s_arready (s_arready),
        .fub_s_rid (s_rid), .fub_s_rdata (s_rdata), .fub_s_rresp (s_rresp),
        .fub_s_rlast (s_rlast), .fub_s_rvalid (s_rvalid), .fub_s_rready (s_rready),
        .f_r_wr_state     (f_r_wr_state),
        .f_r_wr_addr      (f_r_wr_addr),
        .f_r_cyc_total    (f_r_cyc_total),
        .f_r_aw_cov_beats (f_r_aw_cov_beats),
        .f_r_b_beats      (f_r_b_beats),
        .f_r_aw_subs      (f_r_aw_subs),
        .f_r_b_subs       (f_r_b_subs),
        .f_r_os_count     (f_r_os_count),
        .f_r_ws_count     (f_r_ws_count),
        .f_r_w_rem_in_sub (f_r_w_rem_in_sub),
        .f_w_aw_issue     (f_w_aw_issue)
    );

    // ---- reset / environment --------------------------------------------
    reg [7:0] f_past_valid = 0;
    always @(posedge clk) f_past_valid <= f_past_valid + (f_past_valid < 8'hFF);
    initial assume (!rst_n);
    always @(posedge clk) assume (rst_n == (f_past_valid >= 2));   // two reset cycles, then live
    wire live = rst_n && f_past_valid > 2;   // past values are post-reset too

    // configuration is programmed once and holds
    always @(posedge clk) if (f_past_valid > 0 && $past(rst_n) && rst_n) begin
        assume ($stable({cfg_base_addr, cfg_limit_addr, cfg_flush_watermark}));
        assume ($stable({cfg_axi_pkt_mask, cfg_axi_err_select, cfg_axi_error_mask, cfg_axi_timeout_mask,
                         cfg_axi_compl_mask, cfg_axi_thresh_mask, cfg_axi_perf_mask, cfg_axi_addr_mask,
                         cfg_axi_debug_mask}));
        assume ($stable({cfg_axis_pkt_mask, cfg_axis_err_select, cfg_axis_error_mask, cfg_axis_timeout_mask,
                         cfg_axis_compl_mask, cfg_axis_credit_mask, cfg_axis_channel_mask, cfg_axis_stream_mask}));
        assume ($stable({cfg_core_pkt_mask, cfg_core_err_select, cfg_core_error_mask, cfg_core_timeout_mask,
                         cfg_core_compl_mask, cfg_core_thresh_mask, cfg_core_perf_mask, cfg_core_debug_mask}));
    end
    // an 8-byte-aligned window of at least one 4 KB page, below the 4 GB wrap
    always @(posedge clk) begin
        assume (cfg_base_addr[11:0] == 12'h000);
        assume (cfg_limit_addr >= cfg_base_addr + 32'h0000_0FFF);
        assume (cfg_limit_addr <  32'hFFFF_0000);
        assume (cfg_flush_watermark >= 16'd3 && cfg_flush_watermark <= 16'(FIFO_DEPTH_WRITE));
    end
    // a well-behaved monbus source holds its packet until taken
    always @(posedge clk) if (live && $past(monbus_valid) && !$past(monbus_ready)) begin
        assume (monbus_valid);
        assume ($stable(monbus_packet));
        assume ($stable(monbus_timestamp));
    end
    // a well-behaved AXI slave: bvalid holds until bready, and B is only
    // returned when the writer has at least one outstanding sub-burst.
    always @(posedge clk) if (live && $past(m_bvalid) && !$past(m_bready)) assume (m_bvalid);
    always @(posedge clk) if (live && m_bvalid) assume (r_os_count > 3'd0);

    // ---- reference model: routing decision --------------------------------
    wire [3:0] p_type  = monbus_packet[127:124];
    wire [3:0] p_proto = monbus_packet[108:105];
    wire [7:0] p_ec    = monbus_packet[104:97];
    wire       ec_rng  = (p_ec[7:4] == 4'h0);
    wire [3:0] ec_idx  = p_ec[3:0];

    reg m_drop, m_err, m_masked;
    always @* begin
        m_drop = 1'b0; m_err = 1'b0; m_masked = 1'b0;
        case (p_proto)
            PROTOCOL_AXI: begin
                m_drop = cfg_axi_pkt_mask[p_type];
                m_err  = cfg_axi_err_select[p_type] && !m_drop;
                if (ec_rng) case (p_type)
                    T_ERROR:   m_masked = cfg_axi_error_mask[ec_idx];
                    T_TIMEOUT: m_masked = cfg_axi_timeout_mask[ec_idx];
                    T_COMPL:   m_masked = cfg_axi_compl_mask[ec_idx];
                    T_THRESH:  m_masked = cfg_axi_thresh_mask[ec_idx];
                    T_PERF:    m_masked = cfg_axi_perf_mask[ec_idx];
                    T_ADDRM:   m_masked = cfg_axi_addr_mask[ec_idx];
                    T_DEBUG:   m_masked = cfg_axi_debug_mask[ec_idx];
                    default:   m_masked = 1'b0;
                endcase
            end
            PROTOCOL_AXIS: begin
                m_drop = cfg_axis_pkt_mask[p_type];
                m_err  = cfg_axis_err_select[p_type] && !m_drop;
                if (ec_rng) case (p_type)
                    T_ERROR:   m_masked = cfg_axis_error_mask[ec_idx];
                    T_TIMEOUT: m_masked = cfg_axis_timeout_mask[ec_idx];
                    T_COMPL:   m_masked = cfg_axis_compl_mask[ec_idx];
                    T_CREDIT:  m_masked = cfg_axis_credit_mask[ec_idx];
                    T_CHANNEL: m_masked = cfg_axis_channel_mask[ec_idx];
                    T_STREAM:  m_masked = cfg_axis_stream_mask[ec_idx];
                    default:   m_masked = 1'b0;
                endcase
            end
            PROTOCOL_CORE: begin
                m_drop = cfg_core_pkt_mask[p_type];
                m_err  = cfg_core_err_select[p_type] && !m_drop;
                if (ec_rng) case (p_type)
                    T_ERROR:   m_masked = cfg_core_error_mask[ec_idx];
                    T_TIMEOUT: m_masked = cfg_core_timeout_mask[ec_idx];
                    T_COMPL:   m_masked = cfg_core_compl_mask[ec_idx];
                    T_THRESH:  m_masked = cfg_core_thresh_mask[ec_idx];
                    T_PERF:    m_masked = cfg_core_perf_mask[ec_idx];
                    T_DEBUG:   m_masked = cfg_core_debug_mask[ec_idx];
                    default:   m_masked = 1'b0;
                endcase
            end
            default: m_drop = 1'b1;
        endcase
        if (m_masked) begin m_drop = 1'b1; m_err = 1'b0; end
    end
    wire m_to_err   = monbus_valid && !m_drop && m_err;
    wire m_to_write = monbus_valid && !m_drop && !m_err;
    wire m_dropped  = monbus_valid && m_drop;

    // ---- reference model: the 3-beat raw expander -------------------------
    // TS beat is pushed the cycle the packet is accepted; HI and LO follow,
    // each whenever the write FIFO can take a beat.
    reg [1:0] x_st;          // 0 = idle/TS, 1 = HI pending, 2 = LO pending
    wire x_idle   = (x_st == 2'd0);
    wire x_accept = x_idle && m_to_write && !write_fifo_full;
    wire x_push   = x_accept || (!x_idle && !write_fifo_full);
    always @(posedge clk) begin
        if (!rst_n) x_st <= 2'd0;
        else case (x_st)
            2'd0: if (x_accept) x_st <= 2'd1;
            2'd1: if (!write_fifo_full) x_st <= 2'd2;
            2'd2: if (!write_fifo_full) x_st <= 2'd0;
            default: x_st <= 2'd0;
        endcase
    end

    // expected ready: dropped, or the target can take the packet now
    wire exp_ready = m_dropped || (m_to_err && !err_fifo_full) || x_accept;
    wire mb_hs     = monbus_valid && monbus_ready;

    // ---- P1: routing and ready ------------------------------------------
    always @(posedge clk) if (live) begin
        ap_ready_exact:     assert (monbus_ready == exp_ready);
        // a masked or unknown-protocol packet is consumed without a trace
        ap_drop_no_trace:   assert (!(m_dropped && (mb_hs && (x_accept || (m_to_err && !err_fifo_full)))));
    end

    // ---- P2: FIFO accounting ---------------------------------------------
    // gaxi_fifo_sync computes `count` from the NEXT pointers, so a push or a
    // pop shows in the count the same cycle it handshakes; full/empty (hence
    // err_fifo_full, write_fifo_full, irq_out and s_rvalid) are registered and
    // follow the count by one cycle.
    // error records leave three R beats at a time; count the third beat
    reg [1:0] r_slice;
    wire r_hs = s_rvalid && s_rready;
    wire rec_pop = r_hs && (r_slice == 2'd2);
    always @(posedge clk) begin
        if (!rst_n) r_slice <= 2'd0;
        else if (r_hs) r_slice <= (r_slice == 2'd2) ? 2'd0 : r_slice + 2'd1;
    end
    wire rec_push = mb_hs && m_to_err;
    wire w_hs     = m_wvalid && m_wready;
    always @(posedge clk) if (live) begin
        ap_err_count_step:   assert (err_fifo_count == $past(err_fifo_count) + 16'(rec_push) - 16'(rec_pop));
        ap_write_count_step: assert (write_fifo_count == $past(write_fifo_count) + 16'(x_push) - 16'(w_hs));
        ap_err_bound:        assert (err_fifo_count <= 16'(FIFO_DEPTH_ERR));
        ap_write_bound:      assert (write_fifo_count <= 16'(FIFO_DEPTH_WRITE));
        ap_err_full:         assert (err_fifo_full   == ($past(err_fifo_count)   == 16'(FIFO_DEPTH_ERR)));
        ap_write_full:       assert (write_fifo_full == ($past(write_fifo_count) == 16'(FIFO_DEPTH_WRITE)));
        ap_irq_is_pending:   assert (irq_out == ($past(err_fifo_count) != 16'd0));
        ap_rvalid_pending:   assert (!s_rvalid || $past(err_fifo_count) != 16'd0);
        ap_rresp_okay:       assert (!s_rvalid || s_rresp == 2'b00);
    end
    // the first cycle out of reset: nothing pending, no AXI master activity
    // (the counts may already show a same-cycle push; they are covered by the
    // step relation above from this cycle on)
    always @(posedge clk) if (f_past_valid > 0 && rst_n && $past(!rst_n)) begin
        ap_reset_outputs: assert (!irq_out && !err_fifo_full && !write_fifo_full
                                  && !m_awvalid && !m_wvalid && !m_bready && !s_rvalid);
        ap_reset_counts:  assert (err_fifo_count == 16'(rec_push) && write_fifo_count == 16'(x_push));
    end

    // ---- P3: the flush burst is a legal AXI write --------------------------
    // The burst writer is pipelined: a drain cycle may contain several
    // outstanding AW sub-bursts, so the old single-burst tracker is replaced
    // by checks against the DUT's internal FSM and bookkeeping queues.
    localparam logic [1:0] WR_IDLE = 2'd0;
    localparam logic [1:0] WR_RUN  = 2'd1;

    // Aliases for the formal probes of the pipelined writer.
    wire        wr_run            = (f_r_wr_state == WR_RUN);
    wire        wr_idle           = (f_r_wr_state == WR_IDLE);
    wire [9:0]  r_w_rem           = f_r_w_rem_in_sub;
    wire [15:0] r_cyc_total       = f_r_cyc_total;
    wire [16:0] r_aw_cov          = f_r_aw_cov_beats;
    wire [16:0] r_b_beats         = f_r_b_beats;
    wire [8:0]  r_aw_subs         = f_r_aw_subs;
    wire [8:0]  r_b_subs          = f_r_b_subs;
    wire [2:0]  r_os_count        = f_r_os_count;
    wire [2:0]  r_ws_count        = f_r_ws_count;
    wire        w_aw_issue        = f_w_aw_issue;

    wire aw_hs = m_awvalid && m_awready;
    wire b_hs  = m_bvalid  && m_bready;
    wire aw_new = aw_hs;
    wire [ADDR_WIDTH-1:0] aw_last = m_awaddr + ({24'd0, m_awlen} << 3) + 32'd7;

    // Track last accepted AW to check the 8-byte stride across sub-bursts.
    reg [ADDR_WIDTH-1:0] last_aw_addr;
    reg [7:0]            last_aw_len;
    reg                  last_aw_valid;
    always @(posedge clk) begin
        if (!rst_n) last_aw_valid <= 1'b0;
        else if (aw_hs) begin
            last_aw_valid <= 1'b1;
            last_aw_addr  <= m_awaddr;
            last_aw_len   <= m_awlen;
        end
    end

    always @(posedge clk) if (live) begin
        // shape
        ap_aw_shape:   assert (!m_awvalid || (m_awsize == 3'd3 && m_awburst == 2'b01 && m_awid == 1'b0
                                             && m_awaddr[2:0] == 3'b000 && m_awlen < 8'(MAX_BURST_BEATS)));
        ap_aw_window:  assert (!m_awvalid || (m_awaddr >= cfg_base_addr && aw_last <= cfg_limit_addr));
        ap_aw_4kb:     assert (!m_awvalid || (m_awaddr[31:12] == aw_last[31:12]));
        ap_w_strb:     assert (!m_wvalid || m_wstrb == 8'hFF);

        // the three master-write channels only operate during WR_RUN
        ap_aw_in_run:  assert (!m_awvalid || wr_run);
        ap_w_in_run:   assert (!m_wvalid  || wr_run);
        ap_b_in_run:   assert (!m_bready  || wr_run);

        // wlast matches the last beat of the currently-loaded W sub-burst
        ap_wlast_exact: assert (!(m_wvalid && wr_run) || (m_wlast == (r_w_rem == 10'd1)));

        // bookkeeping sanity: covered beats never exceed the cycle total, Bs
        // only return for issued AWs, and outstanding count is exact
        ap_aw_cov_bound: assert (r_aw_cov <= 17'(r_cyc_total));
        ap_b_le_aw:      assert (r_b_subs <= r_aw_subs);
        ap_os_exact:     assert (r_os_count == 3'(r_aw_subs - r_b_subs));
        ap_ws_le_os:     assert (r_ws_count <= r_os_count);
        ap_b_beats_bound:assert (r_b_beats <= 17'(r_cyc_total));

        // addresses advance by 8 bytes per beat across consecutive AWs
        ap_aw_stride:  assert (!(aw_hs && last_aw_valid)
                              || (m_awaddr == last_aw_addr + ADDR_WIDTH'(({24'd0, last_aw_len} + 32'd1) << 3)));

        // close condition: if last cycle the writer was in WR_RUN and every
        // committed beat had been credited and the W side was empty, this
        // cycle it must have returned to WR_IDLE
        ap_close_idle: assert (!($past(wr_run)
                                  && ($past(r_b_beats) == 17'($past(r_cyc_total)))
                                  && ($past(r_aw_cov)  == 17'($past(r_cyc_total)))
                                  && ($past(r_w_rem)   == 10'd0)
                                  && ($past(r_ws_count)==  3'd0))
                              || wr_idle);
    end

    // ---- covers ----------------------------------------------------------
    reg [15:0] wm_at_aw;   // beats in the FIFO when the burst was planned
    always @(posedge clk) if (aw_new) wm_at_aw <= write_fifo_count;
    always @(posedge clk) if (live) begin
        cp_drop_pkt_mask:   cover (mb_hs && m_drop && !m_masked && p_proto == PROTOCOL_AXI);
        cp_drop_event_mask: cover (mb_hs && m_masked && p_proto == PROTOCOL_AXI);
        cp_drop_unknown:    cover (mb_hs && p_proto == 4'h7);
        cp_to_err:          cover (rec_push);
        cp_to_write_axis:   cover (mb_hs && m_to_write && p_proto == PROTOCOL_AXIS);
        cp_to_write_core:   cover (mb_hs && m_to_write && p_proto == PROTOCOL_CORE);
        cp_irq:             cover (irq_out);
        cp_err_full:        cover (err_fifo_full);
        cp_record_read:     cover (rec_pop && s_rlast);
        cp_both_fifos:      cover (err_fifo_count > 0 && write_fifo_count > 0);
        cp_burst_done:      cover (b_hs);
        cp_flush_watermark: cover (b_hs && wm_at_aw >= cfg_flush_watermark);
        cp_flush_timeout:   cover (b_hs && wm_at_aw <  cfg_flush_watermark);
        cp_ready_withheld:  cover (monbus_valid && !monbus_ready && !m_drop);
    end
endmodule
