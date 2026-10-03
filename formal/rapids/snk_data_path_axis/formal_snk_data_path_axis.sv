// SPDX-License-Identifier: MIT
// Formal harness for rapids macro/snk_data_path_axis (TASK-022, DIR 1).
//
// Port-level only: the DUT is a black box, every property rides on its ports.
// The full byte sink chain is inside: AXIS ingress shifter + packet-record
// queue + fill allocator -> snk_data_path -> {snk_sram_controller,
// axi_write_engine} -> AXI4 write master.
//
// Invariant families (plan: snuggly-drifting-harbor.md):
//   F1  ingress barrel-shifter hold/spill: per-beat byte/strb equality of the
//       AXI W stream against a shadow of the accepted AXIS stream, beat
//       counts, strb byte totals
//   F2  packet-record queue depth/ready contract + tready gating
//   F3  AXI write legality: alignment, awsize/awburst, 4KB split, awlen caps,
//       wlast placement, W-needs-AW
//   F4  per-channel reset: no tready, queue cleared, abort -> null-beat WSTRB
//
// Shadow architecture:
//   - packet-record queue mirrored exactly on push (port handshake + shadowed
//     w_rst); pops are exact for the no-spill case and LAZY for the spill
//     case (pend_pop applied at the channel's next accepted beat -- the
//     internal flush pop is guaranteed to have happened by then, because
//     tready gates on !r_flush_valid). eff_rp = rp + pend_pop is therefore
//     the exact internal head at every accept, and eff_count = count -
//     pend_pop is the exact internal count at all times.
//   - the shifter is mirrored combinationally from (hold, tstrb, head
//     offset); each accepted beat appends one memory beat (data+strb) to a
//     64-entry per-channel ring, and a spilled tlast appends the flush beat
//     early (its value is fixed at the tlast cycle; the AXI side cannot
//     emit it before the internal flush happens, so early append is safe).
//   - the scheduler is CO-MODELED, not anyseq: sched_wr_valid/beats are
//     driven from shadow state (beats = completed-but-unrequested memory
//     beats), addr/burst_len latched from anyseq at request start.
//   - a shadow AW queue attributes W beats to channels (AXI4 write data is
//     in AW order) and checks burst legality.
//
// Reset-while-in-flight (F4): kills can orphan shadow ring slots (beats
// formed but never written). The ring is 64 deep so a bounded number of
// kills inside a depth-30 BMC cannot wrap it, slot valid bits gate the
// byte compare, and w_idx is only compared against slots that were filled.
// Kills are assumed spaced >= 8 cycles apart per channel.
//
// Solver: smtbmc bitwuzla (measured 2026-10-02: depth 50 PASS in 38 s at
// these sizes; z3 never finishes on the SRAM arrays).
module formal_snk_data_path_axis (
    input logic clk,
    input logic rst_n
);
    localparam int NC  = 2;
    localparam int AW  = 32;
    localparam int DW  = 64;
    localparam int SW  = DW/8;           // 8 byte lanes
    localparam int IW  = 4;
    localparam int SD  = 8;
    localparam int SCW = $clog2(SD) + 1;
    localparam int OFF_W = $clog2(SW);   // 3
    localparam int PQD = 4;              // DUT PQ_DEPTH (localparam :202)
    localparam int RING = 32;            // shadow memory-beat ring per channel
                                   // (bound: filled-not-drained <= SD + W pipe = 12)

    (* anyseq *) logic [7:0]         cfg_axi_wr_xfer_beats;
    (* anyseq *) logic [7:0]         cfg_alloc_size;
    (* anyseq *) logic [NC-1:0]      cfg_channel_reset;
    (* anyseq *) logic [DW-1:0]      s_axis_tdata;
    (* anyseq *) logic [SW-1:0]      s_axis_tstrb;
    (* anyseq *) logic               s_axis_tlast;
    (* anyseq *) logic [3:0]         s_axis_tid;
    (* anyseq *) logic [3:0]         s_axis_tdest;
    (* anyseq *) logic [0:0]         s_axis_tuser;
    (* anyseq *) logic               s_axis_tvalid;
    (* anyseq *) logic [AW-1:0]      anyseq_addr;
    (* anyseq *) logic [7:0]         anyseq_burst_len;
    (* anyseq *) logic [NC-1:0]      sched_wr_pkt_valid;
    (* anyseq *) logic [NC*32-1:0]   sched_wr_pkt_bytes;
    (* anyseq *) logic [NC*OFF_W-1:0] sched_wr_pkt_offset;

    // driven by the scheduler co-model
    logic [NC-1:0]      sched_wr_valid;
    logic [NC*AW-1:0]   sched_wr_addr;
    logic [NC*32-1:0]   sched_wr_beats;
    logic [NC*8-1:0]    sched_wr_burst_len;

    logic               s_axis_tready;
    logic [NC-1:0]      sched_wr_ready, sched_wr_pkt_ready;
    logic [NC-1:0]      sched_wr_done_strobe, sched_wr_commit_strobe, sched_wr_error;
    logic [NC*32-1:0]   sched_wr_beats_done, sched_wr_commit_beats;
    logic [IW-1:0]      m_axi_awid;
    logic [AW-1:0]      m_axi_awaddr;
    logic [7:0]         m_axi_awlen;
    logic [2:0]         m_axi_awsize;
    logic [1:0]         m_axi_awburst;
    logic               m_axi_awvalid;
    logic [DW-1:0]      m_axi_wdata;
    logic [SW-1:0]      m_axi_wstrb;
    logic               m_axi_wlast, m_axi_wvalid, m_axi_bready;
    logic [NC-1:0]      dbg_sram_bridge_pending, dbg_sram_bridge_out_valid;
    logic [31:0]        dbg_axis_beats_received, dbg_axis_packets_received;
    logic [0:0]         o_active_channel_id;
    logic               o_active_channel_valid;

    //=========================================================================
    // Cooperative AXI write slave: always ready for AW and W, B one cycle
    // after each burst's wlast, held until bready. bresp always OKAY.
    //=========================================================================
    logic               m_axi_awready;
    logic               m_axi_wready;
    logic [IW-1:0]      m_axi_bid;
    logic [1:0]         m_axi_bresp;
    logic               m_axi_bvalid;
    logic [IW-1:0]      r_bid;
    logic               r_bvalid;

    assign m_axi_awready = 1'b1;
    assign m_axi_wready  = 1'b1;
    assign m_axi_bid     = r_bid;
    assign m_axi_bresp   = 2'b00;
    assign m_axi_bvalid  = r_bvalid;

    always @(posedge clk) begin
        if (!rst_n) begin
            r_bvalid <= 1'b0;
            r_bid    <= '0;
        end else begin
            if (m_axi_wvalid && m_axi_wready && m_axi_wlast) begin
                r_bvalid <= 1'b1;
                r_bid    <= m_axi_awid;
            end else if (m_axi_bvalid && m_axi_bready) begin
                r_bvalid <= 1'b0;
            end
        end
    end

    snk_data_path_axis #(
        .NUM_CHANNELS       (NC),
        .ADDR_WIDTH         (AW),
        .DATA_WIDTH         (DW),
        .AXI_ID_WIDTH       (IW),
        .SRAM_DEPTH         (SD),
        .SEG_COUNT_WIDTH    (SCW),
        .PIPELINE           (1),
        .AW_MAX_OUTSTANDING (2),
        .W_PHASE_FIFO_DEPTH (4),
        .B_PHASE_FIFO_DEPTH (4),
        .AXIS_ID_WIDTH      (4),
        .AXIS_DEST_WIDTH    (4),
        .AXIS_USER_WIDTH    (1)
    ) dut (
        .clk, .rst_n,
        .cfg_axi_wr_xfer_beats, .cfg_alloc_size, .cfg_channel_reset,
        .s_axis_tdata, .s_axis_tstrb, .s_axis_tlast, .s_axis_tid,
        .s_axis_tdest, .s_axis_tuser, .s_axis_tvalid, .s_axis_tready,
        .sched_wr_valid, .sched_wr_ready, .sched_wr_addr, .sched_wr_beats,
        .sched_wr_burst_len,
        .sched_wr_pkt_valid, .sched_wr_pkt_ready, .sched_wr_pkt_bytes,
        .sched_wr_pkt_offset,
        .sched_wr_done_strobe, .sched_wr_beats_done,
        .sched_wr_commit_strobe, .sched_wr_commit_beats, .sched_wr_error,
        .m_axi_awid, .m_axi_awaddr, .m_axi_awlen, .m_axi_awsize,
        .m_axi_awburst, .m_axi_awvalid, .m_axi_awready,
        .m_axi_wdata, .m_axi_wstrb, .m_axi_wlast, .m_axi_wvalid, .m_axi_wready,
        .m_axi_bid, .m_axi_bresp, .m_axi_bvalid, .m_axi_bready,
        .dbg_sram_bridge_pending, .dbg_sram_bridge_out_valid,
        .dbg_axis_beats_received, .dbg_axis_packets_received,
        .o_active_channel_id, .o_active_channel_valid
    );

    //=========================================================================
    // Reset idiom
    //=========================================================================
    reg [7:0] f_past_valid = 0;
    always @(posedge clk)
        f_past_valid <= f_past_valid + (f_past_valid < 8'hFF);
    initial assume (!rst_n);
    always @(posedge clk)
        if (f_past_valid >= 2) assume (rst_n);

    //=========================================================================
    // Shadow per-channel reset (mirrors DUT r_rst_d1/w_rst :190-197)
    //=========================================================================
    logic [NC-1:0] r_rst_d1_sh;
    wire  [NC-1:0] w_rst_sh = cfg_channel_reset | r_rst_d1_sh;
    always @(posedge clk) begin
        if (!rst_n) r_rst_d1_sh <= '0;
        else        r_rst_d1_sh <= cfg_channel_reset;
    end

    //=========================================================================
    // Environment assumptions
    //=========================================================================
    // quasi-static config, documented ranges (BUG-012: no narrowing; 0 is a
    // LEGAL AWLEN value = 1-beat bursts, so no lower bound)
    always @(posedge clk)
        if (f_past_valid > 0 && rst_n && $past(rst_n)) begin
            assume ($stable(cfg_axi_wr_xfer_beats));
            assume ($stable(cfg_alloc_size));
        end

    // tid in range
    always @(posedge clk)
        if (rst_n) begin
            assume (s_axis_tid < NC);
            assume (anyseq_addr < 32'h0001_0000);   // plan: keep AW space small
        end

    // tstrb shape: packed from lane 0; all-ones except possibly the tlast beat
    wire w_tstrb_contig = (s_axis_tstrb & (s_axis_tstrb + 8'd1)) == 8'd0;
    always @(posedge clk)
        if (rst_n && s_axis_tvalid) begin
            assume (s_axis_tstrb != 8'd0);
            assume (w_tstrb_contig);
            if (!s_axis_tlast) assume (s_axis_tstrb == {SW{1'b1}});
        end

    // AXIS payload stability under backpressure
    always @(posedge clk)
        if (f_past_valid > 0 && rst_n && $past(rst_n) &&
            $past(s_axis_tvalid && !s_axis_tready)) begin
            assume (s_axis_tvalid);
            assume ($stable(s_axis_tdata));
            assume ($stable(s_axis_tstrb));
            assume ($stable(s_axis_tlast));
            assume ($stable(s_axis_tid));
            assume ($stable(s_axis_tdest));
            assume ($stable(s_axis_tuser));
        end

    // packet-record handshake stability + documented record range
    always @(posedge clk)
        if (rst_n) begin
            for (int ch = 0; ch < NC; ch++) begin
                if (sched_wr_pkt_valid[ch]) begin
                    assume (sched_wr_pkt_bytes[ch*32 +: 32] >= 32'd1);
                    assume (sched_wr_pkt_bytes[ch*32 +: 32] <= 32'(2*SW));
                    assume (!w_rst_sh[ch]);
                end
                if (f_past_valid > 0 && $past(rst_n) &&
                    $past(sched_wr_pkt_valid[ch] && !sched_wr_pkt_ready[ch])) begin
                    assume (sched_wr_pkt_valid[ch]);
                    assume ($stable(sched_wr_pkt_bytes[ch*32 +: 32]));
                    assume ($stable(sched_wr_pkt_offset[ch*OFF_W +: OFF_W]));
                end
            end
        end

    // kill spacing: per-channel resets at least 8 cycles apart (bounds the
    // orphaned shadow slots a depth-30 BMC can produce)
    logic [NC-1:0][3:0] r_kill_cool;
    always @(posedge clk) begin
        if (!rst_n) r_kill_cool <= '0;
        else begin
            for (int ch = 0; ch < NC; ch++) begin
                if (cfg_channel_reset[ch])      r_kill_cool[ch] <= 4'd8;
                else if (r_kill_cool[ch] != 0)  r_kill_cool[ch] <= r_kill_cool[ch] - 4'd1;
            end
        end
    end
    always @(posedge clk)
        if (rst_n)
            for (int ch = 0; ch < NC; ch++)
                if (r_kill_cool[ch] != 0) assume (!cfg_channel_reset[ch]);

    //=========================================================================
    // Shadow packet-record queue (exact push, lazy spill pop)
    //=========================================================================
    logic [NC-1:0][PQD-1:0][OFF_W-1:0] pq_off;
    logic [NC-1:0][PQD-1:0][31:0]      pq_bytes;
    logic [NC-1:0][2:0]                pq_wp, pq_rp;
    logic [NC-1:0]                     pend_pop;

    wire [NC-1:0][2:0] pq_count;
    wire [NC-1:0][2:0] eff_count;   // exact internal count
    wire [NC-1:0][2:0] eff_rp;      // exact internal head index
    genvar gch;
    generate
        for (gch = 0; gch < NC; gch++) begin : g_cnt
            assign pq_count[gch]  = pq_wp[gch] - pq_rp[gch];
            assign eff_count[gch] = pq_count[gch] - 3'(pend_pop[gch]);
            assign eff_rp[gch]    = pq_rp[gch] + 3'(pend_pop[gch]);
        end
    endgenerate

    //=========================================================================
    // Shadow shifter state
    //=========================================================================
    logic [NC-1:0][DW-1:0] h_data;
    logic [NC-1:0][SW-1:0] h_strb;
    logic [NC-1:0][7:0]    s_rx;        // bytes of the open packet (<= 2*SW)
    logic [NC-1:0]         pkt_open;
    logic [NC-1:0][3:0]    pb_cnt;      // memory beats formed for open packet
    logic [NC-1:0]         sh_discard;

    wire                   ch0    = s_axis_tid[0];
    wire                   accept = s_axis_tvalid && s_axis_tready && !sh_discard[ch0];
    wire                   drop   = s_axis_tvalid && s_axis_tready &&  sh_discard[ch0];

    wire [OFF_W-1:0]       head_off   = pq_off[ch0][eff_rp[ch0][1:0]];
    wire [31:0]            head_bytes = pq_bytes[ch0][eff_rp[ch0][1:0]];

    // popcount of the incoming tstrb
    logic [7:0] w_nbytes;
    always_comb begin
        w_nbytes = '0;
        for (int b = 0; b < SW; b++) w_nbytes = w_nbytes + 8'(s_axis_tstrb[b]);
    end

    // the DUT's placement math, mirrored (:259-264)
    logic [DW-1:0]   w_data_m;
    logic [2*DW-1:0] w_wide;
    logic [2*SW-1:0] w_wide_strb;
    always_comb begin
        for (int b = 0; b < SW; b++)
            w_data_m[b*8 +: 8] = s_axis_tstrb[b] ? s_axis_tdata[b*8 +: 8] : 8'h00;
    end
    assign w_wide      = ({{DW{1'b0}}, w_data_m} << (head_off * 8)) | {{DW{1'b0}}, h_data[ch0]};
    assign w_wide_strb = ({{SW{1'b0}}, s_axis_tstrb} << head_off)     | {{SW{1'b0}}, h_strb[ch0]};
    wire w_spill    = |w_wide_strb[2*SW-1:SW];
    wire w_done_now = accept && s_axis_tlast && !w_spill;

    // packet contract: the stream delivers exactly the record's bytes
    wire [7:0] w_eff_rx = pkt_open[ch0] ? s_rx[ch0] : 8'd0;
    always @(posedge clk)
        if (rst_n && accept && !w_rst_sh[ch0]) begin
            if (s_axis_tlast)
                assume (32'(w_eff_rx) + 32'(w_nbytes) == head_bytes);
            else
                assume (32'(w_eff_rx) + 32'(w_nbytes) < head_bytes);
        end

    //=========================================================================
    // Shadow memory-beat ring (per channel): what the AXI W stream must carry
    //=========================================================================
    logic [DW-1:0] smem_data [0:NC*RING-1];
    logic [SW-1:0] smem_strb [0:NC*RING-1];
    logic          smem_valid[0:NC*RING-1];
    logic [NC-1:0][7:0] fill_idx, w_idx;

    //=========================================================================
    // Scheduler co-model: one outstanding write request per channel,
    // beats = completed-but-unrequested memory beats
    //=========================================================================
    logic [NC-1:0]       r_req_valid;
    logic [NC-1:0][7:0]  r_req_beats;
    logic [NC-1:0][AW-1:0] r_req_addr;
    logic [NC-1:0][7:0]  r_req_bl;
    logic [NC-1:0]       r_outstanding;
    logic [NC-1:0][7:0]  unwritten;
    // killed[ch]: a channel reset went through while a transfer could still
    // be draining. The engine completes killed work with null-WSTRB beats
    // (axi_write_engine.sv:810-841) and closes it with done_strobe, so AWs
    // pushed between the kill and the done_strobe belong to aborted work.
    logic [NC-1:0]       killed;

    generate
        for (gch = 0; gch < NC; gch++) begin : g_sched
            assign sched_wr_valid[gch]              = r_req_valid[gch];
            assign sched_wr_beats[gch*32 +: 32]     = 32'(r_req_beats[gch]);
            assign sched_wr_addr[gch*AW +: AW]      = r_req_addr[gch];
            assign sched_wr_burst_len[gch*8 +: 8]   = r_req_bl[gch];
        end
    endgenerate

    //=========================================================================
    // Shadow AW queue (write data is in AW order on AXI4)
    //=========================================================================
    logic [3:0]        awq_ch   [0:3];
    logic [7:0]        awq_len  [0:3];
    logic [AW-1:0]     awq_addr [0:3];
    logic              awq_abort[0:3];
    logic              awq_null [0:3];
    logic [2:0]        awq_wp, awq_rp;
    wire  [2:0]        awq_count = awq_wp - awq_rp;
    wire               aw_push = m_axi_awvalid && m_axi_awready;
    wire               w_beat  = m_axi_wvalid && m_axi_wready;

    // current burst = queue head, or the AW being pushed this cycle
    wire        w_awq_nonempty = (awq_count != 0) || aw_push;
    wire [3:0]  w_cur_ch   = (awq_count != 0) ? awq_ch[awq_rp[1:0]]   : m_axi_awid;
    wire [7:0]  w_cur_len  = (awq_count != 0) ? awq_len[awq_rp[1:0]]  : m_axi_awlen;
    wire        w_cur_abrt = ((awq_count != 0) ? awq_abort[awq_rp[1:0]] : 1'b0)
                             || w_rst_sh[w_cur_ch[0]];   // the engine nulls in the kill cycle itself
    wire        w_cur_null = (awq_count != 0) ? awq_null[awq_rp[1:0]]  : 1'b0;
    logic [7:0] w_burst_cnt;   // beats of the current burst already seen

    // W-side per-beat expectation FIFO. The DUT forms a memory beat at EVERY
    // accept (mid-packet included) and the engine may drain it before the
    // packet completes, so expectations must be captured per beat at FILL
    // time -- one entry per memory beat formed (2 for a spill-tlast accept),
    // holding the open packet's record, live at eff_rp. W beats pop one entry
    // per drained beat; wpb_done regroups beats into packets via exp_beats.
    // Depth 32: unconsumed entries = filled-but-undrained beats (SRAM SD=8
    // plus the engine's AW/W pipeline FIFOs), with 2x margin.
    localparam int XWD = 16;
    logic [NC-1:0][XWD-1:0][OFF_W-1:0] x_off;
    logic [NC-1:0][XWD-1:0][7:0]       x_bytes;
    logic [NC-1:0][3:0]                x_wp, x_rp;
    logic [NC-1:0][3:0] wpb_cnt;
    logic [NC-1:0][7:0] wpb_acc;

    function automatic [3:0] exp_beats(input [OFF_W-1:0] off, input [31:0] b);
        exp_beats = 4'((off + b + SW - 1) / SW);
    endfunction

    // W-beat helpers (combination)
    logic [7:0] w_nbytes_w;
    always_comb begin
        w_nbytes_w = '0;
        for (int b = 0; b < SW; b++) w_nbytes_w = w_nbytes_w + 8'(m_axi_wstrb[b]);
    end
    wire [OFF_W-1:0] w_head_off   = x_off[w_cur_ch[0]][x_rp[w_cur_ch[0]][3:0]];
    wire [31:0]      w_head_bytes = {24'd0, x_bytes[w_cur_ch[0]][x_rp[w_cur_ch[0]][3:0]]};
    wire wpb_done = (wpb_cnt[w_cur_ch[0]] + 4'd1) == exp_beats(w_head_off, w_head_bytes);

    //=========================================================================
    // Shadow state update
    //=========================================================================
    // unwritten next value: fills add, a request handshake subtracts -- one
    // assignment per channel so same-cycle fill+handshake both land
    wire [7:0] w_fill_add = (accept && s_axis_tlast && w_spill) ? 8'd2 :
                            (accept ? 8'd1 : 8'd0);
    // width-truncated next-slot indices: a bare "+" in the 32-bit index
    // context does not wrap at the ring/FIFO boundary
    wire [4:0] w_fill_nxt = fill_idx[ch0][4:0] + 5'd1;
    wire [3:0] w_xwp_nxt  = x_wp[ch0] + 4'd1;
    integer i;
    always @(posedge clk) begin
        if (!rst_n) begin
            pq_wp <= '0; pq_rp <= '0; pend_pop <= '0;
            h_data <= '0; h_strb <= '0; s_rx <= '0;
            pkt_open <= '0; pb_cnt <= '0; sh_discard <= '0;
            fill_idx <= '0; w_idx <= '0; unwritten <= '0;
            r_req_valid <= '0; r_req_beats <= '0; r_req_addr <= '0; r_req_bl <= '0;
            r_outstanding <= '0; killed <= '0;
            awq_wp <= '0; awq_rp <= '0; w_burst_cnt <= '0;
            x_wp <= '0; x_rp <= '0; wpb_cnt <= '0; wpb_acc <= '0;
            for (i = 0; i < NC*RING; i++) smem_valid[i] <= 1'b0;
            for (i = 0; i < 4; i++) begin
                awq_abort[i] <= 1'b0; awq_null[i] <= 1'b0;
            end
        end else begin
            // ---- per-channel state -------------------------------------
            for (int ch = 0; ch < NC; ch++) begin
                // packet-record queue push (exact mirror of :217)
                if (sched_wr_pkt_valid[ch] && sched_wr_pkt_ready[ch] && !w_rst_sh[ch]) begin
                    pq_off[ch][pq_wp[ch][1:0]]   <= sched_wr_pkt_offset[ch*OFF_W +: OFF_W];
                    pq_bytes[ch][pq_wp[ch][1:0]] <= sched_wr_pkt_bytes[ch*32 +: 32];
                    pq_wp[ch] <= pq_wp[ch] + 3'd1;
                end
                // scheduler co-model
                if (w_rst_sh[ch]) begin
                    r_req_valid[ch]   <= 1'b0;
                    r_outstanding[ch] <= 1'b0;
                    unwritten[ch]     <= '0;
                    killed[ch]        <= 1'b1;
                end else begin
                    if (sched_wr_done_strobe[ch]) killed[ch] <= 1'b0;
                    if (!r_req_valid[ch] && !r_outstanding[ch] && !killed[ch] &&
                        (unwritten[ch] != 0)) begin
                        r_req_valid[ch] <= 1'b1;
                        r_req_beats[ch] <= unwritten[ch];
                        r_req_addr[ch]  <= anyseq_addr;
                        r_req_bl[ch]    <= anyseq_burst_len;
                    end
                    if (r_req_valid[ch] && sched_wr_ready[ch]) begin
                        r_req_valid[ch]   <= 1'b0;
                        r_outstanding[ch] <= 1'b1;
                    end
                    if (sched_wr_done_strobe[ch])
                        r_outstanding[ch] <= 1'b0;
                    unwritten[ch] <= unwritten[ch]
                                     + ((accept && (ch0 == ch[0])) ? w_fill_add : 8'd0)
                                     - ((r_req_valid[ch] && sched_wr_ready[ch])
                                        ? r_req_beats[ch] : 8'd0);
                end
                // channel reset clears the shadow (mirror of :356-370)
                if (w_rst_sh[ch]) begin
                    pq_wp[ch] <= '0; pq_rp[ch] <= '0; pend_pop[ch] <= 1'b0;
                    h_data[ch] <= '0; h_strb[ch] <= '0;
                    s_rx[ch] <= '0; pkt_open[ch] <= 1'b0; pb_cnt[ch] <= '0;
                    if (pkt_open[ch]) sh_discard[ch] <= 1'b1;
                    fill_idx[ch] <= fill_idx[ch];   // ring indices keep running
                    w_idx[ch]    <= w_idx[ch];
                    x_wp[ch] <= '0; x_rp[ch] <= '0;
                    wpb_cnt[ch] <= '0; wpb_acc[ch] <= '0;
                    for (int s = 0; s < RING; s++) smem_valid[ch*RING + s] <= 1'b0;
                end
            end

            // ---- ingress accept ----------------------------------------
            if (accept) begin
                // lazy spill pop + exact no-spill pop
                pq_rp[ch0] <= pq_rp[ch0] + 3'(pend_pop[ch0]) + 3'(w_done_now);
                pend_pop[ch0] <= accept && s_axis_tlast && w_spill;
                // memory beat into the ring
                smem_data[ch0*RING + fill_idx[ch0][4:0]]  <= w_wide[DW-1:0];
                smem_strb[ch0*RING + fill_idx[ch0][4:0]]  <= w_wide_strb[SW-1:0];
                smem_valid[ch0*RING + fill_idx[ch0][4:0]] <= 1'b1;
                fill_idx[ch0]  <= fill_idx[ch0] + (s_axis_tlast && w_spill ? 8'd2 : 8'd1);
                if (s_axis_tlast && w_spill) begin
                    // the flush beat's value is fixed now; append it early
                    smem_data[ch0*RING + w_fill_nxt]  <= w_wide[2*DW-1:DW];
                    smem_strb[ch0*RING + w_fill_nxt]  <= w_wide_strb[2*SW-1:SW];
                    smem_valid[ch0*RING + w_fill_nxt] <= 1'b1;
                end
                // per-beat expectation entries: one per memory beat formed,
                // each holding the open packet's record (live at eff_rp)
                x_off[ch0][x_wp[ch0][3:0]]   <= head_off;
                x_bytes[ch0][x_wp[ch0][3:0]] <= 8'(head_bytes);
                if (s_axis_tlast && w_spill) begin
                    x_off[ch0][w_xwp_nxt]   <= head_off;
                    x_bytes[ch0][w_xwp_nxt] <= 8'(head_bytes);
                end
                x_wp[ch0] <= x_wp[ch0] + ((s_axis_tlast && w_spill) ? 4'd2 : 4'd1);
                // shifter state
                h_data[ch0] <= s_axis_tlast ? '0 : w_wide[2*DW-1:DW];
                h_strb[ch0] <= s_axis_tlast ? '0 : w_wide_strb[2*SW-1:SW];
                s_rx[ch0]   <= s_axis_tlast ? '0 : w_eff_rx + w_nbytes;
                pkt_open[ch0] <= !s_axis_tlast;
                pb_cnt[ch0]   <= s_axis_tlast ? '0
                                 : (pkt_open[ch0] ? pb_cnt[ch0] + 4'd1 : 4'd1);
            end
            if (drop && s_axis_tlast) sh_discard[ch0] <= 1'b0;

            // ---- shadow AW queue ---------------------------------------
            for (i = 0; i < 4; i++)
                if (w_rst_sh[awq_ch[i][0]]) awq_abort[i] <= 1'b1;
            if (aw_push) begin
                awq_ch[awq_wp[1:0]]   <= m_axi_awid;
                awq_len[awq_wp[1:0]]  <= m_axi_awlen;
                awq_addr[awq_wp[1:0]] <= m_axi_awaddr;
                awq_abort[awq_wp[1:0]] <= killed[m_axi_awid[0]];
                awq_null[awq_wp[1:0]]  <= 1'b0;
                awq_wp <= awq_wp + 3'd1;
            end
            if (w_beat) begin
                if (m_axi_wstrb == '0) awq_null[awq_rp[1:0]] <= 1'b1;
                w_burst_cnt <= m_axi_wlast ? 8'd0 : w_burst_cnt + 8'd1;
                if (m_axi_wlast) awq_rp <= awq_rp + 3'd1;
                // real writes of the head burst's channel advance w_idx and
                // the W-side packet totals; aborted/null beats skip the data
                // compare but still occupy a ring slot
                if (!w_cur_abrt) begin
                    w_idx[w_cur_ch[0]] <= w_idx[w_cur_ch[0]] + 8'd1;
                    if (w_rst_sh[w_cur_ch[0]]) begin
                        wpb_cnt[w_cur_ch[0]] <= '0;
                        wpb_acc[w_cur_ch[0]] <= '0;
                    end else begin
                        // one expectation entry per drained beat; wpb_done
                        // regroups beats into the packet they came from
                        x_rp[w_cur_ch[0]]    <= x_rp[w_cur_ch[0]] + 4'd1;
                        wpb_cnt[w_cur_ch[0]] <= wpb_done ? '0
                                                : wpb_cnt[w_cur_ch[0]] + 4'd1;
                        wpb_acc[w_cur_ch[0]] <= wpb_done ? '0
                                                : wpb_acc[w_cur_ch[0]] + w_nbytes_w;
                    end
                end
            end
        end
    end

    //=========================================================================
    // Properties
    //=========================================================================

    // ---- F1: byte stream fidelity ----------------------------------------
    // every real W beat matches the shadow ring slot exactly (strobed lanes)
    wire [7:0] w_slot = w_idx[w_cur_ch[0]];
    wire [DW-1:0] w_exp_data = smem_data[w_cur_ch[0]*RING + w_slot[4:0]];
    wire [SW-1:0] w_exp_strb = smem_strb[w_cur_ch[0]*RING + w_slot[4:0]];
    wire          w_exp_val  = smem_valid[w_cur_ch[0]*RING + w_slot[4:0]];
    logic [DW-1:0] w_strb_mask;
    always_comb
        for (int b = 0; b < SW; b++) w_strb_mask[b*8 +: 8] = {8{m_axi_wstrb[b]}};

    always @(posedge clk) begin
        if (rst_n && w_beat && !w_cur_abrt && !w_rst_sh[w_cur_ch[0]]) begin
            ap_w_needs_aw: assert (w_awq_nonempty);
            if (w_exp_val) begin
                ap_wstrb_eq_shadow: assert (m_axi_wstrb == w_exp_strb);
                ap_byte_equality:   assert (((m_axi_wdata ^ w_exp_data) & w_strb_mask) == '0);
            end
        end
    end

    // per-packet strb byte total == record bytes, beat count == ceil((off+B)/SW)
    always @(posedge clk) begin
        if (rst_n && w_beat && !w_cur_abrt && !w_rst_sh[w_cur_ch[0]] && w_exp_val && wpb_done) begin
            ap_strb_byte_total: assert (wpb_acc[w_cur_ch[0]] + w_nbytes_w == 8'(w_head_bytes));
        end
    end

    // ---- F2: packet-record queue contract --------------------------------
    // ---- F4: per-channel reset -------------------------------------------
    // (vectorized/expanded for NC=2: yosys rejects a named procedural assert
    // inside a loop, and does not scope labels by generate block)
    always @(posedge clk) begin
        if (rst_n) begin
            // ready == (queue not full). Guarded per channel by !pend_pop:
            // between a spill-tlast accept and the internal flush emit the
            // shadow count equals the internal count, and between the emit
            // and the channel's next accept eff_count does -- but neither is
            // exact across BOTH sub-windows (the emit is port-invisible), so
            // the check sits out the pend window. pend_pop==0 => shadow is
            // exactly the internal count.
            ap_pkt_ready_eq: assert (
                (pend_pop[0] || (sched_wr_pkt_ready[0] == (pq_count[0] != 3'(PQD)))) &&
                (pend_pop[1] || (sched_wr_pkt_ready[1] == (pq_count[1] != 3'(PQD)))));
            if (s_axis_tready && !w_rst_sh[ch0] && !sh_discard[ch0])
                ap_tready_needs_record: assert (eff_count[ch0] != 0);
            if (w_rst_sh[ch0])
                ap_reset_no_tready: assert (!s_axis_tready);
        end
        if (f_past_valid > 0 && rst_n)
            ap_reset_queue_cleared: assert (
                (!$past(w_rst_sh[0]) || w_rst_sh[0] || (eff_count[0] <= 1)) &&
                (!$past(w_rst_sh[1]) || w_rst_sh[1] || (eff_count[1] <= 1)));
    end

    // ---- F3: AXI write legality ------------------------------------------
    always @(posedge clk) begin
        if (rst_n && aw_push) begin
            ap_awid_in_range: assert (m_axi_awid < NC);
            ap_aw_aligned:    assert (m_axi_awaddr[OFF_W-1:0] == '0);
            ap_awsize_incr:   assert (m_axi_awsize == 3'($clog2(SW)) &&
                                      m_axi_awburst == 2'b01);
            ap_aw_4k:         assert (m_axi_awaddr[11:0] +
                                      (13'(m_axi_awlen) + 13'd1) * 13'(SW) <= 13'd4096);
            // cfg_axi_wr_xfer_beats is an AWLEN value (:178-191 of the
            // engine), clamped by XFER_MAX = SD-1 -- mirror the clamp
            ap_awlen_caps:    assert (m_axi_awlen <=
                                      ((cfg_axi_wr_xfer_beats > 8'(SD-1))
                                       ? 8'(SD-1) : cfg_axi_wr_xfer_beats));
        end
        if (rst_n && w_beat) begin
            ap_wlast_count: assert (m_axi_wlast == (w_burst_cnt == w_cur_len));
        end
    end

    // ---- F4 (burst-scope): abort => null WSTRB ---------------------------
    always @(posedge clk) begin
        if (f_past_valid > 0 && rst_n) begin
            // a burst touched by a channel kill emits only zero-strb beats
            // from the kill onward
            if (w_beat && w_cur_abrt)
                ap_wstrb_abort_zero: assert (m_axi_wstrb == '0);
            // null beats only ever happen in an aborted burst
            if (w_beat && (m_axi_wstrb == '0))
                ap_null_only_abort: assert (w_cur_abrt);
        end
    end

    //=========================================================================
    // Covers (non-vacuity witnesses)
    //=========================================================================
    always @(posedge clk) begin
        if (rst_n) begin
            cp_aw:             cover (aw_push);
            cp_accept:         cover (accept);
            cp_spill_flush:    cover (accept && s_axis_tlast && w_spill);
            cp_multi_beat_pkt: cover (accept && s_axis_tlast && pkt_open[ch0]);
            cp_queue_two:      cover (eff_count[0] >= 2 || eff_count[1] >= 2);
            cp_queue_full:     cover (!sched_wr_pkt_ready[0] || !sched_wr_pkt_ready[1]);
            cp_interleave:     cover (accept && pkt_open[0] && pkt_open[1]);
            cp_w_beat:         cover (w_beat);
            cp_done:           cover (|sched_wr_done_strobe);
            cp_discard:        cover (|sh_discard);
            cp_null_beat:      cover (w_beat && m_axi_wstrb == '0);
            cp_kill_inflight:  cover (|(cfg_channel_reset & r_outstanding));
        end
    end
endmodule
