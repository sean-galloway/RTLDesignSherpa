// SPDX-License-Identifier: MIT
// Formal harness for rapids macro/src_data_path_axis (TASK-022, DIR 2).
//
// Port-level only: the DUT is a black box on its AXI4 read-master, AXIS
// master, and scheduler ports. NO hierarchical references: yosys 0.62 does
// not resolve them reliably in this flow (implicit wires merge badly with
// flattened names -- measured 2026-10-03; DIR 1 used none either). The one
// place the source side's data boundary is internal -- which R beats LAND
// in the SRAM vs are dropped on a channel reset -- is closed by an exact
// co-model of the engine's discard logic (axi_read_engine.sv:236-295,
// 597-600), all of it port-observable, rather than by assuming the engine's
// behavior. The egress shifter is checked in closed form against the
// observed output stream (see "Shadow egress model" below).
//
// Invariant families (plan: docs/superpowers/plans/2026-10-03-rapids-task-022-dir2-src-proof.md):
//   F1  egress shifter hold/spill: m_axis beats vs the shadow shifter fed by
//       the shadow SRAM ring (byte/strb equality, byte totals)
//   F2  packet-record queue contract + pop gating
//   F3  AXI read legality: arid/aralignment/arsize/arburst, 4KB split, arlen
//       caps, rlast placement (via the shadow AR FIFO)
//   F4  per-channel reset: no tvalid window, queues cleared, R beats of a
//       reset channel discarded
// (Tasks 3-5 land the properties; this file is the Task 2 core.)
//
// Solver: smtbmc bitwuzla (z3 dies on the SRAM arrays -- DIR 1, measured).
module formal_src_data_path_axis (
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
    localparam int OFF_W = (SW > 1) ? $clog2(SW) : 1;   // 3
    localparam int CIW = (NC > 1) ? $clog2(NC) : 1;     // 1
    localparam int PQD = 4;              // DUT PQ_DEPTH (src_data_path_axis:235)
    localparam int PQS = 8;              // shadow STORAGE depth: the DUT pops
                                         // its record at a packet's EMIT while
                                         // the shadow pops at the final beat's
                                         // HANDSHAKE, so during that skew the
                                         // DUT (its count one lower) still
                                         // grants ready and a legal push lands
                                         // on a shadow-full queue -- with only
                                         // PQD slots the write pointer wraps
                                         // onto the occupied head slot and
                                         // overwrites the in-flight packet's
                                         // record (CEX 2026-10-03,
                                         // ap_strb_eq_shadow_1b @ step 13).
                                         // Max shadow occupancy is DUT depth
                                         // (4) + skew (1) = 5, so 8 slots make
                                         // the wrap onto an un-popped slot
                                         // unreachable. PQD itself is unchanged:
                                         // ap_pq_ready_eq still models the
                                         // DUT's own depth-4 queue exactly.
    localparam int RING = 32;            // shadow memory-beat ring per channel
                                         // (bound: filled-not-drained <= SD + fill/drain pipe)
    localparam int ARQ = 4;              // shadow AR FIFO (>= AR_MAX_OUTSTANDING=2 + margin)

    // ---- DUT config (quasi-static, assumed below) ------------------------
    (* anyseq *) logic [7:0]         cfg_axi_rd_xfer_beats;
    (* anyseq *) logic [7:0]         cfg_drain_size;
    (* anyseq *) logic [NC-1:0]      cfg_channel_reset;

    // ---- scheduler interface: the co-model below drives the request side
    //      (level protocol -- the source macro has no sched_rd_ready); the
    //      packet-record side stays anyseq (the records are the egress spec)
    logic [NC-1:0]      sched_rd_valid;
    logic [NC-1:0][AW-1:0] sched_rd_addr;
    logic [NC-1:0][31:0] sched_rd_beats;
    (* anyseq *) logic [NC-1:0]      sched_rd_pkt_valid;
    logic [NC-1:0]                  sched_rd_pkt_ready;
    (* anyseq *) logic [NC-1:0][31:0] sched_rd_pkt_bytes;
    (* anyseq *) logic [NC-1:0][OFF_W-1:0] sched_rd_pkt_offset;

    // ---- AXIS master (DUT drives) ----------------------------------------
    logic [DW-1:0]      m_axis_tdata;
    logic [SW-1:0]      m_axis_tstrb;
    logic               m_axis_tlast;
    logic [3:0]         m_axis_tid;
    logic [3:0]         m_axis_tdest;
    logic [0:0]         m_axis_tuser;
    logic               m_axis_tvalid;
    (* anyseq *) logic  m_axis_tready;   // the consumer is a free environment

    // ---- AXI4 read master -------------------------------------------------
    logic [IW-1:0]      m_axi_arid;
    logic [AW-1:0]      m_axi_araddr;
    logic [7:0]         m_axi_arlen;
    logic [2:0]         m_axi_arsize;
    logic [1:0]         m_axi_arburst;
    logic               m_axi_arvalid;
    logic               m_axi_arready;
    (* anyseq *) logic [IW-1:0]  m_axi_rid;
    (* anyseq *) logic [DW-1:0]  m_axi_rdata;
    (* anyseq *) logic [1:0]     m_axi_rresp;
    (* anyseq *) logic           m_axi_rlast;
    (* anyseq *) logic           m_axi_rvalid;
    logic               m_axi_rready;

    // ---- DUT debug --------------------------------------------------------
    logic [NC-1:0]      dbg_rd_all_complete;
    logic [31:0]        dbg_r_beats_rcvd;
    logic [31:0]        dbg_sram_writes;
    logic [NC-1:0]      dbg_arb_request;
    logic [NC-1:0]      dbg_sram_bridge_pending;
    logic [NC-1:0]      dbg_sram_bridge_out_valid;
    logic [31:0]        dbg_axis_beats_sent;
    logic [31:0]        dbg_axis_packets_sent;
    logic [NC-1:0]      sched_rd_done_strobe;
    logic [NC-1:0][31:0] sched_rd_beats_done;
    logic [NC-1:0]      sched_rd_error;

    //=========================================================================
    // DUT
    //=========================================================================
    src_data_path_axis #(
        .NUM_CHANNELS       (NC),
        .ADDR_WIDTH         (AW),
        .DATA_WIDTH         (DW),
        .AXI_ID_WIDTH       (IW),
        .SRAM_DEPTH         (SD),
        .SEG_COUNT_WIDTH    (SCW),
        .PIPELINE           (1),
        .AR_MAX_OUTSTANDING (2),     // DIR 1 geometry: small engine queues
        .AXIS_ID_WIDTH      (4),
        .AXIS_DEST_WIDTH    (4),
        .AXIS_USER_WIDTH    (1)
    ) dut (
        .clk, .rst_n,
        .cfg_axi_rd_xfer_beats, .cfg_drain_size, .cfg_channel_reset,
        .sched_rd_valid, .sched_rd_addr, .sched_rd_beats,
        .sched_rd_pkt_valid, .sched_rd_pkt_ready, .sched_rd_pkt_bytes,
        .sched_rd_pkt_offset,
        .sched_rd_done_strobe, .sched_rd_beats_done, .sched_rd_error,
        .m_axis_tdata, .m_axis_tstrb, .m_axis_tlast, .m_axis_tid,
        .m_axis_tdest, .m_axis_tuser, .m_axis_tvalid, .m_axis_tready,
        .m_axi_arid, .m_axi_araddr, .m_axi_arlen, .m_axi_arsize,
        .m_axi_arburst, .m_axi_arvalid, .m_axi_arready,
        .m_axi_rid, .m_axi_rdata, .m_axi_rresp, .m_axi_rlast,
        .m_axi_rvalid, .m_axi_rready,
        .dbg_rd_all_complete, .dbg_r_beats_rcvd, .dbg_sram_writes,
        .dbg_arb_request, .dbg_sram_bridge_pending, .dbg_sram_bridge_out_valid,
        .dbg_axis_beats_sent, .dbg_axis_packets_sent
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
    // Shadow per-channel reset (mirrors DUT r_rst_d1/w_rst :224-230)
    //=========================================================================
    logic [NC-1:0] r_rst_d1_sh;
    wire  [NC-1:0] w_rst_sh = cfg_channel_reset | r_rst_d1_sh;
    always @(posedge clk) begin
        if (!rst_n) r_rst_d1_sh <= '0;
        else        r_rst_d1_sh <= cfg_channel_reset;
    end

    //=========================================================================
    // Cooperative AXI read slave
    //=========================================================================
    // Always ready for AR. R is constrained to a shadow memory image so the
    // DUT cannot fabricate read data: an address returns the same beat for
    // every AR that covers it. Window: 4 KiB (512 beats), araddr[31:12] == 0.
    assign m_axi_arready = 1'b1;

    // Shadow memory image, 4 KiB window as a FLAT anyseq vector: yosys does
    // not expand an anyseq array that has no procedural write port ("does
    // not map to an unexpanded memory"), and a variable-index read of a flat
    // anyseq vector needs no memory semantics. Same consistency contract: an
    // address returns the same beat for every AR that covers it.
    (* anyseq *) logic [512*DW-1:0] shadow_mem;

    // shadow AR FIFO: in-order R stream (AXI4 R has no interleaving)
    logic [IW-1:0]  arq_id   [0:ARQ-1];
    logic [AW-1:0]  arq_addr [0:ARQ-1];
    logic [7:0]     arq_len  [0:ARQ-1];
    logic [ARQ-1:0] arq_vld;
    logic [2:0]     arq_wp, arq_rp;
    wire  [2:0]     arq_count = arq_wp - arq_rp;
    wire            ar_push = m_axi_arvalid && m_axi_arready;
    wire            ar_pop;
    // head entry = queue head, or the AR being pushed this cycle
    wire            arq_nonempty = (arq_count != 0) || ar_push;
    wire [AW-1:0]   arq_h_addr  = (arq_count != 0) ? arq_addr[arq_rp[1:0]]  : m_axi_araddr;
    wire [7:0]      arq_h_len   = (arq_count != 0) ? arq_len[arq_rp[1:0]]   : m_axi_arlen;
    wire [IW-1:0]   arq_h_id    = (arq_count != 0) ? arq_id[arq_rp[1:0]]    : m_axi_arid;

    // per-head beat counter: beats of the head burst already returned
    logic [7:0] rbeat_cnt;
    wire [8:0]  w_head_addr = 9'((arq_h_addr[11:3] + 9'(rbeat_cnt)) & 9'h1FF);

    assign ar_pop = m_axi_rvalid && m_axi_rready && m_axi_rlast;

    always @(posedge clk) begin
        if (!rst_n) begin
            arq_wp <= '0; arq_rp <= '0; arq_vld <= '0; rbeat_cnt <= '0;
        end else begin
            if (ar_push) begin
                arq_id[arq_wp[1:0]]   <= m_axi_arid;
                arq_addr[arq_wp[1:0]] <= m_axi_araddr;
                arq_len[arq_wp[1:0]]  <= m_axi_arlen;
                arq_wp <= arq_wp + 3'd1;
                if (arq_count == 0)
                    arq_vld[arq_wp[1:0]] <= 1'b1;
            end
            if (ar_pop) begin
                arq_vld[arq_rp[1:0]] <= 1'b0;
                arq_rp <= arq_rp + 3'd1;
                rbeat_cnt <= '0;
            end else if (m_axi_rvalid && m_axi_rready) begin
                rbeat_cnt <= rbeat_cnt + 8'd1;
            end
            // NOTE: no kill handling here. A reset channel's in-flight ARs
            // still return R beats (the engine accepts and DROPS them,
            // axi_read_engine.sv:597-600), so the shadow AR FIFO keeps
            // serving their rdata/rlast until each burst's RLAST pops it.
        end
    end

    // R constraints: only when an in-order head exists, data from the shadow
    // image at the head's beat address, id/resp/last per the head contract.
    wire arq_head_vld = arq_vld[arq_rp[1:0]] || (arq_count == 0 && ar_push);
    always @(posedge clk) begin
        if (rst_n) begin
            assume (m_axi_rvalid == arq_head_vld);
            if (arq_head_vld) begin
                assume (m_axi_rid    == arq_h_id);
                assume (m_axi_rresp  == 2'b00);
                assume (m_axi_rdata  == shadow_mem[w_head_addr*DW +: DW]);
                assume (m_axi_rlast  == (rbeat_cnt == arq_h_len));
            end
        end
    end

    // R stability under backpressure (the harness owns rvalid)
    always @(posedge clk)
        if (f_past_valid > 0 && rst_n && $past(rst_n) &&
            $past(m_axi_rvalid && !m_axi_rready)) begin
            assume (m_axi_rvalid);
            assume ($stable(m_axi_rdata));
            assume ($stable(m_axi_rid));
            assume ($stable(m_axi_rlast));
            assume ($stable(m_axi_rresp));
        end

    //=========================================================================
    // Engine discard co-model (axi_read_engine.sv:236-295, 597-600).
    // The R->SRAM path is a DIRECT passthrough: a beat lands in the SRAM
    // exactly when m_axi_rvalid && m_axi_rready && !w_rd_discard, with
    //   w_rd_discard = r_rd_flush[rid] | cfg_channel_reset[rid]
    //   r_rd_flush  <= cfg_channel_reset | (r_rd_flush & outstanding!=0)
    //   outstanding[ch]: +1 on AR handshake for ch, -1 on RLAST for ch,
    //   both-same-cycle unchanged, cleared only by aresetn.
    // All of that is port-observable, so the shadow mirrors it exactly
    // instead of reaching two levels into the DUT (yosys resolves only
    // one-level hierarchical references -- measured 2026-10-03).
    //=========================================================================
    logic [NC-1:0]       sh_flush;
    logic [NC-1:0][7:0]  sh_osc;
    logic [NC-1:0]       w_incr, w_decr;
    always_comb begin
        for (int ch = 0; ch < NC; ch++) begin
            w_incr[ch] = m_axi_arvalid && m_axi_arready && (m_axi_arid[NC-1:0] == ch[NC-1:0]);
            w_decr[ch] = m_axi_rvalid && m_axi_rready && m_axi_rlast
                      && (m_axi_rid[NC-1:0] == ch[NC-1:0]);
        end
    end
    always @(posedge clk) begin
        if (!rst_n) begin
            sh_flush <= '0;
            sh_osc   <= '0;
        end else begin
            for (int ch = 0; ch < NC; ch++) begin
                sh_flush[ch] <= cfg_channel_reset[ch]
                              | (sh_flush[ch] && (sh_osc[ch] != 8'd0));
                case ({w_incr[ch], w_decr[ch]})
                    2'b10: sh_osc[ch] <= sh_osc[ch] + 8'd1;
                    2'b01: sh_osc[ch] <= sh_osc[ch] - 8'd1;
                    default: ;
                endcase
            end
        end
    end
    wire w_discard_sh = sh_flush[m_axi_rid[NC-1:0]] | cfg_channel_reset[m_axi_rid[NC-1:0]];

    //=========================================================================
    // Shadow memory-beat ring (per channel): one entry per R beat that LANDS
    // in the SRAM. Rewound on channel reset, same as the DUT's SRAM pointers
    // (src_sram_controller r_ch_rst_n): post-kill fills overwrite the
    // orphaned tail in the same order.
    //=========================================================================
    logic [DW-1:0] smem_data [0:NC*RING-1];
    logic          smem_valid[0:NC*RING-1];
    logic [NC-1:0][7:0] fill_idx;
    wire land_beat = m_axi_rvalid && m_axi_rready && !w_discard_sh;
    wire land_ch   = m_axi_rid[0];

    integer i;
    always @(posedge clk) begin
        if (!rst_n) begin
            fill_idx <= '0;
            for (i = 0; i < NC*RING; i++) smem_valid[i] <= 1'b0;
        end else begin
            if (land_beat) begin
                smem_data[land_ch*RING + fill_idx[land_ch][4:0]]  <= m_axi_rdata;
                smem_valid[land_ch*RING + fill_idx[land_ch][4:0]] <= 1'b1;
                fill_idx[land_ch] <= fill_idx[land_ch] + 8'd1;
            end
            for (int ch = 0; ch < NC; ch++)
                if (w_rst_sh[ch]) fill_idx[ch] <= '0;
        end
    end

    //=========================================================================
    // Environment assumptions (skeleton set; Tasks 3-5 extend)
    //=========================================================================
    // quasi-static config
    always @(posedge clk)
        if (f_past_valid > 0 && rst_n && $past(rst_n)) begin
            assume ($stable(cfg_axi_rd_xfer_beats));
            assume ($stable(cfg_drain_size));
        end

    // small address window (4 KiB -> the 512-beat shadow image)
    always @(posedge clk)
        if (rst_n && m_axi_arvalid)
            assume (m_axi_araddr[31:12] == 20'd0);

    // packet-record handshake stability + documented record range
    always @(posedge clk)
        if (rst_n) begin
            for (int ch = 0; ch < NC; ch++) begin
                if (sched_rd_pkt_valid[ch]) begin
                    assume (sched_rd_pkt_bytes[ch] >= 32'd1);
                    assume (sched_rd_pkt_bytes[ch] <= 32'(2*SW));
                    assume (!w_rst_sh[ch]);
                end
                if (f_past_valid > 0 && $past(rst_n) &&
                    $past(sched_rd_pkt_valid[ch] && !sched_rd_pkt_ready[ch])) begin
                    assume (sched_rd_pkt_valid[ch]);
                    assume ($stable(sched_rd_pkt_bytes[ch]));
                    assume ($stable(sched_rd_pkt_offset[ch]));
                end
            end
        end

    // AXIS consumer: tready anyseq is legal; payload stability is the DUT's
    // obligation (asserted in Task 4). No assumption needed here.

    // completing-beat stimulus assumption: while a killed channel's
    // completing beat is still pending, the scheduler does not re-arm the
    // channel (a new record would be ambiguous with the completing beat at
    // the port). Stimulus-side, not a DUT-hazard assumption.
    always @(posedge clk)
        if (rst_n && s_flt_valid)
            assume (!sched_rd_pkt_valid[s_flt_ch]);

    // consumer-drain assumption: a beat presented for a channel in its reset
    // window is accepted within the window. The DUT handles an arbitrary
    // stall correctly (the beat completes whenever tready comes); this
    // narrows the PROOF ENVIRONMENT so a packet's FIRST beat need not be
    // verified against state the reset legitimately destroyed (no emit
    // visibility at the port). Compare the 8-cycle kill spacing -- a
    // documented environment bound, not a DUT-hazard assumption.
    always @(posedge clk)
        if (rst_n && m_axis_tvalid && w_rst_sh[m_axis_tid[CIW-1:0]])
            assume (m_axis_tready);

    // kill spacing: per-channel resets at least 8 cycles apart (bounds the
    // orphaned shadow slots a bounded BMC can produce), same as DIR 1.
    logic [NC-1:0][3:0] r_kill_cool;
    always @(posedge clk) begin
        if (!rst_n) r_kill_cool <= '0;
        else begin
            for (int ch = 0; ch < NC; ch++) begin
                if (cfg_channel_reset[ch])     r_kill_cool[ch] <= 4'd8;
                else if (r_kill_cool[ch] != 0) r_kill_cool[ch] <= r_kill_cool[ch] - 4'd1;
            end
        end
    end
    always @(posedge clk)
        if (rst_n)
            for (int ch = 0; ch < NC; ch++)
                if (r_kill_cool[ch] != 0) assume (!cfg_channel_reset[ch]);

    //=========================================================================
    // Scheduler co-model (level protocol: no sched_rd_ready on the source
    // side). Descriptor-driven, NOT pool-driven: reads are requested BEFORE
    // their beats land (a pool-of-landed-beats model deadlocks -- measured
    // 2026-10-03: no AR ever fires). A per-channel descriptor {addr, beats}
    // is posted by anyseq when the channel is idle; the engine re-samples
    // sched_rd_beats at EVERY AR and transfers min(left, 4k-cap) beats
    // (axi_read_engine.sv:426-427); the shadow decrements `left` by each
    // issued AR at the handshake (the lagged done_strobe would be one cycle
    // stale -- the engine can issue back-to-back ARs).
    //=========================================================================
    (* anyseq *) logic [NC-1:0]         anyseq_desc_post;   // post when idle/done
    (* anyseq *) logic [NC-1:0][AW-1:0] anyseq_desc_addr;
    (* anyseq *) logic [NC-1:0][7:0]    anyseq_desc_beats;
    logic [NC-1:0]         r_desc_valid;
    logic [NC-1:0][AW-1:0] r_desc_addr;
    logic [NC-1:0][7:0]    r_desc_left;    // beats not yet issued
    genvar gch;

    generate
        for (gch = 0; gch < NC; gch++) begin : g_req
            assign sched_rd_valid[gch] = r_desc_valid[gch];
            assign sched_rd_beats[gch] = 32'(r_desc_left[gch]);
            assign sched_rd_addr[gch]  = r_desc_addr[gch];
        end
    endgenerate

    // a descriptor of 0 beats would make the engine compute ARLEN = 0-1
    // (sched_rd_beats-1 underflow, axi_read_engine.sv:426-427): real
    // descriptors always carry at least one beat
    always @(posedge clk)
        if (rst_n)
            for (int ch = 0; ch < NC; ch++)
                if (anyseq_desc_post[ch])
                    assume (anyseq_desc_beats[ch] != 8'd0);

    always @(posedge clk) begin
        if (!rst_n) begin
            r_desc_valid <= '0;
            r_desc_addr  <= '0;
            r_desc_left  <= '0;
        end else begin
            for (int ch = 0; ch < NC; ch++) begin
                if (w_rst_sh[ch]) begin
                    r_desc_valid[ch] <= 1'b0;
                    r_desc_left[ch]  <= '0;
                end else begin
                    if (ar_push && (m_axi_arid[1:0] == 2'(ch)))
                        r_desc_left[ch] <= r_desc_left[ch] - (m_axi_arlen + 8'd1);
                    // descriptor completes when its last beat is issued; a new
                    // one may be posted the same cycle (back-to-back)
                    if (ar_push && (m_axi_arid[1:0] == 2'(ch)) &&
                        (r_desc_left[ch] == (m_axi_arlen + 8'd1))) begin
                        if (anyseq_desc_post[ch]) begin
                            r_desc_valid[ch] <= 1'b1;
                            r_desc_left[ch]  <= anyseq_desc_beats[ch];
                            r_desc_addr[ch]  <= anyseq_desc_addr[ch];
                        end else begin
                            r_desc_valid[ch] <= 1'b0;
                        end
                    end else if (!r_desc_valid[ch] && anyseq_desc_post[ch]) begin
                        r_desc_valid[ch] <= 1'b1;
                        r_desc_left[ch]  <= anyseq_desc_beats[ch];
                        r_desc_addr[ch]  <= anyseq_desc_addr[ch];
                    end
                    // address walks the descriptor, one AR's bytes per AR,
                    // wrapped into the 4 KiB window (the engine caps AT the
                    // boundary, so a crossing increment is the wrap case)
                    if (ar_push && (m_axi_arid[1:0] == 2'(ch)))
                        r_desc_addr[ch] <= (r_desc_addr[ch]
                                            + ((32'(m_axi_arlen) + 32'd1) << OFF_W))
                                           & 32'h0000_0FFF;
                end
            end
        end
    end

    //=========================================================================
    // Shadow packet-record queue (exact push on the port handshake; pop on
    // the shadow's own packet-done; reset last so it wins)
    //=========================================================================
    logic [NC-1:0][PQS-1:0][OFF_W-1:0] pq_off;
    logic [NC-1:0][PQS-1:0][31:0]      pq_bytes;
    logic [NC-1:0][2:0]                pq_wp, pq_rp;

    wire [NC-1:0][2:0] pq_count;
    generate
        for (gch = 0; gch < NC; gch++) begin : g_pq
            assign pq_count[gch] = pq_wp[gch] - pq_rp[gch];
        end
    endgenerate

    //=========================================================================
    // Shadow egress model -- closed form, port-driven.
    //
    // The output stream is checked beat by beat at the m_axis handshake;
    // channel attribution rides on tid. Per channel, packets are sequential
    // (a new one starts at the first beat after the previous packet's
    // tlast), so the shadow keeps per-channel packet state advanced ONLY by
    // observed output beats.
    //
    // Expected beat i of a packet (off, bytes) -- closed form of the DUT's
    // sequential shifter (src_data_path_axis:293-337). At this geometry
    // bytes <= 2*SW so a packet has at most mem_total = exp_beats(off,bytes)
    // <= 3 memory beats (ring rd .. rd+mem_total-1) and K = ceil(bytes/SW)
    // <= 2 emitted beats:
    //   primed = (off != 0) && (mem_total > 1)   -- pop 0 fills the hold only
    //   c_i    = i + (primed ? 1 : 0)            -- pop that produces emit i
    //   c_i < mem_total: pop-emit. data = hold | beat<<.. with hold = the
    //     bytes above the offset of the PREVIOUS pop's beat (0 when c_i==0)
    //   c_i == mem_total: flush emit (final beat, off != 0): data = the
    //     hold left by the last pop
    //   nbytes_i = min(bytes - SW*i, SW); strb = contiguous nbytes_i;
    //   last_i = (SW*(i+1) >= bytes)
    //=========================================================================
    logic [NC-1:0]         s_pkt_act;      // a packet is open for the channel
    logic [NC-1:0][OFF_W-1:0] s_pk_off;
    logic [NC-1:0][31:0]   s_pk_bytes;
    logic [NC-1:0][3:0]    s_emit_i;       // emitted beats seen this packet
    logic [NC-1:0][7:0]    s_rd_idx;       // ring drain base (per channel)
    logic [NC-1:0][7:0]    s_rpb_acc;      // emitted byte accumulator

    // completing-beat snapshot: the DUT does not clear r_out on a channel
    // reset ("a beat already in the output register still completes",
    // src_data_path_axis:401), so a NON-LAST beat in flight at kill time
    // handshakes AFTER the reset. Its expectation is captured at the
    // pre-reset handshake; the environment is assumed not to re-arm the
    // channel (no new record) until that beat has handshaked -- a scheduler
    // stimulus assumption, not a DUT-hazard assumption.
    logic            s_flt_valid;
    logic [DW-1:0]   s_flt_data;
    logic [SW-1:0]   s_flt_strb;
    logic            s_flt_last;
    logic [CIW-1:0]  s_flt_ch;

    function automatic [3:0] exp_beats(input [OFF_W-1:0] off, input [31:0] b);
        exp_beats = 4'((off + b + SW - 1) / SW);
    endfunction

    function automatic [7:0] popcnt(input [SW-1:0] s);
        popcnt = '0;
        for (int b = 0; b < SW; b++) popcnt = popcnt + 8'(s[b]);
    endfunction

    // expected-beat computation for (off, bytes, emit index i, ring base rd)
    function automatic [DW-1:0] exp_data(
        input [OFF_W-1:0] off, input [31:0] bytes, input [3:0] i,
        input [DW-1:0] b0, input [DW-1:0] b1, input [DW-1:0] b2);
        logic [3:0]  mt;
        logic [3:0]  c;
        logic [DW-1:0] hold;
        logic [DW-1:0] beat;
        begin
            mt   = exp_beats(off, bytes);
            c    = i + ((off != '0 && mt > 1) ? 4'd1 : 4'd0);
            beat = (c == 0) ? b0 : (c == 1) ? b1 : b2;
            hold = '0;
            if (off != '0 && c != 0)
                hold = ((c == 1) ? b0 : b1) >> (off * 8);
            if (c < mt)
                exp_data = (off != '0 && c != 0)
                           ? (hold | (beat << ((SW - 32'(off)) * 8)))
                           : (beat >> (off * 8));
            else    // flush: the hold left by the last pop
                exp_data = ((mt == 1) ? b0 : (mt == 2) ? b1 : b2) >> (off * 8);
        end
    endfunction

    function automatic [7:0] exp_nbytes(input [31:0] bytes, input [3:0] i);
        exp_nbytes = (bytes - 32'(SW)*32'(i) >= 32'(SW)) ? 8'(SW)
                     : 8'(bytes - 32'(SW)*32'(i));
    endfunction

    // ring beats at the packet base of channel ch
    wire [CIW-1:0] m_ch = m_axis_tid[CIW-1:0];
    wire [DW-1:0]  r_b0 = smem_data[m_ch*RING + s_rd_idx[m_ch] + 8'd0];
    wire [DW-1:0]  r_b1 = smem_data[m_ch*RING + s_rd_idx[m_ch] + 8'd1];
    wire [DW-1:0]  r_b2 = smem_data[m_ch*RING + s_rd_idx[m_ch] + 8'd2];

    // current packet expectation (channel = current output tid)
    wire [3:0]     s_cmt   = exp_beats(s_pk_off[m_ch], s_pk_bytes[m_ch]);
    wire [DW-1:0]  s_xdata = exp_data(s_pk_off[m_ch], s_pk_bytes[m_ch],
                                      s_emit_i[m_ch], r_b0, r_b1, r_b2);
    wire [7:0]     s_xnb   = exp_nbytes(s_pk_bytes[m_ch], s_emit_i[m_ch]);
    wire [SW-1:0]  s_xstrb = (s_xnb >= 8'(SW)) ? {SW{1'b1}} : ~({SW{1'b1}} << s_xnb);
    wire           s_xlast = (32'(SW)*(32'(s_emit_i[m_ch]) + 32'd1) >= s_pk_bytes[m_ch]);
    // the next-beat prediction used for the completing-beat snapshot
    wire [3:0]     s_nmt   = s_cmt;
    wire [DW-1:0]  s_ndata = exp_data(s_pk_off[m_ch], s_pk_bytes[m_ch],
                                      s_emit_i[m_ch] + 4'd1, r_b0, r_b1, r_b2);
    wire [7:0]     s_nnb   = exp_nbytes(s_pk_bytes[m_ch], s_emit_i[m_ch] + 4'd1);
    wire [SW-1:0]  s_nstrb = (s_nnb >= 8'(SW)) ? {SW{1'b1}} : ~({SW{1'b1}} << s_nnb);
    wire           s_nlast = (32'(SW)*(32'(s_emit_i[m_ch]) + 32'd2) >= s_pk_bytes[m_ch]);

    // NEW-packet expectation: at a first beat the s_pk_* registers still
    // hold the previous packet, so the expectation must come from the
    // record-queue HEAD (the record this beat opens)
    wire [OFF_W-1:0] s_h_off   = pq_off[m_ch][pq_rp[m_ch][2:0]];
    wire [31:0]      s_h_bytes = pq_bytes[m_ch][pq_rp[m_ch][2:0]];
    wire [3:0]       s_h_cmt   = exp_beats(s_h_off, s_h_bytes);
    wire [DW-1:0]    s_h_xdata = exp_data(s_h_off, s_h_bytes, 4'd0, r_b0, r_b1, r_b2);
    wire [7:0]       s_h_xnb   = exp_nbytes(s_h_bytes, 4'd0);
    wire [SW-1:0]    s_h_xstrb = (s_h_xnb >= 8'(SW)) ? {SW{1'b1}} : ~({SW{1'b1}} << s_h_xnb);
    wire             s_h_xlast = (32'(SW) >= s_h_bytes);

    wire m_hand = m_axis_tvalid && m_axis_tready;

    //=========================================================================
    // Shadow packet bookkeeping (advanced only by observed output beats)
    //=========================================================================
    always @(posedge clk) begin
        if (!rst_n) begin
            s_pkt_act <= '0; s_pk_off <= '0; s_pk_bytes <= '0;
            s_emit_i  <= '0; s_rd_idx <= '0; s_rpb_acc <= '0;
            s_flt_valid <= 1'b0; s_flt_data <= '0; s_flt_strb <= '0;
            s_flt_last <= 1'b0; s_flt_ch <= '0;
            pq_wp <= '0; pq_rp <= '0;
        end else begin
            // record push (exact port handshake mirror of :362-367)
            for (int ch = 0; ch < NC; ch++) begin
                if (sched_rd_pkt_valid[ch] && sched_rd_pkt_ready[ch] && !w_rst_sh[ch]) begin
                    pq_off[ch][pq_wp[ch][2:0]]   <= sched_rd_pkt_offset[ch];
                    pq_bytes[ch][pq_wp[ch][2:0]] <= sched_rd_pkt_bytes[ch];
                    pq_wp[ch] <= pq_wp[ch] + 3'd1;
                end
            end

            if (m_hand) begin
                if (s_pkt_act[m_ch]) begin
                    // mid-packet beat: the byte-total accounting runs; the
                    // final beat also retires the packet (ring base advances
                    // by mem_total, the record pops, state clears)
                    if (s_xlast) begin
                        s_rpb_acc[m_ch] <= '0;
                        s_rd_idx[m_ch]  <= s_rd_idx[m_ch] + 8'(s_cmt);
                        pq_rp[m_ch]     <= pq_rp[m_ch] + 3'd1;
                        s_pkt_act[m_ch] <= 1'b0;
                        s_emit_i[m_ch]  <= '0;
                        s_flt_valid     <= 1'b0;   // no completing beat pending
                    end else begin
                        s_rpb_acc[m_ch] <= s_rpb_acc[m_ch] + popcnt(m_axis_tstrb);
                        s_emit_i[m_ch]  <= s_emit_i[m_ch] + 4'd1;
                        // a non-final beat may be the one sitting in r_out
                        // when a kill arrives: capture its successor
                        s_flt_valid <= 1'b1;
                        s_flt_data  <= s_ndata;
                        s_flt_strb  <= s_nstrb;
                        s_flt_last  <= s_nlast;
                        s_flt_ch    <= m_ch;
                    end
                end else if (s_flt_valid && (s_flt_ch == m_ch)) begin
                    // the completing beat of a killed packet
                    s_flt_valid <= 1'b0;
                end else begin
                    // first beat of a new packet (the record must exist --
                    // ap_out_needs_rec asserts it); the completing snapshot
                    // for the OTHER channel is untouched. s_emit_i is the
                    // index of the NEXT expected emit: the first beat IS
                    // emit 0, so the next is emit 1 -- a 0 here leaves every
                    // mid-packet beat checked against the closed form one
                    // emit low (CEX 2026-10-03 #2: a 12-byte off=0 packet's
                    // second beat predicted pop 0 / 8 lanes while the DUT
                    // emitted pop 1 / 4 lanes, ap_strb_eq_shadow @ step 13)
                    s_pk_off[m_ch]  <= pq_off[m_ch][pq_rp[m_ch][2:0]];
                    s_pk_bytes[m_ch] <= pq_bytes[m_ch][pq_rp[m_ch][2:0]];
                    s_emit_i[m_ch]  <= 4'd1;
                    if (!(s_flt_valid && (s_flt_ch == m_ch)))
                        s_flt_valid <= 1'b0;   // stale snapshot: no kill came
                    if (s_h_xlast) begin
                        // single-beat packet: retires on this very handshake
                        // (the DUT popped its record at emit, one cycle
                        // before the shadow would in the open-packet path)
                        s_pkt_act[m_ch] <= 1'b0;
                        pq_rp[m_ch]     <= pq_rp[m_ch] + 3'd1;
                        s_rd_idx[m_ch]  <= s_rd_idx[m_ch] + 8'(s_h_cmt);
                        s_rpb_acc[m_ch] <= '0;
                    end else begin
                        s_pkt_act[m_ch] <= 1'b1;
                        s_rpb_acc[m_ch] <= popcnt(m_axis_tstrb);
                    end
                end
            end

            // channel reset last, so it wins: the record queue and the
            // open-packet state are cleared; the completing snapshot stays
            for (int ch = 0; ch < NC; ch++) begin
                if (w_rst_sh[ch]) begin
                    pq_wp[ch] <= '0; pq_rp[ch] <= '0;
                    s_pkt_act[ch] <= 1'b0;
                    s_emit_i[ch]  <= '0;
                    s_rd_idx[ch]  <= '0;
                    s_rpb_acc[ch] <= '0;
                end
            end
        end
    end

    //=========================================================================
    // F1: egress byte fidelity
    //=========================================================================
    logic [DW-1:0] m_strb_mask;
    always_comb
        for (int b = 0; b < SW; b++) m_strb_mask[b*8 +: 8] = {8{m_axis_tstrb[b]}};

    always @(posedge clk) begin
        if (rst_n && f_past_valid > 2 && m_hand) begin
            // a beat with no open packet and no completing snapshot is a new
            // packet: its record must exist in the shadow queue
            if (!s_pkt_act[m_ch] && !(s_flt_valid && (s_flt_ch == m_ch)))
                ap_out_needs_rec: assert (pq_count[m_ch] != 0);
            if (s_pkt_act[m_ch]) begin
                ap_byte_equality: assert (((m_axis_tdata ^ s_xdata) & m_strb_mask) == '0);
                ap_strb_eq_shadow: assert (m_axis_tstrb == s_xstrb &&
                                           m_axis_tlast == s_xlast);
                if (m_axis_tlast) begin
                    ap_byte_total: assert (32'(s_rpb_acc[m_ch])
                                           + 32'(popcnt(m_axis_tstrb)) == s_pk_bytes[m_ch]);
                end
            end else if (s_flt_valid && (s_flt_ch == m_ch)) begin
                ap_byte_equality_f: assert (((m_axis_tdata ^ s_flt_data) & m_strb_mask) == '0);
                ap_strb_eq_shadow_f: assert (m_axis_tstrb == s_flt_strb &&
                                             m_axis_tlast == s_flt_last);
            end else begin
                // new packet's first beat: payload equality rides on the
                // HEAD record's emit-0 expectation (the s_pk_* registers
                // still hold the previous packet here)
                ap_byte_equality_1b: assert (((m_axis_tdata ^ s_h_xdata) & m_strb_mask) == '0);
                ap_strb_eq_shadow_1b: assert (m_axis_tstrb == s_h_xstrb &&
                                              m_axis_tlast == s_h_xlast);
                if (s_h_xlast) begin
                    // single-beat packet: the whole byte budget is this beat
                    ap_byte_total_1b: assert (32'(popcnt(m_axis_tstrb)) == s_h_bytes);
                end
            end
        end
    end

    //=========================================================================
    // F3: AXI read legality (per-family labels -- the mutation battery
    // targets one family at a time)
    //=========================================================================
    // burst coverage helper: (arlen+1) beats starting at araddr stay inside
    // one 4 KB region (AXI4 A3.4.1)
    function automatic ar_in_4k(input [AW-1:0] addr, input [7:0] arlen);
        ar_in_4k = (32'(addr[11:0]) + ((32'(arlen) + 32'd1) << OFF_W)) <= 32'd4096;
    endfunction

    always @(posedge clk) begin
        if (rst_n && f_past_valid > 2 && m_axi_arvalid) begin
            ap_arid_in_range:  assert (m_axi_arid < IW'(NC));
            ap_ar_aligned:     assert (m_axi_araddr[OFF_W-1:0] == '0);
            ap_arsize_incr:    assert (m_axi_arsize == 3'($clog2(SW)) &&
                                       m_axi_arburst == 2'b01);
            ap_arlen_caps:     assert (m_axi_arlen <= cfg_axi_rd_xfer_beats);
            ap_ar_4k:          assert (ar_in_4k(m_axi_araddr, m_axi_arlen));
            // no AR for a channel in its reset/flush window, and never more
            // beats than the descriptor offers (the level-protocol contract)
            ap_ar_no_reset:    assert (!(cfg_channel_reset[m_axi_arid[NC-1:0]] ||
                                         sh_flush[m_axi_arid[NC-1:0]]));
            ap_ar_within_desc: assert (r_desc_left[m_axi_arid[NC-1:0]] >= (m_axi_arlen + 8'd1));
            // TEMP DEBUG: the co-model must never offer valid with 0 beats
            // left (the engine computes ARLEN = beats-1 with no zero guard);
            // a fail here is a co-model bug, not a DUT bug
            ap_dbg_no_zero_offer: assert (!dbg_zero_offer);
        end
    end

    logic dbg_zero_offer;
    always_comb begin
        dbg_zero_offer = 1'b0;
        for (int ch = 0; ch < NC; ch++)
            dbg_zero_offer |= sched_rd_valid[ch] && (r_desc_left[ch] == 8'd0);
    end

    //=========================================================================
    // F2: record-queue contract + AXIS master discipline
    //=========================================================================
    // the DUT's ready is exactly the shadow queue's non-fullness, adjusted
    // for the one-record skew while a packet's FINAL beat sits in the output
    // register: the DUT pops its record queue at emit time, the shadow at
    // the beat's handshake, so between the emit edge and the handshake edge
    // the DUT count is one lower (a mid-flight final beat: valid && tlast)
    logic rdy_eq_pred;
    always_comb begin
        rdy_eq_pred = 1'b1;
        for (int ch = 0; ch < NC; ch++) begin
            rdy_eq_pred &= (sched_rd_pkt_ready[ch] ==
                            ((pq_count[ch] - ((m_axis_tvalid && m_axis_tlast &&
                                               (m_axis_tid[CIW-1:0] == CIW'(ch))) ? 3'd1 : 3'd0)) < 3'(PQD)));
        end
    end

    always @(posedge clk) begin
        if (rst_n && f_past_valid > 2) begin
            // the DUT's ready is exactly the shadow queue's non-fullness
            // (both are fed by the same port pushes, so they cannot drift)
            ap_pq_ready_eq: assert (rdy_eq_pred);
            // AXIS master payload stability under backpressure (the DUT's
            // obligation, the mirror of the sink harness's s_axis assumption)
            if ($past(rst_n) && $past(m_axis_tvalid && !m_axis_tready)) begin
                ap_axis_stable: assert (m_axis_tvalid &&
                                        $stable(m_axis_tdata) && $stable(m_axis_tstrb) &&
                                        $stable(m_axis_tlast) && $stable(m_axis_tid));
            end
        end
    end

    wire [NC-1:0] pq_nonempty;
    wire [NC-1:0] osc_nonempty;
    generate
        for (gch = 0; gch < NC; gch++) begin : g_ne
            assign pq_nonempty[gch]  = (pq_count[gch] != 0);
            assign osc_nonempty[gch] = (sh_osc[gch] != 8'd0);
        end
    endgenerate

    //=========================================================================
    // F4: per-channel reset -- no new output during the window, queues cleared
    //=========================================================================
    // a channel's 2-cycle window (cfg | registered cfg) has just ended when
    // the registered term is still set and the combined term has dropped
    wire [NC-1:0] w_rst_ended = r_rst_d1_sh & ~w_rst_sh;
    logic rdy_after_rst;
    always_comb begin
        rdy_after_rst = 1'b1;
        for (int ch = 0; ch < NC; ch++)
            if (w_rst_ended[ch])
                rdy_after_rst &= sched_rd_pkt_ready[ch];
    end

    // registered window vector: the emit that loaded the currently-rising
    // beat happened last cycle for the CURRENT tid (r_out_ch is a load-time
    // value), so index the past window by the current tid, not a past one
    logic [NC-1:0] w_rst_sh_q;
    always @(posedge clk)
        if (!rst_n) w_rst_sh_q <= '0;
        else        w_rst_sh_q <= w_rst_sh;

    always @(posedge clk) begin
        if (rst_n && f_past_valid > 2) begin
            // no output EMITTED during the reset window. A beat PRESENTED
            // (valid) during the window was loaded the previous cycle --
            // r_out_valid rises one edge after w_emit -- so a valid that
            // rises while the window is up implies the emit was enabled
            // pre-window (the DUT gates w_pop and flush on w_rst). A rise
            // with the window already up last cycle is an in-window emit.
            if (m_axis_tvalid && w_rst_sh[m_axis_tid[CIW-1:0]] && !$past(m_axis_tvalid)) begin
                ap_reset_no_new_out: assert (!w_rst_sh_q[m_axis_tid[CIW-1:0]]);
            end
            // the record queue is cleared by the end of the window
            ap_reset_ready: assert (rdy_after_rst);
        end
    end

    //=========================================================================
    // Covers (F1/F3/F4 set; Task 5 adds cp_done)
    //=========================================================================
    wire s_pop_emit  = s_pkt_act[m_ch] && (s_emit_i[m_ch] + ((s_pk_off[m_ch] != '0 && s_cmt > 1) ? 4'd1 : 4'd0) < s_cmt);
    wire s_hold_used = s_pkt_act[m_ch] && (s_pk_off[m_ch] != '0)
                       && (s_emit_i[m_ch] + ((s_cmt > 1) ? 4'd1 : 4'd0) != 0);
    always @(posedge clk) begin
        if (rst_n) begin
            cp_ar:             cover (m_axi_arvalid && m_axi_arready);
            cp_t_beat:         cover (m_hand);
            cp_pop:            cover (m_hand && s_pop_emit);
            cp_hold_prime:     cover (m_hand && s_hold_used);
            cp_flush:          cover (m_hand && s_pkt_act[m_ch] &&
                                      (s_emit_i[m_ch] + ((s_pk_off[m_ch] != '0 && s_cmt > 1) ? 4'd1 : 4'd0) == s_cmt));
            cp_multi_beat_pkt: cover (m_hand && s_pk_bytes[m_ch] > 32'(SW));
            cp_queue_two:      cover (pq_count[0] >= 2 || pq_count[1] >= 2);
            cp_queue_full:     cover (!sched_rd_pkt_ready[0] || !sched_rd_pkt_ready[1]);
            cp_interleave:     cover (m_hand && s_pkt_act[0] && s_pkt_act[1]);
            cp_discard:        cover (|(cfg_channel_reset & (s_pkt_act | pq_nonempty)));
            cp_kill_inflight:  cover (|(cfg_channel_reset & osc_nonempty));
            cp_done:           cover (ar_push &&
                                      (r_desc_left[m_axi_arid[NC-1:0]] == (m_axi_arlen + 8'd1)));
        end
    end

    //=========================================================================
    // Properties (Tasks 4-5)
    //=========================================================================

endmodule
