// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// Module: monbus_tally_axil
// Purpose: Drop-in replacement for the monitor-trace capture SRAM (debug_sram)
//          in the STREAM monitor harness. Presents the monbus record-ingest
//          write surface the sdpram did, but instead of storing beats it
//          tabulates them, and exposes a SEPARATE dedicated config/readback
//          AXIL port for the host:
//
//            s_axil     (record ingest, W only): the monbus group's RAW 3-beat
//                       records -> beat reassembler -> monbus_pkt_tally.
//            cfg_s_axil (host, R + W): R = read tally bins/counts;
//                       W = load the profile legal-set CAM (PROFILE_MODE) at
//                       offset 0x200 + idx*4, or clear it at 0x100.
//
//          Splitting config onto its own AXIL slave keeps the sweeping-address
//          record stream from ever colliding with host config writes (the two
//          share no channel), and gives each tally memory a clean host port.
//
//          Raw-record layout on the ingest write stream (USE_COMPRESSION == 0):
//            beat0 = {tag[3:0]=0, source_ts[59:0]}
//            beat1 = packet[127:64]
//            beat2 = packet[63:0]
//          A mod-3 counter on accepted W beats reconstructs each 128-bit packet;
//          on beat2 it is pushed to the tally. The ingest write ADDRESS is
//          ignored (a tally is order-, not address-addressed on its input).
//
//          cfg_s_axil config write map (PROFILE_MODE only):
//            0x100      PROFILE_CLEAR   W  any write invalidates all CAM entries
//            0x200+i*4  PROFILE_ENTRY   W  wdata = legal key for dense bin i
//                                          {agent[15:0],proto[3:0],type[3:0],event[7:0]}
//          cfg_s_axil reads return the tally bin count at araddr>>2.
//
// Subsystem: NexysA7/stream_characterization (monitor flow)
// Author: sean galloway

`timescale 1ns / 1ps
`include "reset_defs.svh"

module monbus_tally_axil
    import monitor_common_pkg::*;
#(
    parameter int ADDR_WIDTH       = 32,
    parameter int DATA_WIDTH       = 64,   // AXIL data width (monbus beats are 64b)
    parameter int TALLY_COUNT_WIDTH = 32,
    parameter int TALLY_CACHE_DEPTH = 32,
    parameter int TALLY_ADDR_BITS   = 16,
    parameter int TALLY_NUM_LATCH   = 4,
    // Profile mode: agent-resolved dense tally. Set PROFILE_MODE=1 and
    // TALLY_ADDR_BITS >= clog2(N_PROFILE+1). The legal set is loaded over
    // cfg_s_axil (host), never the record-ingest write channel.
    parameter int PROFILE_MODE      = 0,
    parameter int N_PROFILE         = 64,
    parameter int PROF_IDX_W        = (N_PROFILE > 1) ? $clog2(N_PROFILE) : 1,
    parameter int PROF_KEY_W        = 32
) (
    input  logic                    aclk,
    input  logic                    aresetn,

    // === Record-ingest AXIL slave (write only): monbus group RAW records ===
    input  logic [ADDR_WIDTH-1:0]   s_axil_awaddr,
    input  logic [2:0]              s_axil_awprot,
    input  logic                    s_axil_awvalid,
    output logic                    s_axil_awready,
    input  logic [DATA_WIDTH-1:0]   s_axil_wdata,
    input  logic [DATA_WIDTH/8-1:0] s_axil_wstrb,
    input  logic                    s_axil_wvalid,
    output logic                    s_axil_wready,
    output logic [1:0]              s_axil_bresp,
    output logic                    s_axil_bvalid,
    input  logic                    s_axil_bready,
    // Read channel present for surface compatibility but inert (ingest is
    // write-only; the host reads bins via cfg_s_axil).
    input  logic [ADDR_WIDTH-1:0]   s_axil_araddr,
    input  logic [2:0]              s_axil_arprot,
    input  logic                    s_axil_arvalid,
    output logic                    s_axil_arready,
    output logic [DATA_WIDTH-1:0]   s_axil_rdata,
    output logic [1:0]              s_axil_rresp,
    output logic                    s_axil_rvalid,
    input  logic                    s_axil_rready,

    // === Dedicated host config/readback AXIL slave (R = bins, W = config) ===
    input  logic [ADDR_WIDTH-1:0]   cfg_awaddr,
    input  logic [2:0]              cfg_awprot,
    input  logic                    cfg_awvalid,
    output logic                    cfg_awready,
    input  logic [DATA_WIDTH-1:0]   cfg_wdata,
    input  logic [DATA_WIDTH/8-1:0] cfg_wstrb,
    input  logic                    cfg_wvalid,
    output logic                    cfg_wready,
    output logic [1:0]              cfg_bresp,
    output logic                    cfg_bvalid,
    input  logic                    cfg_bready,
    input  logic [ADDR_WIDTH-1:0]   cfg_araddr,
    input  logic [2:0]              cfg_arprot,
    input  logic                    cfg_arvalid,
    output logic                    cfg_arready,
    output logic [DATA_WIDTH-1:0]   cfg_rdata,
    output logic [1:0]              cfg_rresp,
    output logic                    cfg_rvalid,
    input  logic                    cfg_rready,

    // Tally window control (from the harness CSR)
    input  logic                    tally_freeze,
    input  logic                    tally_flush,
    output logic                    tally_flush_busy,
    input  logic                    tally_clear
);

    localparam int LFILL_W = $clog2(TALLY_NUM_LATCH + 1);

    // ------------------------------------------------------------------------
    // Record-ingest write channel: accept AW (address ignored) and W beats;
    // reassemble every 3 beats into a 128-bit packet and push to the tally.
    // ------------------------------------------------------------------------
    logic        w_w_hs, w_tally_in_ready;
    logic [1:0]  r_beat;                          // 3-beat record counter (0,1,2)
    assign s_axil_awready = 1'b1;                 // always accept addresses
    // Beats 0/1 are consumed immediately; the record-completing beat 2 is
    // stalled until the tally can accept, so no count is ever dropped.
    assign s_axil_wready  = (r_beat == 2'd2) ? w_tally_in_ready : 1'b1;
    assign w_w_hs  = s_axil_wvalid & s_axil_wready;

    // B response: one per (aw,w) pair.
    logic r_bvalid;
    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) r_bvalid <= 1'b0;
        else if (w_w_hs)            r_bvalid <= 1'b1;
        else if (s_axil_bready)     r_bvalid <= 1'b0;
    )
    assign s_axil_bvalid = r_bvalid;
    assign s_axil_bresp  = 2'b00;

    // Ingest read channel is inert (host reads bins via cfg_s_axil).
    assign s_axil_arready = 1'b1;
    assign s_axil_rvalid  = 1'b0;
    assign s_axil_rdata   = '0;
    assign s_axil_rresp   = 2'b00;

    // 3-beat record reassembler.
    logic [63:0]                r_pkt_hi;    // packet[127:64] from beat1
    logic [MONBUS_TS_WIDTH-1:0] r_ts;        // ts from beat0
    logic                       w_pkt_valid; // pulse: full packet ready
    monitor_packet_t            w_pkt;
    monbus_timestamp_t          w_pkt_ts;

    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_beat   <= 2'd0;
            r_pkt_hi <= '0;
            r_ts     <= '0;
        end else if (tally_clear) begin
            r_beat   <= 2'd0;            // re-align records on a clear
        end else if (w_w_hs) begin
            case (r_beat)
                2'd0: begin r_ts <= s_axil_wdata[MONBUS_TS_WIDTH-1:0]; r_beat <= 2'd1; end
                2'd1: begin r_pkt_hi <= s_axil_wdata;                  r_beat <= 2'd2; end
                default:                                              r_beat <= 2'd0;
            endcase
        end
    )
    assign w_pkt_valid = w_w_hs & (r_beat == 2'd2);
    assign w_pkt       = {r_pkt_hi, s_axil_wdata};   // {pkt_hi, pkt_lo}
    assign w_pkt_ts    = r_ts;

    // ------------------------------------------------------------------------
    // cfg_s_axil WRITE: config. AW+W accepted together; addr decodes the op.
    //   0x100      -> PROFILE_CLEAR   (invalidate all CAM entries)
    //   0x200+i*4  -> PROFILE_ENTRY i (wdata = legal key, valid = 1)
    // ------------------------------------------------------------------------
    logic                    r_cfg_bvalid;
    logic                    w_cfg_wr;
    assign w_cfg_wr    = cfg_awvalid & cfg_wvalid & ~r_cfg_bvalid;
    assign cfg_awready = w_cfg_wr;
    assign cfg_wready  = w_cfg_wr;

    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) r_cfg_bvalid <= 1'b0;
        else if (w_cfg_wr)          r_cfg_bvalid <= 1'b1;
        else if (cfg_bready)        r_cfg_bvalid <= 1'b0;
    )
    assign cfg_bvalid = r_cfg_bvalid;
    assign cfg_bresp  = 2'b00;

    // Decode (byte-offset windows within the cfg slave).
    logic w_cfg_is_profile, w_cfg_is_clear;
    assign w_cfg_is_profile = (cfg_awaddr[13:8] == 6'h02);   // 0x200-0x2FF
    assign w_cfg_is_clear   = (cfg_awaddr[13:8] == 6'h01);   // 0x100-0x1FF

    logic                    w_profile_clear;
    logic                    w_profile_we;
    logic [PROF_IDX_W-1:0]   w_profile_waddr;
    logic                    w_profile_wvalid;
    logic [PROF_KEY_W-1:0]   w_profile_wkey;
    assign w_profile_clear  = w_cfg_wr & w_cfg_is_clear;
    assign w_profile_we     = w_cfg_wr & w_cfg_is_profile;
    assign w_profile_waddr  = cfg_awaddr[PROF_IDX_W+1:2];
    assign w_profile_wvalid = 1'b1;
    assign w_profile_wkey   = cfg_wdata[PROF_KEY_W-1:0];

    // ------------------------------------------------------------------------
    // cfg_s_axil READ: araddr>>2 selects a bin; rdata returns the count.
    // ------------------------------------------------------------------------
    logic [TALLY_ADDR_BITS-1:0]   r_cfg_rd_addr;
    logic                         r_cfg_rvalid;
    logic [TALLY_COUNT_WIDTH-1:0] w_rd_count;

    assign cfg_arready = ~r_cfg_rvalid;
    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_cfg_rd_addr <= '0;
            r_cfg_rvalid  <= 1'b0;
        end else begin
            if (cfg_arvalid & cfg_arready)
                r_cfg_rd_addr <= cfg_araddr[TALLY_ADDR_BITS+1:2];
            if (cfg_arvalid & cfg_arready)          r_cfg_rvalid <= 1'b1;
            else if (cfg_rvalid & cfg_rready)       r_cfg_rvalid <= 1'b0;
        end
    )
    assign cfg_rvalid = r_cfg_rvalid;
    assign cfg_rresp  = 2'b00;
    assign cfg_rdata  = {{(DATA_WIDTH-TALLY_COUNT_WIDTH){1'b0}}, w_rd_count};

    // ------------------------------------------------------------------------
    // The tally. Profile ports driven by the cfg-write decode above.
    // ------------------------------------------------------------------------
    monbus_pkt_tally #(
        .PKT_WIDTH(128), .TS_WIDTH(64),
        .COUNT_WIDTH(TALLY_COUNT_WIDTH), .CACHE_DEPTH(TALLY_CACHE_DEPTH),
        .NUM_LATCH(TALLY_NUM_LATCH), .ADDR_BITS(TALLY_ADDR_BITS),
        .PROFILE_MODE(PROFILE_MODE), .N_PROFILE(N_PROFILE)
    ) u_tally (
        .clk(aclk), .rst_n(aresetn),
        .in_valid(w_pkt_valid), .in_ready(w_tally_in_ready),
        .in_packet(w_pkt), .in_ts(w_pkt_ts),
        .i_freeze(tally_freeze), .i_flush(tally_flush),
        .o_flush_busy(tally_flush_busy), .i_clear(tally_clear),
        .rd_addr(r_cfg_rd_addr), .rd_count(w_rd_count),
        .i_watch_arm(1'b0), .i_watch_pkttype_mask(16'h0),
        .latch_sel('0), .latch_valid(), .latch_packet(), .latch_ts(),
        .latch_fill(),
        .profile_clear(w_profile_clear), .profile_we(w_profile_we),
        .profile_waddr(w_profile_waddr), .profile_wvalid(w_profile_wvalid),
        .profile_wkey(w_profile_wkey)
    );

endmodule : monbus_tally_axil
