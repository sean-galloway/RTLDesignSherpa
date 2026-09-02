// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// Module: monbus_tally_axil
// Purpose: Drop-in replacement for the monitor-trace capture SRAM (debug_sram)
//          in the STREAM monitor harness. Instead of storing beats it tabulates
//          them into a direct-mapped count SRAM (monbus_pkt_tally).
//
//          FOUR clean AXIL ports — two write, two read — with NO overloading
//          (each channel does exactly one job; the earlier design tied off a
//          read channel and jammed count-reads onto the config port, which bred
//          bugs):
//
//            WRITE ports
//              rec_*   record ingest : monbus group RAW 3-beat records -> beat
//                                      reassembler -> tally. Address ignored.
//              cfgw_*  config write  : program the legal-set CAM via registers
//                                      (0x100 CAM_CLEAR, 0x108 CAM_KEY,
//                                      0x110 CAM_LOAD={valid,index}).
//            READ ports
//              cnt_*   count read    : rdata = tally bin count at araddr>>2.
//              cfgr_*  config read   : rdata = tally config/status (identity,
//                                      profile mode, sizing) — a live readback,
//                                      never tied off.
//
//          Splitting ingest from config keeps the sweeping-address record
//          stream from ever colliding with host config, and splitting the two
//          read ports keeps count readback independent of config readback.
//
//          Raw-record layout on the ingest write stream (USE_COMPRESSION == 0):
//            beat0 = {tag[3:0]=0, source_ts[59:0]}
//            beat1 = packet[127:64]
//            beat2 = packet[63:0]
//          A mod-3 counter on accepted rec_w beats reconstructs each 128-bit
//          packet; on beat2 it is pushed to the tally.
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
    parameter int TALLY_ADDR_BITS   = 7,    // >= clog2(N_PROFILE+1)
    parameter int TALLY_NUM_LATCH   = 4,
    // The legal-set CAM ALWAYS routes packets to dense bins (agent-resolved);
    // the set is loaded over cfgw_* (host), never the record-ingest channel.
    parameter int N_PROFILE         = 64,
    parameter int PROF_IDX_W        = (N_PROFILE > 1) ? $clog2(N_PROFILE) : 1,
    parameter int PROF_KEY_W        = 32,
    parameter int LSEL_WIDTH        = (TALLY_NUM_LATCH > 1) ? $clog2(TALLY_NUM_LATCH) : 1,
    parameter int LFILL_WIDTH       = $clog2(TALLY_NUM_LATCH + 1)
) (
    input  logic                    aclk,
    input  logic                    aresetn,

    // === WRITE port 1: record ingest (AW/W/B only) ===
    input  logic [ADDR_WIDTH-1:0]   rec_awaddr,
    input  logic [2:0]              rec_awprot,
    input  logic                    rec_awvalid,
    output logic                    rec_awready,
    input  logic [DATA_WIDTH-1:0]   rec_wdata,
    input  logic [DATA_WIDTH/8-1:0] rec_wstrb,
    input  logic                    rec_wvalid,
    output logic                    rec_wready,
    output logic [1:0]              rec_bresp,
    output logic                    rec_bvalid,
    input  logic                    rec_bready,

    // === READ port 1: count / bin readback (AR/R only) ===
    input  logic [ADDR_WIDTH-1:0]   cnt_araddr,
    input  logic [2:0]              cnt_arprot,
    input  logic                    cnt_arvalid,
    output logic                    cnt_arready,
    output logic [DATA_WIDTH-1:0]   cnt_rdata,
    output logic [1:0]              cnt_rresp,
    output logic                    cnt_rvalid,
    input  logic                    cnt_rready,

    // === WRITE port 2: config (AW/W/B only) — profile CAM load/clear ===
    input  logic [ADDR_WIDTH-1:0]   cfgw_awaddr,
    input  logic [2:0]              cfgw_awprot,
    input  logic                    cfgw_awvalid,
    output logic                    cfgw_awready,
    input  logic [DATA_WIDTH-1:0]   cfgw_wdata,
    input  logic [DATA_WIDTH/8-1:0] cfgw_wstrb,
    input  logic                    cfgw_wvalid,
    output logic                    cfgw_wready,
    output logic [1:0]              cfgw_bresp,
    output logic                    cfgw_bvalid,
    input  logic                    cfgw_bready,

    // === READ port 2: config / status readback (AR/R only) ===
    input  logic [ADDR_WIDTH-1:0]   cfgr_araddr,
    input  logic [2:0]              cfgr_arprot,
    input  logic                    cfgr_arvalid,
    output logic                    cfgr_arready,
    output logic [DATA_WIDTH-1:0]   cfgr_rdata,
    output logic [1:0]              cfgr_rresp,
    output logic                    cfgr_rvalid,
    input  logic                    cfgr_rready,

    // Tally window control (from the harness CSR)
    input  logic                    tally_freeze,
    input  logic                    tally_flush,      // no-op (no cache); kept for compat
    output logic                    tally_flush_busy, // high while a clear walk runs
    input  logic                    tally_clear
);

    localparam int LFILL_W = $clog2(TALLY_NUM_LATCH + 1);

    // ------------------------------------------------------------------------
    // WRITE port 1 — record ingest: accept AW (address ignored) and W beats;
    // reassemble every 3 beats into a 128-bit packet and push to the tally.
    // ------------------------------------------------------------------------
    logic        w_w_hs, w_tally_in_ready;
    logic [1:0]  r_beat;                          // 3-beat record counter (0,1,2)
    assign rec_awready = 1'b1;                    // always accept addresses
    // Beats 0/1 are consumed immediately; the record-completing beat 2 is
    // stalled until the tally can accept, so no count is ever dropped.
    assign rec_wready  = (r_beat == 2'd2) ? w_tally_in_ready : 1'b1;
    assign w_w_hs      = rec_wvalid & rec_wready;

    // B response: one per (aw,w) pair.
    logic r_rec_bvalid;
    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) r_rec_bvalid <= 1'b0;
        else if (w_w_hs)            r_rec_bvalid <= 1'b1;
        else if (rec_bready)        r_rec_bvalid <= 1'b0;
    )
    assign rec_bvalid = r_rec_bvalid;
    assign rec_bresp  = 2'b00;

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
                2'd0: begin r_ts <= rec_wdata[MONBUS_TS_WIDTH-1:0]; r_beat <= 2'd1; end
                2'd1: begin r_pkt_hi <= rec_wdata;                  r_beat <= 2'd2; end
                default:                                            r_beat <= 2'd0;
            endcase
        end
    )
    assign w_pkt_valid = w_w_hs & (r_beat == 2'd2);
    assign w_pkt       = {r_pkt_hi, rec_wdata};   // {pkt_hi, pkt_lo}
    assign w_pkt_ts    = r_ts;

    // ------------------------------------------------------------------------
    // WRITE port 2 — config: AW and W accepted INDEPENDENTLY (the bridge may
    // present AW then wait for awready before W -- coupling them deadlocks). The
    // write fires once both have landed; the byte offset selects a register
    // (CAM_CLEAR / CAM_KEY / CAM_LOAD -- see the decode below).
    // ------------------------------------------------------------------------
    logic                    r_cfgw_bvalid;
    logic                    r_aw_done, r_w_done;
    logic [ADDR_WIDTH-1:0]   r_cfgw_awaddr;
    logic [DATA_WIDTH-1:0]   r_cfgw_wdata;
    logic                    w_cfgw_wr;
    assign cfgw_awready = ~r_aw_done;                 // accept a new AW when idle
    assign cfgw_wready  = ~r_w_done;                  // accept a new W  when idle
    assign w_cfgw_wr    = r_aw_done & r_w_done & ~r_cfgw_bvalid;

    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_aw_done <= 1'b0; r_w_done <= 1'b0; r_cfgw_bvalid <= 1'b0;
        end else begin
            if (cfgw_awvalid & cfgw_awready) begin r_cfgw_awaddr <= cfgw_awaddr; r_aw_done <= 1'b1; end
            if (cfgw_wvalid  & cfgw_wready)  begin r_cfgw_wdata  <= cfgw_wdata;  r_w_done  <= 1'b1; end
            if (w_cfgw_wr) begin
                r_aw_done <= 1'b0; r_w_done <= 1'b0; r_cfgw_bvalid <= 1'b1;
            end else if (cfgw_bready & r_cfgw_bvalid) begin
                r_cfgw_bvalid <= 1'b0;
            end
        end
    )
    assign cfgw_bvalid = r_cfgw_bvalid;
    assign cfgw_bresp  = 2'b00;

    // Register-based CAM programming (bus-width INDEPENDENT -- the entry index
    // comes from register DATA, not the address, so there is no 4/8-byte stride
    // or addr[2] upsizer hazard). Three registers, 8 bytes apart so each is its
    // own 64-bit word:
    //   0x100 CAM_CLEAR : any write invalidates all CAM entries
    //   0x108 CAM_KEY   : wdata[31:0] latched as the key to load next
    //   0x110 CAM_LOAD  : wdata[31]=valid, wdata[PROF_IDX_W-1:0]=index ->
    //                     load the latched CAM_KEY into entry[index]
    //   0x118 WATCH_CTRL: wdata[31]=arm, wdata[15:0]=pkt_type watch mask
    //   0x120 LATCH_SEL : which capture slot the read port returns
    localparam logic [11:0] REG_CAM_CLEAR  = 12'h100;
    localparam logic [11:0] REG_CAM_KEY    = 12'h108;
    localparam logic [11:0] REG_CAM_LOAD   = 12'h110;
    localparam logic [11:0] REG_WATCH_CTRL = 12'h118;
    localparam logic [11:0] REG_LATCH_SEL  = 12'h120;
    logic [11:0] w_cfg_off;
    assign w_cfg_off = r_cfgw_awaddr[11:0];

    logic w_is_key;
    assign w_is_key = w_cfgw_wr & (w_cfg_off == REG_CAM_KEY);

    // CAM_KEY holding register (loaded into the CAM on the next CAM_LOAD write).
    logic [PROF_KEY_W-1:0] r_cam_key;
    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) r_cam_key <= '0;
        else if (w_is_key)          r_cam_key <= r_cfgw_wdata[PROF_KEY_W-1:0];
    )

    logic                    w_profile_clear;
    logic                    w_profile_we;
    logic [PROF_IDX_W-1:0]   w_profile_waddr;
    logic                    w_profile_wvalid;
    logic [PROF_KEY_W-1:0]   w_profile_wkey;
    assign w_profile_clear  = w_cfgw_wr & (w_cfg_off == REG_CAM_CLEAR);
    assign w_profile_we     = w_cfgw_wr & (w_cfg_off == REG_CAM_LOAD);
    assign w_profile_waddr  = r_cfgw_wdata[PROF_IDX_W-1:0];      // index from data
    assign w_profile_wvalid = r_cfgw_wdata[31];                  // valid bit from data
    assign w_profile_wkey   = r_cam_key;                         // key from CAM_KEY reg

    // First-event capture control. ARMED BY DEFAULT with an empty pkt_type mask:
    // the tally's watch condition is (mask[pkt_type] || out-of-profile), so the
    // default captures exactly the first TALLY_NUM_LATCH UNEXPECTED packets --
    // which is the whole point of the UNEXPECTED bin. Without this the bin gives
    // a count and no way to see WHICH message was out of profile. A host that
    // also wants a known packet type captured writes WATCH_CTRL.
    logic                    r_watch_arm;
    logic [15:0]             r_watch_mask;
    logic [LSEL_WIDTH-1:0]   r_latch_sel;
    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_watch_arm  <= 1'b1;
            r_watch_mask <= 16'h0;
            r_latch_sel  <= '0;
        end else begin
            if (w_cfgw_wr && (w_cfg_off == REG_WATCH_CTRL)) begin
                r_watch_arm  <= r_cfgw_wdata[31];
                r_watch_mask <= r_cfgw_wdata[15:0];
            end
            if (w_cfgw_wr && (w_cfg_off == REG_LATCH_SEL))
                r_latch_sel <= r_cfgw_wdata[LSEL_WIDTH-1:0];
        end
    )

    logic [127:0]            w_latch_packet;
    logic [63:0]             w_latch_ts;
    logic                    w_latch_valid;
    logic [LFILL_WIDTH-1:0]  w_latch_fill;

    // ------------------------------------------------------------------------
    // READ port 1 — count readback: araddr>>3 selects a bin (8-byte stride: one
    // 32-bit count per 64-bit word -- same reason as the cfg entries above, so a
    // 4-byte-strided read of an odd bin can't fall on an empty high half).
    // ------------------------------------------------------------------------
    logic [TALLY_ADDR_BITS-1:0]   r_cnt_rd_addr;
    logic                         r_cnt_rvalid;
    logic [TALLY_COUNT_WIDTH-1:0] w_rd_count;

    // rd_count is REGISTERED inside monbus_pkt_tally -- "valid one cycle after
    // rd_addr" (see its port comment). rvalid must therefore lag the address
    // latch by one cycle.
    //
    // It used to assert on the SAME edge that latched r_cnt_rd_addr, so every
    // read returned the PREVIOUS bin's count: a whole histogram shifted by one,
    // with the first read serving stale data. That is not a simulation detail
    // -- the host sweeps these bins over UART through this same port, so board
    // readback was shifted too, and a first-bin read of 0 reads exactly like
    // "the tally counted nothing".
    logic r_cnt_addr_v;                      // address latched, data not yet out
    assign cnt_arready = ~r_cnt_rvalid & ~r_cnt_addr_v;
    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_cnt_rd_addr <= '0;
            r_cnt_addr_v  <= 1'b0;
            r_cnt_rvalid  <= 1'b0;
        end else begin
            if (cnt_arvalid & cnt_arready)
                r_cnt_rd_addr <= cnt_araddr[TALLY_ADDR_BITS+2:3];
            r_cnt_addr_v <= cnt_arvalid & cnt_arready;
            if (r_cnt_addr_v)                    r_cnt_rvalid <= 1'b1;
            else if (cnt_rvalid & cnt_rready)    r_cnt_rvalid <= 1'b0;
        end
    )
    assign cnt_rvalid = r_cnt_rvalid;
    assign cnt_rresp  = 2'b00;
    assign cnt_rdata  = {{(DATA_WIDTH-TALLY_COUNT_WIDTH){1'b0}}, w_rd_count};

    // ------------------------------------------------------------------------
    // READ port 2 — config/status readback (live; never tied off).
    // 8-byte stride throughout (one 32-bit word per 64-bit bus word), same
    // reason as the count and CAM ports: a 4-byte-strided read of an odd word
    // must not land in an empty high half.
    //   0x00 : identity/version   0x7A11_0001
    //   0x08 : sizing             {N_PROFILE[15:0], TALLY_ADDR_BITS[15:0]}
    //   0x10 : latch status       {valid, fill}  -- how many events captured
    //   0x18 : latch packet[31:0]      0x20 : latch packet[63:32]
    //   0x28 : latch packet[95:64]     0x30 : latch packet[127:96]
    //   0x38 : latch ts[31:0]          0x40 : latch ts[63:32]
    //   else : 0
    // The latch words return the slot selected by LATCH_SEL. Read the status
    // word first: fill is the number of valid slots.
    // ------------------------------------------------------------------------
    localparam logic [31:0] TALLY_ID = 32'h7A11_0000;   // "TA11" tag
    logic [ADDR_WIDTH-1:0] r_cfgr_araddr;
    logic                  r_cfgr_rvalid;
    logic [31:0]           w_cfgr_word;

    assign cfgr_arready = ~r_cfgr_rvalid;
    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_cfgr_araddr <= '0;
            r_cfgr_rvalid <= 1'b0;
        end else begin
            if (cfgr_arvalid & cfgr_arready) r_cfgr_araddr <= cfgr_araddr;
            if (cfgr_arvalid & cfgr_arready)     r_cfgr_rvalid <= 1'b1;
            else if (cfgr_rvalid & cfgr_rready)  r_cfgr_rvalid <= 1'b0;
        end
    )
    always_comb begin
        unique case (r_cfgr_araddr[6:3])
            4'd0:    w_cfgr_word = TALLY_ID | 32'h1;   // bit0 = CAM always on
            4'd1:    w_cfgr_word = {N_PROFILE[15:0], TALLY_ADDR_BITS[15:0]};
            4'd2:    w_cfgr_word = {15'h0, w_latch_valid,
                                    {(16-LFILL_WIDTH){1'b0}}, w_latch_fill};
            4'd3:    w_cfgr_word = w_latch_packet[31:0];
            4'd4:    w_cfgr_word = w_latch_packet[63:32];
            4'd5:    w_cfgr_word = w_latch_packet[95:64];
            4'd6:    w_cfgr_word = w_latch_packet[127:96];
            4'd7:    w_cfgr_word = w_latch_ts[31:0];
            4'd8:    w_cfgr_word = w_latch_ts[63:32];
            default: w_cfgr_word = 32'h0;
        endcase
    end
    assign cfgr_rvalid = r_cfgr_rvalid;
    assign cfgr_rresp  = 2'b00;
    assign cfgr_rdata  = {{(DATA_WIDTH-32){1'b0}}, w_cfgr_word};

    // ------------------------------------------------------------------------
    // The tally. Profile ports driven by the cfgw-write decode above.
    // ------------------------------------------------------------------------
    monbus_pkt_tally #(
        .PKT_WIDTH(128), .TS_WIDTH(64),
        .COUNT_WIDTH(TALLY_COUNT_WIDTH),
        .NUM_LATCH(TALLY_NUM_LATCH), .ADDR_BITS(TALLY_ADDR_BITS),
        .N_PROFILE(N_PROFILE)
    ) u_tally (
        .clk(aclk), .rst_n(aresetn),
        .in_valid(w_pkt_valid), .in_ready(w_tally_in_ready),
        .in_packet(w_pkt), .in_ts(w_pkt_ts),
        .i_freeze(tally_freeze), .i_flush(tally_flush),
        .o_flush_busy(tally_flush_busy), .i_clear(tally_clear),
        .rd_addr(r_cnt_rd_addr), .rd_count(w_rd_count),
        .i_watch_arm(r_watch_arm), .i_watch_pkttype_mask(r_watch_mask),
        .latch_sel(r_latch_sel), .latch_valid(w_latch_valid),
        .latch_packet(w_latch_packet), .latch_ts(w_latch_ts),
        .latch_fill(w_latch_fill),
        .profile_clear(w_profile_clear), .profile_we(w_profile_we),
        .profile_waddr(w_profile_waddr), .profile_wvalid(w_profile_wvalid),
        .profile_wkey(w_profile_wkey)
    );

endmodule : monbus_tally_axil
