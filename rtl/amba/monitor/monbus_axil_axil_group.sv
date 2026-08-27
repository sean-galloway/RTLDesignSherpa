// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// Module: monbus_axil_axil_group
// Purpose: AXIL-slave-read + AXIL-master-write wrapper for monbus_group_core.
//
//   Slave-read leaf:  axil4_slave_rd  (single-beat). Wrapper bridges its
//                     AXIL FUB into monbus_group_core's AXI4-shaped read
//                     FUB by supplying arid=0 / arlen=0 / arsize=3 /
//                     arburst=INCR. The core's rlast and rid go nowhere
//                     (AXIL has no last/id fields).
//
//   Master-write leaf: axil4_master_wr (single-beat). Core's MAX_BURST_BEATS
//                     is forced to 1, so each AW/W pair the core issues
//                     is a single beat. The leaf consumes the W beat
//                     without referencing wlast.
//
//   This wrapper replaces the legacy monbus_axil_group.sv (which fused
//   the core + AXIL skids into a single module).
//
// Subsystem: amba
// Author: sean galloway

`timescale 1ns / 1ps

`include "reset_defs.svh"

module monbus_axil_axil_group
    import monitor_common_pkg::*;
#(
    parameter int FIFO_DEPTH_ERR       = 64,
    parameter int FIFO_DEPTH_WRITE     = 96,   // beats
    parameter int ADDR_WIDTH           = 32,
    // Err-FIFO drain AXIL data width. The monbus record is three 64-bit
    // slices ({tag,ts}, packet[127:64], packet[63:0]). With a 64-bit drain
    // each slice is one beat (3 beats/record). With a 32-bit drain (for a
    // 32-bit host crossbar) a 2:1 read serializer splits each slice into a
    // low then high 32-bit beat (6 beats/record); the err-FIFO record is
    // popped when the slice-2 LEAF beat is consumed, which in 32-bit mode
    // happens on the LOW half of that slice (the high half is replayed from
    // a held register, not a second leaf read).
    parameter int S_AXIL_DATA_WIDTH    = 64,
    parameter int FLUSH_TIMEOUT_CYCLES = 1024,
    parameter int NUM_PROTOCOLS        = 3,
    parameter int USE_COMPRESSION      = 0,
    parameter int HALF_BEAT_EN         = 0,
    parameter int SKID_DEPTH_AR        = 2,
    parameter int SKID_DEPTH_R         = 4,
    parameter int SKID_DEPTH_AW        = 2,
    parameter int SKID_DEPTH_W         = 2,
    parameter int SKID_DEPTH_B         = 2
) (
    input  logic                          axi_aclk,
    input  logic                          axi_aresetn,
    input  logic                          cam_clear,   // sync clear: compressor CAM + stats

    // ----- Monitor-bus input + timestamp -----
    input  logic                          monbus_valid,
    output logic                          monbus_ready,
    input  monitor_packet_t               monbus_packet,
    input  monbus_timestamp_t             monbus_timestamp,

    output monbus_timestamp_t             mon_time_out,

    // ----- AXIL slave read (err FIFO drain) -----
    input  logic                          s_axil_arvalid,
    output logic                          s_axil_arready,
    input  logic [ADDR_WIDTH-1:0]         s_axil_araddr,
    input  logic [2:0]                    s_axil_arprot,

    output logic                          s_axil_rvalid,
    input  logic                          s_axil_rready,
    output logic [S_AXIL_DATA_WIDTH-1:0]  s_axil_rdata,
    output logic [1:0]                    s_axil_rresp,

    // ----- AXIL master write (bulk capture) -----
    output logic                          m_axil_awvalid,
    input  logic                          m_axil_awready,
    output logic [ADDR_WIDTH-1:0]         m_axil_awaddr,
    output logic [2:0]                    m_axil_awprot,

    output logic                          m_axil_wvalid,
    input  logic                          m_axil_wready,
    output logic [63:0]                   m_axil_wdata,
    output logic [7:0]                    m_axil_wstrb,

    input  logic                          m_axil_bvalid,
    output logic                          m_axil_bready,
    input  logic [1:0]                    m_axil_bresp,

    output logic                          irq_out,

    // ----- Config -----
    input  logic [ADDR_WIDTH-1:0]         cfg_base_addr,
    input  logic [ADDR_WIDTH-1:0]         cfg_limit_addr,
    input  logic [15:0]                   cfg_flush_watermark,
    input  logic                          cfg_compress_en,

    // AXI (protocol 0)
    input  logic [15:0]                   cfg_axi_pkt_mask,
    input  logic [15:0]                   cfg_axi_err_select,
    input  logic [15:0]                   cfg_axi_error_mask,
    input  logic [15:0]                   cfg_axi_timeout_mask,
    input  logic [15:0]                   cfg_axi_compl_mask,
    input  logic [15:0]                   cfg_axi_thresh_mask,
    input  logic [15:0]                   cfg_axi_perf_mask,
    input  logic [15:0]                   cfg_axi_addr_mask,
    input  logic [15:0]                   cfg_axi_debug_mask,
    // AXIS (protocol 1)
    input  logic [15:0]                   cfg_axis_pkt_mask,
    input  logic [15:0]                   cfg_axis_err_select,
    input  logic [15:0]                   cfg_axis_error_mask,
    input  logic [15:0]                   cfg_axis_timeout_mask,
    input  logic [15:0]                   cfg_axis_compl_mask,
    input  logic [15:0]                   cfg_axis_credit_mask,
    input  logic [15:0]                   cfg_axis_channel_mask,
    input  logic [15:0]                   cfg_axis_stream_mask,
    // CORE (protocol 4)
    input  logic [15:0]                   cfg_core_pkt_mask,
    input  logic [15:0]                   cfg_core_err_select,
    input  logic [15:0]                   cfg_core_error_mask,
    input  logic [15:0]                   cfg_core_timeout_mask,
    input  logic [15:0]                   cfg_core_compl_mask,
    input  logic [15:0]                   cfg_core_thresh_mask,
    input  logic [15:0]                   cfg_core_perf_mask,
    input  logic [15:0]                   cfg_core_debug_mask,

    // ----- Status / debug -----
    output logic                          err_fifo_full,
    output logic                          write_fifo_full,
    output logic [15:0]                   err_fifo_count,
    output logic [15:0]                   write_fifo_count,

    output logic [31:0]                   mon_compressor_stat_tier1_a,
    output logic [31:0]                   mon_compressor_stat_tier1_b,
    output logic [31:0]                   mon_compressor_stat_tier1_c,
    output logic [31:0]                   mon_compressor_stat_tier0,
    output logic [31:0]                   mon_compressor_stat_cam_miss,
    output logic [31:0]                   mon_compressor_stat_delta_ts_ovf,
    output logic [31:0]                   mon_compressor_stat_event_data_ovf,
    output logic [31:0]                   mon_compressor_stat_ed_delta_ovf
);

    // ==================================================================
    // FUB nets between leaves and core
    // ==================================================================

    // Slave-read (AXIL leaf -> bridge -> core's AXI4-shaped FUB)
    logic [ADDR_WIDTH-1:0]   axil_rd_fub_araddr;
    /* verilator lint_off UNUSED */
    logic [2:0]              axil_rd_fub_arprot;
    /* verilator lint_on UNUSED */
    logic                    axil_rd_fub_arvalid;
    logic                    axil_rd_fub_arready;
    logic [63:0]             axil_rd_fub_rdata;
    logic [1:0]              axil_rd_fub_rresp;
    logic                    axil_rd_fub_rvalid;
    logic                    axil_rd_fub_rready;

    // Master-write (core's AXI4-shaped FUB -> bridge -> AXIL leaf)
    logic [ADDR_WIDTH-1:0]   axil_wr_fub_awaddr;
    logic                    axil_wr_fub_awvalid;
    logic                    axil_wr_fub_awready;
    logic [63:0]             axil_wr_fub_wdata;
    logic [7:0]              axil_wr_fub_wstrb;
    logic                    axil_wr_fub_wvalid;
    logic                    axil_wr_fub_wready;
    logic [1:0]              axil_wr_fub_bresp;
    logic                    axil_wr_fub_bvalid;
    logic                    axil_wr_fub_bready;

    // Core-side AXI4-shaped read FUB (the burst signals are tied off in
    // AXIL builds and arlen is forced to 0)
    /* verilator lint_off UNUSED */
    logic                    core_s_arready_unused;
    logic                    core_s_rlast_unused;
    logic [0:0]              core_s_rid_unused;
    /* verilator lint_on UNUSED */

    // Core-side AXI4-shaped write FUB
    /* verilator lint_off UNUSED */
    logic [0:0]              core_m_awid_unused;
    logic [7:0]              core_m_awlen_unused;
    logic [2:0]              core_m_awsize_unused;
    logic [1:0]              core_m_awburst_unused;
    logic                    core_m_wlast_unused;
    /* verilator lint_on UNUSED */

    // ==================================================================
    // Err-FIFO drain: a 64-bit axil4_slave_rd leaf bridges the external AXIL
    // read onto the core's 64-bit read FUB one-to-one. For a 32-bit external
    // bus a phase counter splits each 64-bit beat into two reads (low then
    // high): the external AR is forwarded to the leaf only on the low beat, so
    // the leaf issues exactly one core read per PAIR and never prefetches; the
    // leaf's R beat is consumed on the LOW read (drv_rready is asserted only
    // in PH_LOW) and its upper half is replayed from r_hi_half on the high
    // read -- not held and consumed on the high beat.
    // ==================================================================
    logic                          drv_arvalid;   // external AR seen by the leaf
    logic                          drv_arready;
    logic [63:0]                   drv_rdata;      // leaf's 64-bit beat
    logic [1:0]                    drv_rresp;
    logic                          drv_rvalid;
    logic                          drv_rready;     // external R consumed at the leaf

    axil4_slave_rd #(
        .AXIL_ADDR_WIDTH (ADDR_WIDTH),
        .AXIL_DATA_WIDTH (64),
        .SKID_DEPTH_AR   (SKID_DEPTH_AR),
        .SKID_DEPTH_R    (SKID_DEPTH_R)
    ) u_axil_rd (
        .aclk           (axi_aclk),
        .aresetn        (axi_aresetn),
        .s_axil_araddr  (s_axil_araddr),
        .s_axil_arprot  (s_axil_arprot),
        .s_axil_arvalid (drv_arvalid),
        .s_axil_arready (drv_arready),
        .s_axil_rdata   (drv_rdata),
        .s_axil_rresp   (drv_rresp),
        .s_axil_rvalid  (drv_rvalid),
        .s_axil_rready  (drv_rready),
        .fub_araddr     (axil_rd_fub_araddr),
        .fub_arprot     (axil_rd_fub_arprot),
        .fub_arvalid    (axil_rd_fub_arvalid),
        .fub_arready    (axil_rd_fub_arready),
        .fub_rdata      (axil_rd_fub_rdata),
        .fub_rresp      (axil_rd_fub_rresp),
        .fub_rvalid     (axil_rd_fub_rvalid),
        .fub_rready     (axil_rd_fub_rready),
        .busy           ()
    );

    generate
    if (S_AXIL_DATA_WIDTH == 64) begin : g_drain_direct
        // 64-bit external: wire the leaf straight through.
        assign drv_arvalid    = s_axil_arvalid;
        assign s_axil_arready = drv_arready;
        assign s_axil_rdata   = drv_rdata;
        assign s_axil_rresp   = drv_rresp;
        assign s_axil_rvalid  = drv_rvalid;
        assign drv_rready     = s_axil_rready;
    end else begin : g_drain_2to1
        // 32-bit external: each 64-bit leaf beat is presented as a low then a
        // high external read. Every PAIR of external reads costs exactly one
        // 64-bit core read: the LOW read of a pair is the one forwarded to the
        // leaf (streaming the beat through and latching its high half), and the
        // HIGH read is served locally from that latch.
        //
        // The AR router and the R server keep SEPARATE phase bits:
        //
        //   r_ar_phase  advances on each accepted external AR
        //   r_phase     advances on each completed external R beat
        //
        // They must be separate because AXI4-Lite does not order AR(n+1) after
        // R(n): a master is free to issue the high read's AR before the low
        // read's R beat has been returned. Routing AR off the R-side phase (as
        // this block originally did) sent that early AR to the leaf as a
        // spurious extra core read, and then stalled forever waiting for an AR
        // the master had already issued.
        //
        // The leaf therefore still sees exactly one core read per pair, but a
        // pipelining master may have several PAIRS in flight at once, so the
        // leaf's AR skid can legitimately hold up to SKID_DEPTH_AR outstanding
        // core reads. High-half ARs that arrive before their beat is ready are
        // banked in r_hi_ar (a small credit counter, not a single flag) and
        // spent when the corresponding high beat is consumed; s_axil_arready
        // backpressures once those credits are exhausted.
        localparam logic PH_LOW = 1'b0, PH_HIGH = 1'b1;
        // Credits for locally-absorbed high-half ARs. Sized to the leaf's AR
        // skid so neither side is the sole bottleneck (>=2 so a pipelining
        // master always gets at least one pair ahead).
        localparam int HI_AR_CREDITS = (SKID_DEPTH_AR < 2) ? 2 : SKID_DEPTH_AR;
        localparam int HI_CNT_W      = $clog2(HI_AR_CREDITS + 1);

        logic                r_ar_phase;  // AR-side pair phase
        logic                r_phase;     // R-side pair phase
        logic [31:0]         r_hi_half;
        logic [HI_CNT_W-1:0] r_hi_ar;     // banked high-half ARs awaiting their R

        logic w_hi_ar_room;               // room to bank another high-half AR
        logic w_hi_ar_inc;                // a high-half AR was accepted
        logic w_hi_ar_dec;                // a high-half beat was consumed

        assign w_hi_ar_room = (r_hi_ar != HI_CNT_W'(HI_AR_CREDITS));

        // AR: the low half of a pair goes to the leaf; the high half is
        // absorbed here as a credit. Keyed off r_ar_phase so an early
        // high-half AR is never mistaken for the next pair's low half.
        assign drv_arvalid    = (r_ar_phase == PH_LOW) && s_axil_arvalid;
        assign s_axil_arready = (r_ar_phase == PH_LOW) ? drv_arready : w_hi_ar_room;

        // R: low phase streams the leaf's low half (consuming the beat); high
        // phase replays the latched high half once its AR has been banked.
        // Gating the high R on r_hi_ar still enforces AXIL AR-before-R, so a
        // master holding rready from the low beat cannot consume the high beat
        // before asking for it.
        assign s_axil_rvalid  = (r_phase == PH_LOW) ? drv_rvalid : (r_hi_ar != '0);
        assign s_axil_rdata   = (r_phase == PH_LOW) ? drv_rdata[31:0] : r_hi_half;
        assign s_axil_rresp   = 2'b00;
        assign drv_rready     = (r_phase == PH_LOW) && s_axil_rready;

        assign w_hi_ar_inc = s_axil_arvalid && s_axil_arready &&
                             (r_ar_phase == PH_HIGH);
        assign w_hi_ar_dec = s_axil_rvalid && s_axil_rready &&
                             (r_phase == PH_HIGH);

        `ALWAYS_FF_RST(axi_aclk, axi_aresetn,
            if (`RST_ASSERTED(axi_aresetn)) begin
                r_ar_phase <= PH_LOW;
                r_phase    <= PH_LOW;
                r_hi_half  <= 32'd0;
                r_hi_ar    <= '0;
            end else begin
                // AR side: one toggle per accepted external AR.
                if (s_axil_arvalid && s_axil_arready)
                    r_ar_phase <= ~r_ar_phase;

                // R side: one toggle per completed external R beat.
                if (s_axil_rvalid && s_axil_rready) begin
                    if (r_phase == PH_LOW) begin
                        r_hi_half <= drv_rdata[63:32];
                        r_phase   <= PH_HIGH;
                    end else begin
                        r_phase   <= PH_LOW;
                    end
                end

                // High-half AR credits.
                if (w_hi_ar_inc && !w_hi_ar_dec)
                    r_hi_ar <= r_hi_ar + 1'b1;
                else if (!w_hi_ar_inc && w_hi_ar_dec)
                    r_hi_ar <= r_hi_ar - 1'b1;
            end
        )
    end
    endgenerate

    // ==================================================================
    // AXIL master write leaf
    // ==================================================================
    axil4_master_wr #(
        .AXIL_ADDR_WIDTH (ADDR_WIDTH),
        .AXIL_DATA_WIDTH (64),
        .SKID_DEPTH_AW   (SKID_DEPTH_AW),
        .SKID_DEPTH_W    (SKID_DEPTH_W),
        .SKID_DEPTH_B    (SKID_DEPTH_B)
    ) u_axil_wr (
        .aclk           (axi_aclk),
        .aresetn        (axi_aresetn),

        .fub_awaddr     (axil_wr_fub_awaddr),
        .fub_awprot     (3'b000),
        .fub_awvalid    (axil_wr_fub_awvalid),
        .fub_awready    (axil_wr_fub_awready),
        .fub_wdata      (axil_wr_fub_wdata),
        .fub_wstrb      (axil_wr_fub_wstrb),
        .fub_wvalid     (axil_wr_fub_wvalid),
        .fub_wready     (axil_wr_fub_wready),
        .fub_bresp      (axil_wr_fub_bresp),
        .fub_bvalid     (axil_wr_fub_bvalid),
        .fub_bready     (axil_wr_fub_bready),

        .m_axil_awaddr  (m_axil_awaddr),
        .m_axil_awprot  (m_axil_awprot),
        .m_axil_awvalid (m_axil_awvalid),
        .m_axil_awready (m_axil_awready),
        .m_axil_wdata   (m_axil_wdata),
        .m_axil_wstrb   (m_axil_wstrb),
        .m_axil_wvalid  (m_axil_wvalid),
        .m_axil_wready  (m_axil_wready),
        .m_axil_bresp   (m_axil_bresp),
        .m_axil_bvalid  (m_axil_bvalid),
        .m_axil_bready  (m_axil_bready),

        .busy           ()
    );

    // ==================================================================
    // Protocol-agnostic core
    // ==================================================================
    monbus_group_core #(
        .FIFO_DEPTH_ERR       (FIFO_DEPTH_ERR),
        .FIFO_DEPTH_WRITE     (FIFO_DEPTH_WRITE),
        .ADDR_WIDTH           (ADDR_WIDTH),
        .AXI_ID_WIDTH_M       (1),
        .AXI_ID_WIDTH_S       (1),
        .MAX_BURST_BEATS      (1),   // AXIL master: single-beat
        .FLUSH_TIMEOUT_CYCLES (FLUSH_TIMEOUT_CYCLES),
        .NUM_PROTOCOLS        (NUM_PROTOCOLS),
        .USE_COMPRESSION      (USE_COMPRESSION),
        .HALF_BEAT_EN         (HALF_BEAT_EN)
    ) u_core (
        .axi_aclk    (axi_aclk),
        .axi_aresetn (axi_aresetn),
        .cam_clear   (cam_clear),

        .monbus_valid     (monbus_valid),
        .monbus_ready     (monbus_ready),
        .monbus_packet    (monbus_packet),
        .monbus_timestamp (monbus_timestamp),
        .mon_time_out     (mon_time_out),

        .irq_out          (irq_out),
        .err_fifo_full    (err_fifo_full),
        .write_fifo_full  (write_fifo_full),
        .err_fifo_count   (err_fifo_count),
        .write_fifo_count (write_fifo_count),

        .cfg_base_addr        (cfg_base_addr),
        .cfg_limit_addr       (cfg_limit_addr),
        .cfg_flush_watermark  (cfg_flush_watermark),
        .cfg_compress_en      (cfg_compress_en),

        .cfg_axi_pkt_mask     (cfg_axi_pkt_mask),
        .cfg_axi_err_select   (cfg_axi_err_select),
        .cfg_axi_error_mask   (cfg_axi_error_mask),
        .cfg_axi_timeout_mask (cfg_axi_timeout_mask),
        .cfg_axi_compl_mask   (cfg_axi_compl_mask),
        .cfg_axi_thresh_mask  (cfg_axi_thresh_mask),
        .cfg_axi_perf_mask    (cfg_axi_perf_mask),
        .cfg_axi_addr_mask    (cfg_axi_addr_mask),
        .cfg_axi_debug_mask   (cfg_axi_debug_mask),

        .cfg_axis_pkt_mask     (cfg_axis_pkt_mask),
        .cfg_axis_err_select   (cfg_axis_err_select),
        .cfg_axis_error_mask   (cfg_axis_error_mask),
        .cfg_axis_timeout_mask (cfg_axis_timeout_mask),
        .cfg_axis_compl_mask   (cfg_axis_compl_mask),
        .cfg_axis_credit_mask  (cfg_axis_credit_mask),
        .cfg_axis_channel_mask (cfg_axis_channel_mask),
        .cfg_axis_stream_mask  (cfg_axis_stream_mask),

        .cfg_core_pkt_mask     (cfg_core_pkt_mask),
        .cfg_core_err_select   (cfg_core_err_select),
        .cfg_core_error_mask   (cfg_core_error_mask),
        .cfg_core_timeout_mask (cfg_core_timeout_mask),
        .cfg_core_compl_mask   (cfg_core_compl_mask),
        .cfg_core_thresh_mask  (cfg_core_thresh_mask),
        .cfg_core_perf_mask    (cfg_core_perf_mask),
        .cfg_core_debug_mask   (cfg_core_debug_mask),

        .mon_compressor_stat_tier1_a        (mon_compressor_stat_tier1_a),
        .mon_compressor_stat_tier1_b        (mon_compressor_stat_tier1_b),
        .mon_compressor_stat_tier1_c        (mon_compressor_stat_tier1_c),
        .mon_compressor_stat_tier0          (mon_compressor_stat_tier0),
        .mon_compressor_stat_cam_miss       (mon_compressor_stat_cam_miss),
        .mon_compressor_stat_delta_ts_ovf   (mon_compressor_stat_delta_ts_ovf),
        .mon_compressor_stat_event_data_ovf (mon_compressor_stat_event_data_ovf),
        .mon_compressor_stat_ed_delta_ovf   (mon_compressor_stat_ed_delta_ovf),

        // Master-write FUB (core drives, wrapper feeds AXIL leaf)
        .fub_m_awid    (core_m_awid_unused),
        .fub_m_awaddr  (axil_wr_fub_awaddr),
        .fub_m_awlen   (core_m_awlen_unused),
        .fub_m_awsize  (core_m_awsize_unused),
        .fub_m_awburst (core_m_awburst_unused),
        .fub_m_awvalid (axil_wr_fub_awvalid),
        .fub_m_awready (axil_wr_fub_awready),

        .fub_m_wdata   (axil_wr_fub_wdata),
        .fub_m_wstrb   (axil_wr_fub_wstrb),
        .fub_m_wlast   (core_m_wlast_unused),
        .fub_m_wvalid  (axil_wr_fub_wvalid),
        .fub_m_wready  (axil_wr_fub_wready),

        .fub_m_bid     (1'b0),
        .fub_m_bresp   (axil_wr_fub_bresp),
        .fub_m_bvalid  (axil_wr_fub_bvalid),
        .fub_m_bready  (axil_wr_fub_bready),

        // Slave-read FUB (wrapper drives from AXIL leaf -> core)
        .fub_s_arid    (1'b0),
        .fub_s_araddr  (axil_rd_fub_araddr),
        .fub_s_arlen   (8'd0),       // single-beat
        .fub_s_arsize  (3'd3),       // 8 bytes
        .fub_s_arburst (2'b01),      // INCR
        .fub_s_arvalid (axil_rd_fub_arvalid),
        .fub_s_arready (axil_rd_fub_arready),

        .fub_s_rid     (core_s_rid_unused),
        .fub_s_rdata   (axil_rd_fub_rdata),
        .fub_s_rresp   (axil_rd_fub_rresp),
        .fub_s_rlast   (core_s_rlast_unused),
        .fub_s_rvalid  (axil_rd_fub_rvalid),
        .fub_s_rready  (axil_rd_fub_rready)
    );

endmodule : monbus_axil_axil_group
