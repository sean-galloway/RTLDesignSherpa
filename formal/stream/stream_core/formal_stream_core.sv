// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// Formal wrapper for stream_core (yosys-compatible, sv2v-preprocessed)
// Run with: sby stream_core.sby
//
// This is the largest STREAM integration module. We use small parameters
// (NUM_CHANNELS=2, DATA_WIDTH=64, SRAM_DEPTH=16, USE_AXI_MONITORS=0)
// and shallow BMC depth (15) to keep the proof tractable.

module formal_stream_core (
    input  logic        clk,
    input  logic        rst_n
);

    // =========================================================================
    // Parameters (minimal for tractability)
    // =========================================================================
    localparam int NC  = 2;          // 2 channels (not 8)
    localparam int AW  = 32;         // 32-bit address (not 64)
    localparam int DW  = 64;         // 64-bit data (not 512)
    localparam int IW  = 4;          // 4-bit AXI ID
    localparam int UW  = 1;          // 1-bit user (log2(NC))

    // =========================================================================
    // Free inputs (driven by formal engine)
    // =========================================================================

    // APB interface
    (* anyseq *) reg [NC-1:0]          apb_valid;
    (* anyseq *) reg [NC*AW-1:0]       apb_addr_flat;

    // Configuration (held constant for tractability)
    (* anyseq *) reg [NC-1:0]          cfg_channel_enable;
    (* anyseq *) reg [NC-1:0]          cfg_channel_reset;
    (* anyseq *) reg                   cfg_sched_enable;
    (* anyseq *) reg [15:0]            cfg_sched_timeout_cycles;
    (* anyseq *) reg                   cfg_sched_timeout_enable;
    (* anyseq *) reg                   cfg_sched_err_enable;
    (* anyseq *) reg                   cfg_sched_compl_enable;
    (* anyseq *) reg                   cfg_sched_perf_enable;
    (* anyseq *) reg                   cfg_desceng_enable;
    (* anyseq *) reg                   cfg_desceng_prefetch;
    (* anyseq *) reg [3:0]             cfg_desceng_fifo_thresh;
    (* anyseq *) reg [AW-1:0]          cfg_desceng_addr0_base;
    (* anyseq *) reg [AW-1:0]          cfg_desceng_addr0_limit;
    (* anyseq *) reg [AW-1:0]          cfg_desceng_addr1_base;
    (* anyseq *) reg [AW-1:0]          cfg_desceng_addr1_limit;

    // Monitor config (tied off for USE_AXI_MONITORS=0)
    (* anyseq *) reg                   cfg_desc_mon_enable;
    (* anyseq *) reg                   cfg_desc_mon_err_enable;
    (* anyseq *) reg                   cfg_desc_mon_perf_enable;
    (* anyseq *) reg                   cfg_desc_mon_timeout_enable;
    (* anyseq *) reg [31:0]            cfg_desc_mon_timeout_cycles;
    (* anyseq *) reg [31:0]            cfg_desc_mon_latency_thresh;
    (* anyseq *) reg [15:0]            cfg_desc_mon_pkt_mask;
    (* anyseq *) reg [3:0]             cfg_desc_mon_err_select;
    (* anyseq *) reg [7:0]             cfg_desc_mon_err_mask;
    (* anyseq *) reg [7:0]             cfg_desc_mon_timeout_mask;
    (* anyseq *) reg [7:0]             cfg_desc_mon_compl_mask;
    (* anyseq *) reg [7:0]             cfg_desc_mon_thresh_mask;
    (* anyseq *) reg [7:0]             cfg_desc_mon_perf_mask;
    (* anyseq *) reg [7:0]             cfg_desc_mon_addr_mask;
    (* anyseq *) reg [7:0]             cfg_desc_mon_debug_mask;

    (* anyseq *) reg                   cfg_rdeng_mon_enable;
    (* anyseq *) reg                   cfg_rdeng_mon_err_enable;
    (* anyseq *) reg                   cfg_rdeng_mon_perf_enable;
    (* anyseq *) reg                   cfg_rdeng_mon_timeout_enable;
    (* anyseq *) reg [31:0]            cfg_rdeng_mon_timeout_cycles;
    (* anyseq *) reg [31:0]            cfg_rdeng_mon_latency_thresh;
    (* anyseq *) reg [15:0]            cfg_rdeng_mon_pkt_mask;
    (* anyseq *) reg [3:0]             cfg_rdeng_mon_err_select;
    (* anyseq *) reg [7:0]             cfg_rdeng_mon_err_mask;
    (* anyseq *) reg [7:0]             cfg_rdeng_mon_timeout_mask;
    (* anyseq *) reg [7:0]             cfg_rdeng_mon_compl_mask;
    (* anyseq *) reg [7:0]             cfg_rdeng_mon_thresh_mask;
    (* anyseq *) reg [7:0]             cfg_rdeng_mon_perf_mask;
    (* anyseq *) reg [7:0]             cfg_rdeng_mon_addr_mask;
    (* anyseq *) reg [7:0]             cfg_rdeng_mon_debug_mask;

    (* anyseq *) reg                   cfg_wreng_mon_enable;
    (* anyseq *) reg                   cfg_wreng_mon_err_enable;
    (* anyseq *) reg                   cfg_wreng_mon_perf_enable;
    (* anyseq *) reg                   cfg_wreng_mon_timeout_enable;
    (* anyseq *) reg [31:0]            cfg_wreng_mon_timeout_cycles;
    (* anyseq *) reg [31:0]            cfg_wreng_mon_latency_thresh;
    (* anyseq *) reg [15:0]            cfg_wreng_mon_pkt_mask;
    (* anyseq *) reg [3:0]             cfg_wreng_mon_err_select;
    (* anyseq *) reg [7:0]             cfg_wreng_mon_err_mask;
    (* anyseq *) reg [7:0]             cfg_wreng_mon_timeout_mask;
    (* anyseq *) reg [7:0]             cfg_wreng_mon_compl_mask;
    (* anyseq *) reg [7:0]             cfg_wreng_mon_thresh_mask;
    (* anyseq *) reg [7:0]             cfg_wreng_mon_perf_mask;
    (* anyseq *) reg [7:0]             cfg_wreng_mon_addr_mask;
    (* anyseq *) reg [7:0]             cfg_wreng_mon_debug_mask;

    (* anyseq *) reg [7:0]             cfg_axi_rd_xfer_beats;
    (* anyseq *) reg [7:0]             cfg_axi_wr_xfer_beats;
    (* anyseq *) reg                   cfg_perf_enable;
    (* anyseq *) reg                   cfg_perf_mode;
    (* anyseq *) reg                   cfg_perf_clear;

    // AXI descriptor read responses
    (* anyseq *) reg                   m_axi_desc_arready;
    (* anyseq *) reg [IW-1:0]          m_axi_desc_rid;
    (* anyseq *) reg [255:0]           m_axi_desc_rdata;
    (* anyseq *) reg [1:0]             m_axi_desc_rresp;
    (* anyseq *) reg                   m_axi_desc_rlast;
    (* anyseq *) reg [UW-1:0]          m_axi_desc_ruser;
    (* anyseq *) reg                   m_axi_desc_rvalid;

    // AXI data read responses
    (* anyseq *) reg                   m_axi_rd_arready;
    (* anyseq *) reg [IW-1:0]          m_axi_rd_rid;
    (* anyseq *) reg [DW-1:0]          m_axi_rd_rdata;
    (* anyseq *) reg [1:0]             m_axi_rd_rresp;
    (* anyseq *) reg                   m_axi_rd_rlast;
    (* anyseq *) reg [UW-1:0]          m_axi_rd_ruser;
    (* anyseq *) reg                   m_axi_rd_rvalid;

    // AXI data write responses
    (* anyseq *) reg                   m_axi_wr_awready;
    (* anyseq *) reg                   m_axi_wr_wready;
    (* anyseq *) reg [IW-1:0]          m_axi_wr_bid;
    (* anyseq *) reg [1:0]             m_axi_wr_bresp;
    (* anyseq *) reg [UW-1:0]          m_axi_wr_buser;
    (* anyseq *) reg                   m_axi_wr_bvalid;

    // MonBus
    (* anyseq *) reg                   mon_ready;

    // Perf
    (* anyseq *) reg                   perf_fifo_rd;

    // =========================================================================
    // DUT outputs
    // =========================================================================
    wire [NC-1:0]      apb_ready_o;
    wire               system_idle_o;
    wire [NC-1:0]      descriptor_engine_idle_o;
    wire [NC-1:0]      scheduler_idle_o;
    wire [NC*7-1:0]    scheduler_state_flat_o;
    wire [NC-1:0]      sched_error_o;
    wire [NC-1:0]      axi_rd_all_complete_o;
    wire [NC-1:0]      axi_wr_all_complete_o;

    wire               m_axi_desc_arvalid_o;
    wire               m_axi_desc_rready_o;
    wire               m_axi_rd_arvalid_o;
    wire               m_axi_rd_rready_o;
    wire               m_axi_wr_awvalid_o;
    wire               m_axi_wr_wvalid_o;
    wire               m_axi_wr_bready_o;

    wire               mon_valid_o;
    wire [63:0]        mon_packet_o;

    // =========================================================================
    // DUT instantiation
    // =========================================================================
    stream_core #(
        .NUM_CHANNELS       (NC),
        .ADDR_WIDTH         (AW),
        .DATA_WIDTH         (DW),
        .AXI_ID_WIDTH       (IW),
        .FIFO_DEPTH         (16),
        .AR_MAX_OUTSTANDING (4),
        .AW_MAX_OUTSTANDING (4),
        .USE_AXI_MONITORS   (0),
        .SKID_DEPTH_AR      (2),
        .SKID_DEPTH_R       (2),
        .SKID_DEPTH_AW      (2),
        .SKID_DEPTH_W       (2),
        .SKID_DEPTH_B       (2)
    ) dut (
        .clk                (clk),
        .rst_n              (rst_n),

        // APB interface
        .apb_valid          (apb_valid),
        .apb_ready          (apb_ready_o),
        .apb_addr           (apb_addr_flat),

        // Configuration
        .cfg_channel_enable         (cfg_channel_enable),
        .cfg_channel_reset          (cfg_channel_reset),
        .cfg_sched_enable           (cfg_sched_enable),
        .cfg_sched_timeout_cycles   (cfg_sched_timeout_cycles),
        .cfg_sched_timeout_enable   (cfg_sched_timeout_enable),
        .cfg_sched_err_enable       (cfg_sched_err_enable),
        .cfg_sched_compl_enable     (cfg_sched_compl_enable),
        .cfg_sched_perf_enable      (cfg_sched_perf_enable),
        .cfg_desceng_enable         (cfg_desceng_enable),
        .cfg_desceng_prefetch       (cfg_desceng_prefetch),
        .cfg_desceng_fifo_thresh    (cfg_desceng_fifo_thresh),
        .cfg_desceng_addr0_base     (cfg_desceng_addr0_base),
        .cfg_desceng_addr0_limit    (cfg_desceng_addr0_limit),
        .cfg_desceng_addr1_base     (cfg_desceng_addr1_base),
        .cfg_desceng_addr1_limit    (cfg_desceng_addr1_limit),

        // Descriptor AXI monitor config
        .cfg_desc_mon_enable        (cfg_desc_mon_enable),
        .cfg_desc_mon_err_enable    (cfg_desc_mon_err_enable),
        .cfg_desc_mon_perf_enable   (cfg_desc_mon_perf_enable),
        .cfg_desc_mon_timeout_enable(cfg_desc_mon_timeout_enable),
        .cfg_desc_mon_timeout_cycles(cfg_desc_mon_timeout_cycles),
        .cfg_desc_mon_latency_thresh(cfg_desc_mon_latency_thresh),
        .cfg_desc_mon_pkt_mask      (cfg_desc_mon_pkt_mask),
        .cfg_desc_mon_err_select    (cfg_desc_mon_err_select),
        .cfg_desc_mon_err_mask      (cfg_desc_mon_err_mask),
        .cfg_desc_mon_timeout_mask  (cfg_desc_mon_timeout_mask),
        .cfg_desc_mon_compl_mask    (cfg_desc_mon_compl_mask),
        .cfg_desc_mon_thresh_mask   (cfg_desc_mon_thresh_mask),
        .cfg_desc_mon_perf_mask     (cfg_desc_mon_perf_mask),
        .cfg_desc_mon_addr_mask     (cfg_desc_mon_addr_mask),
        .cfg_desc_mon_debug_mask    (cfg_desc_mon_debug_mask),

        // Read engine AXI monitor config
        .cfg_rdeng_mon_enable        (cfg_rdeng_mon_enable),
        .cfg_rdeng_mon_err_enable    (cfg_rdeng_mon_err_enable),
        .cfg_rdeng_mon_perf_enable   (cfg_rdeng_mon_perf_enable),
        .cfg_rdeng_mon_timeout_enable(cfg_rdeng_mon_timeout_enable),
        .cfg_rdeng_mon_timeout_cycles(cfg_rdeng_mon_timeout_cycles),
        .cfg_rdeng_mon_latency_thresh(cfg_rdeng_mon_latency_thresh),
        .cfg_rdeng_mon_pkt_mask      (cfg_rdeng_mon_pkt_mask),
        .cfg_rdeng_mon_err_select    (cfg_rdeng_mon_err_select),
        .cfg_rdeng_mon_err_mask      (cfg_rdeng_mon_err_mask),
        .cfg_rdeng_mon_timeout_mask  (cfg_rdeng_mon_timeout_mask),
        .cfg_rdeng_mon_compl_mask    (cfg_rdeng_mon_compl_mask),
        .cfg_rdeng_mon_thresh_mask   (cfg_rdeng_mon_thresh_mask),
        .cfg_rdeng_mon_perf_mask     (cfg_rdeng_mon_perf_mask),
        .cfg_rdeng_mon_addr_mask     (cfg_rdeng_mon_addr_mask),
        .cfg_rdeng_mon_debug_mask    (cfg_rdeng_mon_debug_mask),

        // Write engine AXI monitor config
        .cfg_wreng_mon_enable        (cfg_wreng_mon_enable),
        .cfg_wreng_mon_err_enable    (cfg_wreng_mon_err_enable),
        .cfg_wreng_mon_perf_enable   (cfg_wreng_mon_perf_enable),
        .cfg_wreng_mon_timeout_enable(cfg_wreng_mon_timeout_enable),
        .cfg_wreng_mon_timeout_cycles(cfg_wreng_mon_timeout_cycles),
        .cfg_wreng_mon_latency_thresh(cfg_wreng_mon_latency_thresh),
        .cfg_wreng_mon_pkt_mask      (cfg_wreng_mon_pkt_mask),
        .cfg_wreng_mon_err_select    (cfg_wreng_mon_err_select),
        .cfg_wreng_mon_err_mask      (cfg_wreng_mon_err_mask),
        .cfg_wreng_mon_timeout_mask  (cfg_wreng_mon_timeout_mask),
        .cfg_wreng_mon_compl_mask    (cfg_wreng_mon_compl_mask),
        .cfg_wreng_mon_thresh_mask   (cfg_wreng_mon_thresh_mask),
        .cfg_wreng_mon_perf_mask     (cfg_wreng_mon_perf_mask),
        .cfg_wreng_mon_addr_mask     (cfg_wreng_mon_addr_mask),
        .cfg_wreng_mon_debug_mask    (cfg_wreng_mon_debug_mask),

        .cfg_axi_rd_xfer_beats      (cfg_axi_rd_xfer_beats),
        .cfg_axi_wr_xfer_beats      (cfg_axi_wr_xfer_beats),
        .cfg_perf_enable             (cfg_perf_enable),
        .cfg_perf_mode               (cfg_perf_mode),
        .cfg_perf_clear              (cfg_perf_clear),

        // Status
        .system_idle            (system_idle_o),
        .descriptor_engine_idle (descriptor_engine_idle_o),
        .scheduler_idle         (scheduler_idle_o),
        .scheduler_state        (scheduler_state_flat_o),
        .sched_error            (sched_error_o),
        .axi_rd_all_complete    (axi_rd_all_complete_o),
        .axi_wr_all_complete    (axi_wr_all_complete_o),

        .perf_fifo_empty        (),
        .perf_fifo_full         (),
        .perf_fifo_count        (),
        .perf_fifo_rd           (perf_fifo_rd),
        .perf_fifo_data_low     (),
        .perf_fifo_data_high    (),

        // AXI descriptor fetch
        .m_axi_desc_arid        (),
        .m_axi_desc_araddr      (),
        .m_axi_desc_arlen       (),
        .m_axi_desc_arsize      (),
        .m_axi_desc_arburst     (),
        .m_axi_desc_arlock      (),
        .m_axi_desc_arcache     (),
        .m_axi_desc_arprot      (),
        .m_axi_desc_arqos       (),
        .m_axi_desc_arregion    (),
        .m_axi_desc_aruser      (),
        .m_axi_desc_arvalid     (m_axi_desc_arvalid_o),
        .m_axi_desc_arready     (m_axi_desc_arready),
        .m_axi_desc_rid         (m_axi_desc_rid),
        .m_axi_desc_rdata       (m_axi_desc_rdata),
        .m_axi_desc_rresp       (m_axi_desc_rresp),
        .m_axi_desc_rlast       (m_axi_desc_rlast),
        .m_axi_desc_ruser       (m_axi_desc_ruser),
        .m_axi_desc_rvalid      (m_axi_desc_rvalid),
        .m_axi_desc_rready      (m_axi_desc_rready_o),

        // AXI data read
        .m_axi_rd_arid          (),
        .m_axi_rd_araddr        (),
        .m_axi_rd_arlen         (),
        .m_axi_rd_arsize        (),
        .m_axi_rd_arburst       (),
        .m_axi_rd_arlock        (),
        .m_axi_rd_arcache       (),
        .m_axi_rd_arprot        (),
        .m_axi_rd_arqos         (),
        .m_axi_rd_arregion      (),
        .m_axi_rd_aruser        (),
        .m_axi_rd_arvalid       (m_axi_rd_arvalid_o),
        .m_axi_rd_arready       (m_axi_rd_arready),
        .m_axi_rd_rid           (m_axi_rd_rid),
        .m_axi_rd_rdata         (m_axi_rd_rdata),
        .m_axi_rd_rresp         (m_axi_rd_rresp),
        .m_axi_rd_rlast         (m_axi_rd_rlast),
        .m_axi_rd_ruser         (m_axi_rd_ruser),
        .m_axi_rd_rvalid        (m_axi_rd_rvalid),
        .m_axi_rd_rready        (m_axi_rd_rready_o),

        // AXI data write
        .m_axi_wr_awid          (),
        .m_axi_wr_awaddr        (),
        .m_axi_wr_awlen         (),
        .m_axi_wr_awsize        (),
        .m_axi_wr_awburst       (),
        .m_axi_wr_awlock        (),
        .m_axi_wr_awcache       (),
        .m_axi_wr_awprot        (),
        .m_axi_wr_awqos         (),
        .m_axi_wr_awregion      (),
        .m_axi_wr_awuser        (),
        .m_axi_wr_awvalid       (m_axi_wr_awvalid_o),
        .m_axi_wr_awready       (m_axi_wr_awready),
        .m_axi_wr_wdata         (),
        .m_axi_wr_wstrb         (),
        .m_axi_wr_wlast         (),
        .m_axi_wr_wuser         (),
        .m_axi_wr_wvalid        (m_axi_wr_wvalid_o),
        .m_axi_wr_wready        (m_axi_wr_wready),
        .m_axi_wr_bid           (m_axi_wr_bid),
        .m_axi_wr_bresp         (m_axi_wr_bresp),
        .m_axi_wr_buser         (m_axi_wr_buser),
        .m_axi_wr_bvalid        (m_axi_wr_bvalid),
        .m_axi_wr_bready        (m_axi_wr_bready_o),

        // Status/debug
        .cfg_sts_desc_mon_busy          (),
        .cfg_sts_desc_mon_active_txns   (),
        .cfg_sts_desc_mon_error_count   (),
        .cfg_sts_desc_mon_txn_count     (),
        .cfg_sts_desc_mon_conflict_error(),
        .cfg_sts_rdeng_skid_busy        (),
        .cfg_sts_rdeng_mon_active_txns  (),
        .cfg_sts_rdeng_mon_error_count  (),
        .cfg_sts_rdeng_mon_txn_count    (),
        .cfg_sts_rdeng_mon_conflict_error(),
        .cfg_sts_wreng_skid_busy        (),
        .cfg_sts_wreng_mon_active_txns  (),
        .cfg_sts_wreng_mon_error_count  (),
        .cfg_sts_wreng_mon_txn_count    (),
        .cfg_sts_wreng_mon_conflict_error(),

        // Monitor bus
        .mon_valid              (mon_valid_o),
        .mon_ready              (mon_ready),
        .mon_packet             (mon_packet_o)
    );

    // =========================================================================
    // Formal infrastructure
    // =========================================================================
    reg [7:0] f_past_valid = 0;
    always @(posedge clk)
        f_past_valid <= f_past_valid + (f_past_valid < 8'hFF);

    // Reset sequence: assert reset for first 2 cycles
    initial assume (!rst_n);
    always @(posedge clk) begin
        if (f_past_valid >= 2) assume (rst_n);
    end

    // =========================================================================
    // Environment constraints
    // =========================================================================

    // Bound transfer beats for tractability
    always @(posedge clk) begin
        if (rst_n) begin
            assume (cfg_axi_rd_xfer_beats >= 8'd1);
            assume (cfg_axi_rd_xfer_beats <= 8'd4);
            assume (cfg_axi_wr_xfer_beats >= 8'd1);
            assume (cfg_axi_wr_xfer_beats <= 8'd4);
        end
    end

    // =========================================================================
    // P1: Reset clears system_idle to 1 (all channels idle after reset)
    // =========================================================================
    always @(posedge clk) begin
        if (f_past_valid > 0 && $past(!rst_n))
            ap_reset_system_idle: assert (system_idle_o == 1'b1);
    end

    // =========================================================================
    // P2: Reset clears per-channel idle signals
    // =========================================================================
    always @(posedge clk) begin
        if (f_past_valid > 0 && $past(!rst_n))
            ap_reset_sched_idle: assert (scheduler_idle_o == {NC{1'b1}});
    end

    always @(posedge clk) begin
        if (f_past_valid > 0 && $past(!rst_n))
            ap_reset_desc_idle: assert (descriptor_engine_idle_o == {NC{1'b1}});
    end

    // =========================================================================
    // P3: Reset clears AXI output valid signals
    // =========================================================================
    always @(posedge clk) begin
        if (f_past_valid > 0 && $past(!rst_n))
            ap_reset_desc_arvalid: assert (m_axi_desc_arvalid_o == 1'b0);
    end

    always @(posedge clk) begin
        if (f_past_valid > 0 && $past(!rst_n))
            ap_reset_rd_arvalid: assert (m_axi_rd_arvalid_o == 1'b0);
    end

    always @(posedge clk) begin
        if (f_past_valid > 0 && $past(!rst_n))
            ap_reset_wr_awvalid: assert (m_axi_wr_awvalid_o == 1'b0);
    end

    always @(posedge clk) begin
        if (f_past_valid > 0 && $past(!rst_n))
            ap_reset_wr_wvalid: assert (m_axi_wr_wvalid_o == 1'b0);
    end

    // =========================================================================
    // P4: Reset clears scheduler error flags
    // =========================================================================
    always @(posedge clk) begin
        if (f_past_valid > 0 && $past(!rst_n))
            ap_reset_sched_error: assert (sched_error_o == {NC{1'b0}});
    end

    // =========================================================================
    // P5: Reset clears monitor bus valid
    // =========================================================================
    always @(posedge clk) begin
        if (f_past_valid > 0 && $past(!rst_n))
            ap_reset_mon_valid: assert (mon_valid_o == 1'b0);
    end

    // =========================================================================
    // P6: system_idle implies all scheduler_idle bits set
    // =========================================================================
    always @(posedge clk) begin
        if (rst_n && system_idle_o)
            ap_system_idle_implies_sched: assert (scheduler_idle_o == {NC{1'b1}});
    end

    // =========================================================================
    // Cover properties
    // =========================================================================

    // System not idle (some channel active)
    always @(posedge clk) begin
        if (rst_n)
            cp_system_active: cover (!system_idle_o);
    end

    // Descriptor fetch AXI transaction
    always @(posedge clk) begin
        if (rst_n)
            cp_desc_arvalid: cover (m_axi_desc_arvalid_o);
    end

    // Data read AXI transaction
    always @(posedge clk) begin
        if (rst_n)
            cp_rd_arvalid: cover (m_axi_rd_arvalid_o);
    end

    // Data write AXI transaction
    always @(posedge clk) begin
        if (rst_n)
            cp_wr_awvalid: cover (m_axi_wr_awvalid_o);
    end

    // Monitor bus active
    always @(posedge clk) begin
        if (rst_n)
            cp_mon_valid: cover (mon_valid_o);
    end

endmodule
