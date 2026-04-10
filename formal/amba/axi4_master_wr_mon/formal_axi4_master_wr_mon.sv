// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 RTL Design Sherpa
//
// Formal proof for axi4_master_wr_mon
//
// This module wraps axi4_master_wr (skid buffers) + axi_monitor_filtered.
// It is purely structural -- no sequential logic of its own.
//
// Properties verified:
//   P1: Reset clears monbus_valid
//   P2: Reset clears busy
//   P3: Protocol field in monbus_packet is AXI (3'b000) when valid
//   P4: active_transactions bounded by MAX_TRANSACTIONS
//   P5: cfg_conflict_error is combinational: |(pkt_mask & err_select)

module formal_axi4_master_wr_mon (
    input wire clk,
    input wire rst_n
);

    // =========================================================================
    // Parameters (small for tractability)
    // =========================================================================
    localparam integer IW = 2;
    localparam integer AW = 8;
    localparam integer DW = 8;
    localparam integer UW = 1;
    localparam integer SW = DW / 8;
    localparam integer MAX_TRANSACTIONS = 2;

    // =========================================================================
    // Free inputs -- slave-side AXI (fub_axi_*)
    // =========================================================================
    (* anyseq *) reg [IW-1:0]  fub_axi_awid;
    (* anyseq *) reg [AW-1:0]  fub_axi_awaddr;
    (* anyseq *) reg [7:0]     fub_axi_awlen;
    (* anyseq *) reg [2:0]     fub_axi_awsize;
    (* anyseq *) reg [1:0]     fub_axi_awburst;
    (* anyseq *) reg           fub_axi_awlock;
    (* anyseq *) reg [3:0]     fub_axi_awcache;
    (* anyseq *) reg [2:0]     fub_axi_awprot;
    (* anyseq *) reg [3:0]     fub_axi_awqos;
    (* anyseq *) reg [3:0]     fub_axi_awregion;
    (* anyseq *) reg [UW-1:0]  fub_axi_awuser;
    (* anyseq *) reg           fub_axi_awvalid;

    (* anyseq *) reg [DW-1:0]  fub_axi_wdata;
    (* anyseq *) reg [SW-1:0]  fub_axi_wstrb;
    (* anyseq *) reg           fub_axi_wlast;
    (* anyseq *) reg [UW-1:0]  fub_axi_wuser;
    (* anyseq *) reg           fub_axi_wvalid;

    (* anyseq *) reg           fub_axi_bready;

    // Free inputs -- master-side AXI (m_axi_*)
    (* anyseq *) reg           m_axi_awready;
    (* anyseq *) reg           m_axi_wready;
    (* anyseq *) reg [IW-1:0]  m_axi_bid;
    (* anyseq *) reg [1:0]     m_axi_bresp;
    (* anyseq *) reg [UW-1:0]  m_axi_buser;
    (* anyseq *) reg           m_axi_bvalid;

    // Free inputs -- monitor config
    (* anyseq *) reg           cfg_monitor_enable;
    (* anyseq *) reg           cfg_error_enable;
    (* anyseq *) reg           cfg_timeout_enable;
    (* anyseq *) reg           cfg_perf_enable;
    (* anyseq *) reg [15:0]    cfg_timeout_cycles;
    (* anyseq *) reg [31:0]    cfg_latency_threshold;

    // Free inputs -- filtering config
    (* anyseq *) reg [15:0]    cfg_axi_pkt_mask;
    (* anyseq *) reg [15:0]    cfg_axi_err_select;
    (* anyseq *) reg [15:0]    cfg_axi_error_mask;
    (* anyseq *) reg [15:0]    cfg_axi_timeout_mask;
    (* anyseq *) reg [15:0]    cfg_axi_compl_mask;
    (* anyseq *) reg [15:0]    cfg_axi_thresh_mask;
    (* anyseq *) reg [15:0]    cfg_axi_perf_mask;
    (* anyseq *) reg [15:0]    cfg_axi_addr_mask;
    (* anyseq *) reg [15:0]    cfg_axi_debug_mask;

    // Free inputs -- monbus downstream
    (* anyseq *) reg           monbus_ready;

    // =========================================================================
    // DUT outputs
    // =========================================================================
    wire                fub_axi_awready;
    wire                fub_axi_wready;
    wire [IW-1:0]       fub_axi_bid;
    wire [1:0]          fub_axi_bresp;
    wire [UW-1:0]       fub_axi_buser;
    wire                fub_axi_bvalid;
    wire [IW-1:0]       m_axi_awid;
    wire [AW-1:0]       m_axi_awaddr;
    wire [7:0]          m_axi_awlen;
    wire [2:0]          m_axi_awsize;
    wire [1:0]          m_axi_awburst;
    wire                m_axi_awlock;
    wire [3:0]          m_axi_awcache;
    wire [2:0]          m_axi_awprot;
    wire [3:0]          m_axi_awqos;
    wire [3:0]          m_axi_awregion;
    wire [UW-1:0]       m_axi_awuser;
    wire                m_axi_awvalid;
    wire [DW-1:0]       m_axi_wdata;
    wire [SW-1:0]       m_axi_wstrb;
    wire                m_axi_wlast;
    wire [UW-1:0]       m_axi_wuser;
    wire                m_axi_wvalid;
    wire                m_axi_bready;
    wire                monbus_valid;
    wire [63:0]         monbus_packet;
    wire                busy;
    wire [7:0]          active_transactions;
    wire [15:0]         error_count;
    wire [31:0]         transaction_count;
    wire                cfg_conflict_error;

    // =========================================================================
    // DUT instantiation
    // =========================================================================
    axi4_master_wr_mon #(
        .SKID_DEPTH_AW      (2),
        .SKID_DEPTH_W       (2),
        .SKID_DEPTH_B       (2),
        .AXI_ID_WIDTH       (IW),
        .AXI_ADDR_WIDTH     (AW),
        .AXI_DATA_WIDTH     (DW),
        .AXI_USER_WIDTH     (UW),
        .UNIT_ID            (1),
        .AGENT_ID           (11),
        .MAX_TRANSACTIONS   (MAX_TRANSACTIONS),
        .ENABLE_FILTERING   (1),
        .ADD_PIPELINE_STAGE (0)
    ) dut (
        .aclk                   (clk),
        .aresetn                (rst_n),
        // Slave side (input)
        .fub_axi_awid           (fub_axi_awid),
        .fub_axi_awaddr         (fub_axi_awaddr),
        .fub_axi_awlen          (fub_axi_awlen),
        .fub_axi_awsize         (fub_axi_awsize),
        .fub_axi_awburst        (fub_axi_awburst),
        .fub_axi_awlock         (fub_axi_awlock),
        .fub_axi_awcache        (fub_axi_awcache),
        .fub_axi_awprot         (fub_axi_awprot),
        .fub_axi_awqos          (fub_axi_awqos),
        .fub_axi_awregion       (fub_axi_awregion),
        .fub_axi_awuser         (fub_axi_awuser),
        .fub_axi_awvalid        (fub_axi_awvalid),
        .fub_axi_awready        (fub_axi_awready),
        .fub_axi_wdata          (fub_axi_wdata),
        .fub_axi_wstrb          (fub_axi_wstrb),
        .fub_axi_wlast          (fub_axi_wlast),
        .fub_axi_wuser          (fub_axi_wuser),
        .fub_axi_wvalid         (fub_axi_wvalid),
        .fub_axi_wready         (fub_axi_wready),
        .fub_axi_bid            (fub_axi_bid),
        .fub_axi_bresp          (fub_axi_bresp),
        .fub_axi_buser          (fub_axi_buser),
        .fub_axi_bvalid         (fub_axi_bvalid),
        .fub_axi_bready         (fub_axi_bready),
        // Master side (output)
        .m_axi_awid             (m_axi_awid),
        .m_axi_awaddr           (m_axi_awaddr),
        .m_axi_awlen            (m_axi_awlen),
        .m_axi_awsize           (m_axi_awsize),
        .m_axi_awburst          (m_axi_awburst),
        .m_axi_awlock           (m_axi_awlock),
        .m_axi_awcache          (m_axi_awcache),
        .m_axi_awprot           (m_axi_awprot),
        .m_axi_awqos            (m_axi_awqos),
        .m_axi_awregion         (m_axi_awregion),
        .m_axi_awuser           (m_axi_awuser),
        .m_axi_awvalid          (m_axi_awvalid),
        .m_axi_awready          (m_axi_awready),
        .m_axi_wdata            (m_axi_wdata),
        .m_axi_wstrb            (m_axi_wstrb),
        .m_axi_wlast            (m_axi_wlast),
        .m_axi_wuser            (m_axi_wuser),
        .m_axi_wvalid           (m_axi_wvalid),
        .m_axi_wready           (m_axi_wready),
        .m_axi_bid              (m_axi_bid),
        .m_axi_bresp            (m_axi_bresp),
        .m_axi_buser            (m_axi_buser),
        .m_axi_bvalid           (m_axi_bvalid),
        .m_axi_bready           (m_axi_bready),
        // Monitor config
        .cfg_monitor_enable     (cfg_monitor_enable),
        .cfg_error_enable       (cfg_error_enable),
        .cfg_timeout_enable     (cfg_timeout_enable),
        .cfg_perf_enable        (cfg_perf_enable),
        .cfg_timeout_cycles     (cfg_timeout_cycles),
        .cfg_latency_threshold  (cfg_latency_threshold),
        // Filtering config
        .cfg_axi_pkt_mask       (cfg_axi_pkt_mask),
        .cfg_axi_err_select     (cfg_axi_err_select),
        .cfg_axi_error_mask     (cfg_axi_error_mask),
        .cfg_axi_timeout_mask   (cfg_axi_timeout_mask),
        .cfg_axi_compl_mask     (cfg_axi_compl_mask),
        .cfg_axi_thresh_mask    (cfg_axi_thresh_mask),
        .cfg_axi_perf_mask      (cfg_axi_perf_mask),
        .cfg_axi_addr_mask      (cfg_axi_addr_mask),
        .cfg_axi_debug_mask     (cfg_axi_debug_mask),
        // Monitor bus
        .monbus_valid           (monbus_valid),
        .monbus_ready           (monbus_ready),
        .monbus_packet          (monbus_packet),
        // Status
        .busy                   (busy),
        .active_transactions    (active_transactions),
        .error_count            (error_count),
        .transaction_count      (transaction_count),
        .cfg_conflict_error     (cfg_conflict_error)
    );

    // =========================================================================
    // Reset / past-valid
    // =========================================================================
    reg [7:0] f_past_valid = 0;
    always @(posedge clk) f_past_valid <= f_past_valid + (f_past_valid < 8'hFF);
    initial assume (!rst_n);
    always @(posedge clk) begin
        if (f_past_valid < 5)
            assume (!rst_n);
        else
            assume (rst_n);
    end

    // =========================================================================
    // Environment constraints
    // =========================================================================
    always @(*) begin
        assume (fub_axi_awlen <= 8'd3);
        assume (cfg_perf_enable == 1'b0);
        assume (cfg_timeout_enable == 1'b0);
    end

    // During reset, AXI valid signals should be deasserted (standard practice)
    always @(*) begin
        if (!rst_n) begin
            assume (fub_axi_awvalid == 1'b0);
            assume (fub_axi_wvalid == 1'b0);
            assume (m_axi_bvalid == 1'b0);
        end
    end

    // =========================================================================
    // P1: Reset clears monbus_valid
    // =========================================================================
    always @(posedge clk) begin
        if (f_past_valid >= 3 && !rst_n)
            ap_reset_monbus_valid: assert (monbus_valid == 1'b0);
    end

    // =========================================================================
    // P2: Reset clears busy
    // =========================================================================
    always @(posedge clk) begin
        if (f_past_valid >= 3 && !rst_n)
            ap_reset_busy: assert (busy == 1'b0);
    end

    // =========================================================================
    // P3: Protocol field is AXI (3'b000) when monbus_valid
    // =========================================================================
    always @(posedge clk) begin
        if (rst_n && monbus_valid)
            ap_protocol_axi: assert (monbus_packet[59:57] == 3'b000);
    end

    // =========================================================================
    // P4: active_transactions bounded by MAX_TRANSACTIONS
    // =========================================================================
    always @(posedge clk) begin
        if (rst_n)
            ap_active_bounded: assert (active_transactions <= 8'(MAX_TRANSACTIONS));
    end

    // =========================================================================
    // P5: cfg_conflict_error is combinational
    // =========================================================================
    always @(*) begin
        ap_conflict_combinational:
            assert (cfg_conflict_error == (|(cfg_axi_pkt_mask & cfg_axi_err_select)));
    end

    // =========================================================================
    // Cover properties
    // =========================================================================
    always @(posedge clk) begin
        if (rst_n) begin
            cp_monbus_valid:     cover (monbus_valid);
            cp_monbus_handshake: cover (monbus_valid && monbus_ready);
            cp_busy:             cover (busy);
        end
    end

endmodule
