// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 RTL Design Sherpa
//
// Formal proof for axi4_slave_rd_mon
//
// This module wraps axi4_slave_rd (skid buffers) + axi_monitor_filtered.
// It is purely structural -- no sequential logic of its own.
//
// Properties verified:
//   P1: Reset clears monbus_valid
//   P2: Reset clears busy
//   P3: Protocol field in monbus_packet is AXI (3'b000) when valid
//   P4: active_transactions bounded by MAX_TRANSACTIONS
//   P5: cfg_conflict_error is combinational: |(pkt_mask & err_select)

module formal_axi4_slave_rd_mon (
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
    // Free inputs -- slave-side AXI (s_axi_*)
    // =========================================================================
    (* anyseq *) reg [IW-1:0]  s_axi_arid;
    (* anyseq *) reg [AW-1:0]  s_axi_araddr;
    (* anyseq *) reg [7:0]     s_axi_arlen;
    (* anyseq *) reg [2:0]     s_axi_arsize;
    (* anyseq *) reg [1:0]     s_axi_arburst;
    (* anyseq *) reg           s_axi_arlock;
    (* anyseq *) reg [3:0]     s_axi_arcache;
    (* anyseq *) reg [2:0]     s_axi_arprot;
    (* anyseq *) reg [3:0]     s_axi_arqos;
    (* anyseq *) reg [3:0]     s_axi_arregion;
    (* anyseq *) reg [UW-1:0]  s_axi_aruser;
    (* anyseq *) reg           s_axi_arvalid;
    (* anyseq *) reg           s_axi_rready;

    // Free inputs -- master-side AXI (fub_axi_*)
    (* anyseq *) reg           fub_axi_arready;
    (* anyseq *) reg [IW-1:0]  fub_axi_rid;
    (* anyseq *) reg [DW-1:0]  fub_axi_rdata;
    (* anyseq *) reg [1:0]     fub_axi_rresp;
    (* anyseq *) reg           fub_axi_rlast;
    (* anyseq *) reg [UW-1:0]  fub_axi_ruser;
    (* anyseq *) reg           fub_axi_rvalid;

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
    wire                s_axi_arready;
    wire [IW-1:0]       s_axi_rid;
    wire [DW-1:0]       s_axi_rdata;
    wire [1:0]          s_axi_rresp;
    wire                s_axi_rlast;
    wire [UW-1:0]       s_axi_ruser;
    wire                s_axi_rvalid;
    wire [IW-1:0]       fub_axi_arid;
    wire [AW-1:0]       fub_axi_araddr;
    wire [7:0]          fub_axi_arlen;
    wire [2:0]          fub_axi_arsize;
    wire [1:0]          fub_axi_arburst;
    wire                fub_axi_arlock;
    wire [3:0]          fub_axi_arcache;
    wire [2:0]          fub_axi_arprot;
    wire [3:0]          fub_axi_arqos;
    wire [3:0]          fub_axi_arregion;
    wire [UW-1:0]       fub_axi_aruser;
    wire                fub_axi_arvalid;
    wire                fub_axi_rready;
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
    axi4_slave_rd_mon #(
        .SKID_DEPTH_AR      (2),
        .SKID_DEPTH_R       (2),
        .AXI_ID_WIDTH       (IW),
        .AXI_ADDR_WIDTH     (AW),
        .AXI_DATA_WIDTH     (DW),
        .AXI_USER_WIDTH     (UW),
        .UNIT_ID            (2),
        .AGENT_ID           (20),
        .MAX_TRANSACTIONS   (MAX_TRANSACTIONS),
        .ENABLE_FILTERING   (1),
        .ADD_PIPELINE_STAGE (0)
    ) dut (
        .aclk                   (clk),
        .aresetn                (rst_n),
        // Slave side (input)
        .s_axi_arid             (s_axi_arid),
        .s_axi_araddr           (s_axi_araddr),
        .s_axi_arlen            (s_axi_arlen),
        .s_axi_arsize           (s_axi_arsize),
        .s_axi_arburst          (s_axi_arburst),
        .s_axi_arlock           (s_axi_arlock),
        .s_axi_arcache          (s_axi_arcache),
        .s_axi_arprot           (s_axi_arprot),
        .s_axi_arqos            (s_axi_arqos),
        .s_axi_arregion         (s_axi_arregion),
        .s_axi_aruser           (s_axi_aruser),
        .s_axi_arvalid          (s_axi_arvalid),
        .s_axi_arready          (s_axi_arready),
        .s_axi_rid              (s_axi_rid),
        .s_axi_rdata            (s_axi_rdata),
        .s_axi_rresp            (s_axi_rresp),
        .s_axi_rlast            (s_axi_rlast),
        .s_axi_ruser            (s_axi_ruser),
        .s_axi_rvalid           (s_axi_rvalid),
        .s_axi_rready           (s_axi_rready),
        // Master side (output to backend)
        .fub_axi_arid           (fub_axi_arid),
        .fub_axi_araddr         (fub_axi_araddr),
        .fub_axi_arlen          (fub_axi_arlen),
        .fub_axi_arsize         (fub_axi_arsize),
        .fub_axi_arburst        (fub_axi_arburst),
        .fub_axi_arlock         (fub_axi_arlock),
        .fub_axi_arcache        (fub_axi_arcache),
        .fub_axi_arprot         (fub_axi_arprot),
        .fub_axi_arqos          (fub_axi_arqos),
        .fub_axi_arregion       (fub_axi_arregion),
        .fub_axi_aruser         (fub_axi_aruser),
        .fub_axi_arvalid        (fub_axi_arvalid),
        .fub_axi_arready        (fub_axi_arready),
        .fub_axi_rid            (fub_axi_rid),
        .fub_axi_rdata          (fub_axi_rdata),
        .fub_axi_rresp          (fub_axi_rresp),
        .fub_axi_rlast          (fub_axi_rlast),
        .fub_axi_ruser          (fub_axi_ruser),
        .fub_axi_rvalid         (fub_axi_rvalid),
        .fub_axi_rready         (fub_axi_rready),
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
        assume (s_axi_arlen <= 8'd3);
        assume (cfg_perf_enable == 1'b0);
        assume (cfg_timeout_enable == 1'b0);
    end

    // During reset, AXI valid signals should be deasserted (standard practice)
    always @(*) begin
        if (!rst_n) begin
            assume (s_axi_arvalid == 1'b0);
            assume (fub_axi_rvalid == 1'b0);
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
