// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// Formal proof for apb_monitor -- monitor bus output properties
//
// NOTE: The apb_monitor uses unpacked struct arrays (transaction table)
// which require memory_map in Yosys. Properties that depend on internal
// transaction table state (active_count, error_count) are not reliably
// provable through sv2v + memory_map due to initialization artifacts.
// We focus on I/O-observable properties.
//
// Properties verified:
//   P1: Reset clears monbus_valid (skid buffer output)
//   P2: monbus_packet protocol field is APB (bits [59:57] == 3'b010) when valid
//   P3: monbus_valid handshake -- valid held until ready

module formal_apb_monitor (
    input logic clk,
    input logic rst_n
);

    // =========================================================================
    // Parameters (small for tractability)
    // =========================================================================
    localparam int AW = 12;
    localparam int DW = 32;
    localparam int SW = DW / 8;
    localparam int MAX_TRANS = 2;
    localparam int FIFO_DEPTH = 4;

    // =========================================================================
    // Free inputs (driven by formal engine)
    // =========================================================================
    (* anyseq *) reg              cmd_valid;
    (* anyseq *) reg              cmd_ready;
    (* anyseq *) reg              cmd_pwrite;
    (* anyseq *) reg [AW-1:0]     cmd_paddr;
    (* anyseq *) reg [DW-1:0]     cmd_pwdata;
    (* anyseq *) reg [SW-1:0]     cmd_pstrb;
    (* anyseq *) reg [2:0]        cmd_pprot;

    (* anyseq *) reg              rsp_valid;
    (* anyseq *) reg              rsp_ready;
    (* anyseq *) reg [DW-1:0]     rsp_prdata;
    (* anyseq *) reg              rsp_pslverr;

    (* anyseq *) reg              cfg_error_enable;
    (* anyseq *) reg              cfg_timeout_enable;
    (* anyseq *) reg              cfg_protocol_enable;
    (* anyseq *) reg              cfg_slverr_enable;
    (* anyseq *) reg              cfg_perf_enable;
    (* anyseq *) reg              cfg_latency_enable;
    (* anyseq *) reg              cfg_throughput_enable;
    (* anyseq *) reg              cfg_debug_enable;
    (* anyseq *) reg              cfg_trans_debug_enable;
    (* anyseq *) reg [3:0]        cfg_debug_level;
    (* anyseq *) reg [15:0]       cfg_cmd_timeout_cnt;
    (* anyseq *) reg [15:0]       cfg_rsp_timeout_cnt;
    (* anyseq *) reg [31:0]       cfg_latency_threshold;
    (* anyseq *) reg [15:0]       cfg_throughput_threshold;

    (* anyseq *) reg              monbus_ready;

    // =========================================================================
    // DUT outputs
    // =========================================================================
    wire              monbus_valid;
    wire [63:0]       monbus_packet;
    wire [7:0]        active_count;
    wire [15:0]       error_count;
    wire [31:0]       transaction_count;

    // =========================================================================
    // DUT instantiation
    // =========================================================================
    apb_monitor #(
        .ADDR_WIDTH         (AW),
        .DATA_WIDTH         (DW),
        .UNIT_ID            (1),
        .AGENT_ID           (10),
        .MAX_TRANSACTIONS   (MAX_TRANS),
        .MONITOR_FIFO_DEPTH (FIFO_DEPTH)
    ) dut (
        .aclk                   (clk),
        .aresetn                (rst_n),
        .cmd_valid              (cmd_valid),
        .cmd_ready              (cmd_ready),
        .cmd_pwrite             (cmd_pwrite),
        .cmd_paddr              (cmd_paddr),
        .cmd_pwdata             (cmd_pwdata),
        .cmd_pstrb              (cmd_pstrb),
        .cmd_pprot              (cmd_pprot),
        .rsp_valid              (rsp_valid),
        .rsp_ready              (rsp_ready),
        .rsp_prdata             (rsp_prdata),
        .rsp_pslverr            (rsp_pslverr),
        .cfg_error_enable       (cfg_error_enable),
        .cfg_timeout_enable     (cfg_timeout_enable),
        .cfg_protocol_enable    (cfg_protocol_enable),
        .cfg_slverr_enable      (cfg_slverr_enable),
        .cfg_perf_enable        (cfg_perf_enable),
        .cfg_latency_enable     (cfg_latency_enable),
        .cfg_throughput_enable  (cfg_throughput_enable),
        .cfg_debug_enable       (cfg_debug_enable),
        .cfg_trans_debug_enable (cfg_trans_debug_enable),
        .cfg_debug_level        (cfg_debug_level),
        .cfg_cmd_timeout_cnt    (cfg_cmd_timeout_cnt),
        .cfg_rsp_timeout_cnt    (cfg_rsp_timeout_cnt),
        .cfg_latency_threshold  (cfg_latency_threshold),
        .cfg_throughput_threshold(cfg_throughput_threshold),
        .monbus_valid           (monbus_valid),
        .monbus_ready           (monbus_ready),
        .monbus_packet          (monbus_packet),
        .active_count           (active_count),
        .error_count            (error_count),
        .transaction_count      (transaction_count)
    );

    // =========================================================================
    // Reset and past-valid infrastructure
    // =========================================================================
    reg [7:0] f_past_valid = 0;
    always @(posedge clk) f_past_valid <= f_past_valid + (f_past_valid < 8'hFF);
    initial assume (!rst_n);
    always @(posedge clk) if (f_past_valid >= 2) assume (rst_n);

    // =========================================================================
    // Properties
    // =========================================================================

    // P1: Reset clears monbus_valid (output of skid buffer)
    always @(posedge clk) begin
        if (f_past_valid > 0 && $past(!rst_n))
            ap_reset_monbus_valid: assert (!monbus_valid);
    end

    // P2: monbus_packet protocol field is APB when valid
    always @(posedge clk) begin
        if (rst_n && monbus_valid)
            ap_protocol_apb: assert (monbus_packet[59:57] == 3'b010);
    end

    // P3: monbus_valid handshake -- once asserted, held until ready
    //     (Skid buffer implements this: rd_valid held until rd_ready)
    always @(posedge clk) begin
        if (f_past_valid > 0 && rst_n && $past(rst_n))
            if ($past(monbus_valid) && !$past(monbus_ready))
                ap_valid_held: assert (monbus_valid);
    end

    // =========================================================================
    // Cover points
    // =========================================================================
    always @(posedge clk) begin
        if (rst_n) begin
            cp_monbus_packet: cover (monbus_valid);
            cp_cmd_handshake: cover (cmd_valid && cmd_ready);
            cp_rsp_handshake: cover (rsp_valid && rsp_ready);
            cp_error_event:   cover (monbus_valid && monbus_packet[63:60] == 4'h0);
        end
    end

endmodule
