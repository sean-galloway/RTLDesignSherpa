// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// Formal proof for axi_monitor_reporter
//
// The reporter generates 64-bit monitor-bus packets from a transaction table
// (after sv2v flattening the trans_table becomes a packed bus of
// MAX_TRANSACTIONS * 281 bits).
//
// Properties verified (I/O observable only):
//   P1: Reset clears monbus_valid
//   P2: Reset clears event_count
//   P3: Reset clears event_reported_flags
//   P4: monbus_valid handshake -- once asserted, held until monbus_ready
//   P5: monbus_packet protocol field is AXI (bits [59:57] == 3'b000)
//       when monbus_valid is asserted

module formal_axi_monitor_reporter (
    input wire clk,
    input wire rst_n
);

    // =========================================================================
    // Parameters (small for tractability)
    // =========================================================================
    localparam integer MAX_TRANSACTIONS = 2;
    localparam integer ADDR_WIDTH = 16;
    localparam integer UNIT_ID = 1;
    localparam integer AGENT_ID = 10;
    localparam integer INTR_FIFO_DEPTH = 4;
    localparam integer TRANS_ENTRY_WIDTH = 281;
    localparam integer TABLE_WIDTH = MAX_TRANSACTIONS * TRANS_ENTRY_WIDTH;

    // =========================================================================
    // Free inputs
    // =========================================================================
    (* anyseq *) reg [TABLE_WIDTH-1:0]       trans_table;
    (* anyseq *) reg [MAX_TRANSACTIONS-1:0]  timeout_detected;
    (* anyseq *) reg                         cfg_error_enable;
    (* anyseq *) reg                         cfg_compl_enable;
    (* anyseq *) reg                         cfg_threshold_enable;
    (* anyseq *) reg                         cfg_timeout_enable;
    (* anyseq *) reg                         cfg_perf_enable;
    (* anyseq *) reg                         cfg_debug_enable;
    (* anyseq *) reg                         monbus_ready;
    (* anyseq *) reg [15:0]                  active_trans_threshold;
    (* anyseq *) reg [31:0]                  latency_threshold;

    // =========================================================================
    // DUT outputs
    // =========================================================================
    wire                              monbus_valid;
    wire [63:0]                       monbus_packet;
    wire [15:0]                       event_count;
    wire [15:0]                       perf_completed_count;
    wire [15:0]                       perf_error_count;
    wire [MAX_TRANSACTIONS-1:0]       event_reported_flags;

    // =========================================================================
    // DUT instantiation
    // =========================================================================
    axi_monitor_reporter #(
        .MAX_TRANSACTIONS    (MAX_TRANSACTIONS),
        .ADDR_WIDTH          (ADDR_WIDTH),
        .UNIT_ID             (UNIT_ID),
        .AGENT_ID            (AGENT_ID),
        .IS_READ             (1'b1),
        .ENABLE_PERF_PACKETS (1'b0),
        .INTR_FIFO_DEPTH     (INTR_FIFO_DEPTH)
    ) dut (
        .aclk                   (clk),
        .aresetn                (rst_n),
        .trans_table            (trans_table),
        .timeout_detected       (timeout_detected),
        .cfg_error_enable       (cfg_error_enable),
        .cfg_compl_enable       (cfg_compl_enable),
        .cfg_threshold_enable   (cfg_threshold_enable),
        .cfg_timeout_enable     (cfg_timeout_enable),
        .cfg_perf_enable        (cfg_perf_enable),
        .cfg_debug_enable       (cfg_debug_enable),
        .monbus_ready           (monbus_ready),
        .monbus_valid           (monbus_valid),
        .monbus_packet          (monbus_packet),
        .event_count            (event_count),
        .perf_completed_count   (perf_completed_count),
        .perf_error_count       (perf_error_count),
        .active_trans_threshold (active_trans_threshold),
        .latency_threshold      (latency_threshold),
        .event_reported_flags   (event_reported_flags)
    );

    // =========================================================================
    // Reset / past-valid
    // =========================================================================
    reg [7:0] f_past_valid = 0;
    always @(posedge clk) f_past_valid <= f_past_valid + (f_past_valid < 8'hFF);
    initial assume (!rst_n);
    always @(posedge clk) if (f_past_valid >= 2) assume (rst_n);

    // =========================================================================
    // Environment constraints
    // =========================================================================
    // Disable perf packets (parameter ENABLE_PERF_PACKETS=0 already disables
    // the perf counter path). Disable debug to simplify.
    always @(*) begin
        assume (cfg_perf_enable == 1'b0);
        assume (cfg_debug_enable == 1'b0);
        // threshold logic is complex -- disable for tractability
        assume (cfg_threshold_enable == 1'b0);
    end

    // =========================================================================
    // Properties
    // =========================================================================

    // P1: Reset clears monbus_valid
    always @(posedge clk) begin
        if (f_past_valid > 0 && $past(!rst_n))
            ap_reset_monbus_valid: assert (!monbus_valid);
    end

    // P2: Reset clears event_count
    always @(posedge clk) begin
        if (f_past_valid > 0 && $past(!rst_n))
            ap_reset_event_count: assert (event_count == 16'h0);
    end

    // P3: Reset clears event_reported_flags
    always @(posedge clk) begin
        if (f_past_valid > 0 && $past(!rst_n))
            ap_reset_event_reported: assert (event_reported_flags == {MAX_TRANSACTIONS{1'b0}});
    end

    // P4: monbus_valid handshake: held until ready
    always @(posedge clk) begin
        if (f_past_valid > 0 && rst_n && $past(rst_n))
            if ($past(monbus_valid) && !$past(monbus_ready))
                ap_valid_held: assert (monbus_valid);
    end

    // P5: When monbus_valid, protocol field is AXI (3'b000)
    always @(posedge clk) begin
        if (rst_n && monbus_valid)
            ap_protocol_axi: assert (monbus_packet[59:57] == 3'b000);
    end

    // =========================================================================
    // Cover
    // =========================================================================
    always @(posedge clk) begin
        if (rst_n) begin
            cp_monbus_valid:     cover (monbus_valid);
            cp_monbus_handshake: cover (monbus_valid && monbus_ready);
            cp_event_nonzero:    cover (event_count != 16'h0);
        end
    end

endmodule
