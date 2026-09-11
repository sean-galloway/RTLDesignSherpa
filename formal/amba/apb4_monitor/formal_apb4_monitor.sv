// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// Formal proof for apb4_monitor -- monitor bus output properties
//
// NOTE: The apb4_monitor uses unpacked struct arrays (transaction table)
// which require memory_map in Yosys. Properties that depend on internal
// transaction table state (active_count, error_count) are not reliably
// provable through sv2v + memory_map due to initialization artifacts.
// We focus on I/O-observable properties.
//
// Properties verified:
//   P1: Reset clears monbus_valid (skid buffer output)
//   P2: monbus_packet protocol field is APB (bits [108:105] == 4'h2) when valid
//   P3: monbus_valid handshake -- valid held until ready

module formal_apb4_monitor (
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
    localparam logic [7:0]  UNIT_ID  = 8'h01;
    localparam logic [15:0] AGENT_ID = 16'h000A;

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

    // Broadcast monitor time
    (* anyseq *) reg [63:0]       i_mon_time;

    // =========================================================================
    // DUT outputs
    // =========================================================================
    wire              monbus_valid;
    wire [127:0]      monbus_packet;
    wire [63:0]       monbus_timestamp;
    wire [7:0]        active_count;
    wire [15:0]       error_count;
    wire [31:0]       transaction_count;

    // =========================================================================
    // DUT instantiation
    // =========================================================================
    apb4_monitor #(
        .ADDR_WIDTH         (AW),
        .DATA_WIDTH         (DW),
        .UNIT_ID            (UNIT_ID),
        .AGENT_ID           (AGENT_ID),
        .MAX_TRANSACTIONS   (MAX_TRANS),
        .MONITOR_FIFO_DEPTH (FIFO_DEPTH)
    ) dut (
        .aclk                   (clk),
        .aresetn                (rst_n),
        .i_mon_time             (i_mon_time),
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
        .monbus_timestamp       (monbus_timestamp),
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
            ap_protocol_apb: assert (monbus_packet[108:105] == 4'h2);
    end

    // P3: monbus_valid handshake -- once asserted, held until ready
    //     (Skid buffer implements this: rd_valid held until rd_ready)
    always @(posedge clk) begin
        if (f_past_valid > 0 && rst_n && $past(rst_n))
            if ($past(monbus_valid) && !$past(monbus_ready))
                ap_valid_held: assert (monbus_valid);
    end

    // =========================================================================
    // Transaction-table properties.
    //
    // Added 2026-09-11 with the multiple-driver fix that first let this proof
    // elaborate. The three properties above (reset, protocol tag, valid held)
    // say nothing about the table, and a mutation that never marks a terminal
    // entry reported -- so no slot is ever freed and the monitor wedges after
    // MAX_TRANSACTIONS -- passed all of them. cp_drained is what catches it:
    // with slots leaking, occupancy can never come back to zero.
    // =========================================================================
    wire f_cmd_hs = cmd_valid && cmd_ready;
    wire f_rsp_hs = rsp_valid && rsp_ready;

    // rst_n is free for the first two clocks, and the async reset needs a
    // clock to flush the arbitrary initial state sby hands us (setundef
    // -init -expose). Counter properties only hold once that has happened:
    // without this guard error_count is seen "decreasing" from 0xFFFF to 0,
    // which is the reset working, not the counter misbehaving.
    reg f_settled = 1'b0;
    always @(posedge clk) f_settled <= rst_n && $past(rst_n) && f_past_valid > 2;

    // P4: occupancy never exceeds the table
    always @(posedge clk)
        if (f_settled)
            ap_active_bound: assert (active_count <= MAX_TRANS);

    // P5: occupancy only moves by an allocation or a retirement, so it can
    // rise by at most one per clock and fall by at most the table depth
    always @(posedge clk)
        if (f_settled && rst_n && $past(rst_n)) begin
            ap_active_step_up: assert (active_count <= $past(active_count) + 8'(($past(f_cmd_hs) ? 1 : 0)));
            ap_active_no_rise_without_cmd: assert (!(!$past(f_cmd_hs) && active_count > $past(active_count)));
        end

    // P6: transaction_count counts allocations, never decreases, and moves by
    // at most one per clock
    always @(posedge clk)
        if (f_settled && rst_n && $past(rst_n)) begin
            ap_tc_monotonic: assert (transaction_count >= $past(transaction_count));
            ap_tc_step:      assert (transaction_count <= $past(transaction_count) + 32'd1);
            ap_tc_needs_rsp: assert (!(!$past(f_rsp_hs) && transaction_count != $past(transaction_count)));
        end

    // P7: error_count never decreases
    always @(posedge clk)
        if (f_settled && rst_n && $past(rst_n))
            ap_ec_monotonic: assert (error_count >= $past(error_count));

    // =========================================================================
    // Cover points
    // =========================================================================
    always @(posedge clk) begin
        if (rst_n) begin
            cp_monbus_packet: cover (monbus_valid);
            cp_cmd_handshake: cover (cmd_valid && cmd_ready);
            cp_rsp_handshake: cover (rsp_valid && rsp_ready);
            cp_error_event:   cover (monbus_valid && monbus_packet[127:124] == 4'h0);
            cp_table_full:    cover (active_count == MAX_TRANS);
            // The retirement witness: transactions happened AND every slot
            // came back. A monitor that leaks slots cannot reach this.
            cp_drained:       cover (f_past_valid > 8 && transaction_count >= 32'd2 && active_count == 8'd0);
        end
    end

endmodule
