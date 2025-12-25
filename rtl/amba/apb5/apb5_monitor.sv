// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: apb5_monitor
// Purpose: APB5 Monitor with AMBA5 extension monitoring
//
// APB5 Extensions Monitored:
// - PWAKEUP: Wake-up signal events
// - PAUSER/PWUSER: User request/write signal tracking
// - PRUSER/PBUSER: User response signal tracking
// - Parity error detection (when enabled)
//
// This module extends the APB4 monitoring capabilities to include
// APB5-specific events like wake-up sequences, user signal changes,
// and parity error detection.
//
// Documentation: rtl/amba/PRD.md
// Subsystem: amba
//
// Author: sean galloway
// Created: 2025-12-21

`timescale 1ns / 1ps

`include "reset_defs.svh"

module apb5_monitor
    import monitor_common_pkg::*;
    import monitor_amba4_pkg::*;
    import monitor_amba5_pkg::*;
#(
    parameter int ADDR_WIDTH          = 32,
    parameter int DATA_WIDTH          = 32,
    parameter int AUSER_WIDTH         = 4,
    parameter int WUSER_WIDTH         = 4,
    parameter int RUSER_WIDTH         = 4,
    parameter int BUSER_WIDTH         = 4,
    parameter int UNIT_ID             = 1,     // 4-bit Unit ID
    parameter int AGENT_ID            = 10,    // 8-bit Agent ID
    parameter int MAX_TRANSACTIONS    = 4,     // APB is typically single outstanding
    parameter int MONITOR_FIFO_DEPTH  = 8,     // Monitor packet FIFO depth
    parameter bit ENABLE_PARITY_MON   = 0,     // Enable parity monitoring

    // Short params
    parameter int AW                  = ADDR_WIDTH,
    parameter int DW                  = DATA_WIDTH,
    parameter int SW                  = DW/8,
    parameter int AUW                 = AUSER_WIDTH,
    parameter int WUW                 = WUSER_WIDTH,
    parameter int RUW                 = RUSER_WIDTH,
    parameter int BUW                 = BUSER_WIDTH
)
(
    // Clock and Reset
    input  logic                     aclk,
    input  logic                     aresetn,

    // Command Interface Monitoring
    input  logic                     cmd_valid,
    input  logic                     cmd_ready,
    input  logic                     cmd_pwrite,
    input  logic [AW-1:0]            cmd_paddr,
    input  logic [DW-1:0]            cmd_pwdata,
    input  logic [SW-1:0]            cmd_pstrb,
    input  logic [2:0]               cmd_pprot,
    input  logic [AUW-1:0]           cmd_pauser,
    input  logic [WUW-1:0]           cmd_pwuser,

    // Response Interface Monitoring
    input  logic                     rsp_valid,
    input  logic                     rsp_ready,
    input  logic [DW-1:0]            rsp_prdata,
    input  logic                     rsp_pslverr,
    input  logic [RUW-1:0]           rsp_pruser,
    input  logic [BUW-1:0]           rsp_pbuser,

    // APB5 Wake-up Monitoring
    input  logic                     apb5_pwakeup,

    // APB5 Parity Error Inputs (when ENABLE_PARITY_MON=1)
    input  logic                     parity_error_wdata,
    input  logic                     parity_error_rdata,
    input  logic                     parity_error_ctrl,

    // Configuration - Error Detection
    input  logic                     cfg_error_enable,
    input  logic                     cfg_timeout_enable,
    input  logic                     cfg_protocol_enable,
    input  logic                     cfg_slverr_enable,
    input  logic                     cfg_parity_enable,

    // Configuration - APB5 Event Enables
    input  logic                     cfg_wakeup_enable,
    input  logic                     cfg_user_enable,

    // Configuration - Performance Monitoring
    input  logic                     cfg_perf_enable,
    input  logic                     cfg_latency_enable,

    // Configuration - Thresholds
    input  logic [15:0]              cfg_cmd_timeout_cnt,
    input  logic [15:0]              cfg_rsp_timeout_cnt,
    input  logic [31:0]              cfg_latency_threshold,
    input  logic [15:0]              cfg_wakeup_timeout_cnt,

    // Monitor bus interface
    output logic                     monbus_valid,
    input  logic                     monbus_ready,
    output logic [63:0]              monbus_packet,

    // Status outputs
    output logic [7:0]               active_count,
    output logic [15:0]              error_count,
    output logic [31:0]              transaction_count,
    output logic                     wakeup_active
);

    // -------------------------------------------------------------------------
    // Internal Signals
    // -------------------------------------------------------------------------

    // Transaction tracking
    bus_transaction_t r_trans_table[MAX_TRANSACTIONS];
    logic [7:0] r_active_count;
    logic [15:0] r_error_count;
    logic [31:0] r_transaction_count;

    // Transaction state tracking
    typedef enum logic [1:0] {
        CMD_RSP_IDLE     = 2'b00,
        CMD_RSP_CMD_SENT = 2'b01,
        CMD_RSP_COMPLETE = 2'b10
    } cmd_rsp_state_t;

    cmd_rsp_state_t r_trans_state;
    cmd_rsp_state_t w_next_trans_state;
    logic w_state_change;

    // Timing tracking
    logic [31:0] r_timestamp;
    logic [31:0] r_cmd_start_time;
    logic [15:0] r_cmd_timeout_timer;
    logic [15:0] r_rsp_timeout_timer;

    // Wake-up tracking
    logic r_pwakeup_prev;
    logic r_wakeup_active;
    logic [15:0] r_wakeup_timer;
    logic w_wakeup_rising;
    logic w_wakeup_falling;
    logic w_wakeup_timeout;

    // Transaction management
    logic [MAX_TRANSACTIONS-1:0] w_free_slot;
    logic [$clog2(MAX_TRANSACTIONS)-1:0] w_free_idx;
    logic w_has_free_slot;
    logic [MAX_TRANSACTIONS-1:0] w_active_trans;
    logic [$clog2(MAX_TRANSACTIONS)-1:0] w_active_idx;
    logic w_has_active_trans;
    logic [MAX_TRANSACTIONS-1:0] w_completed_trans;

    // Command/Response handshake detection
    logic w_cmd_handshake;
    logic w_rsp_handshake;

    // Error detection
    logic w_cmd_timeout;
    logic w_rsp_timeout;
    logic w_protocol_violation;
    logic w_parity_error;
    logic w_latency_threshold_exceeded;

    // Performance metrics
    logic [31:0] w_current_latency;

    // Event generation
    logic w_generate_error_event;
    logic w_generate_timeout_event;
    logic w_generate_perf_event;
    logic w_generate_wakeup_event;
    logic w_generate_parity_event;
    logic w_generate_completion_event;
    logic [3:0] w_error_event_code;
    logic [3:0] w_timeout_event_code;
    logic [3:0] w_wakeup_event_code;
    logic [3:0] w_parity_event_code;

    // Monitor packet FIFO
    typedef struct packed {
        logic [3:0]  packet_type;
        logic [3:0]  event_code;
        logic [31:0] event_data;
        logic [7:0]  aux_data;
    } monitor_entry_t;

    logic w_fifo_wr_valid;
    logic w_fifo_wr_ready;
    monitor_entry_t w_fifo_wr_data;
    logic w_fifo_rd_valid;
    logic w_fifo_rd_ready;
    monitor_entry_t w_fifo_rd_data;

    // -------------------------------------------------------------------------
    // Assign Outputs
    // -------------------------------------------------------------------------
    assign active_count = r_active_count;
    assign error_count = r_error_count;
    assign transaction_count = r_transaction_count;
    assign wakeup_active = r_wakeup_active;

    // -------------------------------------------------------------------------
    // Handshake Detection
    // -------------------------------------------------------------------------
    assign w_cmd_handshake = cmd_valid && cmd_ready;
    assign w_rsp_handshake = rsp_valid && rsp_ready;

    // -------------------------------------------------------------------------
    // Timestamp Counter
    // -------------------------------------------------------------------------
    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_timestamp <= '0;
        end else begin
            r_timestamp <= r_timestamp + 1'b1;
        end
    )

    // -------------------------------------------------------------------------
    // Wake-up Tracking (APB5 specific)
    // -------------------------------------------------------------------------
    assign w_wakeup_rising = apb5_pwakeup && !r_pwakeup_prev;
    assign w_wakeup_falling = !apb5_pwakeup && r_pwakeup_prev;

    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_pwakeup_prev <= 1'b0;
            r_wakeup_active <= 1'b0;
            r_wakeup_timer <= '0;
        end else begin
            r_pwakeup_prev <= apb5_pwakeup;

            if (w_wakeup_rising) begin
                r_wakeup_active <= 1'b1;
                r_wakeup_timer <= '0;
            end else if (w_wakeup_falling) begin
                r_wakeup_active <= 1'b0;
                r_wakeup_timer <= '0;
            end else if (r_wakeup_active) begin
                r_wakeup_timer <= r_wakeup_timer + 1'b1;
            end
        end
    )

    assign w_wakeup_timeout = r_wakeup_active &&
                              (r_wakeup_timer >= cfg_wakeup_timeout_cnt) &&
                              (cfg_wakeup_enable);

    // -------------------------------------------------------------------------
    // Transaction State Machine
    // -------------------------------------------------------------------------
    always_comb begin
        w_next_trans_state = r_trans_state;

        case (r_trans_state)
            CMD_RSP_IDLE: begin
                if (w_cmd_handshake) begin
                    w_next_trans_state = CMD_RSP_CMD_SENT;
                end
            end

            CMD_RSP_CMD_SENT: begin
                if (w_rsp_handshake) begin
                    w_next_trans_state = CMD_RSP_COMPLETE;
                end
            end

            CMD_RSP_COMPLETE: begin
                w_next_trans_state = CMD_RSP_IDLE;
            end

            default: begin
                w_next_trans_state = CMD_RSP_IDLE;
            end
        endcase
    end

    assign w_state_change = (w_next_trans_state != r_trans_state);

    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_trans_state <= CMD_RSP_IDLE;
        end else begin
            r_trans_state <= w_next_trans_state;
        end
    )

    // -------------------------------------------------------------------------
    // Transaction Table Management
    // -------------------------------------------------------------------------

    // Find free slot
    always_comb begin
        w_free_slot = '0;
        w_free_idx = '0;
        w_has_free_slot = 1'b0;

        for (int i = 0; i < MAX_TRANSACTIONS; i++) begin
            if (!r_trans_table[i].valid && !w_has_free_slot) begin
                w_free_slot[i] = 1'b1;
                w_free_idx = i[$clog2(MAX_TRANSACTIONS)-1:0];
                w_has_free_slot = 1'b1;
            end
        end
    end

    // Find active transaction
    always_comb begin
        w_active_trans = '0;
        w_active_idx = '0;
        w_has_active_trans = 1'b0;

        for (int i = 0; i < MAX_TRANSACTIONS; i++) begin
            if (r_trans_table[i].valid &&
                (r_trans_table[i].state == TRANS_ADDR_PHASE ||
                 r_trans_table[i].state == TRANS_DATA_PHASE) &&
                !w_has_active_trans) begin
                w_active_trans[i] = 1'b1;
                w_active_idx = i[$clog2(MAX_TRANSACTIONS)-1:0];
                w_has_active_trans = 1'b1;
            end
        end
    end

    // Find completed transactions
    always_comb begin
        w_completed_trans = '0;

        for (int i = 0; i < MAX_TRANSACTIONS; i++) begin
            if (r_trans_table[i].valid &&
                (r_trans_table[i].state == TRANS_COMPLETE ||
                 r_trans_table[i].state == TRANS_ERROR) &&
                r_trans_table[i].event_reported) begin
                w_completed_trans[i] = 1'b1;
            end
        end
    end

    // -------------------------------------------------------------------------
    // Transaction Lifecycle Management
    // -------------------------------------------------------------------------
    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            for (int i = 0; i < MAX_TRANSACTIONS; i++) begin
                r_trans_table[i] <= '0;
            end
            r_active_count <= '0;
            r_transaction_count <= '0;
            r_cmd_start_time <= '0;
        end else begin

            // Command handshake - start new transaction
            if (w_cmd_handshake && w_has_free_slot) begin
                r_trans_table[w_free_idx].valid <= 1'b1;
                r_trans_table[w_free_idx].state <= TRANS_DATA_PHASE;
                r_trans_table[w_free_idx].addr <= {{(64-AW){1'b0}}, cmd_paddr};
                r_trans_table[w_free_idx].burst <= {{1'b0}, cmd_pwrite};
                r_trans_table[w_free_idx].channel <= {cmd_pprot, cmd_pstrb[2:0]};
                r_trans_table[w_free_idx].cmd_received <= 1'b1;
                r_trans_table[w_free_idx].data_started <= cmd_pwrite;
                r_trans_table[w_free_idx].addr_timestamp <= r_timestamp;
                r_trans_table[w_free_idx].data_timestamp <= r_timestamp;
                r_trans_table[w_free_idx].event_code <= '0;
                r_trans_table[w_free_idx].event_reported <= 1'b0;
                r_trans_table[w_free_idx].addr_timer <= '0;
                r_trans_table[w_free_idx].resp_timer <= '0;

                r_active_count <= r_active_count + 1'b1;
                r_cmd_start_time <= r_timestamp;
            end

            // Response handshake - complete transaction
            if (w_rsp_handshake && w_has_active_trans) begin
                r_trans_table[w_active_idx].data_completed <= 1'b1;
                r_trans_table[w_active_idx].resp_received <= 1'b1;
                r_trans_table[w_active_idx].resp_timestamp <= r_timestamp;

                if (rsp_pslverr && cfg_slverr_enable) begin
                    r_trans_table[w_active_idx].state <= TRANS_ERROR;
                    r_trans_table[w_active_idx].event_code <= APB_ERR_PSLVERR;
                    r_error_count <= r_error_count + 1'b1;
                end else begin
                    r_trans_table[w_active_idx].state <= TRANS_COMPLETE;
                    r_trans_table[w_active_idx].event_code <= APB_COMPL_TRANS_COMPLETE;
                end

                r_transaction_count <= r_transaction_count + 1'b1;
            end

            // Clean up completed transactions
            for (int i = 0; i < MAX_TRANSACTIONS; i++) begin
                if (w_completed_trans[i]) begin
                    r_trans_table[i].valid <= 1'b0;
                    r_active_count <= r_active_count - 1'b1;
                end
            end
        end
    )

    // -------------------------------------------------------------------------
    // Timeout Detection
    // -------------------------------------------------------------------------
    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_cmd_timeout_timer <= '0;
            r_rsp_timeout_timer <= '0;
        end else begin
            if (r_trans_state == CMD_RSP_IDLE && cmd_valid && !cmd_ready) begin
                r_cmd_timeout_timer <= r_cmd_timeout_timer + 1'b1;
            end else begin
                r_cmd_timeout_timer <= '0;
            end

            if (r_trans_state == CMD_RSP_CMD_SENT && (!rsp_valid || !rsp_ready)) begin
                r_rsp_timeout_timer <= r_rsp_timeout_timer + 1'b1;
            end else begin
                r_rsp_timeout_timer <= '0;
            end
        end
    )

    assign w_cmd_timeout = cfg_timeout_enable &&
                           (r_cmd_timeout_timer >= cfg_cmd_timeout_cnt) &&
                           (r_cmd_timeout_timer != '0);

    assign w_rsp_timeout = cfg_timeout_enable &&
                           (r_rsp_timeout_timer >= cfg_rsp_timeout_cnt) &&
                           (r_rsp_timeout_timer != '0);

    // -------------------------------------------------------------------------
    // Error Detection
    // -------------------------------------------------------------------------
    always_comb begin
        w_protocol_violation = 1'b0;
        w_parity_error = 1'b0;

        if (cfg_protocol_enable) begin
            if (rsp_valid && r_trans_state == CMD_RSP_IDLE) begin
                w_protocol_violation = 1'b1;
            end
            if (cmd_valid && r_trans_state == CMD_RSP_CMD_SENT) begin
                w_protocol_violation = 1'b1;
            end
        end

        if (cfg_parity_enable && ENABLE_PARITY_MON) begin
            w_parity_error = parity_error_wdata || parity_error_rdata || parity_error_ctrl;
        end
    end

    // -------------------------------------------------------------------------
    // Performance Monitoring
    // -------------------------------------------------------------------------
    always_comb begin
        w_current_latency = '0;
        w_latency_threshold_exceeded = 1'b0;

        if (w_has_active_trans && r_trans_table[w_active_idx].valid) begin
            w_current_latency = r_timestamp - r_trans_table[w_active_idx].addr_timestamp;
            w_latency_threshold_exceeded = cfg_perf_enable && cfg_latency_enable &&
                                           (w_current_latency > cfg_latency_threshold);
        end
    end

    // -------------------------------------------------------------------------
    // Event Generation Logic
    // -------------------------------------------------------------------------
    always_comb begin
        w_generate_error_event = 1'b0;
        w_generate_timeout_event = 1'b0;
        w_generate_perf_event = 1'b0;
        w_generate_wakeup_event = 1'b0;
        w_generate_parity_event = 1'b0;
        w_generate_completion_event = 1'b0;
        w_error_event_code = APB_ERR_PSLVERR;
        w_timeout_event_code = APB_TIMEOUT_SETUP;
        w_wakeup_event_code = APB5_WAKEUP_REQUEST;
        w_parity_event_code = APB5_PARITY_PWDATA_ERROR;

        // Error events
        if (cfg_error_enable) begin
            if (w_protocol_violation) begin
                w_generate_error_event = 1'b1;
                w_error_event_code = APB_ERR_SETUP_VIOLATION;
            end else if (rsp_pslverr && w_rsp_handshake && cfg_slverr_enable) begin
                w_generate_error_event = 1'b1;
                w_error_event_code = APB_ERR_PSLVERR;
            end
        end

        // Timeout events
        if (cfg_timeout_enable) begin
            if (w_cmd_timeout) begin
                w_generate_timeout_event = 1'b1;
                w_timeout_event_code = APB_TIMEOUT_SETUP;
            end else if (w_rsp_timeout) begin
                w_generate_timeout_event = 1'b1;
                w_timeout_event_code = APB_TIMEOUT_ACCESS;
            end else if (w_wakeup_timeout) begin
                w_generate_timeout_event = 1'b1;
                w_timeout_event_code = APB_TIMEOUT_ACCESS;  // Use generic timeout
            end
        end

        // Wake-up events (APB5)
        if (cfg_wakeup_enable) begin
            if (w_wakeup_rising) begin
                w_generate_wakeup_event = 1'b1;
                w_wakeup_event_code = APB5_WAKEUP_REQUEST;
            end else if (w_wakeup_falling) begin
                w_generate_wakeup_event = 1'b1;
                w_wakeup_event_code = APB5_WAKEUP_ACKNOWLEDGED;
            end
        end

        // Parity error events (APB5)
        if (cfg_parity_enable && w_parity_error) begin
            w_generate_parity_event = 1'b1;
            if (parity_error_wdata) begin
                w_parity_event_code = APB5_PARITY_PWDATA_ERROR;
            end else if (parity_error_rdata) begin
                w_parity_event_code = APB5_PARITY_PRDATA_ERROR;
            end else begin
                w_parity_event_code = APB5_PARITY_PREADY_ERROR;
            end
        end

        // Performance events
        if (cfg_perf_enable && w_latency_threshold_exceeded) begin
            w_generate_perf_event = 1'b1;
        end

        // Completion events
        if (w_rsp_handshake && !rsp_pslverr) begin
            w_generate_completion_event = 1'b1;
        end
    end

    // -------------------------------------------------------------------------
    // Monitor Packet FIFO
    // -------------------------------------------------------------------------
    gaxi_fifo_sync #(
        .REGISTERED      (1),
        .DATA_WIDTH      ($bits(monitor_entry_t)),
        .DEPTH           (MONITOR_FIFO_DEPTH),
        .ALMOST_WR_MARGIN(1),
        .ALMOST_RD_MARGIN(1),
        .INSTANCE_NAME   ("APB5_MONITOR_FIFO")
    ) monitor_fifo (
        .axi_aclk      (aclk),
        .axi_aresetn   (aresetn),
        .wr_valid      (w_fifo_wr_valid),
        .wr_ready      (w_fifo_wr_ready),
        .wr_data       (w_fifo_wr_data),
        .rd_ready      (w_fifo_rd_ready),
        /* verilator lint_off PINCONNECTEMPTY */
        .count         (),
        /* verilator lint_on PINCONNECTEMPTY */
        .rd_valid      (w_fifo_rd_valid),
        .rd_data       (w_fifo_rd_data)
    );

    // FIFO write logic - priority: Error > Parity > Timeout > Wakeup > Performance > Completion
    always_comb begin
        w_fifo_wr_valid = 1'b0;
        w_fifo_wr_data = '0;

        if (w_generate_error_event) begin
            w_fifo_wr_valid = 1'b1;
            w_fifo_wr_data.packet_type = PktTypeError;
            w_fifo_wr_data.event_code = w_error_event_code;
            w_fifo_wr_data.event_data = cmd_paddr;
            w_fifo_wr_data.aux_data = {4'h0, cmd_pprot, cmd_pwrite};
        end else if (w_generate_parity_event) begin
            w_fifo_wr_valid = 1'b1;
            w_fifo_wr_data.packet_type = PktTypeError;
            w_fifo_wr_data.event_code = w_parity_event_code;
            w_fifo_wr_data.event_data = cmd_paddr;
            w_fifo_wr_data.aux_data = {5'h0,
                parity_error_wdata, parity_error_rdata, parity_error_ctrl};
        end else if (w_generate_timeout_event) begin
            w_fifo_wr_valid = 1'b1;
            w_fifo_wr_data.packet_type = PktTypeTimeout;
            w_fifo_wr_data.event_code = w_timeout_event_code;
            w_fifo_wr_data.event_data = w_has_active_trans ?
                r_trans_table[w_active_idx].addr[31:0] : cmd_paddr;
            w_fifo_wr_data.aux_data = r_cmd_timeout_timer[7:0];
        end else if (w_generate_wakeup_event) begin
            w_fifo_wr_valid = 1'b1;
            w_fifo_wr_data.packet_type = PktTypeAPB;  // Use APB-specific packet type
            w_fifo_wr_data.event_code = w_wakeup_event_code;
            w_fifo_wr_data.event_data = {16'h0, r_wakeup_timer};
            w_fifo_wr_data.aux_data = {7'h0, r_wakeup_active};
        end else if (w_generate_perf_event) begin
            w_fifo_wr_valid = 1'b1;
            w_fifo_wr_data.packet_type = PktTypePerf;
            w_fifo_wr_data.event_code = cmd_pwrite ? APB_PERF_WRITE_LATENCY : APB_PERF_READ_LATENCY;
            w_fifo_wr_data.event_data = w_current_latency;
            w_fifo_wr_data.aux_data = {4'h0, cmd_pprot, cmd_pwrite};
        end else if (w_generate_completion_event) begin
            w_fifo_wr_valid = 1'b1;
            w_fifo_wr_data.packet_type = PktTypeCompletion;
            w_fifo_wr_data.event_code = APB_COMPL_TRANS_COMPLETE;
            w_fifo_wr_data.event_data = cmd_paddr;
            w_fifo_wr_data.aux_data = {4'h0, cmd_pprot, cmd_pwrite};
        end
    end

    // Mark events as reported
    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            // Reset handled in transaction management
        end else begin
            for (int i = 0; i < MAX_TRANSACTIONS; i++) begin
                if (r_trans_table[i].valid &&
                    (r_trans_table[i].state == TRANS_COMPLETE || r_trans_table[i].state == TRANS_ERROR) &&
                    !r_trans_table[i].event_reported && w_fifo_wr_valid && w_fifo_wr_ready) begin
                    r_trans_table[i].event_reported <= 1'b1;
                end
            end
        end
    )

    // -------------------------------------------------------------------------
    // Monitor Bus Packet Construction
    // -------------------------------------------------------------------------
    logic                w_monbus_pkt_valid;
    logic                w_monbus_pkt_ready;
    logic [63:0]         w_monbus_pkt_data;

    assign w_monbus_pkt_valid = w_fifo_rd_valid;
    assign w_fifo_rd_ready = w_monbus_pkt_ready;

    // Construct 64-bit monitor packet
    assign w_monbus_pkt_data[63:60] = w_fifo_rd_data.packet_type;
    assign w_monbus_pkt_data[59:57] = PROTOCOL_APB;
    assign w_monbus_pkt_data[56:53] = w_fifo_rd_data.event_code;
    assign w_monbus_pkt_data[52:47] = 6'h0;                          // channel_id
    assign w_monbus_pkt_data[46:43] = UNIT_ID[3:0];
    assign w_monbus_pkt_data[42:35] = AGENT_ID[7:0];
    assign w_monbus_pkt_data[34:3]  = w_fifo_rd_data.event_data;
    assign w_monbus_pkt_data[2:0]   = w_fifo_rd_data.aux_data[2:0];

    // Monitor bus output skid buffer
    gaxi_skid_buffer #(
        .DATA_WIDTH    (64),
        .DEPTH         (2),
        .INSTANCE_NAME ("APB5_MONITOR_MONBUS_SKB")
    ) monbus_skid_buffer (
        .axi_aclk      (aclk),
        .axi_aresetn   (aresetn),
        .wr_valid      (w_monbus_pkt_valid),
        .wr_ready      (w_monbus_pkt_ready),
        .wr_data       (w_monbus_pkt_data),
        .rd_valid      (monbus_valid),
        .rd_ready      (monbus_ready),
        .rd_data       (monbus_packet),
        /* verilator lint_off PINCONNECTEMPTY */
        .count         (),
        .rd_count      ()
        /* verilator lint_on PINCONNECTEMPTY */
    );

endmodule : apb5_monitor
