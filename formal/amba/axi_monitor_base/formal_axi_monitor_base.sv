// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 RTL Design Sherpa
//
// Formal proof for axi_monitor_base -- AXI monitor infrastructure
// Verifies reset clears monbus output, no spurious monbus without cmd activity
// Uses sv2v-flattened Verilog (packages + all deps inlined)

module formal_axi_monitor_base (
    input logic clk,
    input logic rst_n
);

    // =========================================================================
    // Parameters (small for tractability)
    // =========================================================================
    localparam int UNIT_ID          = 9;
    localparam int AGENT_ID         = 99;
    localparam int MAX_TRANSACTIONS = 2;
    localparam int ADDR_WIDTH       = 16;
    localparam int ID_WIDTH         = 4;
    localparam int ADDR_BITS_IN_PKT = 16;
    localparam int IS_READ          = 1;
    localparam int IS_AXI           = 1;
    localparam int ENABLE_PERF      = 0;
    localparam int ENABLE_DEBUG     = 0;
    localparam int INTR_FIFO_DEPTH  = 4;
    localparam int DEBUG_FIFO_DEPTH = 4;

    // =========================================================================
    // Free inputs
    // =========================================================================
    (* anyseq *) reg [ADDR_WIDTH-1:0]  cmd_addr;
    (* anyseq *) reg [ID_WIDTH-1:0]    cmd_id;
    (* anyseq *) reg [7:0]             cmd_len;
    (* anyseq *) reg [2:0]             cmd_size;
    (* anyseq *) reg [1:0]             cmd_burst;
    (* anyseq *) reg                   cmd_valid;
    (* anyseq *) reg                   cmd_ready;

    (* anyseq *) reg [ID_WIDTH-1:0]    data_id;
    (* anyseq *) reg                   data_last;
    (* anyseq *) reg [1:0]             data_resp;
    (* anyseq *) reg                   data_valid;
    (* anyseq *) reg                   data_ready;

    (* anyseq *) reg [ID_WIDTH-1:0]    resp_id;
    (* anyseq *) reg [1:0]             resp_code;
    (* anyseq *) reg                   resp_valid;
    (* anyseq *) reg                   resp_ready;

    (* anyseq *) reg [3:0]             cfg_freq_sel;
    (* anyseq *) reg [3:0]             cfg_addr_cnt;
    (* anyseq *) reg [3:0]             cfg_data_cnt;
    (* anyseq *) reg [3:0]             cfg_resp_cnt;

    (* anyseq *) reg                   cfg_error_enable;
    (* anyseq *) reg                   cfg_compl_enable;
    (* anyseq *) reg                   cfg_threshold_enable;
    (* anyseq *) reg                   cfg_timeout_enable;
    (* anyseq *) reg                   cfg_perf_enable;
    (* anyseq *) reg                   cfg_debug_enable;

    (* anyseq *) reg [3:0]             cfg_debug_level;
    (* anyseq *) reg [15:0]            cfg_debug_mask;
    (* anyseq *) reg [15:0]            cfg_active_trans_threshold;
    (* anyseq *) reg [31:0]            cfg_latency_threshold;

    (* anyseq *) reg                   monbus_ready;

    // =========================================================================
    // DUT outputs
    // =========================================================================
    wire                monbus_valid_o;
    wire [63:0]         monbus_packet_o;
    wire                block_ready_o;
    wire                busy_o;
    wire [7:0]          active_count_o;

    // =========================================================================
    // DUT instantiation
    // =========================================================================
    axi_monitor_base #(
        .UNIT_ID             (UNIT_ID),
        .AGENT_ID            (AGENT_ID),
        .MAX_TRANSACTIONS    (MAX_TRANSACTIONS),
        .ADDR_WIDTH          (ADDR_WIDTH),
        .ID_WIDTH            (ID_WIDTH),
        .ADDR_BITS_IN_PKT    (ADDR_BITS_IN_PKT),
        .IS_READ             (IS_READ),
        .IS_AXI              (IS_AXI),
        .ENABLE_PERF_PACKETS (ENABLE_PERF),
        .ENABLE_DEBUG_MODULE (ENABLE_DEBUG),
        .INTR_FIFO_DEPTH     (INTR_FIFO_DEPTH),
        .DEBUG_FIFO_DEPTH    (DEBUG_FIFO_DEPTH)
    ) dut (
        .aclk                      (clk),
        .aresetn                   (rst_n),
        .cmd_addr                  (cmd_addr),
        .cmd_id                    (cmd_id),
        .cmd_len                   (cmd_len),
        .cmd_size                  (cmd_size),
        .cmd_burst                 (cmd_burst),
        .cmd_valid                 (cmd_valid),
        .cmd_ready                 (cmd_ready),
        .data_id                   (data_id),
        .data_last                 (data_last),
        .data_resp                 (data_resp),
        .data_valid                (data_valid),
        .data_ready                (data_ready),
        .resp_id                   (resp_id),
        .resp_code                 (resp_code),
        .resp_valid                (resp_valid),
        .resp_ready                (resp_ready),
        .cfg_freq_sel              (cfg_freq_sel),
        .cfg_addr_cnt              (cfg_addr_cnt),
        .cfg_data_cnt              (cfg_data_cnt),
        .cfg_resp_cnt              (cfg_resp_cnt),
        .cfg_error_enable          (cfg_error_enable),
        .cfg_compl_enable          (cfg_compl_enable),
        .cfg_threshold_enable      (cfg_threshold_enable),
        .cfg_timeout_enable        (cfg_timeout_enable),
        .cfg_perf_enable           (cfg_perf_enable),
        .cfg_debug_enable          (cfg_debug_enable),
        .cfg_debug_level           (cfg_debug_level),
        .cfg_debug_mask            (cfg_debug_mask),
        .cfg_active_trans_threshold(cfg_active_trans_threshold),
        .cfg_latency_threshold     (cfg_latency_threshold),
        .monbus_valid              (monbus_valid_o),
        .monbus_ready              (monbus_ready),
        .monbus_packet             (monbus_packet_o),
        .block_ready               (block_ready_o),
        .busy                      (busy_o),
        .active_count              (active_count_o)
    );

    // =========================================================================
    // Formal infrastructure
    // =========================================================================
    reg [7:0] f_past_valid = 0;
    always @(posedge clk)
        f_past_valid <= f_past_valid + (f_past_valid < 8'hFF);

    initial assume (!rst_n);
    always @(posedge clk) if (f_past_valid >= 2) assume (rst_n);

    // =========================================================================
    // Environment constraints
    // =========================================================================

    // Constrain burst length for tractability
    always @(*) begin
        assume (cmd_len <= 8'd3);
    end

    // Keep all packet enables off except error for tractability
    // (reduces state space while still testing core path)
    always @(*) begin
        assume (cfg_perf_enable == 1'b0);
        assume (cfg_debug_enable == 1'b0);
    end

    // =========================================================================
    // Shadow model: track whether any AXI activity has occurred
    // =========================================================================
    reg f_any_cmd_seen = 0;
    reg f_any_data_seen = 0;

    always @(posedge clk) begin
        if (!rst_n) begin
            f_any_cmd_seen <= 0;
            f_any_data_seen <= 0;
        end else begin
            if (cmd_valid && cmd_ready)
                f_any_cmd_seen <= 1;
            if (data_valid && data_ready)
                f_any_data_seen <= 1;
        end
    end

    // =========================================================================
    // P1: Reset clears monbus_valid
    // =========================================================================
    always @(posedge clk) begin
        if (f_past_valid > 0 && $past(!rst_n))
            ap_reset_monbus_valid: assert (monbus_valid_o == 1'b0);
    end

    // =========================================================================
    // P2: Reset clears active_count
    // =========================================================================
    always @(posedge clk) begin
        if (f_past_valid > 0 && $past(!rst_n))
            ap_reset_active_count: assert (active_count_o == 8'h0);
    end

    // =========================================================================
    // P3: Reset clears busy
    // =========================================================================
    always @(posedge clk) begin
        if (f_past_valid > 0 && $past(!rst_n))
            ap_reset_busy: assert (busy_o == 1'b0);
    end

    // =========================================================================
    // P4: active_count bounded by MAX_TRANSACTIONS
    // =========================================================================
    always @(posedge clk) begin
        if (rst_n)
            ap_count_bounded: assert (active_count_o <= 8'(MAX_TRANSACTIONS));
    end

    // =========================================================================
    // P5: busy consistent with active_count
    //     busy == (active_count > 0)
    // =========================================================================
    always @(posedge clk) begin
        if (rst_n)
            ap_busy_iff_active: assert (busy_o == (active_count_o > 0));
    end

    // =========================================================================
    // P6: No monbus_valid in the first few cycles after reset
    //     (before any AXI activity can complete a transaction and be reported)
    // =========================================================================
    always @(posedge clk) begin
        if (f_past_valid >= 1 && f_past_valid <= 3 && rst_n)
            ap_no_early_monbus: assert (!monbus_valid_o || f_any_cmd_seen || f_any_data_seen);
    end

    // =========================================================================
    // P7: monbus_packet is zero when monbus_valid is deasserted
    //     (from the priority mux in axi_monitor_base)
    // =========================================================================
    always @(*) begin
        if (!monbus_valid_o)
            ap_packet_zero_when_invalid: assert (monbus_packet_o == 64'h0);
    end

    // =========================================================================
    // P8: block_ready behavior
    //     With MAX_TRANSACTIONS=2, block_ready should always be 0
    //     (the condition is MAX_TRANSACTIONS > 2 for block_ready to ever assert)
    // =========================================================================
    always @(posedge clk) begin
        if (rst_n)
            ap_block_ready_zero: assert (block_ready_o == 1'b0);
    end

    // =========================================================================
    // Cover properties
    // =========================================================================

    // monbus_valid asserted (an event was reported)
    always @(posedge clk) begin
        if (rst_n)
            cp_monbus_valid: cover (monbus_valid_o);
    end

    // busy asserted
    always @(posedge clk) begin
        if (rst_n)
            cp_busy: cover (busy_o);
    end

    // active_count reaches MAX_TRANSACTIONS
    always @(posedge clk) begin
        if (rst_n)
            cp_table_full: cover (active_count_o == 8'(MAX_TRANSACTIONS));
    end

    // Monitor bus handshake (valid && ready)
    always @(posedge clk) begin
        if (rst_n)
            cp_monbus_handshake: cover (monbus_valid_o && monbus_ready);
    end

    // Return to idle after being busy
    always @(posedge clk) begin
        if (f_past_valid > 0 && rst_n && $past(rst_n) && $past(busy_o))
            cp_busy_to_idle: cover (!busy_o);
    end

endmodule
