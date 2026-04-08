// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// Formal proof for apb5_monitor -- monitor bus output properties + APB5 extensions
//
// NOTE: Same memory_map limitation as apb_monitor. Properties focus on
// I/O-observable behavior rather than internal transaction table state.
//
// Properties verified:
//   P1: Reset clears monbus_valid
//   P2: monbus_packet protocol field is APB when valid
//   P3: monbus_valid handshake -- valid held until ready

module formal_apb5_monitor (
    input logic clk,
    input logic rst_n
);

    // =========================================================================
    // Parameters (small for tractability)
    // =========================================================================
    localparam int AW  = 12;
    localparam int DW  = 32;
    localparam int SW  = DW / 8;
    localparam int AUW = 1;
    localparam int WUW = 1;
    localparam int RUW = 1;
    localparam int BUW = 1;
    localparam int MAX_TRANS = 2;
    localparam int FIFO_DEPTH = 4;

    // =========================================================================
    // Free inputs
    // =========================================================================
    (* anyseq *) reg              cmd_valid;
    (* anyseq *) reg              cmd_ready;
    (* anyseq *) reg              cmd_pwrite;
    (* anyseq *) reg [AW-1:0]     cmd_paddr;
    (* anyseq *) reg [DW-1:0]     cmd_pwdata;
    (* anyseq *) reg [SW-1:0]     cmd_pstrb;
    (* anyseq *) reg [2:0]        cmd_pprot;
    (* anyseq *) reg [AUW-1:0]    cmd_pauser;
    (* anyseq *) reg [WUW-1:0]    cmd_pwuser;

    (* anyseq *) reg              rsp_valid;
    (* anyseq *) reg              rsp_ready;
    (* anyseq *) reg [DW-1:0]     rsp_prdata;
    (* anyseq *) reg              rsp_pslverr;
    (* anyseq *) reg [RUW-1:0]    rsp_pruser;
    (* anyseq *) reg [BUW-1:0]    rsp_pbuser;

    (* anyseq *) reg              apb5_pwakeup;
    (* anyseq *) reg              parity_error_wdata;
    (* anyseq *) reg              parity_error_rdata;
    (* anyseq *) reg              parity_error_ctrl;

    (* anyseq *) reg              cfg_error_enable;
    (* anyseq *) reg              cfg_timeout_enable;
    (* anyseq *) reg              cfg_protocol_enable;
    (* anyseq *) reg              cfg_slverr_enable;
    (* anyseq *) reg              cfg_parity_enable;
    (* anyseq *) reg              cfg_wakeup_enable;
    (* anyseq *) reg              cfg_user_enable;
    (* anyseq *) reg              cfg_perf_enable;
    (* anyseq *) reg              cfg_latency_enable;
    (* anyseq *) reg [15:0]       cfg_cmd_timeout_cnt;
    (* anyseq *) reg [15:0]       cfg_rsp_timeout_cnt;
    (* anyseq *) reg [31:0]       cfg_latency_threshold;
    (* anyseq *) reg [15:0]       cfg_wakeup_timeout_cnt;

    (* anyseq *) reg              monbus_ready;

    // =========================================================================
    // DUT outputs
    // =========================================================================
    wire              monbus_valid;
    wire [63:0]       monbus_packet;
    wire [7:0]        active_count;
    wire [15:0]       error_count;
    wire [31:0]       transaction_count;
    wire              wakeup_active;

    // =========================================================================
    // DUT instantiation
    // =========================================================================
    apb5_monitor #(
        .ADDR_WIDTH         (AW),
        .DATA_WIDTH         (DW),
        .AUSER_WIDTH        (AUW),
        .WUSER_WIDTH        (WUW),
        .RUSER_WIDTH        (RUW),
        .BUSER_WIDTH        (BUW),
        .UNIT_ID            (1),
        .AGENT_ID           (10),
        .MAX_TRANSACTIONS   (MAX_TRANS),
        .MONITOR_FIFO_DEPTH (FIFO_DEPTH),
        .ENABLE_PARITY_MON  (0)
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
        .cmd_pauser             (cmd_pauser),
        .cmd_pwuser             (cmd_pwuser),
        .rsp_valid              (rsp_valid),
        .rsp_ready              (rsp_ready),
        .rsp_prdata             (rsp_prdata),
        .rsp_pslverr            (rsp_pslverr),
        .rsp_pruser             (rsp_pruser),
        .rsp_pbuser             (rsp_pbuser),
        .apb5_pwakeup           (apb5_pwakeup),
        .parity_error_wdata     (parity_error_wdata),
        .parity_error_rdata     (parity_error_rdata),
        .parity_error_ctrl      (parity_error_ctrl),
        .cfg_error_enable       (cfg_error_enable),
        .cfg_timeout_enable     (cfg_timeout_enable),
        .cfg_protocol_enable    (cfg_protocol_enable),
        .cfg_slverr_enable      (cfg_slverr_enable),
        .cfg_parity_enable      (cfg_parity_enable),
        .cfg_wakeup_enable      (cfg_wakeup_enable),
        .cfg_user_enable        (cfg_user_enable),
        .cfg_perf_enable        (cfg_perf_enable),
        .cfg_latency_enable     (cfg_latency_enable),
        .cfg_cmd_timeout_cnt    (cfg_cmd_timeout_cnt),
        .cfg_rsp_timeout_cnt    (cfg_rsp_timeout_cnt),
        .cfg_latency_threshold  (cfg_latency_threshold),
        .cfg_wakeup_timeout_cnt (cfg_wakeup_timeout_cnt),
        .monbus_valid           (monbus_valid),
        .monbus_ready           (monbus_ready),
        .monbus_packet          (monbus_packet),
        .active_count           (active_count),
        .error_count            (error_count),
        .transaction_count      (transaction_count),
        .wakeup_active          (wakeup_active)
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

    // P1: Reset clears monbus_valid
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
            cp_monbus_packet:  cover (monbus_valid);
            cp_cmd_handshake:  cover (cmd_valid && cmd_ready);
            cp_rsp_handshake:  cover (rsp_valid && rsp_ready);
            cp_wakeup_rising:  cover (apb5_pwakeup && wakeup_active);
            cp_error_event:    cover (monbus_valid && monbus_packet[63:60] == 4'h0);
        end
    end

endmodule
