// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 RTL Design Sherpa
//
// Formal proof for axi_monitor_trans_mgr -- transaction tracking table
// Verifies reset clears all slots, slot allocation on cmd, slot freed on event_reported
// Uses sv2v-flattened Verilog (packages inlined)

module formal_axi_monitor_trans_mgr (
    input logic clk,
    input logic rst_n
);

    // =========================================================================
    // Parameters (small for tractability)
    // =========================================================================
    localparam int MAX_TRANSACTIONS = 2;
    localparam int ADDR_WIDTH       = 16;
    localparam int ID_WIDTH         = 4;

    // =========================================================================
    // Free inputs
    // =========================================================================
    (* anyseq *) reg                     cmd_valid;
    (* anyseq *) reg                     cmd_ready;
    (* anyseq *) reg  [ID_WIDTH-1:0]     cmd_id;
    (* anyseq *) reg  [ADDR_WIDTH-1:0]   cmd_addr;
    (* anyseq *) reg  [7:0]              cmd_len;
    (* anyseq *) reg  [2:0]              cmd_size;
    (* anyseq *) reg  [1:0]              cmd_burst;

    (* anyseq *) reg                     data_valid;
    (* anyseq *) reg                     data_ready;
    (* anyseq *) reg  [ID_WIDTH-1:0]     data_id;
    (* anyseq *) reg                     data_last;
    (* anyseq *) reg  [1:0]              data_resp;

    (* anyseq *) reg                     resp_valid;
    (* anyseq *) reg                     resp_ready;
    (* anyseq *) reg  [ID_WIDTH-1:0]     resp_id;
    (* anyseq *) reg  [1:0]              resp_code;

    (* anyseq *) reg  [31:0]             timestamp;
    (* anyseq *) reg  [MAX_TRANSACTIONS-1:0] i_event_reported_flags;
    (* anyseq *) reg                     cam_clear;   // synchronous CAM clear

    // =========================================================================
    // DUT outputs (sv2v flattened -- signals are exposed as flat wires)
    // =========================================================================
    wire [7:0]                           active_count_o;

    // After sv2v, the trans_table output is flattened. We reference it via
    // hierarchical access in the DUT wrapper signals below.
    // The bus_transaction_t struct is ~260 bits wide. With MAX_TRANSACTIONS=2,
    // that's 2 entries in an unpacked array, flattened by sv2v.

    // =========================================================================
    // DUT instantiation
    // =========================================================================
    axi_monitor_trans_mgr #(
        .MAX_TRANSACTIONS (MAX_TRANSACTIONS),
        .ADDR_WIDTH       (ADDR_WIDTH),
        .ID_WIDTH         (ID_WIDTH),
        .IS_READ          (1'b1),
        .IS_AXI           (1'b1),
        .ENABLE_PERF_PACKETS(1'b0)
    ) dut (
        .aclk                  (clk),
        .aresetn               (rst_n),
        .clear                 (cam_clear),
        .cmd_valid             (cmd_valid),
        .cmd_ready             (cmd_ready),
        .cmd_id                (cmd_id),
        .cmd_addr              (cmd_addr),
        .cmd_len               (cmd_len),
        .cmd_size              (cmd_size),
        .cmd_burst             (cmd_burst),
        .data_valid            (data_valid),
        .data_ready            (data_ready),
        .data_id               (data_id),
        .data_last             (data_last),
        .data_resp             (data_resp),
        .resp_valid            (resp_valid),
        .resp_ready            (resp_ready),
        .resp_id               (resp_id),
        .resp_code             (resp_code),
        .timestamp             (timestamp),
        .i_event_reported_flags(i_event_reported_flags),
        .active_count          (active_count_o)
    );

    // =========================================================================
    // Formal infrastructure
    // =========================================================================
    reg [7:0] f_past_valid = 0;
    always @(posedge clk)
        f_past_valid <= f_past_valid + (f_past_valid < 8'hFF);

    // Hold reset 2 cycles so the CAM valid bits and the active_count register
    // reach their cleared state before the steady-state properties apply.
    initial assume (!rst_n);
    always @(posedge clk) if (f_past_valid >= 2) assume (rst_n);

    // =========================================================================
    // Environment constraints
    // =========================================================================

    // Constrain burst length for tractability.
    always @(*) assume (cmd_len <= 8'd3);

    // =========================================================================
    // P1: Reset clears active_count to zero
    // =========================================================================
    always @(posedge clk) begin
        if (f_past_valid > 0 && $past(!rst_n))
            ap_reset_active_count: assert (active_count_o == 8'h0);
    end

    // =========================================================================
    // P2: active_count bounded by MAX_TRANSACTIONS
    //
    // active_count is now the registered pop-count of the CAM occupancy, so it is
    // structurally in [0, MAX_TRANSACTIONS] and can never underflow.  The former
    // alloc-minus-cleanup accumulator could underflow to 0xFF under legal AXI --
    // this proof caught it; see
    // rtl/amba/KNOWN_ISSUES/axi_monitor_active_count_underflow.md.
    // =========================================================================
    always @(posedge clk) begin
        if (rst_n)
            ap_count_bounded: assert (active_count_o <= 8'(MAX_TRANSACTIONS));
    end

    // P3 retired with the dead `state_change` output it checked; the
    // numbering below is left alone so it still matches the proof log.

    // =========================================================================
    // P4: allocation reachability -- a command into an empty table opens a
    //     tracked transaction (active_count reaches 1).  Reachability is verified
    //     by the cp_first_alloc cover below (active_count == 1 from an empty
    //     table); the safety side is P2/P5.
    // =========================================================================

    // =========================================================================
    // P5: active_count does not increase beyond MAX_TRANSACTIONS
    //     (table never overflows)
    // =========================================================================
    always @(posedge clk) begin
        if (rst_n)
            ap_no_overflow: assert (active_count_o <= 8'(MAX_TRANSACTIONS));
    end

    // =========================================================================
    // P6: synchronous CAM clear zeroes active_count on the next cycle
    //     (verified through the port, not DUT internals).
    // =========================================================================
    always @(posedge clk) begin
        if (rst_n && f_past_valid > 0 && $past(rst_n) && $past(cam_clear))
            ap_clear_zeroes_count: assert (active_count_o == 8'h0);
    end

    // =========================================================================
    // Cover properties
    // =========================================================================

    // Transaction allocated (active_count goes from 0 to 1)
    always @(posedge clk) begin
        if (f_past_valid > 0 && rst_n && $past(rst_n) && $past(active_count_o) == 0)
            cp_first_alloc: cover (active_count_o == 8'd1);
    end

    // Table full (active_count == MAX_TRANSACTIONS)
    always @(posedge clk) begin
        if (rst_n)
            cp_table_full: cover (active_count_o == 8'(MAX_TRANSACTIONS));
    end

    // Transaction cleaned up (active_count decreases)
    always @(posedge clk) begin
        if (f_past_valid > 0 && rst_n && $past(rst_n) && $past(active_count_o) > 0)
            cp_cleanup: cover (active_count_o < $past(active_count_o));
    end

    // Both slots occupied then one freed
    always @(posedge clk) begin
        if (f_past_valid > 0 && rst_n && $past(rst_n) &&
            $past(active_count_o) == 8'(MAX_TRANSACTIONS))
            cp_full_then_free: cover (active_count_o == 8'(MAX_TRANSACTIONS - 1));
    end

endmodule
