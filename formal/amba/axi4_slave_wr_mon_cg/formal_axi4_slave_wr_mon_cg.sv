// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 RTL Design Sherpa
//
// Formal proof for axi4_slave_wr_mon
//
// This module wraps axi4_slave_wr (skid buffers) + axi_monitor_filtered.
// It is purely structural -- no sequential logic of its own.
//
// Properties verified:
//   P1: Reset clears monbus_valid
//   P2: Reset clears busy
//   P3: Protocol field in monbus_packet is AXI (3'b000) when valid
//   P4: active_transactions bounded by MAX_TRANSACTIONS
//   P5: cfg_conflict_error is combinational: |(pkt_mask & err_select)
//   P6: Monitor backpressure gating — when w_block_ready is low, the
//       wrapper output s_axi_awready must be low (so upstream AW
//       handshake cannot complete and the monitor cannot lose events).

module formal_axi4_slave_wr_mon_cg (
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
    // MAX_TRANSACTIONS must exceed the internal BLOCK_MARGIN (3 for tables
    // < 16, so block_ready = active_count < MAX-3)... except that for
    // MAX <= 3 axi_monitor_base ties block_ready to CONSTANT 1, which made
    // every block_ready-gating property here structurally unfalsifiable at
    // the old value of 2. At 4 the gate engages with a single outstanding
    // transaction (active_count >= 1 -> block_ready=0), the cheapest
    // configuration in which the in-RTL wrapper gating properties
    // (ap_block_ready_gating / ap_disabled_never_stalls) actually bite.
    localparam integer MAX_TRANSACTIONS = 4;
    localparam integer CG_ICW = 3;   // small idle counter keeps gating reachable
    localparam logic [7:0]  UNIT_ID  = 8'h02;
    localparam logic [15:0] AGENT_ID = 16'h0015;

    // =========================================================================
    // Free inputs -- slave-side AXI (s_axi_*)
    // =========================================================================
    (* anyseq *) reg [IW-1:0]  s_axi_awid;
    (* anyseq *) reg [AW-1:0]  s_axi_awaddr;
    (* anyseq *) reg [7:0]     s_axi_awlen;
    (* anyseq *) reg [2:0]     s_axi_awsize;
    (* anyseq *) reg [1:0]     s_axi_awburst;
    (* anyseq *) reg           s_axi_awlock;
    (* anyseq *) reg [3:0]     s_axi_awcache;
    (* anyseq *) reg [2:0]     s_axi_awprot;
    (* anyseq *) reg [3:0]     s_axi_awqos;
    (* anyseq *) reg [3:0]     s_axi_awregion;
    (* anyseq *) reg [UW-1:0]  s_axi_awuser;
    (* anyseq *) reg           s_axi_awvalid;

    (* anyseq *) reg [DW-1:0]  s_axi_wdata;
    (* anyseq *) reg [SW-1:0]  s_axi_wstrb;
    (* anyseq *) reg           s_axi_wlast;
    (* anyseq *) reg [UW-1:0]  s_axi_wuser;
    (* anyseq *) reg           s_axi_wvalid;

    (* anyseq *) reg           s_axi_bready;

    // Free inputs -- master-side AXI (fub_axi_*)
    (* anyseq *) reg           fub_axi_awready;
    (* anyseq *) reg           fub_axi_wready;
    (* anyseq *) reg [IW-1:0]  fub_axi_bid;
    (* anyseq *) reg [1:0]     fub_axi_bresp;
    (* anyseq *) reg [UW-1:0]  fub_axi_buser;
    (* anyseq *) reg           fub_axi_bvalid;

    // Free inputs -- monitor config
    (* anyseq *) reg           cam_clear;
    (* anyseq *) reg           cfg_monitor_enable;
    (* anyseq *) reg           cfg_error_enable;
    (* anyseq *) reg           cfg_timeout_enable;
    (* anyseq *) reg           cfg_perf_enable;
    (* anyseq *) reg [15:0]    cfg_timeout_cycles;
    (* anyseq *) reg [31:0]    cfg_latency_threshold;
    // These were NOT connected at all. An unconnected DUT input is
    // folded to a constant by opt -full, so with cfg_perf_enable and
    // cfg_timeout_enable assumed low and completion/debug/threshold
    // pinned low, NO packet class could ever be enabled and
    // cp_monbus_valid was unreachable whatever the RTL did.
    (* anyseq *) reg           cfg_compl_enable;
    (* anyseq *) reg           cfg_debug_enable;
    (* anyseq *) reg           cfg_threshold_enable;

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

    // Free inputs -- clock gating config
    (* anyseq *) reg               cfg_cg_enable;
    (* anyseq *) reg [CG_ICW-1:0]  cfg_cg_idle_count;

    // Broadcast monitor time
    (* anyseq *) reg [63:0]    i_mon_time;

    // =========================================================================
    // DUT outputs
    // =========================================================================
    wire                s_axi_awready;
    wire                s_axi_wready;
    wire [IW-1:0]       s_axi_bid;
    wire [1:0]          s_axi_bresp;
    wire [UW-1:0]       s_axi_buser;
    wire                s_axi_bvalid;
    wire [IW-1:0]       fub_axi_awid;
    wire [AW-1:0]       fub_axi_awaddr;
    wire [7:0]          fub_axi_awlen;
    wire [2:0]          fub_axi_awsize;
    wire [1:0]          fub_axi_awburst;
    wire                fub_axi_awlock;
    wire [3:0]          fub_axi_awcache;
    wire [2:0]          fub_axi_awprot;
    wire [3:0]          fub_axi_awqos;
    wire [3:0]          fub_axi_awregion;
    wire [UW-1:0]       fub_axi_awuser;
    wire                fub_axi_awvalid;
    wire [DW-1:0]       fub_axi_wdata;
    wire [SW-1:0]       fub_axi_wstrb;
    wire                fub_axi_wlast;
    wire [UW-1:0]       fub_axi_wuser;
    wire                fub_axi_wvalid;
    wire                fub_axi_bready;
    wire                monbus_valid;
    wire [127:0]        monbus_packet;
    wire [63:0]         monbus_timestamp;
    wire                busy;
    wire [7:0]          active_transactions;
    wire [15:0]         error_count;
    wire [31:0]         transaction_count;
    wire                cfg_conflict_error;
    wire                cg_gating;
    wire                cg_idle;

    // =========================================================================
    // DUT instantiation
    // =========================================================================
    axi4_slave_wr_mon_cg #(
        .SKID_DEPTH_AW      (2),
        .SKID_DEPTH_W       (2),
        .SKID_DEPTH_B       (2),
        .AXI_ID_WIDTH       (IW),
        .AXI_ADDR_WIDTH     (AW),
        .AXI_DATA_WIDTH     (DW),
        .AXI_USER_WIDTH     (UW),
        .UNIT_ID            (UNIT_ID),
        .AGENT_ID           (AGENT_ID),
        .MAX_TRANSACTIONS   (MAX_TRANSACTIONS),
        .ENABLE_FILTERING   (1),
        .ADD_PIPELINE_STAGE (0),
        .CG_IDLE_COUNT_WIDTH(CG_ICW)
    ) dut (
        .aclk                   (clk),
        .aresetn                (rst_n),
        // cam_clear was previously left UNCONNECTED, which yosys models as
        // a constant-x clear -- the transaction CAM could never hold an
        // entry, so every occupancy-dependent property (active bound,
        // block_ready gating) was structurally vacuous in this proof.
        .cam_clear              (cam_clear),
        .i_mon_time             (i_mon_time),
        // Slave side (input)
        .s_axi_awid             (s_axi_awid),
        .s_axi_awaddr           (s_axi_awaddr),
        .s_axi_awlen            (s_axi_awlen),
        .s_axi_awsize           (s_axi_awsize),
        .s_axi_awburst          (s_axi_awburst),
        .s_axi_awlock           (s_axi_awlock),
        .s_axi_awcache          (s_axi_awcache),
        .s_axi_awprot           (s_axi_awprot),
        .s_axi_awqos            (s_axi_awqos),
        .s_axi_awregion         (s_axi_awregion),
        .s_axi_awuser           (s_axi_awuser),
        .s_axi_awvalid          (s_axi_awvalid),
        .s_axi_awready          (s_axi_awready),
        .s_axi_wdata            (s_axi_wdata),
        .s_axi_wstrb            (s_axi_wstrb),
        .s_axi_wlast            (s_axi_wlast),
        .s_axi_wuser            (s_axi_wuser),
        .s_axi_wvalid           (s_axi_wvalid),
        .s_axi_wready           (s_axi_wready),
        .s_axi_bid              (s_axi_bid),
        .s_axi_bresp            (s_axi_bresp),
        .s_axi_buser            (s_axi_buser),
        .s_axi_bvalid           (s_axi_bvalid),
        .s_axi_bready           (s_axi_bready),
        // Master side (output to backend)
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
        .cfg_compl_enable        (cfg_compl_enable),
        .cfg_debug_enable        (cfg_debug_enable),
        .cfg_threshold_enable    (cfg_threshold_enable),
        .cfg_axi_perf_mask      (cfg_axi_perf_mask),
        .cfg_axi_addr_mask      (cfg_axi_addr_mask),
        .cfg_axi_debug_mask     (cfg_axi_debug_mask),
        // Monitor bus
        .monbus_valid           (monbus_valid),
        .monbus_ready           (monbus_ready),
        .monbus_packet          (monbus_packet),
        .monbus_timestamp       (monbus_timestamp),
        // Status
        .busy                   (busy),
        .active_transactions    (active_transactions),
        .error_count            (error_count),
        .transaction_count      (transaction_count),
        .cfg_conflict_error     (cfg_conflict_error),
        // Clock gating
        .cfg_cg_enable          (cfg_cg_enable),
        .cfg_cg_idle_count      (cfg_cg_idle_count),
        .cg_gating              (cg_gating),
        .cg_idle                (cg_idle)
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
    always @(posedge clk) if (f_past_valid > 0) begin
        assume (cfg_cg_enable == $past(cfg_cg_enable));
        assume (cfg_cg_idle_count == $past(cfg_cg_idle_count));
    end

    always @(*) assume (cfg_cg_idle_count <= 3);

    always @(*) begin
        assume (s_axi_awlen <= 8'd3);
        assume (cfg_perf_enable == 1'b0);
        assume (cfg_timeout_enable == 1'b0);
    end

    // During reset, AXI valid signals should be deasserted (standard practice)
    always @(*) begin
        if (!rst_n) begin
            assume (s_axi_awvalid == 1'b0);
            assume (s_axi_wvalid == 1'b0);
            assume (fub_axi_bvalid == 1'b0);
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
    // P3: Protocol field is AXI (4'h0) when monbus_valid
    // =========================================================================
    always @(posedge clk) begin
        if (rst_n && monbus_valid)
            ap_protocol_axi: assert (monbus_packet[108:105] == 4'h0);
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
    // P6: Monitor backpressure gating — combinational invariant from the
    //     assign at the bottom of axi4_slave_wr_mon:
    //         s_axi_awready = w_core_s_axi_awready & w_block_ready;
    // =========================================================================
    // MOVED IN-RTL (E5): the gating properties now live inside the wrapper
    // under `ifdef FORMAL (ap_block_ready_gating / ap_disabled_never_stalls).
    // The old harness-side formulation referenced dut.w_block_ready, which
    // yosys elaborates as an implicitly-declared FREE wire (see the base-step
    // warning in the sby log), so the property was vacuous -- the guard could
    // always be solved false. In-RTL the real nets are visible.

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
    // =========================================================================
    // Clock-gating properties (TASK-090)
    // =========================================================================
    // The gated clock is modelled as the free clock (see the icg model at the
    // bottom); what is proved here is the wrapper's glue -- what the masks hold
    // while gated, and that real activity wakes it in bounded time.

    always @(posedge clk) begin
        if (f_past_valid >= 3 && $past(!rst_n))
            ap_reset_no_gate: assert (!cg_gating);
    end

    // Request-side readys are masked to 0 while gated, so nothing can be
    // accepted while the clock is stopped.
    always @(*) begin
        if (rst_n && cg_gating) begin
            ap_gated_s_axi_awready_zero: assert (!s_axi_awready);
            ap_gated_s_axi_wready_zero: assert (!s_axi_wready);
            ap_gated_fub_axi_bready_zero: assert (!fub_axi_bready);
        end
    end

    always @(*) begin
        if (rst_n)
            ap_disabled_no_gate: assert (cfg_cg_enable || !cg_gating);
    end

    // Bounded wake. TWO registered stages sit between activity and the gate
    // decision (the wrapper's own wake term, then amba_clock_gate_ctrl's), so
    // gating may survive a clock or two of activity but not three. Same shape
    // as wb4_slave_cg's ap_wake_bounded and the apb *_master_cg fix (TASK-091).
    always @(posedge clk) begin
        if (f_past_valid > 6 && rst_n && $past(rst_n) && $past(rst_n, 2)) begin
            ap_wake_bounded:
                assert (!(s_axi_awvalid && $past(s_axi_awvalid)
                          && $past(s_axi_awvalid, 2)) || !cg_gating);
            // The bug-hunt property: |active_transactions is a term in the
            // wrapper's user_valid. If it were dropped, a monitor holding
            // outstanding transactions could be gated with work in flight.
            ap_no_gate_while_active:
                assert (!((|active_transactions) && $past(|active_transactions)
                          && $past(|active_transactions, 2)) || !cg_gating);
        end
    end

    always @(posedge clk) begin
        if (rst_n) begin
            cp_gating:            cover (cg_gating);
            cp_gated_with_req:    cover (cg_gating && s_axi_awvalid);
            cp_idle:              cover (cg_idle);
        end
    end

endmodule

// Formal model of the integrated clock-gate cell: the gated clock IS the free
// clock. A derived clock is not provable in this repo's single-clock flow, so
// this harness proves the wrapper's glue -- when it gates, what the masks hold
// -- and val/amba/test_mon_cg_gating.py proves the behaviour of an actually
// stopped clock. rtl/common/icg.sv is left out of the flattened DUT on purpose
// (see the Makefile).
module icg (
    input  logic en,
    input  logic clk,
    output logic gclk
);
    assign gclk = clk;
    /* verilator lint_off UNUSEDSIGNAL */
    logic unused_en;
    assign unused_en = en;
    /* verilator lint_on UNUSEDSIGNAL */
endmodule
