// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// Formal wrapper for ctrlrd_engine (RAPIDS Phase-2 control read engine)
// Run with: sby ctrlrd_engine.sby
//
// PORT-LEVEL properties only (the flat is sv2v output; no hierarchical
// references). The drain-on-channel-reset contract from rapids TASK-014 is
// stated here in fabric terms, because the engine's own `ifdef FORMAL block
// is not part of the flat:
//   P1: reset leaves the engine idle with nothing on the fabric
//   P2: an AR is a single 32-bit INCR beat carrying the channel's ID
//   P3: AR stability -- once raised, AR holds (valid, addr, id) until accepted,
//       channel reset included (an abandoned AR is what TASK-014 removed)
//   P4: no second AR while an R beat is still owed (no double issue)
//   P5: r_ready only while an R beat is owed
//   P6: idle means nothing outstanding on the fabric
//   C1: an R beat is drained after a channel reset landed mid-transaction
//   C2: the engine returns to idle after a transaction

module formal_ctrlrd_engine (
    input  logic clk,
    input  logic rst_n
);
    localparam int CHANNEL_ID     = 1;
    localparam int NUM_CHANNELS   = 2;
    localparam int CHAN_WIDTH     = 1;
    localparam int ADDR_WIDTH     = 32;
    localparam int AXI_DATA_WIDTH = 64;
    localparam int AXI_ID_WIDTH   = 4;

    // Free inputs
    (* anyseq *) reg                       ctrlrd_valid;
    (* anyseq *) reg  [ADDR_WIDTH-1:0]     ctrlrd_pkt_addr;
    (* anyseq *) reg  [31:0]               ctrlrd_pkt_data;
    (* anyseq *) reg  [31:0]               ctrlrd_pkt_mask;
    (* anyseq *) reg  [8:0]                cfg_ctrlrd_max_try;
    (* anyseq *) reg                       cfg_channel_reset;
    (* anyseq *) reg                       tick_1us;
    (* anyseq *) reg                       ar_ready;
    (* anyseq *) reg                       r_valid;
    (* anyseq *) reg  [AXI_DATA_WIDTH-1:0] r_data;
    (* anyseq *) reg  [AXI_ID_WIDTH-1:0]   r_id;
    (* anyseq *) reg  [1:0]                r_resp;
    (* anyseq *) reg                       r_last;
    (* anyseq *) reg  [63:0]               i_mon_time;
    (* anyseq *) reg                       mon_ready;

    // DUT outputs
    wire                    ctrlrd_ready;
    wire                    ctrlrd_error;
    wire [31:0]             ctrlrd_result;
    wire                    ctrlrd_engine_idle;
    wire                    ar_valid;
    wire [ADDR_WIDTH-1:0]   ar_addr;
    wire [7:0]              ar_len;
    wire [2:0]              ar_size;
    wire [1:0]              ar_burst;
    wire [AXI_ID_WIDTH-1:0] ar_id;
    wire                    ar_lock;
    wire [3:0]              ar_cache;
    wire [2:0]              ar_prot;
    wire [3:0]              ar_qos;
    wire [3:0]              ar_region;
    wire                    r_ready;
    wire                    mon_valid;
    wire [127:0]            mon_packet;
    wire [63:0]             mon_timestamp;

    ctrlrd_engine #(
        .CHANNEL_ID     (CHANNEL_ID),
        .NUM_CHANNELS   (NUM_CHANNELS),
        .CHAN_WIDTH     (CHAN_WIDTH),
        .ADDR_WIDTH     (ADDR_WIDTH),
        .AXI_DATA_WIDTH (AXI_DATA_WIDTH),
        .AXI_ID_WIDTH   (AXI_ID_WIDTH)
    ) dut (
        .clk                (clk),
        .rst_n              (rst_n),
        .ctrlrd_valid       (ctrlrd_valid),
        .ctrlrd_ready       (ctrlrd_ready),
        .ctrlrd_pkt_addr    (ctrlrd_pkt_addr),
        .ctrlrd_pkt_data    (ctrlrd_pkt_data),
        .ctrlrd_pkt_mask    (ctrlrd_pkt_mask),
        .ctrlrd_error       (ctrlrd_error),
        .ctrlrd_result      (ctrlrd_result),
        .cfg_ctrlrd_max_try (cfg_ctrlrd_max_try),
        .cfg_channel_reset  (cfg_channel_reset),
        .tick_1us           (tick_1us),
        .ctrlrd_engine_idle (ctrlrd_engine_idle),
        .ar_valid           (ar_valid),
        .ar_ready           (ar_ready),
        .ar_addr            (ar_addr),
        .ar_len             (ar_len),
        .ar_size            (ar_size),
        .ar_burst           (ar_burst),
        .ar_id              (ar_id),
        .ar_lock            (ar_lock),
        .ar_cache           (ar_cache),
        .ar_prot            (ar_prot),
        .ar_qos             (ar_qos),
        .ar_region          (ar_region),
        .r_valid            (r_valid),
        .r_ready            (r_ready),
        .r_data             (r_data),
        .r_id               (r_id),
        .r_resp             (r_resp),
        .r_last             (r_last),
        .i_mon_time         (i_mon_time),
        .mon_valid          (mon_valid),
        .mon_ready          (mon_ready),
        .mon_packet         (mon_packet),
        .mon_timestamp      (mon_timestamp)
    );

    // =========================================================================
    // Formal infrastructure
    // =========================================================================
    reg [7:0] f_past_valid = 0;
    always @(posedge clk)
        f_past_valid <= f_past_valid + (f_past_valid < 8'hFF);

    initial assume (!rst_n);
    always @(posedge clk) begin
        if (f_past_valid >= 2) assume (rst_n);
    end

    wire f_ar_xfer = ar_valid && ar_ready;
    wire f_r_xfer  = r_valid && r_ready && r_last;

    // Ghost: one AR may be outstanding (accepted, R beat not yet returned).
    reg                    f_outstanding = 0;
    reg [AXI_ID_WIDTH-1:0] f_ar_id       = 0;
    always @(posedge clk) begin
        if (!rst_n) begin
            f_outstanding <= 1'b0;
        end else begin
            if (f_ar_xfer) begin
                f_outstanding <= 1'b1;
                f_ar_id       <= ar_id;
            end else if (f_r_xfer) begin
                f_outstanding <= 1'b0;
            end
        end
    end

    // =========================================================================
    // Environment: an AXI slave that answers only what it was asked
    // =========================================================================
    always @(posedge clk) begin
        if (rst_n) begin
            // A response exists only for the outstanding read, with its ID and
            // as the single beat the engine asked for.
            assume (!r_valid || (f_outstanding && r_id == f_ar_id && r_last));
            // AXI: R holds until accepted.
            if (f_past_valid > 0 && $past(rst_n) && $past(r_valid && !r_ready)) begin
                assume (r_valid);
                assume ($stable(r_data));
                assume ($stable(r_resp));
                assume ($stable(r_id));
            end
        end
    end

    // =========================================================================
    // Properties
    // =========================================================================
    always @(posedge clk) begin
        // P1: reset leaves the engine idle with nothing on the fabric
        if (f_past_valid > 0 && $past(!rst_n)) begin
            ap_reset_idle:    assert (ctrlrd_engine_idle);
            ap_reset_no_ar:   assert (!ar_valid);
            ap_reset_no_err:  assert (!ctrlrd_error);
        end

        if (rst_n) begin
            // P2: a single 32-bit INCR beat carrying the channel's ID
            if (ar_valid) begin
                ap_ar_len:   assert (ar_len == 8'd0);
                ap_ar_burst: assert (ar_burst == 2'b01);
                ap_ar_id:    assert (ar_id[CHAN_WIDTH-1:0] == CHANNEL_ID[CHAN_WIDTH-1:0]);
            end
            // P3: AR stability, channel reset included (TASK-014 drain)
            if (f_past_valid > 0 && $past(rst_n) && $past(ar_valid && !ar_ready)) begin
                ap_ar_hold:        assert (ar_valid);
                ap_ar_addr_stable: assert ($stable(ar_addr));
                ap_ar_id_stable:   assert ($stable(ar_id));
            end
            // P4: no second AR while an R beat is owed
            if (f_ar_xfer)
                ap_no_double_issue: assert (!f_outstanding);
            // P5: r_ready only while an R beat is owed
            if (r_ready)
                ap_rready_owed: assert (f_outstanding);
            // P6: idle means nothing outstanding on the fabric
            if (ctrlrd_engine_idle) begin
                ap_idle_no_ar:  assert (!ar_valid);
                ap_idle_no_out: assert (!f_outstanding);
            end
        end
    end

    // =========================================================================
    // Covers
    // =========================================================================
    reg f_reset_mid_txn = 0;
    always @(posedge clk) begin
        if (!rst_n) f_reset_mid_txn <= 1'b0;
        else if (cfg_channel_reset && (ar_valid || f_outstanding)) f_reset_mid_txn <= 1'b1;
    end
    always @(posedge clk) begin
        if (rst_n) begin
            // C1: a channel reset landed mid-transaction and the R beat was still drained
            cp_drain_after_reset: cover (f_reset_mid_txn && f_r_xfer);
            // C2: back to idle after a completed transaction
            cp_idle_after_txn: cover (f_past_valid > 8 && $past(f_outstanding) && !f_outstanding && ctrlrd_engine_idle);
        end
    end

endmodule : formal_ctrlrd_engine
