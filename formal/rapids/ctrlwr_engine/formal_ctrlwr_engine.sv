// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// Formal wrapper for ctrlwr_engine (RAPIDS Phase-2 control write engine)
// Run with: sby ctrlwr_engine.sby
//
// PORT-LEVEL properties only (the flat is sv2v output; no hierarchical
// references). The drain-on-channel-reset contract from rapids TASK-014 is
// stated in fabric terms, because the engine's own `ifdef FORMAL block is not
// part of the flat:
//   P1: reset leaves the engine idle with nothing on the fabric
//   P2: an AW is a single 32-bit INCR beat carrying the channel's ID; W is one
//       beat with w_last
//   P3: AW and W stability -- once raised they hold until accepted, channel
//       reset included (an abandoned phase is what TASK-014 removed)
//   P4: W only after its AW was accepted; no second AW while a B is owed
//   P5: b_ready only while a B is owed
//   P6: idle means nothing outstanding on the fabric
//   C1: a B is drained after a channel reset landed mid-transaction
//   C2: the engine returns to idle after a transaction

module formal_ctrlwr_engine (
    input  logic clk,
    input  logic rst_n
);
    localparam int CHANNEL_ID   = 1;
    localparam int NUM_CHANNELS = 2;
    localparam int CHAN_WIDTH   = 1;
    localparam int ADDR_WIDTH   = 32;
    localparam int AXI_ID_WIDTH = 4;

    // Free inputs
    (* anyseq *) reg                     ctrlwr_valid;
    (* anyseq *) reg  [ADDR_WIDTH-1:0]   ctrlwr_pkt_addr;
    (* anyseq *) reg  [31:0]             ctrlwr_pkt_data;
    (* anyseq *) reg                     cfg_channel_reset;
    (* anyseq *) reg                     aw_ready;
    (* anyseq *) reg                     w_ready;
    (* anyseq *) reg                     b_valid;
    (* anyseq *) reg  [AXI_ID_WIDTH-1:0] b_id;
    (* anyseq *) reg  [1:0]              b_resp;
    (* anyseq *) reg  [63:0]             i_mon_time;
    (* anyseq *) reg                     mon_ready;

    // DUT outputs
    wire                    ctrlwr_ready;
    wire                    ctrlwr_error;
    wire                    ctrlwr_engine_idle;
    wire                    aw_valid;
    wire [ADDR_WIDTH-1:0]   aw_addr;
    wire [7:0]              aw_len;
    wire [2:0]              aw_size;
    wire [1:0]              aw_burst;
    wire [AXI_ID_WIDTH-1:0] aw_id;
    wire                    aw_lock;
    wire [3:0]              aw_cache;
    wire [2:0]              aw_prot;
    wire [3:0]              aw_qos;
    wire [3:0]              aw_region;
    wire                    w_valid;
    wire [31:0]             w_data;
    wire [3:0]              w_strb;
    wire                    w_last;
    wire                    b_ready;
    wire                    mon_valid;
    wire [127:0]            mon_packet;
    wire [63:0]             mon_timestamp;

    ctrlwr_engine #(
        .CHANNEL_ID   (CHANNEL_ID),
        .NUM_CHANNELS (NUM_CHANNELS),
        .CHAN_WIDTH   (CHAN_WIDTH),
        .ADDR_WIDTH   (ADDR_WIDTH),
        .AXI_ID_WIDTH (AXI_ID_WIDTH)
    ) dut (
        .clk                (clk),
        .rst_n              (rst_n),
        .ctrlwr_valid       (ctrlwr_valid),
        .ctrlwr_ready       (ctrlwr_ready),
        .ctrlwr_pkt_addr    (ctrlwr_pkt_addr),
        .ctrlwr_pkt_data    (ctrlwr_pkt_data),
        .ctrlwr_error       (ctrlwr_error),
        .cfg_channel_reset  (cfg_channel_reset),
        .ctrlwr_engine_idle (ctrlwr_engine_idle),
        .aw_valid           (aw_valid),
        .aw_ready           (aw_ready),
        .aw_addr            (aw_addr),
        .aw_len             (aw_len),
        .aw_size            (aw_size),
        .aw_burst           (aw_burst),
        .aw_id              (aw_id),
        .aw_lock            (aw_lock),
        .aw_cache           (aw_cache),
        .aw_prot            (aw_prot),
        .aw_qos             (aw_qos),
        .aw_region          (aw_region),
        .w_valid            (w_valid),
        .w_ready            (w_ready),
        .w_data             (w_data),
        .w_strb             (w_strb),
        .w_last             (w_last),
        .b_valid            (b_valid),
        .b_ready            (b_ready),
        .b_id               (b_id),
        .b_resp             (b_resp),
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

    wire f_aw_xfer = aw_valid && aw_ready;
    wire f_w_xfer  = w_valid && w_ready;
    wire f_b_xfer  = b_valid && b_ready;

    // Ghost: one write may be outstanding. f_aw_out: AW accepted, B not yet
    // returned. f_w_owed: AW accepted, its W beat not yet accepted.
    reg                    f_aw_out = 0;
    reg                    f_w_owed = 0;
    reg [AXI_ID_WIDTH-1:0] f_aw_id  = 0;
    always @(posedge clk) begin
        if (!rst_n) begin
            f_aw_out <= 1'b0;
            f_w_owed <= 1'b0;
        end else begin
            if (f_aw_xfer) begin
                f_aw_out <= 1'b1;
                f_w_owed <= 1'b1;
                f_aw_id  <= aw_id;
            end
            if (f_w_xfer) f_w_owed <= 1'b0;
            if (f_b_xfer) f_aw_out <= 1'b0;
        end
    end

    // =========================================================================
    // Environment: an AXI slave that answers only the write it was given
    // =========================================================================
    always @(posedge clk) begin
        if (rst_n) begin
            // B exists only after the whole write (AW and W) was accepted.
            assume (!b_valid || (f_aw_out && !f_w_owed && b_id == f_aw_id));
            // AXI: B holds until accepted.
            if (f_past_valid > 0 && $past(rst_n) && $past(b_valid && !b_ready)) begin
                assume (b_valid);
                assume ($stable(b_resp));
                assume ($stable(b_id));
            end
        end
    end

    // =========================================================================
    // Properties
    // =========================================================================
    always @(posedge clk) begin
        // P1: reset leaves the engine idle with nothing on the fabric
        if (f_past_valid > 0 && $past(!rst_n)) begin
            ap_reset_idle:   assert (ctrlwr_engine_idle);
            ap_reset_no_aw:  assert (!aw_valid);
            ap_reset_no_w:   assert (!w_valid);
            ap_reset_no_err: assert (!ctrlwr_error);
        end

        if (rst_n) begin
            // P2: single 32-bit INCR beat with the channel's ID; W is one beat
            if (aw_valid) begin
                ap_aw_len:   assert (aw_len == 8'd0);
                ap_aw_burst: assert (aw_burst == 2'b01);
                ap_aw_id:    assert (aw_id[CHAN_WIDTH-1:0] == CHANNEL_ID[CHAN_WIDTH-1:0]);
            end
            if (w_valid)
                ap_w_last: assert (w_last);
            // P3: AW and W stability, channel reset included (TASK-014 drain)
            if (f_past_valid > 0 && $past(rst_n) && $past(aw_valid && !aw_ready)) begin
                ap_aw_hold:        assert (aw_valid);
                ap_aw_addr_stable: assert ($stable(aw_addr));
                ap_aw_id_stable:   assert ($stable(aw_id));
            end
            if (f_past_valid > 0 && $past(rst_n) && $past(w_valid && !w_ready)) begin
                ap_w_hold:        assert (w_valid);
                ap_w_data_stable: assert ($stable(w_data));
            end
            // P4: W only after its AW; no second AW while a B is owed
            if (w_valid)
                ap_w_after_aw: assert (f_w_owed);
            if (f_aw_xfer)
                ap_no_double_issue: assert (!f_aw_out);
            // P5: b_ready only while a B is owed
            if (b_ready)
                ap_bready_owed: assert (f_aw_out && !f_w_owed);
            // P6: idle means nothing outstanding on the fabric
            if (ctrlwr_engine_idle) begin
                ap_idle_no_aw:  assert (!aw_valid);
                ap_idle_no_w:   assert (!w_valid);
                ap_idle_no_out: assert (!f_aw_out);
            end
        end
    end

    // =========================================================================
    // Covers
    // =========================================================================
    reg f_reset_mid_txn = 0;
    always @(posedge clk) begin
        if (!rst_n) f_reset_mid_txn <= 1'b0;
        else if (cfg_channel_reset && (aw_valid || w_valid || f_aw_out)) f_reset_mid_txn <= 1'b1;
    end
    always @(posedge clk) begin
        if (rst_n) begin
            // C1: a channel reset landed mid-transaction and the B was still drained
            cp_drain_after_reset: cover (f_reset_mid_txn && f_b_xfer);
            // C2: back to idle after a completed transaction
            cp_idle_after_txn: cover (f_past_valid > 8 && $past(f_aw_out) && !f_aw_out && ctrlwr_engine_idle);
        end
    end

endmodule : formal_ctrlwr_engine
