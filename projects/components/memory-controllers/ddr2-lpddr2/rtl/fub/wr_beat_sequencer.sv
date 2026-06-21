// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2026 sean galloway
//
// Module: wr_beat_sequencer
// Purpose: Pull W beats out of the axi_frontend's `w_buf` via the wr CAM's
//          beat_pull port, pack them into DFI_RATE DRAM beats per DFI cycle,
//          drive dfi_wrdata / dfi_wrdata_en / dfi_wrdata_mask with PHY
//          alignment, and emit b_complete when the write retires.
//
// v2 architecture (multi-outstanding):
//          Up to MAX_CONCURRENT ops can be in flight at once. The FUB
//          maintains MAX_CONCURRENT per-op contexts; each context holds
//          (slot, len, staging buffer, pull progress, wait counter).
//
//          PULL pipeline (one beat_pull port shared across ops):
//            * Picks the first op needing pulls (priority encoder)
//            * Pulls one beat per cycle into that op's staging buffer
//            * Independent of DRIVE — PULL can run for op[1] while DRIVE
//              runs for op[0]
//
//          DRIVE pipeline (one dfi_wrdata bus shared across ops):
//            * Drives ops in op-valid acceptance order (FIFO)
//            * For each op at head: count t_phy_wrlat from acceptance,
//              then drive the burst from the staging buffer
//            * After burst: pop FIFO, free op slot, emit b_complete
//
//          op_ready_o is high whenever ANY op slot is free → the
//          scheduler can issue back-to-back WRs without waiting for
//          the previous DRIVE to complete.
//
// AXI ↔ DFI mask polarity:
//          AXI wstrb=1 means "write this byte". DFI mask=1 means
//          "MASK this byte (don't write)". So dfi_wrdata_mask = ~wstrb.
//
// v2 / v3 TODO:
//   * (streaming pre-pull) PULL still starts at op-acceptance time. For
//     bursts where len > t_phy_wrlat, the DRIVE start will be delayed
//     until PULL completes — wait_cnt is gated on r_op_pull_done. A
//     future revision monitors wr_cmd_cam snapshots and pre-pulls before
//     the WR command is issued.
//   * (back-to-back DRIVE) v2 assumes the scheduler respects tCCD so
//     two ops' DRIVE windows don't overlap. If they would, the second
//     op's DRIVE waits until the first finishes, which violates the
//     PHY's t_phy_wrlat window for op[1].

`timescale 1ns / 1ps

`include "reset_defs.svh"

module wr_beat_sequencer
    import ddr2_lpddr2_pkg::*;
#(
    parameter int WR_CAM_DEPTH    = 16,
    parameter int W_BUF_PTR_WIDTH = 7,
    parameter int BURST_LEN_WIDTH = 8,
    parameter int DRAM_BEAT_WIDTH = 64,
    parameter int DFI_RATE        = 2,                                // 2 or 4
    parameter int DFI_DATA_WIDTH  = DRAM_BEAT_WIDTH * DFI_RATE,
    parameter int DRAM_STRB_WIDTH = DRAM_BEAT_WIDTH / 8,
    parameter int DFI_STRB_WIDTH  = DFI_DATA_WIDTH / 8,
    parameter int DFI_EN_WIDTH    = 1,
    parameter int MAX_BURST_LEN   = 256,
    // v2 multi-outstanding: number of concurrent ops in flight.
    parameter int MAX_CONCURRENT  = 2,

    parameter int WSL = $clog2(WR_CAM_DEPTH),
    parameter int WPW = W_BUF_PTR_WIDTH,
    parameter int BLW = BURST_LEN_WIDTH,
    parameter int RATE_LOG2 = $clog2(DFI_RATE),
    parameter int MCL = (MAX_CONCURRENT > 1) ? $clog2(MAX_CONCURRENT) : 1
) (
    input  logic                       mc_clk,
    input  logic                       mc_rst_n,

    // ----- timing (CSR-loaded after PHY init) -----
    input  logic [3:0]                 cwl_i,            // CAS write latency (informational; unused)
    input  logic [7:0]                 t_phy_wrlat_i,    // PHY wrdata_en latency from WRITE command

    // ----- write-op handshake from scheduler -----
    input  logic                       op_valid_i,
    output logic                       op_ready_o,
    input  logic [WSL-1:0]             op_slot_i,
    input  logic [BLW-1:0]             op_len_i,

    // ----- pull beats out of axi_frontend's w_buf -----
    output logic                       beat_pull_strb_o,
    output logic [WSL-1:0]             beat_pull_slot_o,
    input  logic [WPW-1:0]             beat_pull_ptr_i,
    input  logic [WPW-1:0]             beat_pull_strb_ptr_i,
    input  logic                       beat_pull_last_i,
    input  logic [DRAM_BEAT_WIDTH-1:0] wbuf_rd_data_i,
    input  logic [DRAM_STRB_WIDTH-1:0] wbuf_rd_strb_i,

    // ----- DFI write data interface -----
    output logic [DFI_DATA_WIDTH-1:0]  dfi_wrdata_o,
    output logic [DFI_EN_WIDTH-1:0]    dfi_wrdata_en_o,
    output logic [DFI_STRB_WIDTH-1:0]  dfi_wrdata_mask_o,

    // ----- b_complete back to wr CAM -----
    output logic                       b_complete_strb_o,
    output logic [WSL-1:0]             b_complete_slot_o
);

    localparam int MAX_LOG2 = $clog2(MAX_BURST_LEN);

    //=========================================================================
    // Per-op contexts (MAX_CONCURRENT slots)
    //=========================================================================
    logic [MAX_CONCURRENT-1:0]            r_op_valid;
    logic [MAX_CONCURRENT-1:0][WSL-1:0]   r_op_slot;
    logic [MAX_CONCURRENT-1:0][BLW-1:0]   r_op_len;
    logic [MAX_CONCURRENT-1:0][BLW-1:0]   r_op_beats_pulled;
    logic [MAX_CONCURRENT-1:0]            r_op_pull_done;
    logic [MAX_CONCURRENT-1:0][7:0]       r_op_wait_cnt;
    logic [MAX_CONCURRENT-1:0]            r_op_drive_started;
    logic [MAX_CONCURRENT-1:0][BLW-1:0]   r_op_dfi_cycle_cnt;

    // Per-op staging buffers — stored as 2D arrays to keep distributed
    // memory friendly. Total: MAX_CONCURRENT * MAX_BURST_LEN * DRAM_BEAT_WIDTH.
    logic [DRAM_BEAT_WIDTH-1:0] r_stage_data [MAX_CONCURRENT][MAX_BURST_LEN];
    logic [DRAM_STRB_WIDTH-1:0] r_stage_strb [MAX_CONCURRENT][MAX_BURST_LEN];

    //=========================================================================
    // DRIVE order FIFO — ops are driven in op-valid acceptance order.
    // Small FIFO (depth MAX_CONCURRENT) of op slot indices.
    //=========================================================================
    logic [MAX_CONCURRENT-1:0][MCL-1:0] r_drive_fifo;
    logic [MCL:0]                       r_drive_fifo_count;

    //=========================================================================
    // Free-slot priority encoder for allocation.
    //=========================================================================
    logic           w_has_free;
    logic [MCL-1:0] w_free_slot;
    always_comb begin
        w_has_free  = 1'b0;
        w_free_slot = '0;
        for (int unsigned i = 0; i < MAX_CONCURRENT; i++) begin
            if (!w_has_free && !r_op_valid[i]) begin
                w_has_free  = 1'b1;
                w_free_slot = MCL'(i);
            end
        end
    end

    //=========================================================================
    // PULL arbiter — first op needing a pull wins. The PULL is gated on
    // the REGISTERED beat_pull_strb_o so the wr CAM has a cycle to
    // respond after seeing the strobe. The winning op index is also
    // registered (r_pull_op_idx) so the latch on the response cycle
    // targets the same op that the strobe was emitted for, even when
    // the comb winner has flipped (e.g., previous op's pull_done just
    // committed).
    //=========================================================================
    logic           w_pull_have_winner;
    logic [MCL-1:0] w_pull_winner;
    always_comb begin
        w_pull_have_winner = 1'b0;
        w_pull_winner      = '0;
        for (int unsigned i = 0; i < MAX_CONCURRENT; i++) begin
            if (!w_pull_have_winner && r_op_valid[i] && !r_op_pull_done[i]) begin
                w_pull_have_winner = 1'b1;
                w_pull_winner      = MCL'(i);
            end
        end
    end

    // Registered companion of beat_pull_strb_o: holds the op-index that
    // the strobe was emitted for. Used as the latch destination on the
    // response cycle.
    logic [MCL-1:0] r_pull_op_idx;
    logic           r_pull_strb_pending;

    //=========================================================================
    // DRIVE arbiter — only the op at the FIFO head matters.
    //=========================================================================
    logic [MCL-1:0] w_drive_op;
    assign w_drive_op = r_drive_fifo[0];

    logic w_drive_active;
    assign w_drive_active = (r_drive_fifo_count > '0)
                         && r_op_valid[w_drive_op]
                         && r_op_pull_done[w_drive_op]
                         && (r_op_wait_cnt[w_drive_op] == 8'd0)
                         && r_op_drive_started[w_drive_op];

    //=========================================================================
    // Pre-compute DFI cycles needed for the driving op's burst.
    //=========================================================================
    logic [BLW:0] w_dfi_cycles_total;
    assign w_dfi_cycles_total =
        ({1'b0, r_op_len[w_drive_op]} + (BLW+1)'(DFI_RATE - 1)) >> RATE_LOG2;

    logic w_drive_last_cycle;
    assign w_drive_last_cycle = w_drive_active
                             && ((r_op_dfi_cycle_cnt[w_drive_op] + BLW'(1))
                                  == BLW'(w_dfi_cycles_total));

    //=========================================================================
    // Per-lane beat indices for the driving op.
    //=========================================================================
    logic [BLW:0]        w_beat_idx_full [DFI_RATE];
    logic [MAX_LOG2-1:0] w_beat_idx      [DFI_RATE];
    logic                w_beat_in_burst [DFI_RATE];
    for (genvar r = 0; r < DFI_RATE; r++) begin : g_pack_idx
        assign w_beat_idx_full[r] =
            ({1'b0, r_op_dfi_cycle_cnt[w_drive_op]} << RATE_LOG2)
            + (BLW+1)'(r);
        assign w_beat_idx[r]      = w_beat_idx_full[r][MAX_LOG2-1:0];
        assign w_beat_in_burst[r] =
            (w_beat_idx_full[r] < {1'b0, r_op_len[w_drive_op]});
    end

    //=========================================================================
    // Combinational DFI wrdata pack for the current driving op.
    //=========================================================================
    logic [DFI_DATA_WIDTH-1:0] w_dfi_wrdata;
    logic [DFI_STRB_WIDTH-1:0] w_dfi_wrdata_mask;
    logic [DFI_EN_WIDTH-1:0]   w_dfi_wrdata_en;
    always_comb begin
        w_dfi_wrdata      = '0;
        w_dfi_wrdata_mask = '1;
        w_dfi_wrdata_en   = '0;
        if (w_drive_active) begin
            w_dfi_wrdata_en = '1;
            for (int unsigned r = 0; r < DFI_RATE; r++) begin
                if (w_beat_in_burst[r]) begin
                    w_dfi_wrdata[r*DRAM_BEAT_WIDTH +: DRAM_BEAT_WIDTH]
                        = r_stage_data[w_drive_op][w_beat_idx[r]];
                    w_dfi_wrdata_mask[r*DRAM_STRB_WIDTH +: DRAM_STRB_WIDTH]
                        = ~r_stage_strb[w_drive_op][w_beat_idx[r]];
                end
            end
        end
    end

    //=========================================================================
    // Sequential state update.
    //=========================================================================
    `ALWAYS_FF_RST(mc_clk, mc_rst_n, begin
        if (`RST_ASSERTED(mc_rst_n)) begin
            r_op_valid         <= '0;
            r_op_pull_done     <= '0;
            r_op_drive_started <= '0;
            r_op_beats_pulled  <= '{default: '0};
            r_op_wait_cnt      <= '{default: '0};
            r_op_dfi_cycle_cnt <= '{default: '0};
            r_drive_fifo_count <= '0;
            r_pull_op_idx      <= '0;
            r_pull_strb_pending<= 1'b0;
            for (int unsigned i = 0; i < MAX_CONCURRENT; i++) begin
                r_op_slot[i] <= '0;
                r_op_len [i] <= '0;
                r_drive_fifo[i] <= '0;
            end
        end else begin
            //---------------------------------------------------------------
            // 1. Allocate new op on op_valid handshake.
            //---------------------------------------------------------------
            if (op_valid_i && op_ready_o) begin
                r_op_valid        [w_free_slot] <= 1'b1;
                r_op_slot         [w_free_slot] <= op_slot_i;
                r_op_len          [w_free_slot] <= op_len_i;
                r_op_beats_pulled [w_free_slot] <= '0;
                r_op_pull_done    [w_free_slot] <= 1'b0;
                r_op_wait_cnt     [w_free_slot] <= t_phy_wrlat_i;
                r_op_drive_started[w_free_slot] <= 1'b1;
                r_op_dfi_cycle_cnt[w_free_slot] <= '0;
                // Push onto drive-order FIFO at tail.
                r_drive_fifo[r_drive_fifo_count[MCL-1:0]] <= w_free_slot;
                r_drive_fifo_count <= r_drive_fifo_count + 1'b1;
            end

            //---------------------------------------------------------------
            // 2. PULL — latch the response using the REGISTERED op-index
            //    (r_pull_op_idx) that the strobe was emitted for. Using
            //    the comb winner here would race when the previous op's
            //    pull_done just committed and flipped the comb winner.
            //---------------------------------------------------------------
            if (r_pull_strb_pending
                && r_op_valid[r_pull_op_idx]
                && !r_op_pull_done[r_pull_op_idx]) begin
                r_stage_data[r_pull_op_idx]
                    [r_op_beats_pulled[r_pull_op_idx][MAX_LOG2-1:0]]
                    <= wbuf_rd_data_i;
                r_stage_strb[r_pull_op_idx]
                    [r_op_beats_pulled[r_pull_op_idx][MAX_LOG2-1:0]]
                    <= wbuf_rd_strb_i;
                r_op_beats_pulled[r_pull_op_idx]
                    <= r_op_beats_pulled[r_pull_op_idx] + BLW'(1);
                if (beat_pull_last_i) begin
                    r_op_pull_done[r_pull_op_idx] <= 1'b1;
                end
            end

            // Track which op the (next-cycle) strobe is being emitted for.
            r_pull_strb_pending <= w_pull_have_winner;
            if (w_pull_have_winner) begin
                r_pull_op_idx <= w_pull_winner;
            end

            //---------------------------------------------------------------
            // 3. Wait countdown — every op slot with wait_cnt > 0 decrements
            //    each cycle.  (Wait timer starts at op acceptance and
            //    counts the t_phy_wrlat window from the WR command.)
            //---------------------------------------------------------------
            for (int unsigned i = 0; i < MAX_CONCURRENT; i++) begin
                if (r_op_valid[i] && r_op_wait_cnt[i] > 8'd0) begin
                    r_op_wait_cnt[i] <= r_op_wait_cnt[i] - 8'd1;
                end
            end

            //---------------------------------------------------------------
            // 4. DRIVE — head-of-FIFO op increments its dfi_cycle_cnt.
            //---------------------------------------------------------------
            if (w_drive_active) begin
                r_op_dfi_cycle_cnt[w_drive_op]
                    <= r_op_dfi_cycle_cnt[w_drive_op] + BLW'(1);
                if (w_drive_last_cycle) begin
                    // Free the op slot, pop the FIFO.
                    r_op_valid        [w_drive_op] <= 1'b0;
                    r_op_pull_done    [w_drive_op] <= 1'b0;
                    r_op_drive_started[w_drive_op] <= 1'b0;
                    for (int unsigned i = 0; i < MAX_CONCURRENT-1; i++) begin
                        r_drive_fifo[i] <= r_drive_fifo[i+1];
                    end
                    r_drive_fifo_count <= r_drive_fifo_count - 1'b1;
                end
            end
        end
    end)

    //=========================================================================
    // Strict-flop outputs.
    //=========================================================================
    `ALWAYS_FF_RST(mc_clk, mc_rst_n, begin
        if (`RST_ASSERTED(mc_rst_n)) begin
            op_ready_o        <= 1'b1;
            beat_pull_strb_o  <= 1'b0;
            beat_pull_slot_o  <= '0;
            dfi_wrdata_o      <= '0;
            dfi_wrdata_mask_o <= '1;
            dfi_wrdata_en_o   <= '0;
            b_complete_strb_o <= 1'b0;
            b_complete_slot_o <= '0;
        end else begin
            op_ready_o        <= w_has_free;
            beat_pull_strb_o  <= w_pull_have_winner;
            beat_pull_slot_o  <= r_op_slot[w_pull_winner];
            dfi_wrdata_o      <= w_dfi_wrdata;
            dfi_wrdata_mask_o <= w_dfi_wrdata_mask;
            dfi_wrdata_en_o   <= w_dfi_wrdata_en;
            b_complete_strb_o <= w_drive_last_cycle;
            b_complete_slot_o <= r_op_slot[w_drive_op];
        end
    end)

    // Signals not consumed in v2.
    wire unused_v2 = |{ cwl_i, beat_pull_ptr_i, beat_pull_strb_ptr_i };

endmodule : wr_beat_sequencer
