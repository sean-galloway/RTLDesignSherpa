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
// v2.1 streaming:
//          DRIVE is no longer gated on the entire burst being pulled
//          (was r_op_pull_done). Instead each DFI cycle only needs
//          DFI_RATE beats buffered. Drive runs as soon as the current
//          cycle has enough data — pull continues in parallel.
//
//          Constraint: pull rate is 1 beat/cycle while drive consumes
//          DFI_RATE beats/cycle, so drive will outrun pull for bursts
//          where len > t_phy_wrlat * DFI_RATE. For those cases, the
//          scheduler must enforce t_phy_wrlat >= ceil(len/DFI_RATE), or
//          the wbuf_ext_rd interface must be widened to deliver
//          DFI_RATE beats/cycle in a future revision.
//
// v3 TODO:
//   * (true pre-pull) Currently PULL still starts at op-acceptance time.
//     A future revision monitors wr_cmd_cam snapshots and pre-pulls
//     beats before the WR command issues — eliminating the underrun
//     constraint above entirely.
//   * (back-to-back DRIVE) v2 assumes the scheduler respects tCCD so
//     two ops' DRIVE windows don't overlap. If they would, the second
//     op's DRIVE waits until the first finishes, which violates the
//     PHY's t_phy_wrlat window for op[1].

`timescale 1ns / 1ps

`include "reset_defs.svh"

module wr_beat_sequencer
    import pumice_pkg::*;
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
    // v3 pre-pull: when 1, the op context is allocated (and its data pull
    // started) on the scheduler's PENDING-write signal (wr_prepull_*), BEFORE
    // the WR command is accepted; DRIVE is held until op_valid (the command).
    // With the scheduler gating the WR command on wr_data_ready_o, the write
    // data is staged by command time -> dfi_wrdata concurrent with the command
    // (a7ddrphy write_latency=0), no cmd-delay shim. PREPULL_EN=0 is the
    // original behavior (alloc + drive both on op_valid).
    parameter bit PREPULL_EN      = 1'b0,

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
    // DDR2/LPDDR2 burst length (DRAM beats per WR command). The DRAM
    // expects exactly bl_i beats per WR regardless of how many AXI beats
    // the host issued; bursts shorter than bl_i are padded with masked
    // beats. bl_i=0 is treated as "no padding" (legacy / FUB-tests path).
    input  logic [3:0]                 bl_i,

    // ----- write-op handshake from scheduler -----
    input  logic                       op_valid_i,
    output logic                       op_ready_o,
    input  logic [WSL-1:0]             op_slot_i,
    input  logic [BLW-1:0]             op_len_i,

    // ----- pre-pull: scheduler's PENDING write (asserted from select through
    //       command issue, slot locked). Start pulling this slot's data early
    //       so it is staged by the time the WR command is accepted. -----
    input  logic                       wr_prepull_valid_i,
    input  logic [WSL-1:0]             wr_prepull_slot_i,
    input  logic [BLW-1:0]             wr_prepull_len_i,
    output logic                       wr_data_ready_o,   // >=DFI_RATE beats staged

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
    //
    // Mirror of the #31 fix on rd_cl_aligner: was a shift FIFO
    // (r_drive_fifo[i] <= r_drive_fifo[i+1] on drive-last) with
    // r_drive_fifo_count updated by both alloc (+1) and shift (-1)
    // in the same always_ff. Same-cycle alloc + drive-last raced
    // via SystemVerilog last-assignment semantics and dropped ops.
    // Now: proper circular FIFO with MCL+1-bit head/tail pointers,
    // r_drive_fifo entries never move, r_drive_fifo_count updates
    // via a single combined-delta NBA. Every pointer has exactly
    // one update path.
    //=========================================================================
    logic [MAX_CONCURRENT-1:0][MCL-1:0] r_drive_fifo;
    logic [MCL:0]                       r_drive_fifo_count;
    logic [MCL:0]                       r_drive_head_ptr;  // pop position
    logic [MCL:0]                       r_drive_tail_ptr;  // next alloc

    logic [MCL:0] w_drive_head_next;
    logic [MCL:0] w_drive_tail_next;
    assign w_drive_head_next = r_drive_head_ptr + (MCL+1)'(1);
    assign w_drive_tail_next = r_drive_tail_ptr + (MCL+1)'(1);

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
    // Pre-pull lookups: find an allocated op (drive NOT yet started) matching a
    // given slot. Used to (a) avoid double-allocating a pre-pulled slot, and
    // (b) on op_valid, "adopt" the pre-pulled op instead of allocating fresh.
    //=========================================================================
    logic           w_ov_prealloc_hit;   // op matching op_slot_i (armable)
    logic [MCL-1:0] w_ov_prealloc_idx;
    logic           w_pp_alloc_hit;       // op already allocated for prepull slot
    logic [MCL-1:0] w_pp_alloc_idx;
    always_comb begin
        w_ov_prealloc_hit = 1'b0; w_ov_prealloc_idx = '0;
        w_pp_alloc_hit    = 1'b0; w_pp_alloc_idx    = '0;
        for (int unsigned i = 0; i < MAX_CONCURRENT; i++) begin
            if (r_op_valid[i] && !r_op_drive_started[i]) begin
                if (!w_ov_prealloc_hit && r_op_slot[i] == op_slot_i) begin
                    w_ov_prealloc_hit = 1'b1; w_ov_prealloc_idx = MCL'(i);
                end
                if (!w_pp_alloc_hit && r_op_slot[i] == wr_prepull_slot_i) begin
                    w_pp_alloc_hit = 1'b1; w_pp_alloc_idx = MCL'(i);
                end
            end
        end
    end

    // wr_data_ready: the pre-pulled op for the scheduler's pending slot has at
    // least DFI_RATE beats staged (enough for the first drive cycle) or is fully
    // pulled. The scheduler gates the WR command on this so drive can present
    // wrdata concurrent with the command (write_latency=0).
    always_comb begin
        wr_data_ready_o = 1'b1;
        if (PREPULL_EN && wr_prepull_valid_i) begin
            wr_data_ready_o = w_pp_alloc_hit
                && (r_op_pull_done[w_pp_alloc_idx]
                    || ({1'b0, r_op_beats_pulled[w_pp_alloc_idx]}
                        >= (BLW+1)'(DFI_RATE)));
        end
    end

    // Pre-pull allocation this cycle: a pending write whose slot isn't already
    // allocated, there's a free slot, and op_valid isn't consuming it.
    logic w_prepull_alloc;
    assign w_prepull_alloc = PREPULL_EN && wr_prepull_valid_i
                          && !w_pp_alloc_hit && w_has_free
                          && !(op_valid_i && op_ready_o && !w_ov_prealloc_hit);

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
    assign w_drive_op = r_drive_fifo[r_drive_head_ptr[MCL-1:0]];

    //=========================================================================
    // Pre-compute DFI cycles needed for the driving op's burst.
    // DDR2/LPDDR2 fixes the DRAM beat count per WR at BL (programmed via
    // MR0 / MR1). When the AXI burst is shorter than BL, we still drive
    // BL/DFI_RATE DFI cycles, masking the unused beats (full mask = no
    // write). bl_i=0 means "no padding" — for FUB tests + the v0 flow
    // where the BL constraint isn't yet wired through.
    //=========================================================================
    logic [BLW:0] w_op_dfi_cycles;
    assign w_op_dfi_cycles =
        ({1'b0, r_op_len[w_drive_op]} + (BLW+1)'(DFI_RATE - 1)) >> RATE_LOG2;

    logic [BLW:0] w_bl_dfi_cycles;
    assign w_bl_dfi_cycles =
        (bl_i == 4'd0)
            ? (BLW+1)'(1'b0)
            : ((((BLW+1)'(bl_i)) + (BLW+1)'(DFI_RATE - 1)) >> RATE_LOG2);

    logic [BLW:0] w_dfi_cycles_total;
    assign w_dfi_cycles_total = (w_op_dfi_cycles > w_bl_dfi_cycles)
                              ? w_op_dfi_cycles
                              : w_bl_dfi_cycles;

    // Streaming DRIVE gate (v2.1): drive can start as soon as the
    // current DFI cycle has DFI_RATE beats buffered, instead of waiting
    // for the entire burst to be pulled. The driving op's current cycle
    // needs beats [dfi_cycle_cnt*DFI_RATE .. (dfi_cycle_cnt+1)*DFI_RATE-1]
    // — that's (dfi_cycle_cnt+1)*DFI_RATE beats total pulled so far.
    // For the last (potentially partial) DFI cycle, require beats_pulled
    // >= r_op_len (== pull_done) since the last cycle may use fewer than
    // DFI_RATE beats.
    //
    // Important constraint: for bursts where len > t_phy_wrlat*DFI_RATE,
    // pull will lag drive (pull is 1 beat/cycle, drive consumes DFI_RATE
    // beats/cycle). To avoid underrun, the scheduler must ensure
    // t_phy_wrlat >= ceil(len/DFI_RATE), or a future revision widens
    // wbuf_ext_rd to DFI_RATE beats/cycle.
    logic [BLW:0] w_beats_needed_for_cur_cycle;
    assign w_beats_needed_for_cur_cycle =
        ({1'b0, r_op_dfi_cycle_cnt[w_drive_op]} + (BLW+1)'(1)) << RATE_LOG2;

    logic w_enough_buffered;
    assign w_enough_buffered =
        r_op_pull_done[w_drive_op] ||
        ({1'b0, r_op_beats_pulled[w_drive_op]} >= w_beats_needed_for_cur_cycle);

    logic w_drive_active;
    assign w_drive_active = (r_drive_fifo_count > '0)
                         && r_op_valid[w_drive_op]
                         && w_enough_buffered
                         && (r_op_wait_cnt[w_drive_op] == 8'd0)
                         && r_op_drive_started[w_drive_op];

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
            r_drive_head_ptr   <= '0;
            r_drive_tail_ptr   <= '0;
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
            //    Writes r_drive_fifo at tail and advances r_drive_tail_ptr.
            //    No FIFO shift ever runs on this or on drive-last (see
            //    section 4) — same fix pattern as rd_cl_aligner #31.
            //---------------------------------------------------------------
            if (!PREPULL_EN) begin
                // Original path: allocate + start driving on op_valid.
                if (op_valid_i && op_ready_o) begin
                    r_op_valid        [w_free_slot] <= 1'b1;
                    r_op_slot         [w_free_slot] <= op_slot_i;
                    r_op_len          [w_free_slot] <= op_len_i;
                    r_op_beats_pulled [w_free_slot] <= '0;
                    r_op_pull_done    [w_free_slot] <= 1'b0;
                    r_op_wait_cnt     [w_free_slot] <= t_phy_wrlat_i;
                    r_op_drive_started[w_free_slot] <= 1'b1;
                    r_op_dfi_cycle_cnt[w_free_slot] <= '0;
                    r_drive_fifo[r_drive_tail_ptr[MCL-1:0]] <= w_free_slot;
                    r_drive_tail_ptr <= w_drive_tail_next;
                end
            end else begin
                // Pre-pull path: allocate on the scheduler's PENDING write
                // (start the data pull early, drive_started=0 so DRIVE holds),
                // then ARM drive when the WR command is accepted (op_valid).
                if (w_prepull_alloc) begin
                    r_op_valid        [w_free_slot] <= 1'b1;
                    r_op_slot         [w_free_slot] <= wr_prepull_slot_i;
                    r_op_len          [w_free_slot] <= wr_prepull_len_i;
                    r_op_beats_pulled [w_free_slot] <= '0;
                    r_op_pull_done    [w_free_slot] <= 1'b0;
                    r_op_wait_cnt     [w_free_slot] <= '0;
                    r_op_drive_started[w_free_slot] <= 1'b0;  // pull only, no drive
                    r_op_dfi_cycle_cnt[w_free_slot] <= '0;
                end
                if (op_valid_i && op_ready_o) begin
                    if (w_ov_prealloc_hit) begin
                        // Adopt the pre-pulled op: arm DRIVE now (data staged).
                        r_op_wait_cnt     [w_ov_prealloc_idx] <= t_phy_wrlat_i;
                        r_op_drive_started[w_ov_prealloc_idx] <= 1'b1;
                        r_op_dfi_cycle_cnt[w_ov_prealloc_idx] <= '0;
                        r_drive_fifo[r_drive_tail_ptr[MCL-1:0]] <= w_ov_prealloc_idx;
                        r_drive_tail_ptr <= w_drive_tail_next;
                    end else begin
                        // Fallback: not pre-pulled — allocate + arm as normal.
                        r_op_valid        [w_free_slot] <= 1'b1;
                        r_op_slot         [w_free_slot] <= op_slot_i;
                        r_op_len          [w_free_slot] <= op_len_i;
                        r_op_beats_pulled [w_free_slot] <= '0;
                        r_op_pull_done    [w_free_slot] <= 1'b0;
                        r_op_wait_cnt     [w_free_slot] <= t_phy_wrlat_i;
                        r_op_drive_started[w_free_slot] <= 1'b1;
                        r_op_dfi_cycle_cnt[w_free_slot] <= '0;
                        r_drive_fifo[r_drive_tail_ptr[MCL-1:0]] <= w_free_slot;
                        r_drive_tail_ptr <= w_drive_tail_next;
                    end
                end
            end

            //---------------------------------------------------------------
            // 1b. Combined FIFO-count delta. Single NBA to r_drive_fifo_count
            //     regardless of same-cycle alloc + drive-last (the #31
            //     pathology). alloc:+1, drive-last:-1, both:0, neither:no-op.
            //---------------------------------------------------------------
            if ((op_valid_i && op_ready_o) && !(w_drive_active && w_drive_last_cycle))
                r_drive_fifo_count <= r_drive_fifo_count + 1'b1;
            else if (!(op_valid_i && op_ready_o) && (w_drive_active && w_drive_last_cycle))
                r_drive_fifo_count <= r_drive_fifo_count - 1'b1;

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
            //    On drive-last: free the slot and advance r_drive_head_ptr.
            //    NO FIFO shift. r_drive_fifo_count is written by the
            //    combined-delta block in section 1b above.
            //---------------------------------------------------------------
            if (w_drive_active) begin
                r_op_dfi_cycle_cnt[w_drive_op]
                    <= r_op_dfi_cycle_cnt[w_drive_op] + BLW'(1);
                if (w_drive_last_cycle) begin
                    r_op_valid        [w_drive_op] <= 1'b0;
                    r_op_pull_done    [w_drive_op] <= 1'b0;
                    r_op_drive_started[w_drive_op] <= 1'b0;
                    r_drive_head_ptr <= w_drive_head_next;
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
            // Free slot for a fresh alloc, OR (pre-pull) the pending write's
            // data is staged so op_valid can adopt its pre-pulled op.
            op_ready_o        <= w_has_free
                              || (PREPULL_EN && wr_prepull_valid_i && wr_data_ready_o);
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
