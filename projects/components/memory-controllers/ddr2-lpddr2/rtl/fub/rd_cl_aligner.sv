// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2026 sean galloway
//
// Module: rd_cl_aligner
// Purpose: Drive `dfi_rddata_en` at the right cycle for an issued READ,
//          capture the PHY's `dfi_rddata` beats (DFI_RATE DRAM beats
//          packed per DFI cycle), and stream them out to the axi_intake's
//          R-emit FSM as DRAM-beat-wide `rd_inject_*` handshakes. Pulse
//          `rd_beat_we` back to the rd CAM per accepted beat so the
//          slot retires after `len` beats.
//
// v2 architecture (multi-outstanding):
//          Up to MAX_CONCURRENT ops can be in flight. The FUB maintains
//          MAX_CONCURRENT per-op contexts, each tracking its own
//          (slot, id, len, wait_cnt, en_remaining, dfi_captured,
//          beats_emitted) and a per-op DFI staging buffer.
//
//          Three pipelines run in parallel, each with its own "head"
//          pointer walking the op-acceptance FIFO:
//            EN pipeline    : drives dfi_rddata_en for the head op
//            CAPTURE pipeline: latches dfi_rddata into the head op's
//                              staging buffer when dfi_rddata_valid fires
//            EMIT pipeline  : streams rd_inject beats to axi_intake
//
//          Each head advances when its phase completes for the head op.
//          The PHY returns rddata in scheduler-issue order, so all three
//          heads walk the same FIFO in order. Op slot is freed when EMIT
//          finishes (beats_emitted == len).
//
//          op_ready_o is high whenever ANY op slot is free.
//
// v2 / v3 TODO:
//   * (OOO across IDs) Emission today is strictly in op-issue order. Full
//     AXI4-compliant OOO across IDs would require per-ID FIFOs. The
//     `rd_in_order_i` input is wired as a placeholder.
//   * Per-op gap during EMIT-head transition: a 1-cycle gap between
//     bursts (allows the strict-flop output lookahead to remain coherent).

`timescale 1ns / 1ps

`include "reset_defs.svh"

module rd_cl_aligner
    import ddr2_lpddr2_pkg::*;
#(
    parameter int RD_CAM_DEPTH    = 16,
    parameter int AXI_ID_WIDTH    = 4,
    parameter int BURST_LEN_WIDTH = 8,
    parameter int DRAM_BEAT_WIDTH = 64,
    parameter int DFI_RATE        = 2,
    parameter int DFI_DATA_WIDTH  = DRAM_BEAT_WIDTH * DFI_RATE,
    parameter int DFI_VALID_WIDTH = 1,
    parameter int DFI_EN_WIDTH    = 1,
    parameter int MAX_BURST_LEN   = 256,
    // v2 multi-outstanding: number of concurrent in-flight read ops.
    parameter int MAX_CONCURRENT  = 2,

    parameter int RSL = $clog2(RD_CAM_DEPTH),
    parameter int IW  = AXI_ID_WIDTH,
    parameter int BLW = BURST_LEN_WIDTH,
    parameter int RATE_LOG2 = $clog2(DFI_RATE),
    parameter int MCL = (MAX_CONCURRENT > 1) ? $clog2(MAX_CONCURRENT) : 1
) (
    input  logic                          mc_clk,
    input  logic                          mc_rst_n,

    // ----- live MR values (CL/AL kept for future scheduler sanity check) -----
    input  logic [3:0]                    cl_i,
    input  logic [3:0]                    al_i,

    // ----- PHY timing (DFI Initialization Status Register-loaded) -----
    input  logic [7:0]                    t_rddata_en_i,

    // ----- TODO: multi-outstanding ordering mode (v2 ignored) -----
    input  logic                          rd_in_order_i,

    // ----- read-op handshake from scheduler -----
    input  logic                          op_valid_i,
    output logic                          op_ready_o,
    input  logic [RSL-1:0]                op_slot_i,
    input  logic [IW-1:0]                 op_id_i,
    input  logic [BLW-1:0]                op_len_i,
    // High on the LAST chunk of a split AR. When low, rd_inject_last_o
    // is masked so the host doesn't see an early rlast on intermediate
    // chunks (issue #22). Tied 1'b1 for callers that never split.
    input  logic                          op_is_last_chunk_i,

    // ----- DFI read data interface -----
    output logic [DFI_EN_WIDTH-1:0]       dfi_rddata_en_o,
    input  logic [DFI_DATA_WIDTH-1:0]     dfi_rddata_i,
    input  logic [DFI_VALID_WIDTH-1:0]    dfi_rddata_valid_i,

    // ----- rd_inject into axi_frontend (one DRAM beat per cycle) -----
    output logic                          rd_inject_valid_o,
    input  logic                          rd_inject_ready_i,
    output logic [IW-1:0]                 rd_inject_id_o,
    output logic [DRAM_BEAT_WIDTH-1:0]    rd_inject_data_o,
    output logic                          rd_inject_last_o,

    // ----- per-beat strobe to rd CAM (beat retire) -----
    output logic                          rd_beat_we_o,
    output logic [RSL-1:0]                rd_beat_slot_o
);

    localparam int MAX_DFI_CYC  = (MAX_BURST_LEN + DFI_RATE - 1) / DFI_RATE;
    localparam int DFI_CYC_LOG2 = (MAX_DFI_CYC > 1) ? $clog2(MAX_DFI_CYC) : 1;

    //=========================================================================
    // Per-op contexts (MAX_CONCURRENT slots)
    //=========================================================================
    logic [MAX_CONCURRENT-1:0]            r_op_valid;
    logic [MAX_CONCURRENT-1:0][RSL-1:0]   r_op_slot;
    logic [MAX_CONCURRENT-1:0][IW-1:0]    r_op_id;
    logic [MAX_CONCURRENT-1:0][BLW-1:0]   r_op_len;
    logic [MAX_CONCURRENT-1:0][7:0]       r_op_wait_cnt;
    logic [MAX_CONCURRENT-1:0][BLW:0]     r_op_en_remaining;
    logic [MAX_CONCURRENT-1:0][BLW:0]     r_op_dfi_captured;
    // ceil(len/DFI_RATE), captured at alloc (constant per op) — see the
    // dfi_cycles_total block. Removes the +/>> from the completion compares.
    logic [MAX_CONCURRENT-1:0][BLW:0]     r_op_dfi_total;
    logic [MAX_CONCURRENT-1:0][BLW-1:0]   r_op_beats_emitted;
    // Per-context is_last_chunk flag — latched at op-accept and read by
    // the EMIT pipeline to gate rd_inject_last_o (issue #22).
    logic [MAX_CONCURRENT-1:0]            r_op_is_last_chunk;

    // Per-op DFI cycle staging.
    logic [DFI_DATA_WIDTH-1:0] r_stage [MAX_CONCURRENT][MAX_DFI_CYC];

    //=========================================================================
    // Op-acceptance FIFO — slot indices in op-valid order.
    //
    // #31: was a shift FIFO (r_fifo[i] <= r_fifo[i+1] on emit-last) with
    // head-idx offsets that decremented to compensate. That compensation
    // raced the same-cycle EN-advance / alloc updates via SystemVerilog
    // last-assignment semantics and dropped ops silently. Now it's a
    // proper circular FIFO: r_fifo entries never move; four absolute
    // pointers walk the array modulo MAX_CONCURRENT. Every pointer has
    // exactly one update path, so no same-cycle race is possible.
    //
    // Pointers are MCL+1 bits so an extra bit disambiguates the
    // full-vs-empty case classical circular FIFOs need to handle
    // (compare all MCL+1 bits for equality; index r_fifo with the low
    // MCL bits).
    //=========================================================================
    logic [MAX_CONCURRENT-1:0][MCL-1:0]   r_fifo;
    logic [MCL:0]                         r_fifo_count;
    logic [MCL:0]                         r_tail_ptr;       // next alloc position
    logic [MCL:0]                         r_emit_head_ptr;  // pop position
    logic [MCL:0]                         r_en_head_ptr;    // EN read position
    logic [MCL:0]                         r_cap_head_ptr;   // CAP read position
    // Registered cap-head op = r_fifo[r_cap_head_ptr], kept in lockstep so the
    // capture CE decode doesn't pay the r_fifo mux (rate=4 FPGA timing).
    logic [MCL-1:0]                       r_cap_op;

    // Pre-compute next-position wraps for the advance guards.
    logic [MCL:0] w_en_head_next;
    logic [MCL:0] w_cap_head_next;
    logic [MCL:0] w_emit_head_next;
    logic [MCL:0] w_tail_next;
    assign w_en_head_next   = r_en_head_ptr   + (MCL+1)'(1);
    assign w_cap_head_next  = r_cap_head_ptr  + (MCL+1)'(1);
    assign w_emit_head_next = r_emit_head_ptr + (MCL+1)'(1);
    assign w_tail_next      = r_tail_ptr      + (MCL+1)'(1);

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
    // EN head + CAPTURE head + EMIT head accessors — read from r_fifo
    // at each pipeline's absolute head pointer (low MCL bits).
    //=========================================================================
    logic [MCL-1:0] w_en_op;
    logic [MCL-1:0] w_emit_op;
    assign w_en_op   = r_fifo[r_en_head_ptr  [MCL-1:0]];
    assign w_emit_op = r_fifo[r_emit_head_ptr[MCL-1:0]];
    // cap-head op is the REGISTERED r_cap_op (see its declaration); the
    // combinational r_fifo[r_cap_head_ptr] is folded into r_cap_op's lockstep.

    //=========================================================================
    // DFI-cycle total per op (= ceil(len/DFI_RATE)). TIMING (rate=4 FPGA
    // closure): precomputed at alloc into r_op_dfi_total (constant per op) so
    // the completion compares don't pay the +/>> on their paths. The CAP total
    // additionally indexes by the REGISTERED cap-head op (r_cap_op, kept in
    // lockstep with r_fifo[r_cap_head_ptr]) so the capture CE decode does not
    // pay the r_fifo mux either. All value-equivalent to the old combinational
    // form (r_op_dfi_total[op] == ceil(r_op_len[op]/DFI_RATE); r_cap_op ==
    // r_fifo[r_cap_head_ptr]); the read-capture behavior is unchanged.
    //=========================================================================
    logic [BLW:0] w_emit_dfi_cycles_total;
    assign w_emit_dfi_cycles_total = r_op_dfi_total[w_emit_op];

    logic [BLW:0] w_en_dfi_cycles_total;
    assign w_en_dfi_cycles_total   = r_op_dfi_total[w_en_op];

    logic [BLW:0] w_cap_dfi_cycles_total;
    assign w_cap_dfi_cycles_total  = r_op_dfi_total[r_cap_op];

    //=========================================================================
    // EN pipeline: drive en for the EN-head op while its en_remaining > 0
    // and its wait_cnt has elapsed.
    //=========================================================================
    logic w_en_active;
    assign w_en_active = (r_fifo_count > '0)
                      && r_op_valid[w_en_op]
                      && (r_op_wait_cnt[w_en_op] == 8'd0)
                      && (r_op_en_remaining[w_en_op] > '0);

    logic w_en_complete_for_head;
    assign w_en_complete_for_head = w_en_active
                                 && (r_op_en_remaining[w_en_op] == (BLW+1)'(1));

    //=========================================================================
    // EMIT pipeline: stream beats from the EMIT-head op's staging buffer.
    // Uses post-handshake lookahead (next_beats) so the registered output
    // stays aligned with what the external consumer captures.
    //=========================================================================
    logic w_handshake;
    assign w_handshake = rd_inject_valid_o && rd_inject_ready_i;

    logic [BLW:0]   w_next_beats_full;
    logic [BLW-1:0] w_next_beats;
    assign w_next_beats_full = {1'b0, r_op_beats_emitted[w_emit_op]}
                             + (w_handshake ? (BLW+1)'(1) : (BLW+1)'(0));
    assign w_next_beats = w_next_beats_full[BLW-1:0];

    logic [DFI_CYC_LOG2-1:0] w_emit_dfi_idx;
    logic [RATE_LOG2-1:0]    w_emit_rate_idx;
    assign w_emit_dfi_idx  = w_next_beats[BLW-1:RATE_LOG2];
    assign w_emit_rate_idx = w_next_beats[RATE_LOG2-1:0];

    logic w_emit_available;
    assign w_emit_available = (w_next_beats_full >> RATE_LOG2)
                            < r_op_dfi_captured[w_emit_op];

    logic w_next_in_burst;
    assign w_next_in_burst = (w_next_beats_full < {1'b0, r_op_len[w_emit_op]});

    logic w_emit_active;
    assign w_emit_active = (r_fifo_count > '0)
                        && r_op_valid[w_emit_op];

    logic [DRAM_BEAT_WIDTH-1:0] w_emit_data;
    assign w_emit_data =
        r_stage[w_emit_op][w_emit_dfi_idx]
               [w_emit_rate_idx * DRAM_BEAT_WIDTH +: DRAM_BEAT_WIDTH];

    //=========================================================================
    // Combinational next-cycle output values.
    //=========================================================================
    logic                       w_op_ready;
    logic [DFI_EN_WIDTH-1:0]    w_dfi_rddata_en;
    logic                       w_rd_inject_valid;
    logic                       w_rd_inject_last;
    logic                       w_rd_beat_we;

    assign w_op_ready        = w_has_free;
    assign w_dfi_rddata_en   = w_en_active ? '1 : '0;
    assign w_rd_inject_valid = w_emit_active && w_next_in_burst
                            && w_emit_available;
    assign w_rd_inject_last  = w_emit_active && w_next_in_burst
                            && ((w_next_beats_full + (BLW+1)'(1))
                                 == {1'b0, r_op_len[w_emit_op]})
                            && r_op_is_last_chunk[w_emit_op];
    assign w_rd_beat_we      = w_handshake;

    //=========================================================================
    // Sequential state update.
    //=========================================================================
    // Combined alloc + emit-last helpers so r_fifo_count only takes one
    // NBA per cycle regardless of concurrent push+pop.
    logic w_alloc;
    logic w_emit_last;
    assign w_alloc     = op_valid_i && op_ready_o;
    assign w_emit_last = w_handshake
                      && ((r_op_beats_emitted[w_emit_op] + BLW'(1))
                          == r_op_len[w_emit_op]);

    `ALWAYS_FF_RST(mc_clk, mc_rst_n, begin
        if (`RST_ASSERTED(mc_rst_n)) begin
            r_op_valid         <= '0;
            r_op_wait_cnt      <= '{default: '0};
            r_op_en_remaining  <= '{default: '0};
            r_op_dfi_captured  <= '{default: '0};
            r_op_dfi_total     <= '{default: '0};
            r_op_beats_emitted <= '{default: '0};
            r_fifo_count       <= '0;
            r_tail_ptr         <= '0;
            r_emit_head_ptr    <= '0;
            r_en_head_ptr      <= '0;
            r_cap_head_ptr     <= '0;
            r_cap_op           <= '0;
            for (int unsigned i = 0; i < MAX_CONCURRENT; i++) begin
                r_op_slot[i] <= '0;
                r_op_id  [i] <= '0;
                r_op_len [i] <= '0;
                r_fifo   [i] <= '0;
            end
        end else begin
            //---------------------------------------------------------------
            // 1. Allocate new op on op_valid handshake — write r_fifo at
            //    tail and advance r_tail_ptr. No FIFO shift ever runs.
            //---------------------------------------------------------------
            if (w_alloc) begin
                r_op_valid        [w_free_slot] <= 1'b1;
                r_op_slot         [w_free_slot] <= op_slot_i;
                r_op_id           [w_free_slot] <= op_id_i;
                r_op_len          [w_free_slot] <= op_len_i;
                r_op_is_last_chunk[w_free_slot] <= op_is_last_chunk_i;
                r_op_wait_cnt     [w_free_slot] <= t_rddata_en_i;
                r_op_en_remaining [w_free_slot] <=
                    ({1'b0, op_len_i} + (BLW+1)'(DFI_RATE - 1)) >> RATE_LOG2;
                // Same ceil(len/DFI_RATE), kept constant for the compares.
                r_op_dfi_total    [w_free_slot] <=
                    ({1'b0, op_len_i} + (BLW+1)'(DFI_RATE - 1)) >> RATE_LOG2;
                r_op_dfi_captured [w_free_slot] <= '0;
                r_op_beats_emitted[w_free_slot] <= '0;
                r_fifo[r_tail_ptr[MCL-1:0]] <= w_free_slot;
                r_tail_ptr <= w_tail_next;
                // Alloc into the (empty) cap-head slot: r_cap_op tracks it now.
                // (Only reachable when count==0 => no cap-head advance this
                // cycle, so this can't collide with the advance updates below.)
                if (r_tail_ptr[MCL-1:0] == r_cap_head_ptr[MCL-1:0]) begin
                    r_cap_op <= w_free_slot;
                end
            end

            //---------------------------------------------------------------
            // 2. Combined FIFO-count delta. Single NBA regardless of
            //    same-cycle alloc + emit-last (the pathology behind #31).
            //---------------------------------------------------------------
            if (w_alloc && !w_emit_last)      r_fifo_count <= r_fifo_count + 1'b1;
            else if (!w_alloc && w_emit_last) r_fifo_count <= r_fifo_count - 1'b1;
            // else: no change (net-zero on both, unchanged on neither).

            //---------------------------------------------------------------
            // 3. Per-op wait countdown (every op with wait_cnt > 0).
            //---------------------------------------------------------------
            for (int unsigned i = 0; i < MAX_CONCURRENT; i++) begin
                if (r_op_valid[i] && r_op_wait_cnt[i] > 8'd0) begin
                    r_op_wait_cnt[i] <= r_op_wait_cnt[i] - 8'd1;
                end
            end

            //---------------------------------------------------------------
            // 4. EN pipeline — advance r_en_head_ptr when the current op
            //    is done or invalid AND there's another op ahead. Advance
            //    guard is "next-pointer != tail" — the extra MCL+1 bit on
            //    the pointers disambiguates full-vs-empty for this cmp.
            //
            //    r_en_head_ptr has ONE update source in this block; no
            //    compensating decrement on emit-last (unlike the pre-#31
            //    shift-FIFO scheme).
            //---------------------------------------------------------------
            if (r_fifo_count > '0
                && (w_en_head_next != r_tail_ptr)
                && (!r_op_valid[w_en_op]
                    || (r_op_en_remaining[w_en_op] == '0))) begin
                r_en_head_ptr <= w_en_head_next;
            end else if (w_en_active) begin
                r_op_en_remaining[w_en_op]
                    <= r_op_en_remaining[w_en_op] - (BLW+1)'(1);
                if (w_en_complete_for_head
                    && (w_en_head_next != r_tail_ptr)) begin
                    r_en_head_ptr <= w_en_head_next;
                end
            end

            //---------------------------------------------------------------
            // 5. CAPTURE pipeline — same shape as EN, driven by
            //    dfi_rddata_valid_i landing into the cap-head op's stage.
            //---------------------------------------------------------------
            // Uses r_cap_op (registered == r_fifo[r_cap_head_ptr]) instead of
            // the combinational w_cap_op so the r_stage capture CE decode does
            // not carry the r_fifo mux. On any cap-head advance, r_cap_op is
            // re-loaded from r_fifo[w_cap_head_next] -- the != r_tail_ptr guard
            // guarantees that slot is already allocated (not written this
            // cycle), so the lockstep holds.
            if (r_fifo_count > '0
                && (w_cap_head_next != r_tail_ptr)
                && (!r_op_valid[r_cap_op]
                    || (r_op_dfi_captured[r_cap_op]
                        >= w_cap_dfi_cycles_total))) begin
                r_cap_head_ptr <= w_cap_head_next;
                r_cap_op       <= r_fifo[w_cap_head_next[MCL-1:0]];
            end else if (dfi_rddata_valid_i && (r_fifo_count > '0)
                && r_op_valid[r_cap_op]
                && (r_op_dfi_captured[r_cap_op] < w_cap_dfi_cycles_total)) begin
                r_stage[r_cap_op][r_op_dfi_captured[r_cap_op][DFI_CYC_LOG2-1:0]]
                    <= dfi_rddata_i;
                r_op_dfi_captured[r_cap_op]
                    <= r_op_dfi_captured[r_cap_op] + (BLW+1)'(1);
                if (r_op_dfi_captured[r_cap_op] + (BLW+1)'(1)
                    == w_cap_dfi_cycles_total
                    && (w_cap_head_next != r_tail_ptr)) begin
                    r_cap_head_ptr <= w_cap_head_next;
                    r_cap_op       <= r_fifo[w_cap_head_next[MCL-1:0]];
                end
            end

            //---------------------------------------------------------------
            // 6. EMIT pipeline — advance beat counter every handshake; on
            //    last beat, free the slot and advance r_emit_head_ptr.
            //    No FIFO shift, no compensation on EN/CAP head pointers.
            //---------------------------------------------------------------
            if (w_handshake) begin
                r_op_beats_emitted[w_emit_op]
                    <= r_op_beats_emitted[w_emit_op] + BLW'(1);
                if (w_emit_last) begin
                    r_op_valid       [w_emit_op] <= 1'b0;
                    r_op_dfi_captured[w_emit_op] <= '0;
                    r_emit_head_ptr <= w_emit_head_next;
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
            dfi_rddata_en_o   <= '0;
            rd_inject_valid_o <= 1'b0;
            rd_inject_id_o    <= '0;
            rd_inject_data_o  <= '0;
            rd_inject_last_o  <= 1'b0;
            rd_beat_we_o      <= 1'b0;
            rd_beat_slot_o    <= '0;
        end else begin
            op_ready_o        <= w_op_ready;
            dfi_rddata_en_o   <= w_dfi_rddata_en;
            rd_inject_valid_o <= w_rd_inject_valid;
            rd_inject_id_o    <= r_op_id[w_emit_op];
            rd_inject_data_o  <= w_emit_data;
            rd_inject_last_o  <= w_rd_inject_last;
            rd_beat_we_o      <= w_rd_beat_we;
            rd_beat_slot_o    <= r_op_slot[w_emit_op];
        end
    end)

    wire unused_v2 = |{ cl_i, al_i, rd_in_order_i };

endmodule : rd_cl_aligner
