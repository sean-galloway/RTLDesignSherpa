// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: monbus_halfbeat_packer
// Purpose: Pack two 30-bit half-slots into one 64-bit beat, downstream of
//          monbus_compressor, to break the 1-beat-per-record (66.7%) ceiling.
//          Bit-exact to the Python golden Encoder(half_beat=True).
//
// Subsystem: amba
//
// ============================================================================
// What this is
// ------------
// Sits between monbus_compressor and the write FIFO when the group is built
// with HALF_BEAT_EN==1. The compressor still emits one 64-bit beat per tier-1
// record (and 3 per raw escape), but now flags, via the half sideband, the
// tier-1 records that also fit a 30-bit half-slot and supplies that slot.
//
// This packer buffers one such half-slot; when a second arrives it emits a
// single TAG_HALF_PAIR beat carrying both (0.5 beat/record -> up to 83.3%
// reduction). A non-half beat (a full 64-bit tier-1 slot, or any of a raw
// record's 3 beats) flushes the buffered half first (paired with a NOP slot)
// so record order is preserved, then is forwarded verbatim. A buffered half
// left when the input goes idle is flushed too, so the last record is never
// stranded.
//
// Beat layout (matches monbus_compressor.py):
//   TAG_HALF_PAIR beat = {tag[63:60]=0x4, slotA[59:30], slotB[29:0]}
//   half-slot          = {sub[29:28], idx[27:23], delta_ts[22:13], data[12:0]}
//   NOP slot           = 30'd0  (sub == HSUB_NOP)
//
// Bit-exactness note: the golden flushes a lone trailing half exactly once at
// end-of-stream. This packer flushes whenever its input is idle with a half
// buffered, which is identical for a gap-free record stream (the cosim drives
// records back-to-back, then idles once). A mid-stream input bubble would
// flush early -- harmless (slightly less packing), never wrong.
// ============================================================================

`timescale 1ns / 1ps

`include "reset_defs.svh"

module monbus_halfbeat_packer (
    input  logic        clk,
    input  logic        rst_n,

    // === Input: 64-bit beats from monbus_compressor + half sideband ===
    input  logic        in_valid,
    output logic        in_ready,
    input  logic [63:0] in_slot,
    input  logic        in_half_valid,    // in_slot's record also fits a 30-bit slot
    input  logic [29:0] in_half_slot,

    // === Output: packed 64-bit beats to the write FIFO ===
    output logic        out_valid,
    input  logic        out_ready,
    output logic [63:0] out_slot
);

    localparam logic [3:0]  TAG_HALF_PAIR = 4'h4;
    localparam logic [29:0] NOP_SLOT      = 30'd0;

    // Buffered (first-of-pair) half-slot.
    logic        r_pend_valid;
    logic [29:0] r_pend_slot;

    // Combinational case decode.
    logic pair_now;     // second half arrives -> emit the pair, consume input
    logic buffer_now;   // first half arrives  -> latch it, emit nothing
    logic fwd_now;      // non-half, no pending -> forward in_slot verbatim
    logic flush_fwd;    // non-half, pending    -> flush the lone half first (hold input)
    logic idle_flush;   // input idle, pending  -> flush the lone trailing half

    assign pair_now   =  in_valid &&  in_half_valid &&  r_pend_valid;
    assign buffer_now =  in_valid &&  in_half_valid && !r_pend_valid;
    assign fwd_now    =  in_valid && !in_half_valid && !r_pend_valid;
    assign flush_fwd  =  in_valid && !in_half_valid &&  r_pend_valid;
    assign idle_flush = !in_valid &&  r_pend_valid;

    always_comb begin
        out_valid = pair_now || fwd_now || flush_fwd || idle_flush;
        if (pair_now)
            out_slot = {TAG_HALF_PAIR, r_pend_slot, in_half_slot};
        else if (fwd_now)
            out_slot = in_slot;
        else  // flush_fwd or idle_flush: lone buffered half + NOP partner
            out_slot = {TAG_HALF_PAIR, r_pend_slot, NOP_SLOT};

        // Consume the input only when we actually take it this cycle. A
        // buffer_now always takes it (no output produced). pair_now / fwd_now
        // take it when the beat is accepted. flush_fwd must emit the flush
        // beat first, so it holds the input (consumed next cycle as fwd_now).
        if (buffer_now)      in_ready = 1'b1;
        else if (pair_now)   in_ready = out_ready;
        else if (fwd_now)    in_ready = out_ready;
        else                 in_ready = 1'b0;
    end

    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            r_pend_valid <= 1'b0;
            r_pend_slot  <= '0;
        end else begin
            if (buffer_now) begin
                r_pend_valid <= 1'b1;
                r_pend_slot  <= in_half_slot;
            end else if (out_ready && (pair_now || flush_fwd || idle_flush)) begin
                // pair_now: the buffered half was consumed into the pair.
                // flush_fwd / idle_flush: the lone half was emitted.
                r_pend_valid <= 1'b0;
            end
        end
    )

endmodule : monbus_halfbeat_packer
