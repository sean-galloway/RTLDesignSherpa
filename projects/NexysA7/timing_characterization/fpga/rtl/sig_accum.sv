// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2026 sean galloway
//
// Module: sig_accum
// Purpose: 32-bit XOR signature accumulator with CDC-safe output snapshot.
//
// Description:
//   Folds an arbitrary-width input bus into a 32-bit XOR signature, one fold
//   per source-clock cycle. A free-running snapshot counter exposes the
//   current signature, captured every 2^SNAP_LOG2 cycles, to the slow
//   observation clock through a 2-flop CDC synchroniser. Used by the MMCM
//   sweep wrapper to publish a per-clock-domain pass/fail signature to the
//   on-board LEDs.
//
// Notes:
//   - The signature does not converge to a single value; it's a free running
//     XOR fold. We compare ALIVE (changing) vs STUCK (flat) between
//     consecutive snapshots in the observer domain.
//   - CDC uses sample-when-stable: snapshots are only updated every
//     2^SNAP_LOG2 cycles in the source domain, so the 2-flop sync sees a
//     quasi-static value for many destination-clock cycles.

`timescale 1ns / 1ps

module sig_accum #(
    parameter int IN_WIDTH  = 64,   // total bits being folded each cycle
    parameter int SNAP_LOG2 = 16    // snapshot every 2^16 = 65536 cycles
) (
    // Source clock domain (the MMCM-derived test clock)
    input  logic                src_clk,
    input  logic                src_rst_n,
    input  logic [IN_WIDTH-1:0] src_data,

    // Observation clock domain (slow / safe 100 MHz)
    input  logic                obs_clk,
    input  logic                obs_rst_n,
    output logic [31:0]         obs_sig,        // CDC-safe latched signature
    output logic                obs_alive       // toggles when sig changes
);

    // ---- Source-side XOR fold + periodic snapshot --------------------------
    logic [31:0] r_sig;
    logic [31:0] w_fold;
    logic [SNAP_LOG2-1:0] r_snap_cnt;

    // Reduce the input to a 32-bit XOR fold without leaving any chain
    // unobserved. Replicate / fold IN_WIDTH bits into 32.
    always_comb begin
        w_fold = 32'd0;
        for (int i = 0; i < IN_WIDTH; i++) begin
            w_fold[i % 32] = w_fold[i % 32] ^ src_data[i];
        end
    end

    always_ff @(posedge src_clk or negedge src_rst_n) begin
        if (!src_rst_n) begin
            r_sig      <= 32'd0;
            r_snap_cnt <= '0;
        end else begin
            // Rotate-then-XOR the fold so bit positions cross-pollinate
            // over time and even single-bit FUB outputs eventually touch
            // every bit of r_sig.
            r_sig      <= {r_sig[30:0], r_sig[31]} ^ w_fold;
            r_snap_cnt <= r_snap_cnt + 1'b1;
        end
    end

    // Snapshot register: latched every SNAP_LOG2 cycles in the source domain.
    logic [31:0] r_snap;
    logic        r_snap_strobe;
    always_ff @(posedge src_clk or negedge src_rst_n) begin
        if (!src_rst_n) begin
            r_snap        <= '0;
            r_snap_strobe <= 1'b0;
        end else if (&r_snap_cnt) begin
            r_snap        <= r_sig;
            r_snap_strobe <= ~r_snap_strobe;
        end
    end

    // ---- Observation-side: 2-flop CDC of the (quasi-static) snapshot ------
    // The snapshot is updated by the source side at most once every 2^SNAP_LOG2
    // cycles. With SNAP_LOG2=16 at 200 MHz that's ~328 us between updates -
    // far longer than the 2-flop sync window at any reasonable obs_clk, so
    // tearing-free sampling.
    (* ASYNC_REG = "TRUE" *) logic [31:0] r_sig_meta;
    (* ASYNC_REG = "TRUE" *) logic [31:0] r_sig_sync;
    (* ASYNC_REG = "TRUE" *) logic        r_str_meta;
    (* ASYNC_REG = "TRUE" *) logic        r_str_sync;
    logic                                  r_str_sync_d;
    logic [31:0]                           r_sig_prev;

    always_ff @(posedge obs_clk or negedge obs_rst_n) begin
        if (!obs_rst_n) begin
            r_sig_meta   <= '0;
            r_sig_sync   <= '0;
            r_str_meta   <= 1'b0;
            r_str_sync   <= 1'b0;
            r_str_sync_d <= 1'b0;
            r_sig_prev   <= '0;
        end else begin
            r_sig_meta   <= r_snap;
            r_sig_sync   <= r_sig_meta;
            r_str_meta   <= r_snap_strobe;
            r_str_sync   <= r_str_meta;
            r_str_sync_d <= r_str_sync;
            if (r_str_sync ^ r_str_sync_d) begin
                r_sig_prev <= r_sig_sync;
            end
        end
    end

    assign obs_sig   = r_sig_sync;
    assign obs_alive = (r_sig_sync != r_sig_prev);

endmodule : sig_accum
