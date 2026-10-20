// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: alu_infer_pipe
// Purpose: Result-alignment mailbox and elastic handshake timer for alu_infer_top
//
// Documentation: projects/components/compute-eng-ip/alu-infer/docs/alu_infer_mas
// Subsystem: cell
//
// Author: sean galloway
// Created: 2026-10-17

`timescale 1ns / 1ps

`include "reset_defs.svh"

module alu_infer_pipe #(
    parameter int LINE_W      = 32,
    parameter int ROW_LATENCY = 4
) (
    input  logic              clk,
    input  logic              aresetn,

    input  logic              issue,
    output logic [$clog2(ROW_LATENCY)-1:0] issue_seq,

    input  logic              row_write_valid,
    input  logic [$clog2(ROW_LATENCY)-1:0] row_write_idx,
    input  logic [LINE_W-1:0] row_write_data,
    input  logic [LINE_W-1:0] row_write_flags,

    // Late row write (pipelined adder); a different mailbox slot than
    // row_write in the same cycle by construction.
    input  logic              late_write_valid,
    input  logic [$clog2(ROW_LATENCY)-1:0] late_write_idx,
    input  logic [LINE_W-1:0] late_write_data,

    output logic              ready,

    output logic              result_valid,
    input  logic              result_ready,
    output logic [LINE_W-1:0] result_line,
    output logic [LINE_W-1:0] result_flags
);

    localparam int PTR_W = $clog2(ROW_LATENCY);

    // Head/tail pointers into the ROW_LATENCY-entry circular mailbox.  They
    // wrap modulo ROW_LATENCY so that non-power-of-two latencies are supported.
    logic [PTR_W-1:0] head;
    logic [PTR_W-1:0] tail;

    // Elastic advance: the output stage may hold while result_ready is low.
    logic advance;
    assign advance = !(result_valid && !result_ready);

    // Occupancy tracks the number of in-flight invocations.  It is updated on
    // the same edge as head/tail so that ready reflects the post-retire free
    // slot when the output is being consumed.
    logic [PTR_W:0] occupancy;

    // We can accept a new issue when there is a free mailbox slot.  If the
    // head result is being consumed this cycle, that slot frees up and can be
    // re-issued immediately, keeping steady-state II=1.
    assign ready = advance && ((occupancy < ROW_LATENCY) || (result_valid && result_ready));

    // The issue sequence number exposed to rows is the pre-increment tail.
    assign issue_seq = tail;

    // Per-slot state.  The alignment timer guarantees every result is presented
    // exactly ROW_LATENCY cycles after its issue, even though rows finish at
    // different natural speeds.
    logic [LINE_W-1:0] mb_data  [ROW_LATENCY];
    logic [LINE_W-1:0] mb_flags [ROW_LATENCY];
    logic              mb_arrived [ROW_LATENCY];
    logic              mb_pending [ROW_LATENCY];
    logic [PTR_W:0]    mb_count  [ROW_LATENCY];
    logic              mb_data_valid [ROW_LATENCY];

    // Presentation: head slot is offered once its countdown has expired and the
    // row result has been captured.  Occupancy distinguishes empty from full
    // when ROW_LATENCY is not a power of two (or equals one).
    assign result_valid  = (occupancy != '0) && mb_arrived[head];
    assign result_line   = mb_data[head];
    assign result_flags  = mb_flags[head];

    `ALWAYS_FF_RST(clk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            head      <= '0;
            tail      <= '0;
            occupancy <= '0;
            for (int i = 0; i < ROW_LATENCY; i++) begin
                mb_data[i]       <= '0;
                mb_flags[i]      <= '0;
                mb_arrived[i]    <= 1'b0;
                mb_pending[i]    <= 1'b0;
                mb_count[i]      <= '0;
                mb_data_valid[i] <= 1'b0;
            end
        end else begin
            // Retire: consume the offered head when the downstream accepts.
            if (result_valid && result_ready) begin
                mb_arrived[head]    <= 1'b0;
                mb_pending[head]    <= 1'b0;
                mb_data_valid[head] <= 1'b0;
                mb_count[head]      <= '0;
                head <= (head == PTR_W'(ROW_LATENCY - 1)) ? '0 : head + 1'b1;
            end

            // Issue: allocate the tail slot and start the alignment timer.
            if (issue) begin
                tail <= (tail == PTR_W'(ROW_LATENCY - 1)) ? '0 : tail + 1'b1;
                mb_pending[tail]    <= 1'b1;
                mb_arrived[tail]    <= 1'b0;
                mb_data_valid[tail] <= 1'b0;
                mb_count[tail]      <= (PTR_W+1)'(ROW_LATENCY - 1);
            end

            // Row writes capture the natural-latency result into its slot.  The
            // presentation above still waits for the alignment timer.  The early
            // (issue-time) and late (adder) writes target different slots in the
            // same cycle, so both are applied.
            if (row_write_valid) begin
                mb_data[row_write_idx]       <= row_write_data;
                mb_flags[row_write_idx]      <= row_write_flags;
                mb_data_valid[row_write_idx] <= 1'b1;
            end
            if (late_write_valid) begin
                mb_data[late_write_idx]       <= late_write_data;
                mb_flags[late_write_idx]      <= '0;
                mb_data_valid[late_write_idx] <= 1'b1;
            end

            // Alignment timers: count down to the uniform presentation slot.
            // The timer is loaded with ROW_LATENCY-1 and is held during the
            // issue cycle so that the result is presented exactly ROW_LATENCY
            // cycles after its issue edge.
            for (int i = 0; i < ROW_LATENCY; i++) begin
                if (mb_pending[i] && !mb_arrived[i]) begin
                    // Do not decrement a slot in the same cycle it was issued.
                    if (issue && (i == int'(tail))) begin
                        // hold
                    end else if (mb_count[i] == '0) begin
                        if (mb_data_valid[i]) begin
                            mb_arrived[i] <= 1'b1;
                        end
                    end else begin
                        mb_count[i] <= mb_count[i] - 1'b1;
                    end
                end
            end

            // Update occupancy after retire/issue decisions.
            case ({issue, result_valid && result_ready})
                2'b10:   occupancy <= occupancy + 1'b1;
                2'b01:   occupancy <= occupancy - 1'b1;
                default: occupancy <= occupancy;
            endcase
        end
    )

endmodule : alu_infer_pipe
