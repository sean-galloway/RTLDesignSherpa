// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: alu_infer_pipe
// Purpose: Tag FIFO and arrival join for alu_infer_top's elastic pipeline
//
// Documentation: projects/components/compute-eng-ip/alu-infer/docs/alu_infer_mas
// Subsystem: cell
//
// Author: sean galloway
// Created: 2026-10-17
// Updated: 2026-10-19 -- tag-based alignment (owner ruling 2026-10-18) replaces
//          the alignment-timer mailbox: each issue takes an 8-bit tag, a FIFO
//          tracks the tags in flight, and a result is offered only when every
//          op of its tag group has arrived.  v1 issues one row-op per
//          invocation, so a tag group is a single arrival; multi-op groups
//          (parallel issue) are the growth path the mechanism was ruled for.

`timescale 1ns / 1ps

`include "reset_defs.svh"

module alu_infer_pipe #(
    parameter int LINE_W     = 32,
    parameter int PIPE_DEPTH = 8,
    parameter int TAG_W      = 8
) (
    input  logic              clk,
    input  logic              aresetn,

    input  logic              issue,
    output logic [TAG_W-1:0]  issue_tag,

    // Early row write (combinational rows): arrives at the issue edge, so it
    // targets the tail slot being allocated; row_write_tag == issue_tag by
    // construction.
    input  logic              row_write_valid,
    input  logic [TAG_W-1:0]  row_write_tag,
    input  logic [LINE_W-1:0] row_write_data,
    input  logic [LINE_W-1:0] row_write_flags,

    // Late row write (pipelined adder): joins its invocation by tag compare
    // against the entries in flight.
    input  logic              late_write_valid,
    input  logic [TAG_W-1:0]  late_write_tag,
    input  logic [LINE_W-1:0] late_write_data,

    output logic              ready,

    output logic              result_valid,
    input  logic              result_ready,
    output logic [LINE_W-1:0] result_line,
    output logic [LINE_W-1:0] result_flags
);

    localparam int PTR_W = $clog2(PIPE_DEPTH);

    // Head/tail pointers into the PIPE_DEPTH-entry tag FIFO.  They wrap modulo
    // PIPE_DEPTH so that non-power-of-two depths are supported.
    logic [PTR_W-1:0] head;
    logic [PTR_W-1:0] tail;

    // Free-running tag counter: one 8-bit tag per issue, common to every op
    // the invocation loads into the pipeline.  Tags wrap freely; PIPE_DEPTH
    // (<= 16) in-flight entries can never alias a 256-value space.
    logic [TAG_W-1:0] r_tag;

    // Occupancy tracks the number of in-flight invocations.  It is updated on
    // the same edge as head/tail so that ready reflects the post-retire free
    // slot when the output is being consumed.
    logic [PTR_W:0] occupancy;

    // Elastic issue: accept while the FIFO has a free entry.  A stalled
    // consumer does not block issue until the FIFO is genuinely full -- row
    // results keep landing in their own entries and the head simply holds;
    // this is what "the tags naturally take care of the elastic nature"
    // means.  If the head result is being consumed this cycle, that entry
    // frees up and can be re-issued immediately, keeping steady-state II=1.
    assign ready = (occupancy < PIPE_DEPTH) || (result_valid && result_ready);

    // The tag exposed to the rows at issue is the pre-increment counter.
    assign issue_tag = r_tag;

    // Per-entry state.  The join: an entry's result is offered only once its
    // tag group's arrivals have all landed (v1: the invocation's one row-op).
    logic [TAG_W-1:0]  mb_tag     [PIPE_DEPTH];
    logic [LINE_W-1:0] mb_data    [PIPE_DEPTH];
    logic [LINE_W-1:0] mb_flags   [PIPE_DEPTH];
    logic              mb_arrived [PIPE_DEPTH];
    logic              mb_pending [PIPE_DEPTH];

    // Presentation: the head entry is offered once its group has arrived.
    // Occupancy distinguishes empty from full when PIPE_DEPTH is not a power
    // of two.  Results retire strictly in issue (FIFO) order at their natural
    // group-aligned latency -- a fast row behind a slow one waits at the head.
    assign result_valid  = (occupancy != '0) && mb_arrived[head];
    assign result_line   = mb_data[head];
    assign result_flags  = mb_flags[head];

    `ALWAYS_FF_RST(clk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            head      <= '0;
            tail      <= '0;
            r_tag     <= '0;
            occupancy <= '0;
            for (int i = 0; i < PIPE_DEPTH; i++) begin
                mb_tag[i]     <= '0;
                mb_data[i]    <= '0;
                mb_flags[i]   <= '0;
                mb_arrived[i] <= 1'b0;
                mb_pending[i] <= 1'b0;
            end
        end else begin
            // Retire: consume the offered head when the downstream accepts.
            if (result_valid && result_ready) begin
                mb_arrived[head] <= 1'b0;
                mb_pending[head] <= 1'b0;
                head <= (head == PTR_W'(PIPE_DEPTH - 1)) ? '0 : head + 1'b1;
            end

            // Issue: allocate the tail entry and take the next tag.
            if (issue) begin
                tail <= (tail == PTR_W'(PIPE_DEPTH - 1)) ? '0 : tail + 1'b1;
                r_tag           <= r_tag + 1'b1;
                mb_tag[tail]     <= r_tag;
                mb_pending[tail] <= 1'b1;
                mb_arrived[tail] <= 1'b0;
            end

            // Early row write: combinational rows land at the issue edge, in
            // the tail entry being allocated above (later statements win on
            // the retire-full corner, where tail == head).
            if (row_write_valid) begin
                mb_data[tail]    <= row_write_data;
                mb_flags[tail]   <= row_write_flags;
                mb_arrived[tail] <= 1'b1;
            end

            // Late row write: the pipelined row joins by tag.  Exactly one
            // in-flight entry matches -- tags are unique while in flight.
            if (late_write_valid) begin
                for (int i = 0; i < PIPE_DEPTH; i++) begin
                    if (mb_pending[i] && !mb_arrived[i] && (mb_tag[i] == late_write_tag)) begin
                        mb_data[i]    <= late_write_data;
                        mb_flags[i]   <= '0;
                        mb_arrived[i] <= 1'b1;
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
