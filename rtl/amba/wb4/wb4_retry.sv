// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: wb4_retry
// Purpose: Re-issue a Wishbone command whose termination was RTY, on the
//          FUB side of wb4_master, so the FUB only sees RTY once the retry
//          budget is spent.
//
// Documentation: docs/markdown/rtl-amba/wb4/wb4_retry.md
// Subsystem: amba
//
// Author: sean galloway
// Created: 2026-09-09
//
//==============================================================================
// Description:
//   Sits between a FUB's cmd/rsp queues and wb4_master's. Every command
//   the FUB issues is kept in an in-order completion buffer of INFLIGHT
//   entries until its response has been handed back. A termination of ACK
//   or ERR completes the entry. A termination of RTY, while the entry's
//   retry count is below cfg_max_retries, puts the entry back on the issue
//   path after cfg_retry_delay clocks; when the budget is spent the RTY is
//   handed to the FUB as-is. Responses reach the FUB in command order
//   whatever the order on the bus.
//
//   Re-issue has priority over new commands. cfg_max_retries = 0 makes
//   the block a pass-through (every RTY reaches the FUB).
//
//   ORDER ON THE BUS. A retried command re-appears on the bus after the
//   commands issued behind it, which (with INFLIGHT > 1) may already have
//   terminated. The FUB still sees responses in its own order, but a read
//   issued behind a write that was retried can observe memory from before
//   that write. INFLIGHT = 1 (the default) keeps program order exactly:
//   one command on the bus at a time, retries included. Use INFLIGHT > 1
//   only for traffic with no ordering dependence across transfers.
//
//------------------------------------------------------------------------------
// Parameters:
//------------------------------------------------------------------------------
//   ADDR_WIDTH, DATA_WIDTH
//   INFLIGHT   - completion-buffer entries = commands accepted from the FUB
//                and not yet answered (1 = strict program order)
//
//------------------------------------------------------------------------------
// Behavior:
//------------------------------------------------------------------------------
//   cmd handshake            -> allocate entry at tail, forward to mst_cmd
//   mst_rsp handshake        -> oldest issued entry: ACK/ERR -> DONE;
//                               RTY -> retry (count < cfg_max_retries) or DONE
//   entry at head DONE       -> rsp_valid; pop on rsp handshake
//   entry waiting, timer 0   -> re-issued on mst_cmd before any new command
//
//------------------------------------------------------------------------------
// Related Modules:
//------------------------------------------------------------------------------
//   - wb4_master.sv (behind it), wb4_master_retry.sv (the two together)
//
//------------------------------------------------------------------------------
// Test:
//------------------------------------------------------------------------------
//   Location: val/amba/test_wb4_master_retry.py (through the wrapper)
//==============================================================================

`timescale 1ns / 1ps

`include "reset_defs.svh"

module wb4_retry
    import wb4_pkg::*;
#(
    parameter int ADDR_WIDTH = 32,
    parameter int DATA_WIDTH = 32,
    parameter int INFLIGHT   = 1,
    // Short params
    parameter int AW  = ADDR_WIDTH,
    parameter int DW  = DATA_WIDTH,
    parameter int SW  = DW/8,
    parameter int STW = WB4_STATUS_WIDTH
)
(
    input  logic              clk,
    input  logic              aresetn,

    // Retry policy
    input  logic [7:0]        cfg_max_retries,   // 0 = pass RTY through
    input  logic [15:0]       cfg_retry_delay,   // clocks from RTY to re-issue

    // FUB side
    input  logic              cmd_valid,
    output logic              cmd_ready,
    input  logic              cmd_we,
    input  logic [AW-1:0]     cmd_adr,
    input  logic [DW-1:0]     cmd_dat,
    input  logic [SW-1:0]     cmd_sel,
    output logic              rsp_valid,
    input  logic              rsp_ready,
    output logic [STW-1:0]    rsp_status,
    output logic [DW-1:0]     rsp_dat,

    // wb4_master side
    output logic              mst_cmd_valid,
    input  logic              mst_cmd_ready,
    output logic              mst_cmd_we,
    output logic [AW-1:0]     mst_cmd_adr,
    output logic [DW-1:0]     mst_cmd_dat,
    output logic [SW-1:0]     mst_cmd_sel,
    input  logic              mst_rsp_valid,
    output logic              mst_rsp_ready,
    input  logic [STW-1:0]    mst_rsp_status,
    input  logic [DW-1:0]     mst_rsp_dat,

    // Status
    output logic [31:0]       retry_count,       // re-issues since reset
    output logic [7:0]        active_count       // entries in the buffer
);

    localparam int N  = INFLIGHT;
    localparam int IW = (N > 1) ? $clog2(N) : 1;   // entry index width
    localparam int CW = $clog2(N + 1);             // occupancy width

    typedef enum logic [1:0] {
        E_EMPTY  = 2'd0,
        E_ISSUED = 2'd1,   // on the bus, waiting for its termination
        E_WAIT   = 2'd2,   // terminated RTY, waiting for the retry delay
        E_DONE   = 2'd3    // answered, waiting for the FUB to take it
    } e_state_t;

    // ------------------------------------------------------------------------
    // Completion buffer (ring, head = oldest command)
    // ------------------------------------------------------------------------
    e_state_t       r_state   [N];
    logic           r_we      [N];
    logic [AW-1:0]  r_adr     [N];
    logic [DW-1:0]  r_dat     [N];
    logic [SW-1:0]  r_sel     [N];
    logic [7:0]     r_retries [N];
    logic [15:0]    r_timer   [N];
    logic [STW-1:0] r_status  [N];
    logic [DW-1:0]  r_dat_r   [N];

    logic [IW-1:0]  r_head, r_tail;
    logic [CW-1:0]  r_count;
    logic           w_full, w_empty;

    // Issue log: entry index per command handed to the master, in that order.
    // Depth N: an entry is on the bus at most once at a time.
    logic [IW-1:0]  r_log     [N];
    logic [IW-1:0]  r_log_head, r_log_tail;
    logic [CW-1:0]  r_log_count;

    function automatic logic [IW-1:0] f_wrap(input logic [IW-1:0] i);
        return (32'(i) == N - 1) ? '0 : i + 1'b1;
    endfunction

    assign w_full  = (32'(r_count) >= N);
    assign w_empty = (r_count == '0);

    // ------------------------------------------------------------------------
    // Retry pick: the oldest entry waiting with its timer expired
    // ------------------------------------------------------------------------
    logic           w_retry_valid;
    logic [IW-1:0]  w_retry_idx;
    always_comb begin
        w_retry_valid = 1'b0;
        w_retry_idx   = r_head;
        for (int i = N - 1; i >= 0; i--) begin           // lowest i (oldest) wins
            logic [IW-1:0] idx;
            idx = IW'((32'(r_head) + i) % N);
            if (i < 32'(r_count) && r_state[idx] == E_WAIT && r_timer[idx] == '0) begin
                w_retry_valid = 1'b1;
                w_retry_idx   = idx;
            end
        end
    end

    // ------------------------------------------------------------------------
    // Issue path: retry first, then a new FUB command into a free entry
    // ------------------------------------------------------------------------
    logic w_issue_new, w_issue_retry, w_mst_issue;

    assign mst_cmd_valid = w_retry_valid || (cmd_valid && !w_full);
    assign w_mst_issue   = mst_cmd_valid && mst_cmd_ready;
    assign w_issue_retry = w_mst_issue &&  w_retry_valid;
    assign w_issue_new   = w_mst_issue && !w_retry_valid;
    assign cmd_ready     = !w_retry_valid && !w_full && mst_cmd_ready;

    assign mst_cmd_we  = w_retry_valid ? r_we [w_retry_idx] : cmd_we;
    assign mst_cmd_adr = w_retry_valid ? r_adr[w_retry_idx] : cmd_adr;
    assign mst_cmd_dat = w_retry_valid ? r_dat[w_retry_idx] : cmd_dat;
    assign mst_cmd_sel = w_retry_valid ? r_sel[w_retry_idx] : cmd_sel;

    // ------------------------------------------------------------------------
    // Response path: the master's termination belongs to the oldest issued
    // entry (the log head). Always accepted: its entry is waiting for it.
    // ------------------------------------------------------------------------
    logic           w_rsp_take, w_rsp_is_rty, w_rsp_retry;
    logic [IW-1:0]  w_rsp_idx;

    assign mst_rsp_ready = (r_log_count != '0);
    assign w_rsp_take    = mst_rsp_valid && mst_rsp_ready;
    assign w_rsp_idx     = r_log[r_log_head];
    assign w_rsp_is_rty  = (mst_rsp_status == STW'(WB4_RSP_RTY));
    assign w_rsp_retry   = w_rsp_take && w_rsp_is_rty && (r_retries[w_rsp_idx] < cfg_max_retries);

    // FUB response: the head entry once it is done
    logic w_rsp_pop;
    assign rsp_valid  = !w_empty && (r_state[r_head] == E_DONE);
    assign rsp_status = r_status[r_head];
    assign rsp_dat    = r_dat_r[r_head];
    assign w_rsp_pop  = rsp_valid && rsp_ready;

    assign active_count = 8'(r_count);

    `ALWAYS_FF_RST(clk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_head      <= '0;
            r_tail      <= '0;
            r_count     <= '0;
            r_log_head  <= '0;
            r_log_tail  <= '0;
            r_log_count <= '0;
            retry_count <= '0;
            for (int i = 0; i < N; i++) begin
                r_state[i]   <= E_EMPTY;
                r_we[i]      <= 1'b0;
                r_adr[i]     <= '0;
                r_dat[i]     <= '0;
                r_sel[i]     <= '0;
                r_retries[i] <= '0;
                r_timer[i]   <= '0;
                r_status[i]  <= '0;
                r_dat_r[i]   <= '0;
                r_log[i]     <= '0;
            end
        end else begin
            // Retry delay timers
            for (int i = 0; i < N; i++)
                if (r_state[i] == E_WAIT && r_timer[i] != '0)
                    r_timer[i] <= r_timer[i] - 1'b1;

            // New command: allocate and issue in one clock
            if (w_issue_new) begin
                r_state[r_tail]   <= E_ISSUED;
                r_we[r_tail]      <= cmd_we;
                r_adr[r_tail]     <= cmd_adr;
                r_dat[r_tail]     <= cmd_dat;
                r_sel[r_tail]     <= cmd_sel;
                r_retries[r_tail] <= '0;
                r_tail            <= f_wrap(r_tail);
            end
            // Re-issue
            if (w_issue_retry)
                r_state[w_retry_idx] <= E_ISSUED;
            // Issue log push
            if (w_mst_issue) begin
                r_log[r_log_tail] <= w_retry_valid ? w_retry_idx : r_tail;
                r_log_tail        <= f_wrap(r_log_tail);
            end

            // Termination from the master
            if (w_rsp_take) begin
                r_log_head <= f_wrap(r_log_head);
                if (w_rsp_retry) begin
                    r_state[w_rsp_idx]   <= E_WAIT;
                    r_retries[w_rsp_idx] <= r_retries[w_rsp_idx] + 1'b1;
                    r_timer[w_rsp_idx]   <= cfg_retry_delay;
                    retry_count          <= retry_count + 1'b1;
                end else begin
                    r_state[w_rsp_idx]   <= E_DONE;
                    r_status[w_rsp_idx]  <= mst_rsp_status;
                    r_dat_r[w_rsp_idx]   <= mst_rsp_dat;
                end
            end

            // FUB takes the head
            if (w_rsp_pop) begin
                r_state[r_head] <= E_EMPTY;
                r_head          <= f_wrap(r_head);
            end

            r_count     <= r_count     + CW'(w_issue_new) - CW'(w_rsp_pop);
            r_log_count <= r_log_count + CW'(w_mst_issue) - CW'(w_rsp_take);
        end
    )

`ifdef FORMAL
    logic f_past_valid;
    initial f_past_valid = 1'b0;
    always_ff @(posedge clk) f_past_valid <= 1'b1;
    always_ff @(posedge clk) if (f_past_valid && aresetn && $past(aresetn)) begin
        assert (32'(r_count) <= N);
        assert (32'(r_log_count) <= N);
        // Everything on the bus is an allocated entry.
        assert (r_log_count <= r_count);
        // A retry is never issued while a new command is accepted.
        assert (!(w_issue_retry && cmd_ready));
        // The FUB only ever sees the head, and only once it is done.
        assert (!rsp_valid || r_state[r_head] == E_DONE);
    end
`endif

endmodule : wb4_retry
