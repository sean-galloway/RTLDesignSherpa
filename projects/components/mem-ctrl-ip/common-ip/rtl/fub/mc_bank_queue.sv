// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2026 sean galloway
//
// Module: mc_bank_queue
// Description: One per-(direction, bank) command queue for mc_bank_fifo_store,
//   built for an FPGA: the head and the PEEK entries behind it live in a
//   shift register of flops, so the three values the record build reads
//   every cycle (s0 / s1 / s2 and their valids) are register outputs; the
//   rest of the queue sits in a small reset-free memory (LUTRAM) that is
//   touched once per push and once per pop. There is no FIFO controller:
//   the valids are compares on one registered count, and a pop ends in the
//   shift register's load and a pointer increment.
//
//   Drop-in for gaxi_age_fifo_sync with the age column off (memory-controllers
//   MC-010, ISSUE-001 row 2, 2026-11-08): same wr/rd handshake and the same
//   observable timing -- a push is visible on rd_valid / pk_valid the cycle
//   after it lands, a pop advances the view the cycle after it fires, and
//     rd_valid    = count > 0           rd_data    = the head
//     pk_valid[k] = count > k + 1       pk_data[k] = entry k + 1 behind the head
//   The age ports of the original are not here; mc_bank_fifo_store selects
//   this module when HAS_AGE = 0 (the board) and keeps gaxi_age_fifo_sync
//   when the pool age is wanted. formal/mc_common/mc_bank_queue proves the
//   two agree on every output under the same stimulus.
//
// Parameters:
//   - DATA_WIDTH: payload width ({same-row-as-previous, slot} in the store)
//   - DEPTH:      entries, >= PEEK + 1 (at least the shift register itself; with
//                 DEPTH == PEEK + 1 there is no tail memory and every push
//                 lands in the shift register); need not be a power of two
//   - PEEK:       entries behind the head exposed on pk_* (0 = head only)
// Notes:
//   - The shift register and the tail memory carry no reset (storage, never
//     read while invalid: every pk_data[k] / rd_data read is qualified by its
//     valid, which is a compare on the reset count).
//   - Push and pop in the same cycle: the pop shifts; the refill of the last
//     shift-register slot comes from the memory when it holds anything, else
//     from the push itself; a push that cannot land in the shift register
//     goes to the memory tail. Order is preserved in every case.

`include "reset_defs.svh"

module mc_bank_queue #(
    parameter int  DATA_WIDTH = 4,
    parameter int  DEPTH      = 8,
    parameter int  PEEK       = 2,
    parameter int  DW   = DATA_WIDTH,
    parameter int  D    = DEPTH,
    parameter int  AW   = $clog2(DEPTH),
    parameter int  PKN  = (PEEK > 0) ? PEEK : 1
) (
    input  logic            axi_aclk,
    input  logic            axi_aresetn,
    input  logic            wr_valid,
    output logic            wr_ready,       // not full
    input  logic [DW-1:0]   wr_data,
    input  logic            rd_ready,
    output logic [AW:0]     count,
    output logic            rd_valid,       // not empty
    output logic [DW-1:0]   rd_data,
    output logic            pk_valid      [PKN],
    output logic [DW-1:0]   pk_data       [PKN]
);

    // L entries in the shift register: the head plus the PEEK behind it.
    localparam int L   = PKN + 1;
    localparam int TD  = (D > L) ? (D - L) : 1;            // tail memory entries
    localparam int TAW = (TD > 1) ? $clog2(TD) : 1;
    localparam int CW  = AW + 1;
    localparam int LW  = (L > 1) ? $clog2(L) : 1;          // shift-register index width

    generate if (D < L) begin : g_depth_bad
        $error("mc_bank_queue: DEPTH must be at least PEEK + 1");
    end endgenerate

    logic [CW-1:0]  r_cnt;                 // entries held (shift register + tail)
    logic [DW-1:0]  r_sr   [L];            // [0] = head
    logic [DW-1:0]  r_tail [TD];           // entries behind the shift register, in order
    logic [TAW-1:0] r_wp, r_rp;            // tail memory write / read pointers

    logic w_push, w_pop, w_tail_has;
    logic [CW-1:0] w_tcnt;                 // entries in the tail memory
    assign rd_valid   = (r_cnt != '0);
    assign wr_ready   = (r_cnt != CW'(D));
    assign count      = r_cnt;
    assign w_push     = wr_valid && wr_ready;
    assign w_pop      = rd_ready && rd_valid;
    assign w_tcnt     = (r_cnt > CW'(L)) ? (r_cnt - CW'(L)) : '0;
    assign w_tail_has = (w_tcnt != '0);

    // outputs are the shift register
    assign rd_data = r_sr[0];
    for (genvar k = 0; k < PKN; k++) begin : g_peek
        if (k < PEEK) begin : g_live
            assign pk_valid[k] = (r_cnt > CW'(k + 1));
            assign pk_data[k]  = r_sr[k + 1];
        end else begin : g_off
            assign pk_valid[k] = 1'b0;
            assign pk_data[k]  = '0;
        end
    end

    // pointer step with wrap (TD need not be a power of two)
    function automatic logic [TAW-1:0] f_inc(input logic [TAW-1:0] p);
        return (int'(p) == TD - 1) ? '0 : p + 1'b1;
    endfunction

    // where a push lands when it does not go to the tail memory: the shift
    // register position equal to the count AFTER this cycle's pop
    logic [CW-1:0] w_sr_pos;
    assign w_sr_pos = r_cnt - (w_pop ? CW'(1) : CW'(0));
    logic w_push_to_mem;
    assign w_push_to_mem = w_push && (w_tail_has || (w_sr_pos >= CW'(L)));

    `ALWAYS_FF_RST(axi_aclk, axi_aresetn,
        if (`RST_ASSERTED(axi_aresetn)) begin
            r_cnt <= '0; r_wp <= '0; r_rp <= '0;
        end else begin
            r_cnt <= r_cnt + (w_push ? CW'(1) : CW'(0)) - (w_pop ? CW'(1) : CW'(0));
            if (w_push_to_mem)       r_wp <= f_inc(r_wp);
            if (w_pop && w_tail_has) r_rp <= f_inc(r_rp);
        end
    )

    // storage: reset-free (read only under a valid)
    always_ff @(posedge axi_aclk) begin
        if (w_push_to_mem) r_tail[r_wp] <= wr_data;
        if (w_pop) begin
            for (int i = 0; i < L - 1; i++) r_sr[i] <= r_sr[i + 1];
            // the last slot refills from the tail memory, or from a push that
            // lands exactly there (count after the pop == L - 1)
            if (w_tail_has)                            r_sr[L - 1] <= r_tail[r_rp];
            else if (w_push && (w_sr_pos == CW'(L - 1))) r_sr[L - 1] <= wr_data;
            // a push landing below the last slot (queue was short)
            if (w_push && !w_tail_has && (w_sr_pos < CW'(L - 1))) r_sr[w_sr_pos[LW-1:0]] <= wr_data;
        end else if (w_push && !w_push_to_mem) begin
            r_sr[w_sr_pos[LW-1:0]] <= wr_data;
        end
    end

endmodule : mc_bank_queue
