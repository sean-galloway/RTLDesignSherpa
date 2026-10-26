// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: gaxi_age_fifo_sync
// Purpose: Synchronous valid/ready FIFO whose entries carry an age that
//          counts down toward zero on a shared decrement strobe.
//
// Documentation: docs/markdown/rtl-amba/gaxi/gaxi_age_fifo_sync.md
// Subsystem: amba
//
// Author: sean galloway
// Created: 2026-10-25

`timescale 1ns / 1ps

`include "reset_defs.svh"

//==============================================================================
// Module: gaxi_age_fifo_sync
//==============================================================================
// Description:
//   gaxi_fifo_sync (mux-read form) with a per-entry age beside the data. The
//   writer supplies the age with the entry; every valid entry's age_cnt moves
//   one step toward zero on each age_dec strobe and stops at zero. Each entry
//   also carries an age_thresh flop that, for every valid entry, is 1
//   exactly when its age_cnt is 0 (invalid slots hold stale values). The
//   read side sees the head's age_cnt, the head's age_thresh, and `youngest`,
//   the largest age_cnt among the valid entries.
//
//   Intended use: one of N per-bank queues in front of a scheduler. The
//   writer sets wr_data_age to 0 when no queue holds a valid entry, else one
//   above the largest `youngest` across the N queues, or equal to it when
//   age_dec is high in the same cycle (the pool is retiring an entry at the
//   edge the new one joins, so it has one fewer to wait for). The empty
//   term is not optional: `youngest` reads 0 for an empty pool and for a
//   saturated entry alike, and the two need different ages -- the first
//   entry into an empty pool is already the oldest. age_dec is asserted on
//   every queue whenever any queue retires an entry. An entry's age_cnt is
//   then the number of retirements it still has to wait through before it
//   is the oldest thing in the pool, and rd_age_thresh marks a head that
//   has waited that long.
//
//   Under that rule every entry's age_cnt is at most its rank (the number
//   of older entries still in the pool): a new entry's rank is the count,
//   youngest + 1 is at most the count, and a retirement lowers age_cnt by
//   one (or holds it at 0) while lowering the rank by one or zero. So
//   whenever the pool holds anything, the oldest entry sits at age 0 at
//   the head of its queue with rd_age_thresh high, from the cycle after the
//   edge that made it the oldest. The scheduler's request stage can take
//   the N rd_age_thresh bits as its oldest-first class. Three conditions:
//   exactly one age_dec per retirement (two pops under one strobe leave the
//   oldest at age 1), thresh is a priority term over the plain head-valid
//   requests (the aged head may be timer-blocked), and ties at 0 are
//   normal and need a tie-break.
//
// Features:
//   - Same pointers, flags and storage as gaxi_fifo_sync; any DEPTH >= 2
//   - Ages and thresh flags live in flops (every valid one updates in the
//     same cycle), data in the inferred memory array
//   - Saturating decrement: an age_cnt at zero stays at zero
//   - age_thresh is set from the NEXT age_cnt: it rises at the edge where
//     age_cnt reaches 0 (age_cnt == 1 with age_dec, or a write of age 0),
//     so the head's flag is a flop, not a compare off the counter
//   - youngest is a balanced max tree over the valid entries,
//     ceil(log2(DEPTH)) comparators deep; it does not depend on the
//     writer's age discipline
//   - Mux read only: rd_data, rd_data_age, youngest and rd_age_thresh are
//     combinational off the registers and move the cycle after an edge
//   - PEEK > 0 exposes the PEEK entries behind the head (pk_valid, pk_data,
//     pk_age_thresh per position), for a consumer that reads its queue one
//     or two positions deep -- a scheduler's pop shadow serves a queue from
//     its second entry in the cycle after a pop, and a behind-the-head flag
//     (same row behind, nothing behind) is the next entry's bit
//
//------------------------------------------------------------------------------
// Parameters:
//------------------------------------------------------------------------------
//   DATA_WIDTH:  Width of wr_data / rd_data. Range 1 to 1024. Default 4.
//   AGE_WIDTH:   Width of the age counters. Range 1 to 32. Default 8.
//   DEPTH:       Entries. Range 2 and up; any value, power of two optimal.
//                Default 4. DEPTH=1 does not elaborate (no address bit).
//   PEEK:        Entries behind the head exposed on pk_*. Range 0 to
//                DEPTH-1. Default 0 (pk_* constant 0, PKN = 1).
//   DW / AGEW / D / AW / PKN: derived shorthands, do not override.
//
//------------------------------------------------------------------------------
// Ports:
//------------------------------------------------------------------------------
//   Inputs:
//     axi_aclk:       Clock (rising edge)
//     axi_aresetn:    Async active-low reset
//     age_dec:        Strobe: every valid entry's age_cnt steps toward 0 this cycle
//     wr_valid:       Write handshake
//     wr_data:        Entry payload
//     wr_data_age:    Age stored with the entry, as given; the writer applies
//                     the pool rule (0 into an empty pool, else youngest + 1,
//                     or youngest with age_dec)
//     rd_ready:       Read handshake
//
//   Outputs:
//     wr_ready:       Not full
//     count:          Occupancy, [AW:0]
//     youngest:       Largest age among valid entries; 0 when empty
//     rd_valid:       Not empty
//     rd_data:        Head payload
//     rd_data_age:    Head age_cnt; meaningful only while rd_valid (otherwise
//                     the retired slot's stale age shows)
//     rd_age_thresh:  rd_valid && head age_thresh (the head's age_cnt is 0)
//     pk_valid[k]:    entry k+1 behind the head exists (count > k+1); 0 for k >= PEEK
//     pk_data[k]:     its payload (meaningful while pk_valid[k])
//     pk_age_thresh[k]: pk_valid[k] && its age_thresh
//
//------------------------------------------------------------------------------
// Timing:
//------------------------------------------------------------------------------
//   Write to rd_valid / pk_valid: 1 cycle
//   age_dec to age outputs:       1 cycle (register update, then mux read)
//   Throughput:                   1 entry per cycle each side
//
//------------------------------------------------------------------------------
// Behavior:
//------------------------------------------------------------------------------
//   The decrement applies to the entries that were valid before the edge;
//   the entry written at that edge stores wr_data_age exactly. The writer
//   owns the same-cycle term: with age_dec high it presents youngest rather
//   than youngest + 1, because the arriving entry is in the pool at the same
//   moment as the retirement and has one fewer to wait for. A writer that
//   omits the term lands every write that coincides with a retire one above
//   where it belongs; under continuous write+retire the ages then climb by
//   one per cycle, wrap at 2**AGE_WIDTH, and the wrapped entry jumps the
//   pool (measured in review, 2026-10-25; the test's pool phases check the
//   rank invariant that catches it).
//
//   The empty-pool term matters just as much. A writer that presents
//   youngest + 1 into an empty pool lands the first entry at age 1 with
//   nothing older than it, and every later entry inherits the shift: the
//   oldest entry then always sits at age 1, rd_age_thresh never rises on
//   the oldest head, and a request stage driven from the thresh bits never
//   requests the first command into an idle controller -- nothing fires,
//   nothing retires, nothing decrements. The rule as first written (header,
//   doc example and the test's rank check, 2026-10-25 morning) had exactly
//   this hole; the test's pool phases now check age == rank and that some
//   head carries thresh whenever the pool is occupied.
//
//   The writer rule ties at zero: if youngest is 0 (an entry already
//   saturated, which out-of-order retirement makes common) and age_dec is
//   high, the writer presents 0 and the new entry lands level with the
//   saturated one, not behind it. Saturation already produces ties at 0, so
//   the scheduler must break them anyway; a writer that wants the new entry
//   strictly behind uses youngest + 1 - (age_dec && youngest != 0).
//
//   age_thresh per entry is set from the next age_cnt: on a write it is
//   (wr_data_age == 0); afterwards it rises when age_cnt == 1 and age_dec is
//   high, which is the edge at which age_cnt becomes 0; it holds until the
//   slot is rewritten. For every valid entry age_thresh == (age_cnt == 0).
//
//   A write and a read in the same cycle address different slots (the same
//   slot would need full and empty at once), so neither interferes with the
//   other's age.
//
//   A valid mask is kept as one flop per slot (set on write, cleared on
//   read) rather than derived from the pointers, so the mask is exact for a
//   non-power-of-two DEPTH and the max tree needs no pointer arithmetic.
//
//   The peek positions are the slots at read address + 1 .. + PEEK (modulo
//   DEPTH). The occupied slots are contiguous from the read address, so
//   that slot's valid bit is exactly "entry k+1 exists"; the data and the
//   thresh flag are read off the same arrays as the head. PEEK >= DEPTH
//   would wrap a peek onto the head and does not elaborate.
//
//   If the writer keeps the one-above-largest discipline the ages in one
//   queue are non-decreasing from head to tail and `youngest` equals the
//   tail's age; the tree is kept anyway so the output stays correct under
//   any writer.
//==============================================================================
module gaxi_age_fifo_sync #(
    parameter int  DATA_WIDTH = 4,
    parameter int  AGE_WIDTH  = 8,
    parameter int  DEPTH      = 4,
    parameter int  PEEK       = 0,
    parameter int  DW   = DATA_WIDTH,
    parameter int  AGEW = AGE_WIDTH,
    parameter int  D    = DEPTH,
    parameter int  AW   = $clog2(DEPTH),
    parameter int  PKN  = (PEEK > 0) ? PEEK : 1
) (
    input  logic            axi_aclk,
    input  logic            axi_aresetn,
    input  logic            age_dec,        // step every valid age_cnt toward 0
    input  logic            wr_valid,
    output logic            wr_ready,       // not full
    input  logic [DW-1:0]   wr_data,
    input  logic [AGEW-1:0] wr_data_age,
    input  logic            rd_ready,
    output logic [AW:0]     count,
    output logic [AGEW-1:0] youngest,       // largest age among valid entries
    output logic            rd_valid,       // not empty
    output logic [DW-1:0]   rd_data,
    output logic [AGEW-1:0] rd_data_age,
    output logic            rd_age_thresh,  // head age_cnt has saturated at 0
    // the PEEK entries behind the head (constant 0 when PEEK == 0)
    output logic            pk_valid      [PKN],
    output logic [DW-1:0]   pk_data       [PKN],
    output logic            pk_age_thresh [PKN]
);

    // ---------------------------------------------------------------------
    // Local signals
    // ---------------------------------------------------------------------
    logic [AW-1:0] r_wr_addr, r_rd_addr;
    logic [AW:0]   r_wr_ptr_bin, r_rd_ptr_bin;
    logic [AW:0]   w_wr_ptr_bin_next, w_rd_ptr_bin_next;
    logic          r_wr_full, r_wr_almost_full, r_rd_empty, r_rd_almost_empty;

    logic          w_write, w_read;
    assign w_write = wr_valid && wr_ready;
    assign w_read  = rd_valid && rd_ready;

    // ---------------------------------------------------------------------
    // Pointers and flags: identical to gaxi_fifo_sync
    // ---------------------------------------------------------------------
    counter_bin #(
        .WIDTH (AW + 1),
        .MAX   (D)
    ) write_pointer_inst (
        .clk              (axi_aclk),
        .rst_n            (axi_aresetn),
        .enable           (w_write && !r_wr_full),
        .counter_bin_curr (r_wr_ptr_bin),
        .counter_bin_next (w_wr_ptr_bin_next)
    );

    counter_bin #(
        .WIDTH (AW + 1),
        .MAX   (D)
    ) read_pointer_inst (
        .clk              (axi_aclk),
        .rst_n            (axi_aresetn),
        .enable           (w_read && !r_rd_empty),
        .counter_bin_curr (r_rd_ptr_bin),
        .counter_bin_next (w_rd_ptr_bin_next)
    );

    fifo_control #(
        .DEPTH             (D),
        .ADDR_WIDTH        (AW),
        .ALMOST_RD_MARGIN  (1),
        .ALMOST_WR_MARGIN  (1),
        .REGISTERED        (0)
    ) fifo_control_inst (
        .wr_clk           (axi_aclk),
        .wr_rst_n         (axi_aresetn),
        .rd_clk           (axi_aclk),
        .rd_rst_n         (axi_aresetn),
        .wr_ptr_bin       (w_wr_ptr_bin_next),
        .wdom_rd_ptr_bin  (w_rd_ptr_bin_next),
        .rd_ptr_bin       (w_rd_ptr_bin_next),
        .rdom_wr_ptr_bin  (w_wr_ptr_bin_next),
        .count            (count),
        .wr_full          (r_wr_full),
        .wr_almost_full   (r_wr_almost_full),
        .rd_empty         (r_rd_empty),
        .rd_almost_empty  (r_rd_almost_empty)
    );

    assign wr_ready  = !r_wr_full;
    assign rd_valid  = !r_rd_empty;
    assign r_wr_addr = r_wr_ptr_bin[AW-1:0];
    assign r_rd_addr = r_rd_ptr_bin[AW-1:0];

    // ---------------------------------------------------------------------
    // Data storage: inferred array, no reset, mux read
    // ---------------------------------------------------------------------
    logic [DW-1:0] mem [D];

    always_ff @(posedge axi_aclk) begin
        if (w_write) begin
            mem[r_wr_addr] <= wr_data;
        end
    end

    assign rd_data = mem[r_rd_addr];

    // ---------------------------------------------------------------------
    // Age storage: age_cnt, age_thresh and a valid bit per slot
    // ---------------------------------------------------------------------
    logic [AGEW-1:0] r_age        [D];
    logic            r_age_thresh [D];
    logic            r_valid      [D];

    `ALWAYS_FF_RST(axi_aclk, axi_aresetn,
        if (`RST_ASSERTED(axi_aresetn)) begin
            for (int i = 0; i < D; i++) begin
                r_age[i]        <= '0;
                r_age_thresh[i] <= 1'b0;
                r_valid[i]      <= 1'b0;
            end
        end else begin
            for (int i = 0; i < D; i++) begin
                if (w_write && (r_wr_addr == AW'(i))) begin
                    // New entry: age as given (the writer holds the age_dec
                    // term); thresh from the value being written.
                    r_age[i]        <= wr_data_age;
                    r_age_thresh[i] <= (wr_data_age == '0);
                    r_valid[i]      <= 1'b1;
                end else if (w_read && (r_rd_addr == AW'(i))) begin
                    r_valid[i]      <= 1'b0;
                end else if (age_dec && r_valid[i] && (r_age[i] != '0)) begin
                    r_age[i]        <= r_age[i] - 1'b1;
                    // age_thresh_d: this edge takes age_cnt from 1 to 0
                    r_age_thresh[i] <= (r_age[i] == AGEW'(1));
                end
            end
        end
    )

    assign rd_data_age   = r_age[r_rd_addr];
    assign rd_age_thresh = rd_valid && r_age_thresh[r_rd_addr];

    // ---------------------------------------------------------------------
    // Peek: the PEEK slots behind the head, modulo DEPTH
    // ---------------------------------------------------------------------
    generate
        if (PEEK >= D) begin : g_peek_bad
            $error("gaxi_age_fifo_sync: PEEK must be below DEPTH");
        end
        for (genvar k = 0; k < PKN; k++) begin : g_peek
            if (k < PEEK) begin : g_live
                logic [AW-1:0] w_addr;
                // AW+1 bits so a non-power-of-two DEPTH wraps exactly
                logic [AW:0]   w_sum;
                assign w_sum  = {1'b0, r_rd_addr} + (AW+1)'(k + 1);
                assign w_addr = (w_sum >= (AW+1)'(D)) ? AW'(w_sum - (AW+1)'(D)) : AW'(w_sum);
                assign pk_valid[k]      = r_valid[w_addr];
                assign pk_data[k]       = mem[w_addr];
                assign pk_age_thresh[k] = r_valid[w_addr] && r_age_thresh[w_addr];
            end else begin : g_off
                assign pk_valid[k]      = 1'b0;
                assign pk_data[k]       = '0;
                assign pk_age_thresh[k] = 1'b0;
            end
        end
    endgenerate

    // ---------------------------------------------------------------------
    // youngest: balanced max tree over the valid entries
    // ---------------------------------------------------------------------
    // NP pads DEPTH up to a power of two; padding leaves and invalid slots
    // contribute zero. Level 0 holds the NP leaves, each later level halves
    // the count, the last level is one value. Each level is its own array in
    // its own generate scope: one array for the whole tree reads as a
    // combinational loop to Verilator (UNOPTFLAT) even though no node feeds
    // itself.
    localparam int NP   = 1 << $clog2(D);
    localparam int NLVL = $clog2(D);          // levels above the leaves

    logic [AGEW-1:0] w_leaf [NP];

    generate
        for (genvar i = 0; i < NP; i++) begin : g_leaf
            if (i < D) begin : g_slot
                assign w_leaf[i] = r_valid[i] ? r_age[i] : '0;
            end else begin : g_pad
                assign w_leaf[i] = '0;
            end
        end

        for (genvar lvl = 0; lvl < NLVL; lvl++) begin : g_lvl
            localparam int N_OUT = NP >> (lvl + 1);
            logic [AGEW-1:0] w_max [N_OUT];
            for (genvar k = 0; k < N_OUT; k++) begin : g_node
                logic [AGEW-1:0] w_a, w_b;
                if (lvl == 0) begin : g_from_leaf
                    assign w_a = w_leaf[2*k];
                    assign w_b = w_leaf[2*k+1];
                end else begin : g_from_lvl
                    assign w_a = g_lvl[lvl-1].w_max[2*k];
                    assign w_b = g_lvl[lvl-1].w_max[2*k+1];
                end
                assign w_max[k] = (w_a > w_b) ? w_a : w_b;
            end
        end

        if (NLVL == 0) begin : g_root_leaf
            assign youngest = w_leaf[0];
        end else begin : g_root_tree
            assign youngest = g_lvl[NLVL-1].w_max[0];
        end
    endgenerate

endmodule : gaxi_age_fifo_sync
