// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: char_gen_wr_order_q
// Purpose: Keeps the merged W stream in AW order for char_gen_unit
//
// Documentation: ddr2_char_framework/rtl/char_gen_unit.sv (sole consumer)
//==============================================================================
// Description:
//   AXI4 requires write data to arrive in the same order the write addresses
//   were issued. Once N generators share one AW channel, that ordering is a
//   property of the merge rather than of any one generator, so it has to be
//   recorded: every granted AW pushes its generator index here, and the W mux
//   serves the head until WLAST, then pops.
//
//   The head is bypass-visible on the push cycle. Without that, a generator
//   that already has WVALID up when its AW wins waits a clock before its data
//   is let through -- one bubble per burst, which is nothing at AxLEN=16 and
//   half the write bandwidth at AxLEN=1. The outstanding-vs-latency sweep runs
//   at AxLEN=1, so the bubble is not acceptable there.
//
//   Push and pop may coincide (single-beat burst arriving on an empty queue);
//   the count is unchanged and both pointers step, which is why the pointers
//   are kept separately rather than derived from the count.
//==============================================================================
`timescale 1ns / 1ps
`include "reset_defs.svh"

module char_gen_wr_order_q #(
    // Must cover every AW that can be outstanding at once: NUM_GEN generators
    // times each one's MAX_OUTSTANDING. Sized by the caller, power of two.
    parameter int DEPTH = 64,
    parameter int SELW  = 1,
    // Aliases
    parameter int PTRW  = $clog2(DEPTH)
) (
    input  logic clk,
    input  logic rst_n,

    //---- Push: one entry per accepted AW ---------------------------------
    input  logic            push,
    input  logic [SELW-1:0] push_sel,
    // Held high when the queue cannot take another entry. The caller blocks
    // AW with this rather than dropping it.
    output logic            full,

    //---- Head: who owns the W channel right now --------------------------
    output logic            head_valid,
    output logic [SELW-1:0] head_sel,

    //---- Pop: the head's WLAST went through ------------------------------
    input  logic            pop
);

    logic [SELW-1:0] r_q [DEPTH];
    logic [PTRW-1:0] r_wr_ptr, r_rd_ptr;
    logic [PTRW:0]   r_count;

    logic w_empty;
    logic w_bypass;

    assign w_empty = (r_count == '0);
    assign full    = (r_count == (PTRW+1)'(DEPTH));

    // An empty queue shows the entry being pushed this cycle, so a burst whose
    // data is already waiting starts on the AW handshake itself.
    assign w_bypass   = w_empty && push;
    assign head_valid = !w_empty || w_bypass;
    assign head_sel   = w_empty ? push_sel : r_q[r_rd_ptr];

    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            r_wr_ptr <= '0;
            r_rd_ptr <= '0;
            r_count  <= '0;
        end else begin
            // The entry is stored even when it was bypassed: the bypass only
            // covers the cycle it was pushed on, and a burst longer than one
            // beat still has to find it here next clock.
            if (push) begin
                r_q[r_wr_ptr] <= push_sel;
                r_wr_ptr      <= (r_wr_ptr == PTRW'(DEPTH-1)) ? '0 : (r_wr_ptr + PTRW'(1));
            end
            if (pop) begin
                r_rd_ptr <= (r_rd_ptr == PTRW'(DEPTH-1)) ? '0 : (r_rd_ptr + PTRW'(1));
            end
            case ({push, pop})
                2'b10:   r_count <= r_count + (PTRW+1)'(1);
                2'b01:   r_count <= r_count - (PTRW+1)'(1);
                default: r_count <= r_count;   // 00 idle, 11 push-through
            endcase
        end
    )

endmodule : char_gen_wr_order_q
