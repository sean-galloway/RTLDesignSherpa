// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: hive_c_bram
// Purpose: One HIVE-C memory bank (I-mem or D-mem): a true-dual-port block
//          RAM of WORDS x 32 bits with a registered read on both ports.
//          Port A is read-only (the core's fetch port); port B reads and
//          writes per byte lane (the core's data port, or the loader).
//
// Documentation: projects/components/compute-eng-ip/hive/docs/hive_mas/ch02_blocks/02_hive_c_controller.md
// Subsystem: hive
//
// Author: sean galloway
// Created: 2026-11-27
//
// Parameters:
//   - WORDS: depth in 32-bit words (8192 = 32 KB, the HAS bank size).
//     Power of two.
//
// Notes:
//   - No reset port and no initial block: contents are init-by-write (the
//     loader always writes an image before run).  Each port's array access
//     sits in its own clock-only always_ff, so synthesis infers block RAM
//     (vault/handbook/design/sram-and-memories.md).
//   - Same-address port A read and port B write on one edge: port A returns
//     either word.  RISC-V allows that without FENCE.I between a store and
//     a fetch of the stored word.
//   - Each port's output register holds its last read while its enable is
//     low; the consumer qualifies it (hive_c_loader's response flops).

`timescale 1ns / 1ps

module hive_c_bram #(
    parameter int WORDS = 8192,
    localparam int IDX_W = $clog2(WORDS)
) (
    input  logic              clk,

    // Port A: read only
    input  logic              a_en,
    input  logic [IDX_W-1:0]  a_idx,
    output logic [31:0]       a_dout,

    // Port B: byte-lane write, read
    input  logic              b_en,
    input  logic [3:0]        b_we,
    input  logic [IDX_W-1:0]  b_idx,
    input  logic [31:0]       b_din,
    output logic [31:0]       b_dout
);

`ifndef SYNTHESIS
    initial begin : param_check
        if (WORDS < 2 || (WORDS & (WORDS - 1)) != 0)
            $error("hive_c_bram: WORDS (%0d) must be a power of two >= 2", WORDS);
    end
`endif

    (* ram_style = "block" *)
    /* synthesis ramstyle = "M10K" */
    logic [31:0] r_mem [WORDS];

    always_ff @(posedge clk) begin
        if (a_en) a_dout <= r_mem[a_idx];
    end

    always_ff @(posedge clk) begin
        if (b_en) begin
            for (int lane = 0; lane < 4; lane++) begin
                if (b_we[lane]) r_mem[b_idx][lane*8 +: 8] <= b_din[lane*8 +: 8];
            end
            b_dout <= r_mem[b_idx];
        end
    end

endmodule : hive_c_bram
