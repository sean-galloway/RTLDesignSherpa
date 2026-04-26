// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: gaxi_skid_buffer
// Purpose: Shallow (DEPTH = 2..8) skid / FIFO buffer with ready/valid
//          interfaces on both sides. Used everywhere in the AMBA hierarchy
//          to register AXI/AXIL/APB channel handshakes.
//
// Documentation: rtl/amba/PRD.md
// Subsystem: amba
//
// Author: sean galloway
// Created: 2025-10-18
// Refactored: 2026-04-23 (shift-register storage instead of dynamic
//             indexed part-select into a packed vector — closes 100 MHz
//             timing on Artix-7 for DATA_WIDTH up to at least 256).
//
// ---------------------------------------------------------------------------
// STORAGE
// ---------------------------------------------------------------------------
// The previous implementation stored data as one flat packed vector
// `logic [DATA_WIDTH*DEPTH-1:0] r_data` and used dynamic indexed
// part-select writes:
//     r_data[(DW * r_data_count) +: DW] <= wr_data;
//     r_data[(DW * (r_data_count - 1)) +: DW] <= wr_data;
// With DATA_WIDTH up to 256 bits Vivado synthesised per-bit multipliers
// (CARRY4 chain) and a MUXF7-rooted mux tree 17 logic levels deep. That
// blew 100 MHz on Artix-7 from a block that should functionally be just
// "a 3:1 mux and a flop per bit per slot."
//
// This revision stores data as an unpacked array `r_data[DEPTH]` with
// one `always_ff` per slot in a `generate` loop. Each slot sees a
// 3:1 mux:
//     hold   → r_data[i]        (no transfer, or count moving elsewhere)
//     load   → wr_data          (write-only, count == i at start of cycle)
//     shift  → r_data[i+1]      (read-only, or simultaneous r+w into slot i+1)
// The write-during-simultaneous-r+w lands at `count-1` after the shift,
// so slot (count-1) takes `wr_data` instead of `r_data[i+1]`.
//
// Depth is expected to be one of {2, 4, 6, 8}. The shift-register form
// is optimal at depths 2–3 (the common case for AXI channel skids) and
// still cheaper than the packed-vector form for depths up through 8.
// ---------------------------------------------------------------------------

`timescale 1ns / 1ps

`include "reset_defs.svh"

module gaxi_skid_buffer #(
    parameter int DATA_WIDTH = 32,
    parameter int DEPTH = 2, // Must be one of {2, 4, 6, 8}
    // Legacy shorthand params (kept for source-compatibility)
    parameter int DW = DATA_WIDTH,
    parameter int BUF_WIDTH = DATA_WIDTH * DEPTH,
    parameter int BW = BUF_WIDTH
) (
    // Global Clock and Reset
    input  logic          axi_aclk,
    input  logic          axi_aresetn,

    // input side
    input  logic          wr_valid,
    output logic          wr_ready,
    input  logic [DW-1:0] wr_data,

    // output side
    output logic [3:0]    count,
    output logic          rd_valid,
    input  logic          rd_ready,
    output logic [3:0]    rd_count,
    output logic [DW-1:0] rd_data
);

    // Storage as an UNPACKED array — each slot is an independent register.
    logic [DW-1:0]  r_data [DEPTH];
    logic [3:0]     r_data_count;
    logic           w_wr_xfer;
    logic           w_rd_xfer;

    assign w_wr_xfer = wr_valid & wr_ready;
    assign w_rd_xfer = rd_valid & rd_ready;

    // =========================================================================
    // Per-slot update — 3:1 mux (hold / load / shift) + register.
    //
    // Every slot decodes the same {w_wr_xfer, w_rd_xfer, r_data_count}
    // but its update depends only on its own index i, so synth builds
    // DEPTH independent small cones instead of one giant shared demux.
    // =========================================================================
    generate
        for (genvar gi = 0; gi < DEPTH; gi++) begin : g_slot
            `ALWAYS_FF_RST(axi_aclk, axi_aresetn,
                if (`RST_ASSERTED(axi_aresetn)) begin
                    r_data[gi] <= '0;
                end else begin
                    unique case ({w_wr_xfer, w_rd_xfer})
                        2'b10: begin
                            // Write only: new data lands at the tail
                            // (index == current count).
                            if (r_data_count == gi[3:0]) begin
                                r_data[gi] <= wr_data;
                            end
                            // else: hold — no shift on write-only.
                        end
                        2'b01: begin
                            // Read only: shift down one slot.
                            if (gi < DEPTH-1) begin
                                r_data[gi] <= r_data[gi+1];
                            end else begin
                                r_data[gi] <= '0;  // clear the vacated tail
                            end
                        end
                        2'b11: begin
                            // Simultaneous r+w: shift, and the slot that
                            // would land at count-1 after the shift takes
                            // wr_data instead. For i == count-1 we load
                            // wr_data; for every other slot we shift.
                            if (r_data_count >= 1 &&
                                gi[3:0] == (r_data_count - 4'd1)) begin
                                r_data[gi] <= wr_data;
                            end else if (gi < DEPTH-1) begin
                                r_data[gi] <= r_data[gi+1];
                            end else begin
                                r_data[gi] <= '0;
                            end
                        end
                        default: begin
                            // 2'b00 — hold.
                        end
                    endcase
                end
            )
        end
    endgenerate

    // =========================================================================
    // Count tracking + handshake outputs. Count is 4 bits (DEPTH ≤ 8 +1 for
    // the "full+1" transient), so the arithmetic is trivial.
    // =========================================================================
    `ALWAYS_FF_RST(axi_aclk, axi_aresetn,
        if (`RST_ASSERTED(axi_aresetn)) begin
            r_data_count <= '0;
        end else begin
            unique case ({w_wr_xfer, w_rd_xfer})
                2'b10:   r_data_count <= r_data_count + 4'd1;
                2'b01:   r_data_count <= r_data_count - 4'd1;
                default: ;  // 2'b00 or 2'b11 — count unchanged
            endcase
        end
    )

    `ALWAYS_FF_RST(axi_aclk, axi_aresetn,
        if (`RST_ASSERTED(axi_aresetn)) begin
            wr_ready <= 1'b0;
            rd_valid <= 1'b0;
        end else begin
            wr_ready <= (32'(r_data_count) <= DEPTH-2) ||
                            (32'(r_data_count) == DEPTH-1 && (~w_wr_xfer || w_rd_xfer)) ||
                            (32'(r_data_count) == DEPTH && w_rd_xfer);

            rd_valid <= (r_data_count >= 2) ||
                            (r_data_count == 4'b0001 && (~w_rd_xfer || w_wr_xfer)) ||
                            (r_data_count == 4'b0000 && w_wr_xfer);
        end
    )

    // Head of the shift register is always slot 0.
    assign rd_data  = r_data[0];
    assign rd_count = r_data_count;
    assign count    = r_data_count;

endmodule : gaxi_skid_buffer
