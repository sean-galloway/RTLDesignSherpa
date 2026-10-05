// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: andesite_addr_mapper
// Purpose: addr_mapper
//
// Documentation:
//   projects/components/mem-ctrl-ip/andesite-ddr4-lpddr4/docs/andesite_mas/
//
// Carried from scoria_addr_mapper per andesite HAS ch02; see the P3 commit for
// the recorded andesite delta (this header is free-form provenance).
//
// Author: sean galloway
// Created: 2026-10-04 (carried, andesite delta applied)

`timescale 1ns / 1ps

module andesite_addr_mapper
    import andesite_pkg::*;
#(
    parameter int AXI_ADDR_WIDTH       = 32,
    parameter int NUM_RANKS            = 1,    // 1, 2, or 4
    parameter int NUM_BANKS            = 8,    // 4 or 8
    parameter int ROW_WIDTH            = 14,
    parameter int COL_WIDTH            = 10,
    parameter int BYTE_OFFSET_WIDTH    = 3,    // log2(beat byte size); 8 = 64-bit -> 3
    parameter int BG_WIDTH             = 2     // andesite delta: bank-group field above bank
) (
    // Inputs from axi4_slave_fub (AW or AR side)
    input  logic [AXI_ADDR_WIDTH-1:0]       axi_addr_i,

    // Runtime configuration (CSR live — ADDR_MAP register)
    input  logic [4:0]                      bank_lsb_i,   // bank field LSB in word addr
    input  logic                            hash_en_i,    // enable bank XOR-hash
    input  logic [7:0]                      hash_seed_i,  // XOR-hash seed

    // Decoded outputs to the CAMs
    output logic [$clog2(NUM_RANKS > 1 ? NUM_RANKS : 2)-1:0] rank_o,
    output logic [$clog2(NUM_BANKS)-1:0]    bank_o,
    // andesite delta (MAS 04): bank group sits above the bank field.
    output logic [BG_WIDTH-1:0]             bg_o,
    output logic [ROW_WIDTH-1:0]            row_o,
    output logic [COL_WIDTH-1:0]            col_o
);

    // Short aliases
    localparam int AW = AXI_ADDR_WIDTH;
    localparam int RW = ROW_WIDTH;
    localparam int CW = COL_WIDTH;
    localparam int BW = (NUM_BANKS > 1) ? $clog2(NUM_BANKS) : 1;
    localparam int KW = (NUM_RANKS > 1) ? $clog2(NUM_RANKS) : 1;
    localparam int BO = BYTE_OFFSET_WIDTH;

    // Byte-offset-stripped word address, zero-extended to 32b for the variable
    // shift/mask field extraction below.
    logic [31:0] w_word;
    assign w_word = 32'(axi_addr_i[AW-1:BO]);

    // Kmap citation anchor (docs/kmaps/gen_andesite_kmaps.py CITES): the
    // address-decode structure and field-boundary fence, verbatim from the
    // MAS 04 page so the drift gate diffs the same text at the RTL.
    //   sys_addr -> { cs[CS-1:0],
    //                 bg[BG-1:0]       (DDR4: BG0/BG1; LPDDR4: constant 0),
    //                 bank[BANK-1:0]   (DDR4: 2 bits; LPDDR4: 3 bits),
    //                 row[ROW-1:0], col[COL-1:0] }
    // Field boundaries are runtime CSRs (ADDR_MAP-style), set by the
    // bank_lsb_i knob; the fields above the bank shift with it.

    // Clamp bank_lsb to [0, COL_WIDTH] so col_hi width (CW - bank_lsb) stays >= 0
    // and the row/rank slices land where the geometry expects. (bank_lsb == CW is
    // ROW_MAJOR; below CW inserts the bank into the column = interleave.)
    logic [5:0] w_blsb;
    always_comb w_blsb = ({1'b0, bank_lsb_i} > 6'(CW)) ? 6'(CW) : {1'b0, bank_lsb_i};

    // Variable-base field extraction (barrel shifts / masks, 32b intermediates).
    localparam int BGW = BG_WIDTH;
    logic [31:0] w_col_lo, w_col_hi, w_row32, w_rank32, w_bank32, w_bg32;
    assign w_col_lo = w_word & ((32'd1 << w_blsb) - 32'd1);                    // low col bits below bank
    assign w_bank32 = (w_word >> w_blsb) & ((32'd1 << BW) - 32'd1);            // BW bits at bank_lsb
    assign w_bg32   = (w_word >> (w_blsb + 6'(BW))) & ((32'd1 << BGW) - 32'd1); // andesite: bg above bank
    assign w_col_hi = (w_word >> (w_blsb + 6'(BW) + 6'(BGW))) & ((32'd1 << (6'(CW) - w_blsb)) - 32'd1);
    assign w_row32  = (w_word >> (6'(CW) + 6'(BW) + 6'(BGW))) & ((32'd1 << RW) - 32'd1); // row LSB = CW+BW+BGW (andesite)
    assign w_rank32 = (NUM_RANKS > 1)
                    ? ((w_word >> (6'(CW) + 6'(BW) + 6'(BGW) + 6'(RW))) & ((32'd1 << KW) - 32'd1))
                    : 32'd0;

    // Reassemble the (split) column: low bits = col_lo, high bits = col_hi.
    logic [CW-1:0] w_col;
    assign w_col = CW'(w_col_lo | (w_col_hi << w_blsb));

    logic [RW-1:0]  w_row;
    logic [BW-1:0]  w_bank_raw, w_bank_hashed, w_bank;
    assign w_row      = RW'(w_row32);
    assign w_bank_raw = BW'(w_bank32);

    // Bank XOR-hash: bank[i] ^= row[i] ^ row[i+BW] ^ seed[i] (mid slice clamped so
    // it never runs past ROW_WIDTH). Identical fold to the legacy XOR_HASH scheme.
    for (genvar i = 0; i < BW; i++) begin : g_hash
        localparam int MID = (i + BW < RW) ? (i + BW) : (RW - 1);
        assign w_bank_hashed[i] = w_bank_raw[i] ^ w_row[i] ^ w_row[MID] ^ hash_seed_i[i];
    end
    assign w_bank = hash_en_i ? w_bank_hashed : w_bank_raw;

    // Outputs
    assign col_o  = w_col;
    assign bank_o = w_bank;
    assign bg_o   = BG_WIDTH'(w_bg32);
    assign row_o  = w_row;
    assign rank_o = (NUM_RANKS > 1) ? w_rank32[$clog2(NUM_RANKS > 1 ? NUM_RANKS : 2)-1:0] : '0;

endmodule : andesite_addr_mapper
