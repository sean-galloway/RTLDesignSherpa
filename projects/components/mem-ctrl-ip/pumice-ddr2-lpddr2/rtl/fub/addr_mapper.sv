// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: addr_mapper
// Purpose: Decode a flat AXI address into (rank, bank, row, col) using ONE
//          runtime knob: bank_lsb_i — where the bank field sits in the
//          byte-offset-stripped word address. The column fills below (col_lo)
//          and above (col_hi) the bank; row/rank stack above the column region
//          (their positions are INVARIANT). The classic "schemes" are just
//          settings of bank_lsb, so there is NO scheme mux:
//
//            bank_lsb == COL_WIDTH        -> bank above whole column = ROW_MAJOR
//            bank_lsb == log2(cols/burst) -> minimal col_lo          = BANK_INTERLEAVE
//            in between                   -> partial interleave
//
//          An optional bank XOR-hash (hash_en_i) folds row bits + a seed into
//          the bank index to defeat power-of-two-stride hot-banking (= XOR_HASH).
//
//          Layout (word address, low -> high):
//            [ col_lo(bank_lsb) | bank(BW) | col_hi(CW-bank_lsb) | row(RW) | rank(KW) ]
//            col = { col_hi, col_lo }.  row LSB is always CW+BW.
//
//          Combinational, single stage. Software keeps
//          log2(cols/burst) <= bank_lsb <= COL_WIDTH so a DRAM burst's column
//          walk stays inside one bank; the RTL clamps to [0, COL_WIDTH] to keep
//          the field slices legal.
//
// Documentation: rtl/macro/pumice_csr.rdl (ADDR_MAP register)

`timescale 1ns / 1ps

module addr_mapper
    import pumice_pkg::*;
#(
    parameter int AXI_ADDR_WIDTH       = 32,
    parameter int NUM_RANKS            = 1,    // 1, 2, or 4
    parameter int NUM_BANKS            = 8,    // 4 or 8
    parameter int ROW_WIDTH            = 14,
    parameter int COL_WIDTH            = 10,
    parameter int BYTE_OFFSET_WIDTH    = 3     // log2(beat byte size); 8 = 64-bit -> 3
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

    // Clamp bank_lsb to [0, COL_WIDTH] so col_hi width (CW - bank_lsb) stays >= 0
    // and the row/rank slices land where the geometry expects. (bank_lsb == CW is
    // ROW_MAJOR; below CW inserts the bank into the column = interleave.)
    logic [5:0] w_blsb;
    always_comb w_blsb = ({1'b0, bank_lsb_i} > 6'(CW)) ? 6'(CW) : {1'b0, bank_lsb_i};

    // Variable-base field extraction (barrel shifts / masks, 32b intermediates).
    logic [31:0] w_col_lo, w_col_hi, w_row32, w_rank32, w_bank32;
    assign w_col_lo = w_word & ((32'd1 << w_blsb) - 32'd1);                    // low col bits below bank
    assign w_bank32 = (w_word >> w_blsb) & ((32'd1 << BW) - 32'd1);            // BW bits at bank_lsb
    assign w_col_hi = (w_word >> (w_blsb + 6'(BW))) & ((32'd1 << (6'(CW) - w_blsb)) - 32'd1);
    assign w_row32  = (w_word >> (6'(CW) + 6'(BW))) & ((32'd1 << RW) - 32'd1); // row LSB invariant = CW+BW
    assign w_rank32 = (NUM_RANKS > 1)
                    ? ((w_word >> (6'(CW) + 6'(BW) + 6'(RW))) & ((32'd1 << KW) - 32'd1))
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
    assign row_o  = w_row;
    assign rank_o = (NUM_RANKS > 1) ? w_rank32[$clog2(NUM_RANKS > 1 ? NUM_RANKS : 2)-1:0] : '0;

endmodule : addr_mapper
