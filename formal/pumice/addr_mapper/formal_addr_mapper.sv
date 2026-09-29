// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// Formal wrapper for addr_mapper -- the AXI address -> (rank, bank, row, col)
// decode.
//
// WHY THIS BLOCK. It is the one place where a bug corrupts data with no symptom
// anywhere else. Every other pumice block either damages the DRAM's timing (the
// timers), stalls (the CAMs and intakes), or returns a wrong beat that a
// scoreboard catches. An address decode that ALIASES -- two distinct addresses
// landing on the same (rank, bank, row, col) -- returns the wrong data
// perfectly happily, to the wrong requester, and the only witness is a
// mismatch a long way downstream.
//
// WHAT IS PROVED, and the first one is the whole reason this file exists:
//
//   INJECTIVITY. Two distinct word addresses inside the mappable range never
//   decode to the same tuple -- for EVERY bank_lsb, with and without the XOR
//   hash. This is not a property simulation can establish: it is a statement
//   about all pairs of addresses, and a directed test can only sample them.
//
//   FIELD INVARIANCE. The header claims "row/rank stack above the column region
//   (their positions are INVARIANT)" and "row LSB is always CW+BW". Proved by
//   decoding ONE address through two mappers configured with DIFFERENT bank_lsb
//   and asserting row and rank come out identical. If that ever stopped holding,
//   changing ADDR_MAP.bank_lsb at runtime would silently move data.
//
//   CLAMPING. The RTL clamps bank_lsb to [0, COL_WIDTH] "to keep the field
//   slices legal". Proved by showing an out-of-range bank_lsb decodes exactly as
//   COL_WIDTH does -- so software that writes a bad value gets ROW_MAJOR rather
//   than a corrupt slice.
//
//   THE NAMED SCHEMES. bank_lsb == COL_WIDTH is ROW_MAJOR: the column is the
//   low CW bits and the bank sits directly above it. Checked against a
//   hand-written expectation rather than against the RTL's own expression.
//
// COMBINATIONAL DUT. There is no state, so the BMC depth is 1 -- everything here
// is a statement about one evaluation. The clock exists only because the
// property form needs an edge.
//
// SMALL GEOMETRY ON PURPOSE. 4 banks, 4-bit row, 4-bit column, 2 ranks. The
// decode is a set of variable shifts and masks whose correctness does not depend
// on width; what a small geometry buys is that the mappable address space is
// 11 bits, so "every pair of addresses" is a question the solver can answer
// exhaustively rather than approximately.
//
// YOSYS-COMPATIBLE FORM. DUT pre-flattened by sv2v (yosys cannot parse
// pumice_pkg.sv); immediate assertions in `always @(posedge clk)`.

`timescale 1ns / 1ps

module formal_addr_mapper #(
    parameter int AW  = 16,   // AXI_ADDR_WIDTH
    parameter int NR  = 2,    // NUM_RANKS
    parameter int NB  = 4,    // NUM_BANKS
    parameter int RW  = 4,    // ROW_WIDTH
    parameter int CW  = 4,    // COL_WIDTH
    parameter int BO  = 2,    // BYTE_OFFSET_WIDTH
    parameter int BW  = 2,    // $clog2(NB)
    parameter int KW  = 1     // $clog2(NR)
) (
    input logic clk
);

    // The address space the decode actually covers. Anything above this is
    // masked off by the row/rank slices, so two addresses differing only up
    // there alias BY DESIGN (the map wraps) and must be excluded -- assuming
    // otherwise would make injectivity false for an uninteresting reason.
    localparam int MAPW = CW + BW + RW + KW;   // 11
    localparam int WW   = AW - BO;             // 14, the word-address width

    (* anyconst *) reg [AW-1:0] addr_a, addr_b;
    (* anyconst *) reg [4:0]    blsb, blsb2;
    (* anyconst *) reg          hash_en;
    (* anyconst *) reg [7:0]    hash_seed;

    wire [WW-1:0] word_a = addr_a[AW-1:BO];
    wire [WW-1:0] word_b = addr_b[AW-1:BO];

    always @(*) begin
        // both inside the mappable range
        assume (word_a < (1 << MAPW));
        assume (word_b < (1 << MAPW));
        // byte offsets equal, so this is a statement about WORD addresses: two
        // addresses inside one beat are meant to decode identically.
        assume (addr_a[BO-1:0] == addr_b[BO-1:0]);
        // software keeps bank_lsb in range; the clamp instance below is what
        // covers the out-of-range case deliberately.
        assume (blsb  <= CW);
    end

    // ---- two mappers, same configuration, different addresses ---------------
    wire [KW-1:0] rank_a, rank_b;
    wire [BW-1:0] bank_a, bank_b;
    wire [RW-1:0] row_a,  row_b;
    wire [CW-1:0] col_a,  col_b;

    addr_mapper #(.AXI_ADDR_WIDTH(AW), .NUM_RANKS(NR), .NUM_BANKS(NB),
                  .ROW_WIDTH(RW), .COL_WIDTH(CW), .BYTE_OFFSET_WIDTH(BO)) u_a (
        .axi_addr_i(addr_a), .bank_lsb_i(blsb),
        .hash_en_i(hash_en), .hash_seed_i(hash_seed),
        .rank_o(rank_a), .bank_o(bank_a), .row_o(row_a), .col_o(col_a));

    addr_mapper #(.AXI_ADDR_WIDTH(AW), .NUM_RANKS(NR), .NUM_BANKS(NB),
                  .ROW_WIDTH(RW), .COL_WIDTH(CW), .BYTE_OFFSET_WIDTH(BO)) u_b (
        .axi_addr_i(addr_b), .bank_lsb_i(blsb),
        .hash_en_i(hash_en), .hash_seed_i(hash_seed),
        .rank_o(rank_b), .bank_o(bank_b), .row_o(row_b), .col_o(col_b));

    // ---- same address, a DIFFERENT bank_lsb: row/rank must not move ---------
    wire [KW-1:0] rank_c;  wire [BW-1:0] bank_c;
    wire [RW-1:0] row_c;   wire [CW-1:0] col_c;
    addr_mapper #(.AXI_ADDR_WIDTH(AW), .NUM_RANKS(NR), .NUM_BANKS(NB),
                  .ROW_WIDTH(RW), .COL_WIDTH(CW), .BYTE_OFFSET_WIDTH(BO)) u_c (
        .axi_addr_i(addr_a), .bank_lsb_i(blsb2),
        .hash_en_i(hash_en), .hash_seed_i(hash_seed),
        .rank_o(rank_c), .bank_o(bank_c), .row_o(row_c), .col_o(col_c));

    // ---- the clamp: bank_lsb == COL_WIDTH, to compare an out-of-range one ---
    wire [KW-1:0] rank_d;  wire [BW-1:0] bank_d;
    wire [RW-1:0] row_d;   wire [CW-1:0] col_d;
    addr_mapper #(.AXI_ADDR_WIDTH(AW), .NUM_RANKS(NR), .NUM_BANKS(NB),
                  .ROW_WIDTH(RW), .COL_WIDTH(CW), .BYTE_OFFSET_WIDTH(BO)) u_d (
        .axi_addr_i(addr_a), .bank_lsb_i(5'(CW)),
        .hash_en_i(hash_en), .hash_seed_i(hash_seed),
        .rank_o(rank_d), .bank_o(bank_d), .row_o(row_d), .col_o(col_d));

    // =====================================================================
    // FAMILY 1 -- INJECTIVITY. No two addresses share a location.
    // =====================================================================
    always @(posedge clk) begin
        if (word_a != word_b)
            a_injective: assert (!((rank_a == rank_b) && (bank_a == bank_b)
                               && (row_a  == row_b)  && (col_a  == col_b)));

        // ...and the converse: equal word addresses decode identically. A decode
        // that depended on anything but the address and the configuration would
        // break this, and nothing downstream would notice.
        if (word_a == word_b)
            a_deterministic: assert ((rank_a == rank_b) && (bank_a == bank_b)
                                  && (row_a  == row_b)  && (col_a  == col_b));
    end

    // =====================================================================
    // FAMILY 2 -- FIELD INVARIANCE across bank_lsb.
    // =====================================================================
    always @(posedge clk) begin
        // The header's claim, as a property: only the bank/column split moves
        // with bank_lsb. row and rank are anchored at CW+BW regardless.
        if (blsb2 <= 5'(CW)) begin
            a_row_invariant:  assert (row_c  == row_a);
            a_rank_invariant: assert (rank_c == rank_a);
        end

        // The clamp: an out-of-range bank_lsb decodes exactly as COL_WIDTH.
        // Software that writes a bad value gets ROW_MAJOR, not a corrupt slice.
        if (blsb2 > 5'(CW)) begin
            a_clamp_row:  assert (row_c  == row_d);
            a_clamp_rank: assert (rank_c == rank_d);
            a_clamp_bank: assert (bank_c == bank_d);
            a_clamp_col:  assert (col_c  == col_d);
        end
    end

    // =====================================================================
    // FAMILY 3 -- ROW_MAJOR, against a hand-written expectation.
    // =====================================================================
    // Written from the documented layout rather than from the RTL's expression,
    // so this disagrees if the RTL is rewritten to mean something else.
    //   [ col(CW) | bank(BW) | row(RW) | rank(KW) ]   at bank_lsb == CW
    wire [CW-1:0] exp_col  = word_a[CW-1:0];
    wire [BW-1:0] exp_bank = word_a[CW+BW-1:CW];
    wire [RW-1:0] exp_row  = word_a[CW+BW+RW-1:CW+BW];
    wire [KW-1:0] exp_rank = word_a[CW+BW+RW+KW-1:CW+BW+RW];

    always @(posedge clk) begin
        a_rowmajor_col:  assert (col_d  == exp_col);
        a_rowmajor_row:  assert (row_d  == exp_row);
        a_rowmajor_rank: assert (rank_d == exp_rank);
        // bank only when the hash is off -- with it on, bank is deliberately
        // scrambled, and the hash's own correctness is covered by a_injective.
        if (!hash_en) a_rowmajor_bank: assert (bank_d == exp_bank);
    end

    // =====================================================================
    // COVER -- the interesting configurations are reachable.
    // =====================================================================
    always @(posedge clk) begin
        c_rowmajor:    cover (blsb == 5'(CW));              // bank above the column
        c_interleave:  cover (blsb == 5'd1);                // bank low = interleave
        c_partial:     cover (blsb > 5'd1 && blsb < 5'(CW)); // split column
        c_hash_on:     cover (hash_en);
        c_clamped:     cover (blsb2 > 5'(CW));              // the clamp path taken
        c_split_col:   cover (blsb > 5'd0 && blsb < 5'(CW) && col_a != 0);
    end

endmodule
