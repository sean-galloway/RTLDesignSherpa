// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: mc_addr_mapper
// Purpose: Decode a flat AXI address into (rank, bank group, bank, row, col)
//          using ONE runtime knob: bank_lsb_i — where the bank field sits in
//          the byte-offset-stripped word address. The column fills below
//          (col_lo) and above (col_hi) the bank; row/rank stack above the
//          column region (their positions are INVARIANT). The classic
//          "schemes" are just settings of bank_lsb, so there is NO scheme mux:
//
//            bank_lsb == COL_WIDTH        -> bank above whole column = ROW_MAJOR
//            bank_lsb == log2(burst)      -> minimal col_lo          = BANK_INTERLEAVE
//            in between                   -> partial interleave
//
//          An optional bank XOR-hash (hash_en_i) folds row bits + a seed into
//          the bank index to defeat power-of-two-stride hot-banking.
//
//          Layout (word address, low -> high):
//            HAS_BG=0 (generations 2/3):
//              [ col_lo(bank_lsb) | bank(BW) | col_hi(CW-bank_lsb) | row(RW) | rank(KW) ]
//            HAS_BG=1 (generation 4+, andesite delta):
//              [ col_lo(bank_lsb) | bank(BW) | bg(BGW) | col_hi | row(RW) | rank(KW) ]
//            col = { col_hi, col_lo }.  row LSB is CW+BW (+BGW when HAS_BG).
//
//          Combinational, single stage. Software keeps
//          log2(DRAM_BL) <= bank_lsb <= COL_WIDTH so a DRAM burst's column walk
//          stays inside one bank; the RTL clamps to [0, COL_WIDTH] to keep the
//          field slices legal. DRAM_BL is the right quantity because this block
//          indexes DEVICE WORDS (BYTE_OFFSET_WIDTH = log2(device bytes)) and
//          the core derives SUB_COL_STRIDE = DRAM_BL in those same units.
//
//          MEASURED, not derived: the per-rock addr_mapper tests report the
//          smallest bank_lsb that keeps an aligned burst inside one bank as
//          2 / 3 / 4 for bursts of 4 / 8 / 16 words — i.e. log2(burst). Two
//          wrong versions of this bound were once written down in opposite
//          directions (log2(cols/burst): too restrictive; log2(BL/DFI_RATE):
//          unsafe — pumice BUG-022 tracks the text fix).
//
//          Extracted 2026-10-10 (mem-ctrl-ip reorg Phase 2, Task 2): pumice
//          and scoria implementations were logically IDENTICAL (comment
//          rewraps only); andesite's bank-group field rides as the HAS_BG
//          parameter (BGW = HAS_BG ? BG_WIDTH : 0 keeps generation 2/3
//          arithmetic bit-identical). Knob inventory:
//          common-ip/docs/mc_fub_knobs.md.
//
// Documentation: per-rock ADDR_MAP CSR registers

`timescale 1ns / 1ps

module mc_addr_mapper
    import mc_common_pkg::*;
#(
    parameter int AXI_ADDR_WIDTH       = 32,
    parameter int NUM_RANKS            = 1,    // 1, 2, or 4
    parameter int NUM_BANKS            = 8,    // 4 or 8
    parameter int ROW_WIDTH            = 14,
    parameter int COL_WIDTH            = 10,
    parameter int BYTE_OFFSET_WIDTH    = 3,    // log2(beat byte size); 8 = 64-bit -> 3
    // ANDESITE BG DELTA: bank-group field above bank (DDR4). HAS_BG=0
    // (generations 2/3) compiles BGW to 0 and every shift matches the
    // pre-extraction pumice/scoria arithmetic exactly.
    parameter int BG_WIDTH             = 1,
    parameter bit HAS_BG               = 0
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
    output logic [BG_WIDTH-1:0]             bg_o,         // ANDESITE BG DELTA; '0 when !HAS_BG
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
    localparam int BGW = HAS_BG ? BG_WIDTH : 0;

    // Byte-offset-stripped word address, zero-extended to 32b for the variable
    // shift/mask field extraction below.
    logic [31:0] w_word;
    assign w_word = 32'(axi_addr_i[AW-1:BO]);

    // Clamp bank_lsb to [0, COL_WIDTH] so col_hi width (CW - bank_lsb) stays >= 0
    // and the row/rank slices land where the geometry expects. (bank_lsb == CW is
    // ROW_MAJOR; below CW inserts the bank into the column = interleave.)
    logic [5:0] w_blsb;
    always_comb w_blsb = ({1'b0, bank_lsb_i} > 6'(CW)) ? 6'(CW) : {1'b0, bank_lsb_i};

    // Field extraction WITHOUT barrel shifters (memory-controllers MC-006,
    // ISSUE-001 row 13). Row and rank sit above the whole {col, bank, bg}
    // field, so their slices never depended on bank_lsb and are constant
    // shifts. Column and bank (and bg) do move with bank_lsb, and until
    // 2026-11-07 each was a 32-bit variable shift against a variable mask on
    // the live AW/AR address: four 5-6 level mux cones per intake, timed at
    // the full clock, for a CSR that software writes once per run. Each is
    // now a constant slice per legal bank_lsb position (CW+1 of them),
    // selected by a one-hot decode of the clamped CSR: one decode level on
    // the quasi-static side and one AND-OR level per output bit on the
    // address side. Bit-identical to the shift form for every bank_lsb in
    // [0, COL_WIDTH]; formal/mc_common/mc_addr_mapper a_ref_* proves it
    // against the old expression.
    logic [31:0] w_row32, w_rank32;
    assign w_row32  = (w_word >> (CW + BW + BGW)) & ((32'd1 << RW) - 32'd1);
    assign w_rank32 = (NUM_RANKS > 1)
                    ? ((w_word >> (CW + BW + BGW + RW)) & ((32'd1 << KW) - 32'd1))
                    : 32'd0;

    logic [CW:0]   w_sel;                 // one-hot: w_sel[k] <=> clamped bank_lsb == k
    logic [CW-1:0] w_col_at  [CW+1];      // the column as laid out for bank_lsb == k, gated by w_sel[k]
    logic [BW-1:0] w_bank_at [CW+1];
    logic [31:0]   w_bg_at   [CW+1];      // 32b so BGW == 0 (no bank groups) stays well-formed
    for (genvar k = 0; k <= CW; k++) begin : g_pos
        // bank_lsb == k lays the word out as
        //   [ col_lo(k) | bank(BW) | bg(BGW) | col_hi(CW-k) | row(RW) | rank(KW) ]
        // and every shift and mask below is a constant: pure wiring.
        logic [31:0] w_col_lo_k, w_bank_k, w_bg_k, w_col_hi_k;
        assign w_col_lo_k = w_word & ((32'd1 << k) - 32'd1);
        assign w_bank_k   = (w_word >> k) & ((32'd1 << BW) - 32'd1);
        assign w_bg_k     = HAS_BG ? ((w_word >> (k + BW)) & ((32'd1 << BGW) - 32'd1)) : 32'd0;
        assign w_col_hi_k = (w_word >> (k + BW + BGW)) & ((32'd1 << (CW - k)) - 32'd1);
        assign w_sel[k]     = (w_blsb == 6'(k));
        assign w_col_at[k]  = w_sel[k] ? CW'(w_col_lo_k | (w_col_hi_k << k)) : '0;
        assign w_bank_at[k] = w_sel[k] ? BW'(w_bank_k) : '0;
        assign w_bg_at[k]   = w_sel[k] ? w_bg_k : 32'd0;
    end

    logic [CW-1:0] w_col;
    logic [BW-1:0] w_bank_raw, w_bank_hashed, w_bank;
    logic [31:0]   w_bg32;
    always_comb begin
        w_col      = '0;
        w_bank_raw = '0;
        w_bg32     = '0;
        for (int k = 0; k <= CW; k++) begin
            w_col      |= w_col_at[k];
            w_bank_raw |= w_bank_at[k];
            w_bg32     |= w_bg_at[k];
        end
    end

    logic [RW-1:0]  w_row;
    assign w_row = RW'(w_row32);

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

endmodule : mc_addr_mapper
