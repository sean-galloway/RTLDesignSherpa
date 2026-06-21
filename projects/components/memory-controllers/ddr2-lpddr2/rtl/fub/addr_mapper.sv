// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: addr_mapper
// Purpose: Decode flat AXI address into (rank, bank, row, col) per the
//          currently-active address-mapping scheme.
//
// Description:
//   Combinational FUB (no clock; no reset). One stage from AXI flat
//   address to DRAM-layer tuple. Sits between axi4_slave and the CAMs
//   so the CAMs store the decoded tuple, not the raw address.
//
//   Three schemes are computed in parallel; the runtime-selected
//   scheme is the active output. Mirrors the Python AddressMapping
//   class in the DV repo (bit-for-bit identical decode).
//
// Documentation:
//   docs/ddr2_lpddr2_mas/ch02_blocks/03_addr_mapper.md
//
// Author: sean galloway
// Created: 2026-06-17

`timescale 1ns / 1ps

module addr_mapper
    import ddr2_lpddr2_pkg::*;
#(
    parameter int AXI_ADDR_WIDTH       = 32,
    parameter int NUM_RANKS            = 1,    // 1, 2, or 4
    parameter int NUM_BANKS            = 8,    // 4 or 8
    parameter int ROW_WIDTH            = 14,
    parameter int COL_WIDTH            = 10,
    parameter int BYTE_OFFSET_WIDTH    = 3,    // log2(beat byte size); 8 = 64-bit -> 3
    parameter bit SYNTH_ROW_MAJOR      = 1'b1,
    parameter bit SYNTH_BANK_INTERLEAVE = 1'b1,
    parameter bit SYNTH_XOR_HASH        = 1'b0
) (
    // Inputs from axi4_slave_fub (AW or AR side)
    input  logic [AXI_ADDR_WIDTH-1:0]       axi_addr_i,

    // Runtime configuration (CSR live)
    input  addr_map_scheme_e                scheme_active_i,
    input  logic [7:0]                      xor_seed_i,         // active when XOR_HASH
    input  logic [2:0]                      bg_field_pos_i,     // reserved (DDR4+); tied 0 here

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

    // Strip byte-offset bits; what remains is the column-word address space
    wire [AW-BO-1:0] w_addr_word = axi_addr_i[AW-1:BO];

    //=========================================================================
    // ROW_MAJOR scheme
    //=========================================================================
    //   bits: [rank | row | bank | col]
    // The bank field sits just above the column so the LSBs walk the
    // column within one row before crossing a bank boundary. Best for
    // sequential streaming.

    logic [KW-1:0] w_rm_rank;
    logic [BW-1:0] w_rm_bank;
    logic [RW-1:0] w_rm_row;
    logic [CW-1:0] w_rm_col;

    generate
        if (SYNTH_ROW_MAJOR) begin : g_row_major
            assign w_rm_col  = w_addr_word[CW-1:0];
            assign w_rm_bank = w_addr_word[CW +: BW];
            assign w_rm_row  = w_addr_word[CW + BW +: RW];
            assign w_rm_rank = (NUM_RANKS > 1)
                               ? w_addr_word[CW + BW + RW +: KW]
                               : '0;
        end else begin : g_row_major_off
            assign w_rm_col = '0;
            assign w_rm_bank = '0;
            assign w_rm_row = '0;
            assign w_rm_rank = '0;
        end
    endgenerate

    //=========================================================================
    // BANK_INTERLEAVE scheme
    //=========================================================================
    //   bits: [rank | row | col_hi | bank | col_lo]
    // Bank bits sit between low and high column bits. Cache-line stride
    // round-robins across banks → higher bank parallelism.

    localparam int CL = (CW >= 4) ? 4 : CW;   // col_lo width
    localparam int CH = CW - CL;              // col_hi width

    logic [KW-1:0] w_bi_rank;
    logic [BW-1:0] w_bi_bank;
    logic [RW-1:0] w_bi_row;
    logic [CW-1:0] w_bi_col;

    generate
        if (SYNTH_BANK_INTERLEAVE) begin : g_bank_inter
            logic [CL-1:0] w_bi_col_lo;
            logic [CH-1:0] w_bi_col_hi;
            assign w_bi_col_lo = w_addr_word[CL-1:0];
            assign w_bi_bank   = w_addr_word[CL +: BW];
            assign w_bi_col_hi = w_addr_word[CL + BW +: CH];
            assign w_bi_row    = w_addr_word[CL + BW + CH +: RW];
            assign w_bi_rank   = (NUM_RANKS > 1)
                                 ? w_addr_word[CL + BW + CH + RW +: KW]
                                 : '0;
            assign w_bi_col    = { w_bi_col_hi, w_bi_col_lo };
        end else begin : g_bank_inter_off
            assign w_bi_col = '0;
            assign w_bi_bank = '0;
            assign w_bi_row = '0;
            assign w_bi_rank = '0;
        end
    endgenerate

    //=========================================================================
    // XOR_HASH scheme
    //=========================================================================
    // Same layout as BANK_INTERLEAVE, but the bank field is XOR'd with
    // selected row bits + a runtime seed. Defeats power-of-two stride
    // patterns that hammer one bank.

    logic [KW-1:0] w_xh_rank;
    logic [BW-1:0] w_xh_bank;
    logic [RW-1:0] w_xh_row;
    logic [CW-1:0] w_xh_col;

    generate
        if (SYNTH_XOR_HASH) begin : g_xor_hash
            // Base layout = BANK_INTERLEAVE
            logic [BW-1:0] w_xh_bank_raw;
            logic [CL-1:0] w_xh_col_lo;
            logic [CH-1:0] w_xh_col_hi;
            assign w_xh_col_lo   = w_addr_word[CL-1:0];
            assign w_xh_bank_raw = w_addr_word[CL +: BW];
            assign w_xh_col_hi   = w_addr_word[CL + BW +: CH];
            assign w_xh_row      = w_addr_word[CL + BW + CH +: RW];
            assign w_xh_rank     = (NUM_RANKS > 1)
                                   ? w_addr_word[CL + BW + CH + RW +: KW]
                                   : '0;
            assign w_xh_col      = { w_xh_col_hi, w_xh_col_lo };

            // Hash: bank XOR row[low BW] XOR row[mid BW] XOR seed[BW-1:0]
            // (mid-slice indexing clamped so it doesn't run past ROW_WIDTH)
            for (genvar i = 0; i < BW; i++) begin : g_xh_xor
                localparam int LOW_IDX = i;
                localparam int MID_IDX = (i + BW < RW) ? (i + BW) : (RW - 1);
                assign w_xh_bank[i] = w_xh_bank_raw[i]
                                    ^ w_xh_row[LOW_IDX]
                                    ^ w_xh_row[MID_IDX]
                                    ^ xor_seed_i[i];
            end
        end else begin : g_xor_hash_off
            assign w_xh_col = '0;
            assign w_xh_bank = '0;
            assign w_xh_row = '0;
            assign w_xh_rank = '0;
        end
    endgenerate

    //=========================================================================
    // Runtime scheme mux
    //=========================================================================

    always_comb begin
        unique case (scheme_active_i)
            ADDR_MAP_ROW_MAJOR : begin
                rank_o = w_rm_rank;
                bank_o = w_rm_bank;
                row_o  = w_rm_row;
                col_o  = w_rm_col;
            end
            ADDR_MAP_BANK_INTERLEAVE : begin
                rank_o = w_bi_rank;
                bank_o = w_bi_bank;
                row_o  = w_bi_row;
                col_o  = w_bi_col;
            end
            ADDR_MAP_XOR_HASH : begin
                rank_o = w_xh_rank;
                bank_o = w_xh_bank;
                row_o  = w_xh_row;
                col_o  = w_xh_col;
            end
            default : begin
                rank_o = '0;
                bank_o = '0;
                row_o  = '0;
                col_o  = '0;
            end
        endcase
    end

    // Pin tie: bg_field_pos_i is reserved for DDR4+ bank groups
    wire unused_bgfp = |bg_field_pos_i;

endmodule : addr_mapper
