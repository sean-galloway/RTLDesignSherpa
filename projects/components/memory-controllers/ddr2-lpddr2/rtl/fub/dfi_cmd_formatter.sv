// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2026 sean galloway
//
// Module: dfi_cmd_formatter
// Purpose: Translate the scheduler's chosen `dram_op_e` plus
//          (rank, bank, row, col) into the DFI v2.1 control bus signals
//          per JEDEC truth table for DDR2 (LPDDR2 reuses dfi_address
//          as a 20-bit CA bus — TODO).
//
// Multi-phase output:
//   For DFI_RATE = N, every DFI control signal is packed as N phases:
//     dfi_address_o[ p * DFI_ADDR_WIDTH +: DFI_ADDR_WIDTH ] = phase p
//     dfi_bank_o   [ p * DFI_BANK_WIDTH +: DFI_BANK_WIDTH ] = phase p
//     dfi_*_n_o    [ p * DFI_CTRL_WIDTH +: DFI_CTRL_WIDTH ] = phase p
//     dfi_cs_n_o   [ p * DFI_CS_WIDTH   +: DFI_CS_WIDTH   ] = phase p
//
//   v1 places the issued command on phase 0; phases 1..N-1 emit NOP
//   (cs_n='1, ras_n=cas_n=we_n=1, odt=0). Multi-cmd-per-cycle becomes a
//   scheduler-side feature later; the bus widths are already in place.
//
// DDR2 truth table (JEDEC JESD79-2 Table 49):
//
//   op       cs_n  ras_n cas_n we_n  bank   addr[10]   addr[..0]
//   NOP      0     1     1     1     X      X          X
//   ACT      0     0     1     1     BA     row[10]    row[13:0]
//   RD       0     1     0     1     BA     0          col
//   RDA      0     1     0     1     BA     1          col   (auto-PRE)
//   WR       0     1     0     0     BA     0          col
//   WRA      0     1     0     0     BA     1          col   (auto-PRE)
//   PRE      0     0     1     0     BA     0          X
//   PREA     0     0     1     0     X      1          X
//   REF      0     0     0     1     X      X          X
//   MRS      0     0     0     0     MR_idx MR_data    MR_data
//
//   cs_n is per-rank: cs_n[r]=0 selects rank r; '1 all-deselected = NOP.
//
// LPDDR2 (TODO): dfi_address reused as a 20-bit CA bus, RAS/CAS/WE held
//   idle. Drives NOP for now when memtype_i == MEMTYPE_LPDDR2.

`timescale 1ns / 1ps

`include "reset_defs.svh"

module dfi_cmd_formatter
    import ddr2_lpddr2_pkg::*;
#(
    parameter int NUM_RANKS       = 1,
    parameter int NUM_BANKS       = 8,
    parameter int ROW_WIDTH       = 14,
    parameter int COL_WIDTH       = 10,
    parameter int BURST_LEN_WIDTH = 8,

    // Per-phase DFI widths
    parameter int DFI_RATE        = 2,
    parameter int DFI_ADDR_WIDTH  = 14,
    parameter int DFI_BANK_WIDTH  = 3,
    parameter int DFI_CTRL_WIDTH  = 1,
    parameter int DFI_CS_WIDTH    = NUM_RANKS,

    // Multi-phase bus widths (= per-phase × DFI_RATE)
    parameter int DFI_ADDR_BUS_W  = DFI_ADDR_WIDTH * DFI_RATE,
    parameter int DFI_BANK_BUS_W  = DFI_BANK_WIDTH * DFI_RATE,
    parameter int DFI_CTRL_BUS_W  = DFI_CTRL_WIDTH * DFI_RATE,
    parameter int DFI_CS_BUS_W    = DFI_CS_WIDTH * DFI_RATE,

    parameter int RKW = (NUM_RANKS > 1) ? $clog2(NUM_RANKS) : 1,
    parameter int BKW = $clog2(NUM_BANKS)
) (
    input  logic                          mc_clk,
    input  logic                          mc_rst_n,

    input  memtype_e                      memtype_i,

    // ----- chosen op from scheduler -----
    input  logic                          cmd_valid_i,
    output logic                          cmd_ready_o,
    input  dram_op_e                      cmd_op_i,
    input  logic [RKW-1:0]                cmd_rank_i,
    input  logic [BKW-1:0]                cmd_bank_i,
    input  logic [ROW_WIDTH-1:0]          cmd_row_i,
    input  logic [COL_WIDTH-1:0]          cmd_col_i,
    input  logic [BURST_LEN_WIDTH-1:0]    cmd_len_i,

    // ----- multi-phase DFI control bus -----
    output logic [DFI_ADDR_BUS_W-1:0]     dfi_address_o,
    output logic [DFI_BANK_BUS_W-1:0]     dfi_bank_o,
    output logic [DFI_CTRL_BUS_W-1:0]     dfi_cas_n_o,
    output logic [DFI_CTRL_BUS_W-1:0]     dfi_ras_n_o,
    output logic [DFI_CTRL_BUS_W-1:0]     dfi_we_n_o,
    output logic [DFI_CS_BUS_W-1:0]       dfi_cs_n_o,
    output logic [DFI_CS_BUS_W-1:0]       dfi_odt_o
);

    //=========================================================================
    // Phase-0 decode — combinational DDR2 truth table.
    //=========================================================================
    logic [DFI_ADDR_WIDTH-1:0] w_p0_addr;
    logic [DFI_BANK_WIDTH-1:0] w_p0_bank;
    logic [DFI_CTRL_WIDTH-1:0] w_p0_cas_n;
    logic [DFI_CTRL_WIDTH-1:0] w_p0_ras_n;
    logic [DFI_CTRL_WIDTH-1:0] w_p0_we_n;
    logic [DFI_CS_WIDTH-1:0]   w_p0_cs_n;
    logic [DFI_CS_WIDTH-1:0]   w_p0_odt;

    // Pre-compute the active-rank cs_n mask: cs_n[r]=0 for selected rank,
    // 1 elsewhere. For NUM_RANKS=1, RKW=1 but only bit 0 of cs_n exists.
    logic [DFI_CS_WIDTH-1:0]   w_active_rank_mask;
    always_comb begin
        w_active_rank_mask = '1;
        for (int unsigned r = 0; r < DFI_CS_WIDTH; r++) begin
            if (RKW'(r) == cmd_rank_i) w_active_rank_mask[r] = 1'b0;
        end
    end

    always_comb begin
        // Default: all-deselected NOP
        w_p0_addr  = '0;
        w_p0_bank  = '0;
        w_p0_cas_n = '1;
        w_p0_ras_n = '1;
        w_p0_we_n  = '1;
        w_p0_cs_n  = '1;
        w_p0_odt   = '0;

        if (cmd_valid_i && memtype_i == MEMTYPE_DDR2) begin
            // Default selected NOP — cs_n active for the targeted rank.
            w_p0_cs_n = w_active_rank_mask;

            unique case (cmd_op_i)
                OP_NOP: begin
                    // Selected NOP (defaults above are correct)
                end

                OP_ACT: begin
                    w_p0_ras_n = '0;
                    w_p0_cas_n = '1;
                    w_p0_we_n  = '1;
                    w_p0_bank  = DFI_BANK_WIDTH'(cmd_bank_i);
                    w_p0_addr  = DFI_ADDR_WIDTH'(cmd_row_i);
                end

                OP_RD: begin
                    w_p0_ras_n = '1;
                    w_p0_cas_n = '0;
                    w_p0_we_n  = '1;
                    w_p0_bank  = DFI_BANK_WIDTH'(cmd_bank_i);
                    // A10 = 0 (no auto-precharge)
                    w_p0_addr  = DFI_ADDR_WIDTH'(cmd_col_i);
                end

                OP_RDA: begin
                    w_p0_ras_n = '1;
                    w_p0_cas_n = '0;
                    w_p0_we_n  = '1;
                    w_p0_bank  = DFI_BANK_WIDTH'(cmd_bank_i);
                    // A10 = 1 (auto-precharge)
                    w_p0_addr  = DFI_ADDR_WIDTH'(cmd_col_i)
                              | (DFI_ADDR_WIDTH'(1) << 10);
                end

                OP_WR: begin
                    w_p0_ras_n = '1;
                    w_p0_cas_n = '0;
                    w_p0_we_n  = '0;
                    w_p0_bank  = DFI_BANK_WIDTH'(cmd_bank_i);
                    w_p0_addr  = DFI_ADDR_WIDTH'(cmd_col_i);
                end

                OP_WRA: begin
                    w_p0_ras_n = '1;
                    w_p0_cas_n = '0;
                    w_p0_we_n  = '0;
                    w_p0_bank  = DFI_BANK_WIDTH'(cmd_bank_i);
                    w_p0_addr  = DFI_ADDR_WIDTH'(cmd_col_i)
                              | (DFI_ADDR_WIDTH'(1) << 10);
                end

                OP_PRE: begin
                    w_p0_ras_n = '0;
                    w_p0_cas_n = '1;
                    w_p0_we_n  = '0;
                    w_p0_bank  = DFI_BANK_WIDTH'(cmd_bank_i);
                    // A10 = 0 → single-bank precharge
                end

                OP_PREA: begin
                    w_p0_ras_n = '0;
                    w_p0_cas_n = '1;
                    w_p0_we_n  = '0;
                    // A10 = 1 → all-bank precharge
                    w_p0_addr  = (DFI_ADDR_WIDTH'(1) << 10);
                end

                OP_REF: begin
                    w_p0_ras_n = '0;
                    w_p0_cas_n = '0;
                    w_p0_we_n  = '1;
                end

                OP_MRS: begin
                    w_p0_ras_n = '0;
                    w_p0_cas_n = '0;
                    w_p0_we_n  = '0;
                    // bank   = MR index (MR0..MR3 for DDR2)
                    // addr   = MR data (DDR2 mode-register bits)
                    w_p0_bank  = DFI_BANK_WIDTH'(cmd_bank_i);
                    w_p0_addr  = DFI_ADDR_WIDTH'(cmd_col_i);
                end

                default: begin
                    // OP_REFPB (LPDDR2 only), OP_ZQCS/ZQCL (DDR3+),
                    // OP_SREFE/SREFX/DPDE — driven via CKE / a separate
                    // sequencer; drive NOP here.
                end
            endcase
        end else if (cmd_valid_i && memtype_i == MEMTYPE_LPDDR2) begin
            // LPDDR2 encoding (JESD209-2). CA bus is 10 bits, with each
            // command spanning 2 clock edges → 20 bits total. The LPDDR2
            // PHY does NOT use ras_n / cas_n / we_n; those stay idle (1).
            // We pack the first-edge bits in dfi_address[9:0] and the
            // second-edge bits in dfi_address[19:10]. cs_n must still be
            // active for the targeted rank.
            //
            // SKELETON: this encodes the dominant CA bits per op (cmd
            // class + bank + truncated row/col) so the framework is in
            // place and tests can exercise memtype branching. Bit-exact
            // JESD209-2 compliance — Table 35 + Table 36 — is a v3 TODO.
            w_p0_cs_n  = w_active_rank_mask;
            w_p0_ras_n = '1;   // LPDDR2 holds ras/cas/we idle
            w_p0_cas_n = '1;
            w_p0_we_n  = '1;
            w_p0_bank  = DFI_BANK_WIDTH'(cmd_bank_i);

            unique case (cmd_op_i)
                OP_NOP: w_p0_addr = '0;   // NOP encoding
                OP_ACT:
                    // ACT: CA[1:0] = 00, bank+row across both edges
                    w_p0_addr = (DFI_ADDR_WIDTH'(cmd_bank_i) << 4)
                              | (DFI_ADDR_WIDTH'(cmd_row_i)  << 10);
                OP_RD:
                    // RD:  CA[2:0] = 011, col across edges; A10/AP = 0
                    w_p0_addr = DFI_ADDR_WIDTH'(3'b011)
                              | (DFI_ADDR_WIDTH'(cmd_bank_i) << 4)
                              | (DFI_ADDR_WIDTH'(cmd_col_i)  << 10);
                OP_RDA:
                    w_p0_addr = DFI_ADDR_WIDTH'(3'b011)
                              | (DFI_ADDR_WIDTH'(cmd_bank_i) << 4)
                              | (DFI_ADDR_WIDTH'(cmd_col_i)  << 10)
                              | (DFI_ADDR_WIDTH'(1)          << 19); // AP
                OP_WR:
                    // WR:  CA[2:0] = 010
                    w_p0_addr = DFI_ADDR_WIDTH'(3'b010)
                              | (DFI_ADDR_WIDTH'(cmd_bank_i) << 4)
                              | (DFI_ADDR_WIDTH'(cmd_col_i)  << 10);
                OP_WRA:
                    w_p0_addr = DFI_ADDR_WIDTH'(3'b010)
                              | (DFI_ADDR_WIDTH'(cmd_bank_i) << 4)
                              | (DFI_ADDR_WIDTH'(cmd_col_i)  << 10)
                              | (DFI_ADDR_WIDTH'(1)          << 19); // AP
                OP_PRE:
                    // PRE: CA[3:0] = 1011, AB=0 (single bank)
                    w_p0_addr = DFI_ADDR_WIDTH'(4'b1011)
                              | (DFI_ADDR_WIDTH'(cmd_bank_i) << 4);
                OP_PREA:
                    // PRE-all: AB=1
                    w_p0_addr = DFI_ADDR_WIDTH'(4'b1011)
                              | (DFI_ADDR_WIDTH'(1) << 9);
                OP_REF:
                    // REFab: CA[3:0] = 1011 (with AB context); v3 should
                    // split out OP_REFPB → CA[3:0] = 1001 for per-bank.
                    w_p0_addr = DFI_ADDR_WIDTH'(4'b1011);
                OP_REFPB:
                    w_p0_addr = DFI_ADDR_WIDTH'(4'b1001)
                              | (DFI_ADDR_WIDTH'(cmd_bank_i) << 4);
                OP_MRS:
                    // MRW: CA[1:0]=10, then MR index in [9:2], data in
                    // second edge [17:10]. cmd_bank=MR index, cmd_col=data.
                    w_p0_addr = DFI_ADDR_WIDTH'(2'b10)
                              | (DFI_ADDR_WIDTH'(cmd_bank_i) << 2)
                              | (DFI_ADDR_WIDTH'(cmd_col_i)  << 10);
                default: w_p0_addr = '0;
            endcase
        end
    end

    //=========================================================================
    // Pack phases (next-cycle values, combinational).
    //=========================================================================
    logic [DFI_ADDR_BUS_W-1:0]  w_dfi_address;
    logic [DFI_BANK_BUS_W-1:0]  w_dfi_bank;
    logic [DFI_CTRL_BUS_W-1:0]  w_dfi_cas_n;
    logic [DFI_CTRL_BUS_W-1:0]  w_dfi_ras_n;
    logic [DFI_CTRL_BUS_W-1:0]  w_dfi_we_n;
    logic [DFI_CS_BUS_W-1:0]    w_dfi_cs_n;
    logic [DFI_CS_BUS_W-1:0]    w_dfi_odt;

    always_comb begin
        // Start with NOP default for every phase.
        w_dfi_address = '0;
        w_dfi_bank    = '0;
        w_dfi_cas_n   = '1;
        w_dfi_ras_n   = '1;
        w_dfi_we_n    = '1;
        w_dfi_cs_n    = '1;
        w_dfi_odt     = '0;

        // Phase 0 = the decoded command.
        w_dfi_address[0 +: DFI_ADDR_WIDTH] = w_p0_addr;
        w_dfi_bank   [0 +: DFI_BANK_WIDTH] = w_p0_bank;
        w_dfi_cas_n  [0 +: DFI_CTRL_WIDTH] = w_p0_cas_n;
        w_dfi_ras_n  [0 +: DFI_CTRL_WIDTH] = w_p0_ras_n;
        w_dfi_we_n   [0 +: DFI_CTRL_WIDTH] = w_p0_we_n;
        w_dfi_cs_n   [0 +: DFI_CS_WIDTH]   = w_p0_cs_n;
        w_dfi_odt    [0 +: DFI_CS_WIDTH]   = w_p0_odt;
    end

    //=========================================================================
    // Strict-flop outputs.
    //=========================================================================
    `ALWAYS_FF_RST(mc_clk, mc_rst_n, begin
        if (`RST_ASSERTED(mc_rst_n)) begin
            dfi_address_o <= '0;
            dfi_bank_o    <= '0;
            dfi_cas_n_o   <= '1;
            dfi_ras_n_o   <= '1;
            dfi_we_n_o    <= '1;
            dfi_cs_n_o    <= '1;
            dfi_odt_o     <= '0;
            cmd_ready_o   <= 1'b1;
        end else begin
            dfi_address_o <= w_dfi_address;
            dfi_bank_o    <= w_dfi_bank;
            dfi_cas_n_o   <= w_dfi_cas_n;
            dfi_ras_n_o   <= w_dfi_ras_n;
            dfi_we_n_o    <= w_dfi_we_n;
            dfi_cs_n_o    <= w_dfi_cs_n;
            dfi_odt_o     <= w_dfi_odt;
            cmd_ready_o   <= 1'b1;
        end
    end)

    wire unused_v1 = |{ cmd_len_i };

endmodule : dfi_cmd_formatter
