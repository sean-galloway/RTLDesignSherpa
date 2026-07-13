// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2026 sean galloway
//
// Module: dfi_cmd_formatter
// Purpose: Translate the scheduler's chosen `dram_op_e` plus
//          (rank, bank, row, col) into the DFI v2.1 control bus signals
//          per JEDEC truth table for DDR2, and the bit-exact JESD209-2F
//          Table 60 CA-bus encoding for LPDDR2 (memtype_i selects).
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
// LPDDR2 (memtype_i == MEMTYPE_LPDDR2): the command + scrambled address ride
//   a 10-bit CA bus over two edges, packed as a flat 20-bit word on dfi_address
//   (bit i = CA{i} rising, bit 10+i = CA{i} falling); RAS/CAS/WE held idle, cs_n
//   asserted on phase 0. Bit-exact per JESD209-2F Table 60 — see the w_lpddr2_ca
//   block below and rtl/LPDDR2_CA_ENCODING.md (the shared source of truth with the
//   DV BFM's lpddr_ca.py).

`timescale 1ns / 1ps

`include "reset_defs.svh"

module dfi_cmd_formatter
    import pumice_pkg::*;
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
    parameter int BKW = $clog2(NUM_BANKS),
    parameter int PHW = (DFI_RATE > 1) ? $clog2(DFI_RATE) : 1
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

    // ----- runtime DFI command-phase placement (CSR-driven) -----
    // Which DFI sub-phase carries the READ vs WRITE command, to match the PHY's
    // rdphase/wrphase contract (a7ddrphy DDR2/CL3/nphases=2: rdphase=1,
    // wrphase=0). All other commands stay on phase 0. Defaults preserve the
    // legacy "everything on phase 0" behavior when both are 0.
    input  logic [PHW-1:0]                rd_phase_i,
    input  logic [PHW-1:0]                wr_phase_i,

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
                    // bank = MR index (MR0..MR3 for DDR2)
                    // addr = MR data (DDR2 mode-register bits A[12:0]) — carried
                    // on cmd_row_i (ROW_WIDTH), NOT cmd_col_i: MR0=0x532 needs
                    // bit-10 (tWR[1]) and COL_WIDTH (10) would truncate it.
                    w_p0_bank  = DFI_BANK_WIDTH'(cmd_bank_i);
                    w_p0_addr  = DFI_ADDR_WIDTH'(cmd_row_i);
                end

                default: begin
                    // OP_REFPB (LPDDR2 only), OP_ZQCS/ZQCL (DDR3+),
                    // OP_SREFE/SREFX/DPDE — driven via CKE / a separate
                    // sequencer; drive NOP here.
                end
            endcase
        end
        // LPDDR2 does NOT use the per-phase w_p0_* path: its command + scrambled
        // address ride the multiplexed 10-bit CA bus (2 edges = 20 bits) carried
        // flat on dfi_address, with ras/cas/we held idle. That word is built
        // bit-exact (JESD209-2F Table 60) in w_lpddr2_ca below and placed by the
        // memtype branch in the phase-pack stage. w_p0_* stays at NOP defaults.
    end

    //=========================================================================
    // LPDDR2 CA-bus command word (bit-exact JESD209-2F Table 60).
    // See rtl/LPDDR2_CA_ENCODING.md — the SAME layout the DV BFM encodes against
    // (CocoTBFramework .../dfi/lpddr_ca.py). Flat 20-bit word:
    //   w_lpddr2_ca[i]      = CA{i} rising  edge (i = 0..9)
    //   w_lpddr2_ca[10 + i] = CA{i} falling edge (i = 0..9)
    //=========================================================================
    logic [9:0]  w_ca_r, w_ca_f;   // rising / falling CA0..CA9
    logic [19:0] w_lpddr2_ca;
    logic        w_ca_ap;

    // Zero-extend so pins for wider geometries (R14, C10, C11) read 0 cleanly.
    logic [14:0] w_row15;          // R0..R14
    logic [11:0] w_col12;          // C0..C11 (C0 implied 0, never transmitted)
    logic [7:0]  w_mr_ma, w_mr_op; // MRW: MA[7:0] (index), OP[7:0] (data)
    assign w_row15 = 15'(cmd_row_i);
    assign w_col12 = 12'(cmd_col_i);
    // MRW field packing: the scheduler carries {MR index, MR data} in the ROW
    // field so the full LPDDR2 MR range (MR0..MR63 = MA[5:0]) is reachable
    // without a 3-bit bank port. row[13:8] = MA[5:0] (index), row[7:0] = OP[7:0]
    // (data). MA[7:6] are 0 (MR<=63). See rtl/LPDDR2_CA_ENCODING.md §4.
    assign w_mr_ma = {2'b0, w_row15[13:8]};
    assign w_mr_op = w_row15[7:0];

    assign w_ca_ap = (cmd_op_i == OP_RDA) || (cmd_op_i == OP_WRA);

    always_comb begin
        w_ca_r = '0;
        w_ca_f = '0;
        unique case (cmd_op_i)
            OP_ACT: begin
                // opcode CA0r=0, CA1r=1 ; bank -> CA7r..CA9r
                w_ca_r[1] = 1'b1;
                w_ca_r[7] = cmd_bank_i[0]; w_ca_r[8] = cmd_bank_i[1]; w_ca_r[9] = cmd_bank_i[2];
                // row hi R8..R12 -> CA2r..CA6r
                w_ca_r[2] = w_row15[8]; w_ca_r[3] = w_row15[9];  w_ca_r[4] = w_row15[10];
                w_ca_r[5] = w_row15[11]; w_ca_r[6] = w_row15[12];
                // row lo R0..R7 -> CA0f..CA7f ; R13 -> CA8f ; R14 -> CA9f
                w_ca_f[0] = w_row15[0]; w_ca_f[1] = w_row15[1]; w_ca_f[2] = w_row15[2];
                w_ca_f[3] = w_row15[3]; w_ca_f[4] = w_row15[4]; w_ca_f[5] = w_row15[5];
                w_ca_f[6] = w_row15[6]; w_ca_f[7] = w_row15[7];
                w_ca_f[8] = w_row15[13]; w_ca_f[9] = w_row15[14];
            end
            OP_RD, OP_RDA, OP_WR, OP_WRA: begin
                // opcode CA0r=1, CA1r=0, CA2r = 1(read)/0(write)
                w_ca_r[0] = 1'b1;
                w_ca_r[2] = (cmd_op_i == OP_RD) || (cmd_op_i == OP_RDA);
                w_ca_r[7] = cmd_bank_i[0]; w_ca_r[8] = cmd_bank_i[1]; w_ca_r[9] = cmd_bank_i[2];
                // C1,C2 -> CA5r,CA6r (C0 implied 0)
                w_ca_r[5] = w_col12[1]; w_ca_r[6] = w_col12[2];
                // AP -> CA0f ; C3..C11 -> CA1f..CA9f
                w_ca_f[0] = w_ca_ap;
                w_ca_f[1] = w_col12[3]; w_ca_f[2] = w_col12[4]; w_ca_f[3] = w_col12[5];
                w_ca_f[4] = w_col12[6]; w_ca_f[5] = w_col12[7]; w_ca_f[6] = w_col12[8];
                w_ca_f[7] = w_col12[9]; w_ca_f[8] = w_col12[10]; w_ca_f[9] = w_col12[11];
            end
            OP_PRE: begin
                // opcode CA0r=1, CA1r=1, CA2r=0, CA3r=1 ; AB=0 ; bank -> CA7r..CA9r
                w_ca_r[0] = 1'b1; w_ca_r[1] = 1'b1; w_ca_r[3] = 1'b1;
                w_ca_r[7] = cmd_bank_i[0]; w_ca_r[8] = cmd_bank_i[1]; w_ca_r[9] = cmd_bank_i[2];
            end
            OP_PREA: begin
                // AB=1 (CA4r); bank don't-care
                w_ca_r[0] = 1'b1; w_ca_r[1] = 1'b1; w_ca_r[3] = 1'b1; w_ca_r[4] = 1'b1;
            end
            OP_REF: begin
                // all-bank refresh: CA0r=0, CA1r=0, CA2r=1, CA3r=1
                w_ca_r[2] = 1'b1; w_ca_r[3] = 1'b1;
            end
            OP_REFPB: begin
                // per-bank refresh: CA0r=0, CA1r=0, CA2r=1, CA3r=0
                w_ca_r[2] = 1'b1;
            end
            OP_MRS: begin
                // MRW: MA0..MA5 -> CA4r..CA9r ; MA6,MA7 -> CA0f,CA1f ; OP0..OP7 -> CA2f..CA9f
                // NOTE: init carries MR index on the 3-bit bank port, so only
                // MR0..MR7 are expressible today. Full LPDDR2 MR range (MR10/63…)
                // needs a wider init MR-index path — see TASK-LPDDR2-INIT.
                w_ca_r[4] = w_mr_ma[0]; w_ca_r[5] = w_mr_ma[1]; w_ca_r[6] = w_mr_ma[2];
                w_ca_r[7] = w_mr_ma[3]; w_ca_r[8] = w_mr_ma[4]; w_ca_r[9] = w_mr_ma[5];
                w_ca_f[0] = w_mr_ma[6]; w_ca_f[1] = w_mr_ma[7];
                w_ca_f[2] = w_mr_op[0]; w_ca_f[3] = w_mr_op[1]; w_ca_f[4] = w_mr_op[2];
                w_ca_f[5] = w_mr_op[3]; w_ca_f[6] = w_mr_op[4]; w_ca_f[7] = w_mr_op[5];
                w_ca_f[8] = w_mr_op[6]; w_ca_f[9] = w_mr_op[7];
            end
            default: begin
                // OP_NOP / anything else: CA0r=CA1r=CA2r=CA3r=H (NOP/Deselect)
                w_ca_r[0] = 1'b1; w_ca_r[1] = 1'b1; w_ca_r[2] = 1'b1; w_ca_r[3] = 1'b1;
            end
        endcase
    end

    assign w_lpddr2_ca = {w_ca_f, w_ca_r};

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

    // Target phase for the decoded command: READ on rd_phase, WRITE on
    // wr_phase, everything else on phase 0. This aligns the R/W command with
    // the a7ddrphy rdphase/wrphase so the returned/launched burst lands in the
    // expected DFI cycle. Non-R/W commands (ACT/PRE/REF/MRS) have no data-phase
    // contract, so phase 0 is fine and preserves legacy behavior.
    logic [PHW-1:0] w_cmd_phase;
    always_comb begin
        unique case (cmd_op_i)
            OP_RD, OP_RDA: w_cmd_phase = rd_phase_i;
            OP_WR, OP_WRA: w_cmd_phase = wr_phase_i;
            default:       w_cmd_phase = '0;
        endcase
    end

    always_comb begin
        // Start with NOP default for every phase.
        w_dfi_address = '0;
        w_dfi_bank    = '0;
        w_dfi_cas_n   = '1;
        w_dfi_ras_n   = '1;
        w_dfi_we_n    = '1;
        w_dfi_cs_n    = '1;
        w_dfi_odt     = '0;

        if (memtype_i == MEMTYPE_LPDDR2) begin
            // LPDDR2: the whole 20-bit CA word rides dfi_address (low bits);
            // ras/cas/we stay idle; cs_n asserted for the target rank on phase 0
            // (the two CA edges are already inside the word, so there is no
            // per-DFI-phase command placement). Requires DFI_ADDR_BUS_W >= 20.
            w_dfi_address[19:0] = w_lpddr2_ca;
            if (cmd_valid_i && cmd_op_i != OP_NOP)
                w_dfi_cs_n[0 +: DFI_CS_WIDTH] = w_active_rank_mask;
        end else begin
            // DDR2: place the decoded command on its target phase (rd/wr-phase
            // aware); the other phases stay NOP.
            w_dfi_address[w_cmd_phase*DFI_ADDR_WIDTH +: DFI_ADDR_WIDTH] = w_p0_addr;
            w_dfi_bank   [w_cmd_phase*DFI_BANK_WIDTH +: DFI_BANK_WIDTH] = w_p0_bank;
            w_dfi_cas_n  [w_cmd_phase*DFI_CTRL_WIDTH +: DFI_CTRL_WIDTH] = w_p0_cas_n;
            w_dfi_ras_n  [w_cmd_phase*DFI_CTRL_WIDTH +: DFI_CTRL_WIDTH] = w_p0_ras_n;
            w_dfi_we_n   [w_cmd_phase*DFI_CTRL_WIDTH +: DFI_CTRL_WIDTH] = w_p0_we_n;
            w_dfi_cs_n   [w_cmd_phase*DFI_CS_WIDTH   +: DFI_CS_WIDTH]   = w_p0_cs_n;
            w_dfi_odt    [w_cmd_phase*DFI_CS_WIDTH   +: DFI_CS_WIDTH]   = w_p0_odt;
        end
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
