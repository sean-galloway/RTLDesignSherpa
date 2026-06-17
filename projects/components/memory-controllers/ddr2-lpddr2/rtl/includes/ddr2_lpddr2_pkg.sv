// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: ddr2_lpddr2_pkg
// Purpose: Shared types and constants for the DDR2/LPDDR2 memory controller
//
// Documentation:
//   projects/components/memory-controllers/ddr2-lpddr2/docs/ddr2_lpddr2_has/
//   projects/components/memory-controllers/ddr2-lpddr2/docs/ddr2_lpddr2_mas/
//
// Author: sean galloway
// Created: 2026-06-17

`timescale 1ns / 1ps

package ddr2_lpddr2_pkg;

    //=========================================================================
    // Memtype Enum (build-time selection)
    //=========================================================================

    typedef enum logic [0:0] {
        MEMTYPE_DDR2   = 1'b0,
        MEMTYPE_LPDDR2 = 1'b1
    } memtype_e;

    //=========================================================================
    // DRAM Command Opcodes
    //=========================================================================
    // 4-bit encoding shared between scheduler, cmd_encoder, init_engine,
    // refresh_mgr, power_state, and the CAMs. See MAS §2.14 for the
    // wire-level translation per memtype.

    typedef enum logic [3:0] {
        OP_NOP    = 4'h0,
        OP_ACT    = 4'h1,
        OP_RD     = 4'h2,
        OP_RDA    = 4'h3,   // RD with auto-precharge
        OP_WR     = 4'h4,
        OP_WRA    = 4'h5,   // WR with auto-precharge
        OP_PRE    = 4'h6,
        OP_PREA   = 4'h7,   // PRE all banks
        OP_REF    = 4'h8,   // REFab (all-bank refresh)
        OP_REFPB  = 4'h9,   // REFpb (per-bank, LPDDR2 only)
        OP_MRS    = 4'hA,
        OP_ZQCS   = 4'hB,
        OP_ZQCL   = 4'hC,
        OP_SREFE  = 4'hD,   // Self-refresh entry
        OP_SREFX  = 4'hE,   // Self-refresh exit
        OP_DPDE   = 4'hF    // Deep-power-down entry (LPDDR2 only)
    } dram_op_e;

    //=========================================================================
    // Bank-Machine State
    //=========================================================================
    // See HAS §3.3 / MAS §2.9.

    typedef enum logic [2:0] {
        BANK_IDLE        = 3'h0,
        BANK_ACTIVATING  = 3'h1,
        BANK_ACTIVE      = 3'h2,
        BANK_RD_BUSY     = 3'h3,
        BANK_WR_BUSY     = 3'h4,
        BANK_PRECHARGING = 3'h5,
        BANK_REFRESHING  = 3'h6
    } bank_state_e;

    //=========================================================================
    // Address-Map Scheme
    //=========================================================================
    // See HAS §3.1 / MAS §2.3.

    typedef enum logic [1:0] {
        ADDR_MAP_ROW_MAJOR       = 2'h0,
        ADDR_MAP_BANK_INTERLEAVE = 2'h1,
        ADDR_MAP_XOR_HASH        = 2'h2,
        ADDR_MAP_RSVD            = 2'h3
    } addr_map_scheme_e;

    //=========================================================================
    // Page Policy
    //=========================================================================

    typedef enum logic [1:0] {
        PAGE_POLICY_OPEN         = 2'h0,
        PAGE_POLICY_CLOSE        = 2'h1,
        PAGE_POLICY_HAPPY_HYBRID = 2'h2,
        PAGE_POLICY_RSVD         = 2'h3
    } page_policy_e;

    //=========================================================================
    // ODT Rule (multi-rank)
    //=========================================================================
    // See HAS §3.6 / MAS §2.16.

    typedef enum logic [1:0] {
        ODT_RULE_DEFAULT      = 2'h0,   // Use build-time default
        ODT_RULE_JEDEC_DDR2   = 2'h1,
        ODT_RULE_JEDEC_LPDDR2 = 2'h2,
        ODT_RULE_OFF          = 2'h3    // Forced when NUM_RANKS == 1
    } odt_rule_e;

    //=========================================================================
    // Per-(rank,bank) Decoded Address Tuple
    //=========================================================================
    // Output of addr_mapper, consumed by the CAMs.

    typedef struct packed {
        logic [3:0] rank;     // pad to 4 bits; actual width is $clog2(NUM_RANKS)
        logic [3:0] bank;     // pad to 4 bits; actual width is $clog2(NUM_BANKS)
        logic [17:0] row;     // pad for up to 18-bit rows (DDR3 forward-compat)
        logic [13:0] col;     // pad for up to 14-bit cols
    } decoded_addr_t;

    //=========================================================================
    // Helpers
    //=========================================================================

    function automatic logic is_column_op (input dram_op_e op);
        return (op == OP_RD)  || (op == OP_RDA)
            || (op == OP_WR)  || (op == OP_WRA);
    endfunction

    function automatic logic is_write_op (input dram_op_e op);
        return (op == OP_WR) || (op == OP_WRA);
    endfunction

    function automatic logic is_read_op (input dram_op_e op);
        return (op == OP_RD) || (op == OP_RDA);
    endfunction

    function automatic logic is_refresh_op (input dram_op_e op);
        return (op == OP_REF) || (op == OP_REFPB);
    endfunction

    function automatic logic has_auto_pre (input dram_op_e op);
        return (op == OP_RDA) || (op == OP_WRA);
    endfunction

endpackage : ddr2_lpddr2_pkg
