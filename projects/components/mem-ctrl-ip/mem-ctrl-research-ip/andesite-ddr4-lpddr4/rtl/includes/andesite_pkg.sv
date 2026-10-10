// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: andesite_pkg
// Purpose: Shared types and constants for the DDR4/LPDDR4 memory controller
//
// Documentation:
//   projects/components/mem-ctrl-ip/mem-ctrl-research-ip/andesite-ddr4-lpddr4/docs/andesite_has/
//
// Derived from scoria_pkg (DDR3/LPDDR3). Per family doc 01
// (projects/components/mem-ctrl-ip/docs/01_mem_ctrl_pkg.md) this package
// takes the family memtype design as-is -- one LP axis bit plus a two-bit
// generation field -- because andesite has no legacy CSR to disturb, and it
// carries scoria's dram_op_e encoding widened one bit for OP_MPC. The
// family migration to a shared mem_ctrl_pkg is deferred to andesite RTL
// bring-up per that doc's conditions; until then the three near-identical
// family packages are deliberate and time-boxed.
//
// Author: sean galloway
// Created: 2026-10-04

`timescale 1ns / 1ps

package andesite_pkg;

    //=========================================================================
    // Memtype Enum (build-time selection)
    //=========================================================================
    // Family design, family doc 01 Table 1.0: bit [2] is the LP axis,
    // bits [1:0] are the generation field (2'b00=2, 01=3, 10=4; 2'b11 is
    // generation 5, reserved for basalt). andesite exercises DDR4/LPDDR4.
    // 3'b011 / 3'b111 stay illegal -- decode them as an error, never alias.

    typedef enum logic [2:0] {
        MEMTYPE_DDR2   = 3'b000,   // carried for the family enum; not exercised
        MEMTYPE_DDR3   = 3'b001,   // carried for the family enum; not exercised
        MEMTYPE_DDR4   = 3'b010,
        MEMTYPE_LPDDR2 = 3'b100,   // carried for the family enum; not exercised
        MEMTYPE_LPDDR3 = 3'b101,   // carried for the family enum; not exercised
        MEMTYPE_LPDDR4 = 3'b110
    } memtype_e;

    //=========================================================================
    // DRAM Command Opcodes
    //=========================================================================
    // 5-bit encoding shared between the arbiter, the command formatter, the
    // init sequencer, refresh, ZQ and the CAMs. Carried from scoria_pkg
    // unchanged (values 0-15) and widened to five bits for OP_MPC, the
    // LPDDR4 multipurpose command. The wire-level translation per memtype
    // lives in andesite_dfi_cmd_formatter; OP_MPC's CA-bus encoding is the
    // kmap book's LPDDR4 CA table (docs/kmaps/generated/).

    typedef enum logic [4:0] {
        OP_NOP    = 5'h00,
        OP_ACT    = 5'h01,
        OP_RD     = 5'h02,
        OP_RDA    = 5'h03,   // RD with auto-precharge
        OP_WR     = 5'h04,
        OP_WRA    = 5'h05,   // WR with auto-precharge
        OP_PRE    = 5'h06,
        OP_PREA   = 5'h07,   // PRE all banks
        OP_REF    = 5'h08,   // REFab (all-bank refresh)
        OP_REFPB  = 5'h09,   // REFpb (per-bank); controller-named for LPDDR4
        OP_MRS    = 5'h0A,
        OP_ZQCS   = 5'h0B,   // ZQ calibration short (periodic maintenance)
        OP_ZQCL   = 5'h0C,   // ZQ calibration long (init, and tZQoper)
        OP_SREFE  = 5'h0D,   // Self-refresh entry
        OP_SREFX  = 5'h0E,   // Self-refresh exit
        OP_DPDE   = 5'h0F,   // Deep-power-down entry (LPDDR family)
        OP_MPC    = 5'h10    // LPDDR4 multipurpose command; CA-bus encoding
                             // per the kmap book (LPDDR4 breadth track)
    } dram_op_e;

    //=========================================================================
    // Decoded Address
    //=========================================================================
    // Field order per MAS ch02 04_addr_mapper: bank group sits between chip
    // select and bank. Padded widths carried from scoria; the design point
    // (DDR4: 4 BG x 4 banks; LPDDR4: 8 banks, bg constant) fits with room.

    typedef struct packed {
        logic [3:0]  rank;    // pad to 4 bits; actual width is $clog2(NUM_RANKS)
        logic [3:0]  bg;      // bank group; DDR4 uses 2 bits, LPDDR4 constant 0
        logic [3:0]  bank;    // pad to 4 bits; DDR4 uses 2, LPDDR4 uses 3
        logic [17:0] row;     // pad to 18 bits (DDR3 forward-compat carried on)
        logic [13:0] col;     // pad to 14 bits
    } decoded_addr_t;

    //=========================================================================
    // Opcode helpers (carried from scoria_pkg)
    //=========================================================================

    function automatic logic is_column_op(dram_op_e op);
        return (op == OP_RD) || (op == OP_RDA) || (op == OP_WR) || (op == OP_WRA);
    endfunction

    function automatic logic is_read_op(dram_op_e op);
        return (op == OP_RD) || (op == OP_RDA);
    endfunction

    function automatic logic is_write_op(dram_op_e op);
        return (op == OP_WR) || (op == OP_WRA);
    endfunction

    function automatic logic is_refresh_op(dram_op_e op);
        return (op == OP_REF) || (op == OP_REFPB);
    endfunction

    function automatic logic has_auto_pre(dram_op_e op);
        return (op == OP_RDA) || (op == OP_WRA);
    endfunction

    function automatic logic is_zq_op(dram_op_e op);
        return (op == OP_ZQCS) || (op == OP_ZQCL);
    endfunction

    //=========================================================================
    // Bank State (carried from scoria_pkg -- the per-(rank,bank) bank machine
    // states the carried timers/CAMs/scheduler publish and consume)
    //=========================================================================

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
    // Page Policy (carried from scoria_pkg)
    //=========================================================================

    typedef enum logic [1:0] {
        PAGE_POLICY_OPEN  = 2'h0,
        PAGE_POLICY_CLOSE = 2'h1,
        PAGE_POLICY_RSVD  = 2'h3
    } page_policy_e;

endpackage : andesite_pkg
