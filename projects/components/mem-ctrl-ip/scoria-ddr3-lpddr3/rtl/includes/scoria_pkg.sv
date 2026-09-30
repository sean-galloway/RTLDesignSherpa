// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: scoria_pkg
// Purpose: Shared types and constants for the DDR3/LPDDR3 memory controller
//
// Documentation:
//   projects/components/mem-ctrl-ip/scoria-ddr3-lpddr3/docs/scoria_has/
//
// Derived from pumice_pkg (DDR2/LPDDR2). Per HAS decision D3 this is a
// SEPARATE package rather than an extension of pumice's: pumice's memtype_e
// is one bit wide and already spent on {DDR2, LPDDR2}, and widening it would
// change a CSR in a measured, shipping design for a controller that had no
// RTL. A shared mem_ctrl_pkg with a two-bit memtype becomes worth the
// migration when the DDR4/LPDDR4 controller starts, and both move together.
//
// Author: sean galloway
// Created: 2026-09-30

`timescale 1ns / 1ps

package scoria_pkg;

    //=========================================================================
    // Memtype Enum (build-time selection)
    //=========================================================================

    typedef enum logic [0:0] {
        MEMTYPE_DDR3   = 1'b0,
        MEMTYPE_LPDDR3 = 1'b1
    } memtype_e;

    //=========================================================================
    // DRAM Command Opcodes
    //=========================================================================
    // 4-bit encoding shared between the arbiter, the DFI command formatter,
    // the init sequencer, refresh, ZQ and the CAMs. The wire-level translation
    // per memtype lives in scoria_dfi_cmd_formatter.
    //
    // Carried over from pumice unchanged, and it already covers DDR3: ZQCS,
    // ZQCL, PREA, SREFE and SREFX were defined there before any DDR3 RTL
    // existed. Only their wire encoding differs, which is the formatter's job.

    typedef enum logic [3:0] {
        OP_NOP    = 4'h0,
        OP_ACT    = 4'h1,
        OP_RD     = 4'h2,
        OP_RDA    = 4'h3,   // RD with auto-precharge
        OP_WR     = 4'h4,
        OP_WRA    = 4'h5,   // WR with auto-precharge
        OP_PRE    = 4'h6,
        OP_PREA   = 4'h7,   // PRE all banks; DDR3 gives this its own encoding
        OP_REF    = 4'h8,   // REFab (all-bank refresh)
        OP_REFPB  = 4'h9,   // REFpb (per-bank); LPDDR3 only -- DDR3 adds no
                            // controller-directed per-bank refresh
        OP_MRS    = 4'hA,   // DDR3: MR0..MR3
        OP_ZQCS   = 4'hB,   // ZQ calibration short (periodic maintenance)
        OP_ZQCL   = 4'hC,   // ZQ calibration long (init, and tZQoper)
        OP_SREFE  = 4'hD,   // Self-refresh entry
        OP_SREFX  = 4'hE,   // Self-refresh exit
        OP_DPDE   = 4'hF    // Deep-power-down entry; LPDDR3 only
    } dram_op_e;

    //=========================================================================
    // Bank-Machine State
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
    // Page Policy
    //=========================================================================

    typedef enum logic [1:0] {
        PAGE_POLICY_OPEN  = 2'h0,
        PAGE_POLICY_CLOSE = 2'h1,
        PAGE_POLICY_RSVD  = 2'h3
    } page_policy_e;

    //=========================================================================
    // Per-(rank,bank) Decoded Address Tuple
    //=========================================================================
    // Output of scoria_addr_mapper, consumed by the CAMs. Padded, not sized to the
    // part: the target design point (MT41J256M16, HAS Ch 2.4) needs 15 row
    // bits and 10 column bits, so both fields have headroom. pumice already
    // padded row to 18 "DDR3 forward-compat" -- written ahead of use, and it
    // fits.

    typedef struct packed {
        logic [3:0]  rank;    // pad to 4 bits; actual width is $clog2(NUM_RANKS)
        logic [3:0]  bank;    // pad to 4 bits; DDR3 is 8 banks -> 3 used
        logic [17:0] row;     // pad to 18 bits; MT41J256M16 uses 15
        logic [13:0] col;     // pad to 14 bits; MT41J256M16 uses 10
    } decoded_addr_t;

    //=========================================================================
    // Helpers
    //=========================================================================
    // Each return is ONE LINE, deliberately. pumice_pkg writes is_column_op's
    // return across two lines, and yosys' frontend cannot parse that -- which
    // is why the pumice formal flow must pre-flatten every wrapper through
    // sv2v before proving anything. Keeping these single-line costs nothing
    // and may let scoria's formal area read the package directly.

    function automatic logic is_column_op (input dram_op_e op);
        return (op == OP_RD) || (op == OP_RDA) || (op == OP_WR) || (op == OP_WRA);
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

    function automatic logic is_zq_op (input dram_op_e op);
        return (op == OP_ZQCS) || (op == OP_ZQCL);
    endfunction

endpackage : scoria_pkg
