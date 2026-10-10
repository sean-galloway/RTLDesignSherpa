// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: mc_common_pkg
// Purpose: Family-shared types for the memory-controller research IPs
//          (pumice DDR2/LPDDR2, scoria DDR3/LPDDR3, andesite DDR4/LPDDR4)
//
// Documentation:
//   projects/components/mem-ctrl-ip/common-ip/docs/01_mem_ctrl_pkg.md
//     (family doc 01 — owns the memtype encoding design, Table 1.0)
//   projects/components/mem-ctrl-ip/common-ip/docs/mc_common_pkg_knobs.md
//     (Phase 2 knob inventory: what moved, what stayed, legacy-CSR ruling)
//
// Extracted 2026-10-10 in the mem-ctrl-ip research/common/product reorg
// (docs/superpowers/specs/2026-10-09-mem-ctrl-ip-reorg-design.md, Phase 2).
// The three rock packages carried near-identical definitions; this package
// is the single source. Enum encodings are the FAMILY encodings: memtype_e
// per doc 01 (LP axis bit + two-bit generation field), dram_op_e widened to
// 5 bits so OP_MPC exists once (values 5'h00..5'h0F are identical to the
// legacy 4-bit tables in all three rocks — verified table-by-table).
//
// Legacy CSR note: the rocks' PHY_TIMING.memtype CSR field keeps its
// per-rock 1-bit values for Phase 2 (see knobs doc, "legacy CSR values").
// Each rock maps to the family enum at its single hwif cast site.

`timescale 1ns / 1ps

package mc_common_pkg;

    //=========================================================================
    // Memtype Enum (build-time selection, family doc 01 Table 1.0)
    //=========================================================================
    // Bit [2] is the LP axis; bits [1:0] are the generation field
    // (2'b00=gen2, 2'b01=gen3, 2'b10=gen4; 2'b11 is generation 5, reserved
    // for basalt). 3'b011 / 3'b111 stay illegal -- decode them as an error,
    // never alias.

    typedef enum logic [2:0] {
        MEMTYPE_DDR2   = 3'b000,
        MEMTYPE_DDR3   = 3'b001,
        MEMTYPE_DDR4   = 3'b010,
        MEMTYPE_LPDDR2 = 3'b100,
        MEMTYPE_LPDDR3 = 3'b101,
        MEMTYPE_LPDDR4 = 3'b110
    } memtype_e;

    //=========================================================================
    // DRAM Command Opcodes (family encoding)
    //=========================================================================
    // 5-bit encoding shared between the scheduler/arbiter, the DFI command
    // formatter, the init sequencer, refresh, ZQ, training and the CAMs.
    // The wire-level translation per memtype lives in each rock's DFI
    // command formatter. Values 5'h00..5'h0F match every rock's legacy
    // 4-bit table exactly; OP_MPC is the LPDDR4 addition.

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
        OP_REFPB  = 5'h09,   // REFpb (per-bank); controller-named for LP parts
        OP_MRS    = 5'h0A,   // MR0..MRn per generation
        OP_ZQCS   = 5'h0B,   // ZQ calibration short (periodic maintenance)
        OP_ZQCL   = 5'h0C,   // ZQ calibration long (init, and tZQoper)
        OP_SREFE  = 5'h0D,   // Self-refresh entry
        OP_SREFX  = 5'h0E,   // Self-refresh exit
        OP_DPDE   = 5'h0F,   // Deep-power-down entry (LPDDR family)
        OP_MPC    = 5'h10    // LPDDR4 multipurpose command; CA-bus encoding
                             // per the andesite kmap book
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
    // 2'h2 was PAGE_POLICY_HAPPY_HYBRID in pumice -- retired 2026-08-25 (the
    // HAPPY predictor was never wired into the rearchitected core; its
    // successors live in the rock page-policy FUBs behind policy_mode).

    typedef enum logic [1:0] {
        PAGE_POLICY_OPEN  = 2'h0,
        PAGE_POLICY_CLOSE = 2'h1,
        PAGE_POLICY_RSVD  = 2'h3
    } page_policy_e;

    //=========================================================================
    // Per-(rank,bank) Decoded Address Tuple
    //=========================================================================
    // Output of each rock's addr_mapper, consumed by the CAMs. Padded, not
    // sized to the part (18-bit rows cover the DDR3 design point with
    // headroom; 14-bit cols likewise).

    typedef struct packed {
        logic [3:0]  rank;    // pad to 4 bits; actual width is $clog2(NUM_RANKS)
        logic [3:0]  bank;    // pad to 4 bits; DDR3 is 8 banks -> 3 used
        logic [17:0] row;     // pad to 18 bits; MT41J256M16 uses 15
        logic [13:0] col;     // pad to 14 bits; MT41J256M16 uses 10
    } decoded_addr_t;

    //=========================================================================
    // Helpers
    //=========================================================================
    // Each return is ONE LINE, deliberately: a multi-line return expression
    // breaks yosys' frontend (the reason pumice's formal flow historically
    // had to sv2v-flatten wrappers that imported its package).

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

endpackage : mc_common_pkg
