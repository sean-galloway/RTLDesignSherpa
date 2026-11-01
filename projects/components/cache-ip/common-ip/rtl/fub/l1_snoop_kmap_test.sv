// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: l1_snoop_kmap_test
// Purpose:
//   Combinational decode of {line_state, snoop_type} -> {CRRESP, next_state}
//   per the amber HAS Table 3.0 MESI snoop matrix. Pure wrapper over the
//   l1_pkg functions so the logic has a module boundary the kmap
//   workbook can diff against. VALIDATION HARNESS: not instantiated in the
//   design -- l1_snoop_resp / l1_control call the same l1_pkg functions
//   inline (identical combinational cone; a module wrapper adds nothing
//   to synthesizability). The _test suffix marks that role.
//
// Documentation: projects/components/cache-ip/amber-mesi-l1/docs/amber_has/ch03_architecture/04_coherence_fsm.md
// Subsystem: amber
//
// Author: sean galloway
// Created: 2026-10-06

`timescale 1ns / 1ps

//==============================================================================
// Module: l1_snoop_kmap_test
//==============================================================================
// Description:
//   The snoop responder's response decode as a standalone leaf. The probed
//   line's current MESI state and the snoop type decide the CRRESP bits
//   (DataTransfer / PassDirty / IsShared / WasUnique; Error is always 0 in
//   v1.0) and the line's next state. In the design, l1_snoop_resp applies
//   this decode (via the same l1_pkg functions) onto the ACE CR channel and
//   l1_control applies the next state through the tag array write port.
//
//   Reserved encodings (Owned state -- MOESI headroom not implemented in
//   v1.0 -- and snoop codes 6/7, which are not IHI0022 encodings) decode to
//   the safe default: no data transfer, next state Invalid. The kmap
//   workbook marks those cells don't-care; the RTL returns 0 there.
//
// Combinational. No clock, no reset.
//
//------------------------------------------------------------------------------
// Parameters:
//------------------------------------------------------------------------------
//   None. Encodings come from l1_pkg.
//
//------------------------------------------------------------------------------
// Related Modules:
//------------------------------------------------------------------------------
//   - Instantiated by: nothing -- validation boundary only (the kmap
//     workbook and the gem5 FSM oracle diff against this module)
//   - Functions: l1_pkg.amber_snoop_crresp / amber_snoop_next_state
//
//------------------------------------------------------------------------------
// Test:
//------------------------------------------------------------------------------
//   Location: projects/components/cache-ip/common-ip/dv/tests/test_l1_snoop_kmap.py
//   Run: pytest projects/components/cache-ip/common-ip/dv/tests/test_l1_snoop_kmap.py -v
//
//==============================================================================

module l1_snoop_kmap_test
    import l1_pkg::*;
(
    input  logic [2:0]                    line_state,   // cache_state_t value
    input  logic [2:0]                    snoop_type,   // amber_snoop_t value
    output logic [AMBER_CRRESP_WIDTH-1:0] crresp,       // IHI0022 order:
                                                        // {WU[4],IS[3],PD[2],Err[1],DT[0]}
    output logic [2:0]                    next_state    // cache_state_t value
);

    always_comb begin
        crresp     = amber_snoop_crresp(line_state, snoop_type);
        next_state = amber_snoop_next_state(line_state, snoop_type);
    end

endmodule : l1_snoop_kmap_test
