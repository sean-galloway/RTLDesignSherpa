// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Package: mem_char_pkg
// Purpose: The ONE type the memory-characterization framework needs that is
//          not its own. Exists so the framework never imports a controller's
//          package.
//
// It used to. char_engine_block advertised itself as "the DUT-agnostic half"
// and still carried `import pumice_pkg::*` -- vestigial in that file, but two
// siblings (harness_csr, char_engine_harness) really did take memtype_e from
// it. Two consequences, both bad: the DDR2 controller's package sat in the
// synthesis closure of a LiteDRAM build containing no pumice at all, and a
// DDR3 harness could not reuse the framework without dragging DDR2 in.
//
// Generation-neutral ON PURPOSE. The harness only ever needs one bit -- which
// of its controller's two variants it was built for -- and both families
// encode it in one bit:
//
//     MEMVARIANT_DDR   pumice -> DDR2     scoria -> DDR3
//     MEMVARIANT_LP    pumice -> LPDDR2   scoria -> LPDDR3
//
// Each controller's own package stays the authority for its encoding, and the
// cast at the controller wrapper is the single place a generation is named. Do
// not add DDR2/DDR3 members here: the moment this package knows a generation,
// it belongs to one controller again and the coupling is back.
`timescale 1ns / 1ps

package mem_char_pkg;

    typedef enum logic [0:0] {
        MEMVARIANT_DDR = 1'b0,
        MEMVARIANT_LP  = 1'b1
    } mem_variant_e;

endpackage : mem_char_pkg
