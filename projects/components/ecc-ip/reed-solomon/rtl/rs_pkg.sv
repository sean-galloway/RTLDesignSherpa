// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Package: rs_pkg
// Purpose:
//   Elaboration-time rules about a Reed-Solomon codeword's BEAT LAYOUT, as
//   opposed to its arithmetic. gf_pkg owns the field; this owns the framing.
//   Kept apart deliberately -- gf_pkg is clean GF(2^m) and has no business
//   knowing how a codeword is cut into beats.
//
// Documentation: projects/components/ecc-ip/reed-solomon/docs/rs_fub_catalog.md
// Subsystem: reed-solomon
//
// Author: sean galloway
// Created: 2026-10-01

`timescale 1ns / 1ps

package rs_pkg;

    // Does this profile need rs_beat_packer in the encoder's output path?
    //
    // THE RULE. rs_encoder_core finishes its data phase and starts parity on a
    // FRESH beat, so when k is not a whole number of beats its output carries
    // a partial beat MID-codeword. rs_decoder_core's input contract is the
    // opposite: in_keep may be partial only on a block's LAST beat, and given
    // one earlier it flags the block mis-framed and passes it through
    // UNCORRECTED. So at k % S != 0 the encoder's own output is undecodable by
    // the decoder, and rs_beat_packer has to close the gap.
    //
    // A trailing partial beat is fine and needs no packer: it IS the last
    // beat, which is exactly what the contract allows. That is why the test is
    // k % S and not n % S.
    //
    // WHY THE FRESH PARITY BEAT IS NOT NEGOTIABLE, since the obvious reaction
    // is to fix the encoder instead and delete the packer: parity is the LFSR
    // remainder over ALL k message symbols, and the final partial data beat's
    // symbols are absorbed on the same edge that beat is accepted. The
    // codeword's parity does not exist until the next cycle -- gf_lfsr_encoder
    // reads registered state for exactly that reason. Emitting parity in that
    // beat would mean driving the output from the next-state chain, which is S
    // serially chained GF multiply-accumulate stages, and putting all of it in
    // series with the output mux. It buys no cycles (both paths are already at
    // line rate) and costs the encoder's critical path. The packer stays.
    //
    // ONE DEFINITION ON PURPOSE. Both encoder wrappers used to compute this
    // inline, and a rule written twice is a rule that drifts: a duplicated
    // expected-value in this same design cost a 42-minute cosim to catch once.
    function automatic bit rs_need_pack(input int k_symbols,
                                        input int symbols_per_beat);
        return (k_symbols % symbols_per_beat) != 0;
    endfunction

endpackage : rs_pkg
