// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: gray_counter_chain
// Purpose: Gray Counter Chain for Timing Characterization
//
// Description:
//   Wraps the existing counter_bingray module from rtl/common/ to
//   characterize the combinational depth of binary-to-Gray conversion
//   at various counter widths. The binary counter itself uses dedicated
//   carry logic, but the XOR tree for Gray conversion is pure LUT fabric.
//
//   Structure per instance:
//     enable --> counter_bingray --> counter_bin[WIDTH-1:0]   --> r_out_bin
//                                --> counter_gray[WIDTH-1:0]  --> r_out_gray
//
//   Output flops capture both binary and Gray outputs for timing closure.
//   The interesting path is counter register -> XOR tree -> output flop.
//
// Parameters:
//   WIDTH - Counter width (critical path scales with XOR tree depth)
//           Valid range: 2 to 128
//
// Notes:
//   - Uses counter_bingray from rtl/common/counter_bingray.sv
//   - Gray conversion: gray = bin ^ (bin >> 1) -- WIDTH-1 XOR gates
//   - Critical path is the binary-to-Gray XOR tree
//   - Output flops preserve both binary and Gray for timing analysis
//   - Enable is always asserted for free-running characterization
//
// Documentation: projects/components/timing_characterization/README.md
// Subsystem: timing_characterization
//
// Author: sean galloway
// Created: 2026-03-17

`timescale 1ns / 1ps

`include "reset_defs.svh"

module gray_counter_chain #(
    parameter int WIDTH = 32
) (
    // Clock and Reset
    input  logic              clk,
    input  logic              rst_n,

    //=========================================================================
    // Control Interface
    //=========================================================================
    input  logic              i_enable,

    //=========================================================================
    // Output Interface
    //=========================================================================
    output logic [WIDTH-1:0]  o_counter_bin,
    output logic [WIDTH-1:0]  o_counter_gray
);

    //=========================================================================
    // Gray Counter Instance
    //=========================================================================

    logic [WIDTH-1:0] w_counter_bin;
    logic [WIDTH-1:0] w_counter_bin_next;  // unused but required by port
    logic [WIDTH-1:0] w_counter_gray;

    counter_bingray #(
        .WIDTH (WIDTH)
    ) u_counter (
        .clk              (clk),
        .rst_n            (rst_n),
        .enable           (i_enable),
        .counter_bin      (w_counter_bin),
        .counter_bin_next (w_counter_bin_next),
        .counter_gray     (w_counter_gray)
    );

    //=========================================================================
    // Output Flip-Flops
    //=========================================================================
    // Capture both binary and Gray outputs for timing characterization

    `ifdef XILINX
        (* dont_touch = "true" *)
    `elsif INTEL
        /* synthesis preserve */
    `endif
    logic [WIDTH-1:0] r_out_bin;

    `ifdef XILINX
        (* dont_touch = "true" *)
    `elsif INTEL
        /* synthesis preserve */
    `endif
    logic [WIDTH-1:0] r_out_gray;

    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            r_out_bin  <= '0;
            r_out_gray <= '0;
        end else begin
            r_out_bin  <= w_counter_bin;
            r_out_gray <= w_counter_gray;
        end
    )

    assign o_counter_bin  = r_out_bin;
    assign o_counter_gray = r_out_gray;

    //=========================================================================
    // Assertions for Verification
    //=========================================================================

    `ifdef FORMAL
    initial begin
        assert (WIDTH >= 2) else $fatal(1, "WIDTH must be >= 2");
    end
    `endif

endmodule : gray_counter_chain
