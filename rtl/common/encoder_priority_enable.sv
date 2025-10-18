// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: encoder_priority_enable
// Purpose: Encoder Priority Enable module
//
// Documentation: rtl/common/PRD.md
// Subsystem: common
//
// Author: sean galloway
// Created: 2025-10-18

`timescale 1ns / 1ps

module encoder_priority_enable #(
    parameter int WIDTH = 8
) (
    input  logic [        WIDTH-1:0] priority_in,
    input  logic                     enable,
    output logic [$clog2(WIDTH)-1:0] encode
);

    logic found;

    always_comb begin
        // Default assignments to prevent latches
        encode = '0;
        found = 1'b0;

        if (enable == 1'b1) begin
            // Find the highest priority bit using found flag to prevent overwrites
            for (int i = WIDTH-1; i >= 0; i--) begin
                if (priority_in[i] == 1'b1 && !found) begin
                    encode = $clog2(WIDTH)'(i);
                    found = 1'b1;
                end
            end
        end
    end

endmodule : encoder_priority_enable
