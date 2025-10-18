// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: reverse_vector
// Purpose: Reverse Vector module
//
// Documentation: rtl/common/PRD.md
// Subsystem: common
//
// Author: sean galloway
// Created: 2025-10-18

`timescale 1ns / 1ps

module reverse_vector #(
    parameter int WIDTH = 32
) (
    input        [WIDTH-1:0] vector_in,
    output logic [WIDTH-1:0] vector_rev
);

    always_comb begin
        for (integer i = 0; i < WIDTH; i++) begin
            vector_rev[(WIDTH-1)-i] = vector_in[i];
        end
    end

endmodule : reverse_vector
