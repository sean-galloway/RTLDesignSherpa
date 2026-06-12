// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: math_adder_carry_save
// Purpose: Math Adder Carry Save module
//
// Documentation: rtl/common/PRD.md
// Subsystem: common
//
// Author: sean galloway
// Created: 2025-10-18

`timescale 1ns / 1ps

// Carry Save Adder
module math_adder_carry_save (
    input  logic i_a,
    input  logic i_b,
    input  logic i_c,
    output logic ow_sum,
    output logic ow_carry
);

    assign ow_sum   = i_a ^ i_b ^ i_c;  // XOR gate for sum output
    assign ow_carry = i_a & i_b | i_a & i_c | i_b & i_c;  // OR gate for carry output

endmodule : math_adder_carry_save
