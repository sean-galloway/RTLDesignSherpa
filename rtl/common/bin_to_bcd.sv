// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: bin_to_bcd
// Purpose: //   Binary to Binary Coded Decimal (BCD) converter using shift-and-add-3
//
// Documentation: rtl/common/PRD.md
// Subsystem: common
//
// Author: sean galloway
// Created: 2025-10-18

`timescale 1ns / 1ps

//==============================================================================
// Module: bin_to_bcd
//==============================================================================
// Description:
//   Binary to Binary Coded Decimal (BCD) converter using shift-and-add-3
//   algorithm (Double Dabble). Converts binary input to multi-digit BCD output
//   over multiple clock cycles using a state machine. Each BCD digit represents
//   0-9 in 4 bits. Commonly used for decimal display interfaces.
//
//   Original source: http://www.nandland.com (with fixes applied)
//
//------------------------------------------------------------------------------
// Parameters:
//------------------------------------------------------------------------------
//   WIDTH:
//     Description: Binary input width in bits
//     Type: int
//     Range: 1 to 32
//     Default: 8
//     Constraints: Determines conversion time (WIDTH clock cycles)
//
//   Derived Parameters (localparam - computed automatically):
//     DIGIT_INDEX_WIDTH: Width of digit counter ($clog2(DIGITS))
//
//------------------------------------------------------------------------------
// Notes:
//------------------------------------------------------------------------------
//   - Multi-cycle operation: Conversion takes WIDTH + overhead clock cycles
//   - Start pulse initiates conversion, done pulse indicates completion
//   - Uses FSM with states: IDLE, SHIFT, CK_S_IDX, ADD, CK_D_IDX, BCD_DONE
//   - Algorithm: Shift left, add 3 to any BCD digit >= 5, repeat WIDTH times
//   - Each BCD digit occupies 4 bits (nibble), supports 0-9 range
//
//------------------------------------------------------------------------------
// Related Modules:
//------------------------------------------------------------------------------
//   - hex_to_7seg.sv - 7-segment display encoder
//
//------------------------------------------------------------------------------
// Test:
//------------------------------------------------------------------------------
//   Location: val/common/test_bin_to_bcd.py
//   Run: pytest val/common/test_bin_to_bcd.py -v
//
//==============================================================================
///////////////////////////////////////////////////////////////////////////////
// File Downloaded from http://www.nandland.com
// lots and lots of fixes needed to get this clean and working
///////////////////////////////////////////////////////////////////////////////

`include "reset_defs.svh"
module bin_to_bcd #(
    parameter int WIDTH  = 8,
    parameter int DIGITS = 3
) (
    input  logic                clk,     // Clock signal
    input  logic                rst_n,   // Active-low reset signal
    input  logic                start,
    input  logic [   WIDTH-1:0] binary,
    output logic [DIGITS*4-1:0] bcd,
    output logic                done
);

    typedef enum logic [5:0] {
        IDLE     = 6'b000001,
        SHIFT    = 6'b000010,
        CK_S_IDX = 6'b000100,
        ADD      = 6'b001000,
        CK_D_IDX = 6'b010000,
        BCD_DONE = 6'b100000
    } fsm_state_t;

    fsm_state_t r_fsm_main;

    // The vector that contains the output BCD
    logic [DIGITS*4-1:0] r_bcd;

    // The vector that contains the input binary value being shifted.
    logic [WIDTH-1:0] r_binary;

    // Keeps track of which Decimal Digit we are indexing
    localparam int DIGIT_INDEX_WIDTH = $clog2(DIGITS);
    logic [DIGIT_INDEX_WIDTH-1:0] r_digit_index;

    // Keeps track of which loop iteration we are on.
    // Number of loops performed = WIDTH
    localparam int LOOP_COUNT_WIDTH = $clog2(WIDTH + 1);
    logic [LOOP_COUNT_WIDTH-1:0] r_loop_count;

    logic [3:0] w_bcd_digit;
    logic       r_dv;

    // flop all of the registers
    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            r_fsm_main    <= IDLE;
            r_bcd         <= '0;
            r_binary      <= '0;
            r_digit_index <= '0;
            r_loop_count  <= '0;
            r_dv          <= '0;
        end else begin
            r_dv <= 1'b0;  // Default: done is low

            // Next State for the FSM and wire versions of the various control signal
            casez (r_fsm_main)
                // Stay in this state until start comes along
                IDLE: begin
                    if (start == 1'b1) begin
                        r_binary      <= binary;
                        r_fsm_main    <= SHIFT;
                        r_bcd         <= '0;
                        r_loop_count  <= '0;
                        r_digit_index <= '0;
                    end else begin
                        r_fsm_main <= IDLE;
                    end
                end

                // Always shift the BCD Vector until we have shifted all bits through
                // Shift the most significant bit of r_binary into r_bcd lowest bit.
                SHIFT: begin
                    r_bcd      <= r_bcd << 1;
                    r_bcd[0]   <= r_binary[WIDTH-1];
                    r_binary   <= r_binary << 1;
                    r_fsm_main <= CK_S_IDX;
                end

                // Check if we are done with shifting in r_binary vector
                CK_S_IDX: begin
                    if (r_loop_count == LOOP_COUNT_WIDTH'(WIDTH - 1)) begin
                        r_loop_count <= '0;
                        r_fsm_main   <= BCD_DONE;
                    end else begin
                        r_loop_count <= r_loop_count + 1'b1;
                        r_digit_index <= '0;  // Reset digit index for ADD phase
                        r_fsm_main   <= ADD;
                    end
                end

                // Break down each BCD Digit individually. Check them one-by-one to
                // see if they are greater than 4. If they are, increment by 3.
                // Put the result back into r_bcd Vector.
                ADD: begin
                    if (w_bcd_digit > 4'd4) begin
                        r_bcd[(r_digit_index*4)+:4] <= w_bcd_digit + 4'd3;
                    end
                    r_fsm_main <= CK_D_IDX;
                end

                // Check if we are done incrementing all of the BCD Digits
                CK_D_IDX: begin
                    if (r_digit_index == DIGIT_INDEX_WIDTH'(DIGITS - 1)) begin
                        r_digit_index <= '0;
                        r_fsm_main    <= SHIFT;
                    end else begin
                        r_digit_index <= r_digit_index + 1'b1;
                        r_fsm_main    <= ADD;
                    end
                end

                BCD_DONE: begin
                    r_dv       <= 1'b1;
                    r_fsm_main <= IDLE;
                end

                default: begin
                    r_fsm_main <= IDLE;
                end
            endcase
        end
    )


    assign w_bcd_digit = r_bcd[r_digit_index*4+:4];

    assign bcd = r_bcd;
    assign done = r_dv;

endmodule : bin_to_bcd
