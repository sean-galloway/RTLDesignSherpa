// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: verilog_operators
// Purpose: Verilog Condensed Lrm module
//
// Documentation: rtl/common/PRD.md
// Subsystem: common
//
// Author: sean galloway
// Created: 2025-10-18

module verilog_operators // verilog_lint: waive module-filename
(
    input  logic [7:0] a, b,
    output logic [7:0] a_plus_b,
    output logic [7:0] a_minus_b,
    output logic [7:0] a_times_b,
    output logic [7:0] a_dividedby_b,
    output logic [7:0] a_modulo_b,
    output logic [7:0] a_tothepowerof_b,
    output logic       a_lessthan_b,
    output logic       a_greaterthan_b,
    output logic       a_lessthanorequal_b,
    output logic       a_greaterthanorequal_b,
    output logic       a_equalxz_b,
    output logic       a_notequalxz_b,
    output logic       a_equalu_b,
    output logic       a_notequalu_b,
    output logic       a_and_b,
    output logic       a_or_b,
    output logic       not_a,
    output logic [7:0] not_a_bitwise,
    output logic [7:0] a_or_b_bitwise,
    output logic [7:0] a_and_b_bitwise,
    output logic [7:0] a_xor_b_bitwise,
    output logic [7:0] a_nor_b_bitwise,
    output logic [7:0] a_nand_b_bitwise,
    input  logic [7:0] data,
    output logic [7:0] data_shift_rt,
    output logic [7:0] data_shift_lt
);
    // Verilog Arithmetic Operators:
    //                        Operator     Description
    assign a_plus_b  =        a + b;    // a plus b
    assign a_minus_b =        a - b;    // a minus b
    assign a_times_b =        a * b;    // a multiplied by b
    assign a_dividedby_b =    a / b;    // a divided by b
    assign a_modulo_b =       a % b;    // a modulo b
    assign a_tothepowerof_b = a ** b;   // a to the power of b

    // Verilog Relational Operators:
    //                              Operator      Description
    assign a_lessthan_b =           a < b;     // a less than b
    assign a_greaterthan_b =        a > b;     // a greater than b
    assign a_lessthanorequal_b =    a <= b;    // a less than or equal to b
    assign a_greaterthanorequal_b = a >= b;    // a greater than or equal to b

    // Verilog Equality Operators:
    //                      Operator       Description
    assign a_equalxz_b =    a === b;    // a equal to b, including x and z
    assign a_notequalxz_b = a !== b;    // a not equal to b, including x and z
    assign a_equalu_b =     a == b;     // a equal to b, result can be unknown
    assign a_notequalu_b =  a != b;     // a not equal to b, result can be unknown

    // Verilog Logical Operators:
    //               Operator      Description
    assign a_and_b = a && b;    // evaluates to true if a and b are true
    assign a_or_b =  a || b;    // evaluates to true if a or b are true
    assign not_a =  !a;         // converts non-zero value to zero, and vice versa

    // Verilog Bitwise Operators:
    //                       Operator     Type
    assign not_a_bitwise =   ~a;       // Not
    assign a_or_b_bitwise =   a | b;   // Or
    assign a_and_b_bitwise =  a & b;   // And
    assign a_xor_b_bitwise =  a ^ b;   // Xor
    assign a_nor_b_bitwise =  a ~| b;  // Nor
    assign a_nand_b_bitwise = a ~& b;  // Nane

    // Verilog Shift Operators:
    assign data_shift_rt = data >> 8; // shift right 8 times
    assign data_shift_lt = data << 4; // shift left four time

endmodule : verilog_operators

///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
// Reduction Operators
module reduction_ops  // verilog_lint: waive module-filename
(
    input  logic [3:0] sel,
    output logic       any_sel_hi,
    output logic       all_sel_hi,
    output logic       sel_parity
);
    // Reduction Operators: Generally, used in combinatorial control logic:
    assign any_sel_hi = |sel;      // Or    any_sel_hi = sel[3] | sel[2] | sel[1] | sel[0];
    assign all_sel_hi = &sel;      // And:  all_sel_hi = sel[3] & sel[2] & sel[1] & sel[0];
    assign sel_parity = ^sel;      // XOr:  sel_parity = sel[3] ^ sel[2] ^ sel[1] ^ sel[0];

    assign inv_sel_parity = ~^sel; // XNor: inv_sel_parity =  ~(sel[3] ^ sel[2] ^ sel[1] ^ sel[0]);
    assign inv_any_sel_hi = ~|sel; // Nor:  inv_any_sel_hi = ~(sel[3] | sel[2] | sel[1] | sel[0]);
    assign inv_all_sel_hi = ~&sel; // Nand: inv_all_sel_hi = ~(sel[3] & sel[2] & sel[1] & sel[0]);

endmodule : reduction_ops

///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
// Case Mux
module case_mux // verilog_lint: waive module-filename
(
    input  logic [2:0] a, b, c,
    input  logic [1:0] sel,
    output logic [2:0] out
);

    always_comb begin
        case (sel)
            2'b00:  out = a;
            2'b01:  out = b;
            2'b10:
                begin // an example of multi-lines in a case
                    out[2] = c[2];
                    out[1] = c[1];
                    out[0] = c[0];
                end
            default: out = 0;
        endcase
    end

endmodule : case_mux

///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
// Moore FSM, the commonly used type, not glitchy
module MooreFSM_4State // verilog_lint: waive module-filename
(
    input  logic clk,       // Clock input
    input  logic reset,     // Reset input
    output logic state0,    // State 0 output
    output logic state1,    // State 1 output
    output logic state2     // State 2 output
);

// Define FSM states as parameters
typedef enum logic [1:0] {
    S0 = 2'b00,
    S1 = 2'b01,
    S2 = 2'b10,
    S3 = 2'b11
} states_fsm_t;

// Define FSM state register
states_fsm_t state;

// State transition and output logic
always_ff @(posedge clk or posedge reset) begin
    if (reset) begin
        state <= S0; // Reset to initial state
    end else begin
        // Define state transitions here
        state0 <= 1'b0;
        state1 <= 1'b0;
        state2 <= 1'b0;
        case (state)
            S0: begin
                state <= S1;
                state0 <= 1'b1;
            end
            S1: begin
                state <= S2;
                state1 <= 1'b1;
            end
            S2: begin
                state <= S3;
                state2 <= 1'b1;
            end
            S3: begin
                state <= S0;
            end
            default: begin
                state <= S0; // Default to initial state
            end
        endcase
    end
end

endmodule : MooreFSM_4State

module MooreFSM_4State_OneHot (
    input  logic clk,
    input  logic reset,
    output logic state0,
    output logic state1,
    output logic state2
);

    // Define FSM states with one-hot encoding
    typedef enum logic [3:0] {
        S0 = 4'b0001,
        S1 = 4'b0010,
        S2 = 4'b0100,
        S3 = 4'b1000
    } state_t;

    // Define FSM state register
    state_t state;

    // State transition and output logic
    always_ff @(posedge clk or posedge reset) begin
        if (reset) begin
            state <= S0; // Reset to initial state
        end else begin
            state0 <= 1'b0;
            state1 <= 1'b0;
            state2 <= 1'b0;
            case (state)
                S0: begin
                    state <= S1;
                    state0 <= 1'b1;
                end
                S1: begin
                    state <= S2;
                    state1 <= 1'b1;
                end
                S2: begin
                    state <= S3;
                    state2 <= 1'b1;
                end
                S3: state <= S0;
                default: state <= S0; // Default to initial state
            endcase
        end
    end

endmodule : MooreFSM_4State_OneHot


///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
// Mealy FSM, less Common, Glitchy
module MealyFSM_4State // verilog_lint: waive module-filename
(
    input  logic clk,          // Clock input
    input  logic reset,        // Reset input
    input  logic input_signal, // Input to the FSM
    output logic state0,       // State 0 output
    output logic state1,       // State 1 output
    output logic state2        // State 2 output
);

// Define FSM states as parameters
parameter logic [1:0] S0 = 2'b00;
parameter logic [1:0] S1 = 2'b01;
parameter logic [1:0] S2 = 2'b10;
parameter logic [1:0] S3 = 2'b11;

// Define FSM state registers
logic [1:0] current_state, next_state;

// State transition logic
always @(posedge clk or posedge reset) begin
    if (reset) begin
        current_state <= S0; // Reset to initial state
    end else begin
        current_state <= next_state; // Update current state
    end
end

// Next state and output logic
always_comb begin
    state0 = 1'b0;
    state1 = 1'b0;
    state2 = 1'b0;
    case (current_state)
        S0: begin
            next_state = input_signal ? S1 : S0;
            state0 = 1'b1;
        end
        S1: begin
            next_state = input_signal ? S2 : S0;
            state1 = 1'b1;
        end
        S2: begin
            next_state = input_signal ? S3 : S0;
            state2 = 1'b1;
        end
        S3: begin
            next_state = input_signal ? S0 : S0;
        end
        default: begin
            next_state = S0;
        end
    endcase
end

endmodule

///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
// Simple Parameterized FIFO
// Childishly simple, but now with configurable depth
module SyncFIFO #(
    parameter int DEPTH = 8,
    parameter int DATA_WIDTH = 8
) (
    input  logic                  clk,
    input  logic                  reset_n,
    input  logic                  write_en,
    input  logic [DATA_WIDTH-1:0] data_in,
    input  logic                  read_en,
    output logic [DATA_WIDTH-1:0] data_out,
    output logic                  empty,
    output logic                  full
);
    localparam int PW = $clog2(DEPTH) + 1;
    
    logic [DATA_WIDTH-1:0] mem [DEPTH];
    logic [PW-1:0] wp, rp;
    
    wire do_wr = write_en && !full;
    wire do_rd = read_en  && !empty;
    
    assign empty    = (wp == rp);
    assign full     = (wp[PW-1] != rp[PW-1]) && (wp[PW-2:0] == rp[PW-2:0]);
    assign data_out = do_rd ? mem[rp[$clog2(DEPTH)-1:0]] : '0;

    always_ff @(posedge clk or negedge reset_n) begin
        if (!reset_n) begin
            wp <= '0;
            rp <= '0;
        end else begin
            wp <= wp + PW'(do_wr);
            rp <= rp + PW'(do_rd);
        end
    end

    always_ff @(posedge clk)
        if (do_wr) mem[wp[$clog2(DEPTH)-1:0]] <= data_in;

endmodule

module SyncFIFO #(
    parameter int DEPTH = 8,
    parameter int DATA_WIDTH = 8
) (
    input  logic                  clk,
    input  logic                  reset_n,
    // Write interface
    input  logic                  wr_valid,
    output logic                  wr_ready,
    input  logic [DATA_WIDTH-1:0] wr_data,
    // Read interface
    output logic                  rd_valid,
    input  logic                  rd_ready,
    output logic [DATA_WIDTH-1:0] rd_data
);
    localparam int PW = $clog2(DEPTH) + 1;
    
    logic [DATA_WIDTH-1:0] mem [DEPTH];
    logic [PW-1:0] wp, rp;
    
    wire wr_hsk = wr_valid && wr_ready;
    wire rd_hsk = rd_valid && rd_ready;
    
    assign wr_ready = (wp[PW-1] == rp[PW-1]) || (wp[PW-2:0] != rp[PW-2:0]);
    assign rd_valid = (wp != rp);
    assign rd_data  = mem[rp[$clog2(DEPTH)-1:0]];

    always_ff @(posedge clk or negedge reset_n) begin
        if (!reset_n) begin
            wp <= '0;
            rp <= '0;
        end else begin
            wp <= wp + PW'(wr_hsk);
            rp <= rp + PW'(rd_hsk);
        end
    end

    always_ff @(posedge clk)
        if (wr_hsk) mem[wp[$clog2(DEPTH)-1:0]] <= wr_data;

endmodule

// arbiter
module rr_arbiter #(N=4) (
    input  logic         clk, rst_n,
    input  logic [N-1:0] req,
    output logic [N-1:0] gnt);

    logic [N-1:0] mask;  // rotates after each grant
    logic [N-1:0] gnt_masked, gnt_unmasked;

    // Priority encoder helper (lowest set bit after mask)
    assign gnt_masked   = req & mask & ~(req & mask - 1);  // simplified
    assign gnt_unmasked = req & ~(req - 1);
    assign gnt = |gnt_masked ? gnt_masked : gnt_unmasked;

    always_ff @(posedge clk or negedge rst_n)
        if (!rst_n) mask <= '1;
        else if (|gnt) mask <= {gnt[N-2:0], gnt[N-1]}; // rotate left

endmodule : rr_arbiter
