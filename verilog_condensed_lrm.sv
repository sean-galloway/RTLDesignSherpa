// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: verilog_operators
// Purpose: Verilog Condensed LRM / Common Coding Patterns Reference
//
// Documentation: rtl/common/PRD.md
// Subsystem: common
//
// Author: sean galloway
// Created: 2025-10-18

///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
// Operators: Arithmetic, Relational, Equality, Logical, Bitwise, Shift
///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
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
    assign not_a_bitwise =   ~a;        // Not
    assign a_or_b_bitwise =   a | b;    // Or
    assign a_and_b_bitwise =  a & b;    // And
    assign a_xor_b_bitwise =  a ^ b;    // Xor
    assign a_nor_b_bitwise =  ~(a | b); // Nor  (use explicit parens, ~| is a reduction op)
    assign a_nand_b_bitwise = ~(a & b); // Nand (use explicit parens, ~& is a reduction op)

    // Verilog Shift Operators:
    assign data_shift_rt = data >> 8; // shift right 8 times
    assign data_shift_lt = data << 4; // shift left four times

endmodule : verilog_operators

///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
// Reduction Operators
// Generally used in combinatorial control logic to collapse a vector to a single bit.
///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
module reduction_ops // verilog_lint: waive module-filename
(
    input  logic [3:0] sel,
    output logic       any_sel_hi,      // OR  reduction
    output logic       all_sel_hi,      // AND reduction
    output logic       sel_parity,      // XOR reduction
    output logic       inv_sel_parity,  // XNOR reduction
    output logic       inv_any_sel_hi,  // NOR  reduction
    output logic       inv_all_sel_hi   // NAND reduction
);
    assign any_sel_hi     = |sel;   // Or:   any_sel_hi    = sel[3] | sel[2] | sel[1] | sel[0]
    assign all_sel_hi     = &sel;   // And:  all_sel_hi    = sel[3] & sel[2] & sel[1] & sel[0]
    assign sel_parity     = ^sel;   // Xor:  sel_parity    = sel[3] ^ sel[2] ^ sel[1] ^ sel[0]
    assign inv_sel_parity = ~^sel;  // Xnor: inv_sel_parity = ~(sel[3] ^ sel[2] ^ sel[1] ^ sel[0])
    assign inv_any_sel_hi = ~|sel;  // Nor:  inv_any_sel_hi = ~(sel[3] | sel[2] | sel[1] | sel[0])
    assign inv_all_sel_hi = ~&sel;  // Nand: inv_all_sel_hi = ~(sel[3] & sel[2] & sel[1] & sel[0])

endmodule : reduction_ops

///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
// Case Mux
///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
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
                begin // example of multi-line case body
                    out[2] = c[2];
                    out[1] = c[1];
                    out[0] = c[0];
                end
            default: out = '0;
        endcase
    end

endmodule : case_mux

///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
// unique case / priority case
//
// unique:   tool asserts one-hot coverage; overlap = elaboration error; no match = error
// priority: first matching arm wins; overlap is legal; missing default risks a latch
///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
module case_variants (
    input  logic [1:0] sel,
    input  logic [7:0] a, b, c,
    output logic [7:0] out_unique,
    output logic [7:0] out_priority
);

    always_comb begin
        unique case (sel)          // synthesis/lint tool verifies: no overlap, full coverage
            2'b00:   out_unique = a;
            2'b01:   out_unique = b;
            2'b10:   out_unique = c;
            default: out_unique = '0;
        endcase
    end

    always_comb begin
        priority case (1'b1)       // one-hot style: first true arm wins
            sel[0]:  out_priority = a;
            sel[1]:  out_priority = b;
            default: out_priority = '0;
        endcase
    end

endmodule : case_variants

///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
// Moore FSM (binary encoding)
//
// Proper Moore pattern:
//   - always_ff  : state register (next-state logic)
//   - always_comb: output decode (outputs depend ONLY on current state, never on next_state)
// This prevents glitchy outputs and passes formal checks cleanly.
///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
module MooreFSM_4State // verilog_lint: waive module-filename
(
    input  logic clk,
    input  logic reset_n,
    output logic state0,
    output logic state1,
    output logic state2
);

    typedef enum logic [1:0] {
        S0 = 2'b00,
        S1 = 2'b01,
        S2 = 2'b10,
        S3 = 2'b11
    } states_fsm_t;

    states_fsm_t state;

    // State register
    always_ff @(posedge clk or negedge reset_n) begin
        if (!reset_n) begin
            state <= S0;
        end else begin
            case (state)
                S0:      state <= S1;
                S1:      state <= S2;
                S2:      state <= S3;
                S3:      state <= S0;
                default: state <= S0;
            endcase
        end
    end

    // Output decode — combinatorial, depends only on current state (Moore property)
    always_comb begin
        state0 = 1'b0;
        state1 = 1'b0;
        state2 = 1'b0;
        case (state)
            S0: state0 = 1'b1;
            S1: state1 = 1'b1;
            S2: state2 = 1'b1;
            S3: ;  // no output asserted in S3
            default: ;
        endcase
    end

endmodule : MooreFSM_4State

///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
// Moore FSM (one-hot encoding)
///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
module MooreFSM_4State_OneHot (
    input  logic clk,
    input  logic reset_n,
    output logic state0,
    output logic state1,
    output logic state2
);

    typedef enum logic [3:0] {
        S0 = 4'b0001,
        S1 = 4'b0010,
        S2 = 4'b0100,
        S3 = 4'b1000
    } state_t;

    state_t state;

    // State register
    always_ff @(posedge clk or negedge reset_n) begin
        if (!reset_n) begin
            state <= S0;
        end else begin
            case (state)
                S0:      state <= S1;
                S1:      state <= S2;
                S2:      state <= S3;
                S3:      state <= S0;
                default: state <= S0;
            endcase
        end
    end

    // Output decode
    always_comb begin
        state0 = (state == S0);
        state1 = (state == S1);
        state2 = (state == S2);
    end

endmodule : MooreFSM_4State_OneHot

///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
// Mealy FSM
//
// Outputs depend on BOTH current state AND input_signal.
// Two-always style: separate sequential and combinatorial blocks.
// Note: Mealy outputs can glitch when inputs change between clock edges.
///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
module MealyFSM_4State // verilog_lint: waive module-filename
(
    input  logic clk,
    input  logic reset_n,
    input  logic input_signal,
    output logic state0,
    output logic state1,
    output logic state2
);

    typedef enum logic [1:0] {
        S0 = 2'b00,
        S1 = 2'b01,
        S2 = 2'b10,
        S3 = 2'b11
    } states_fsm_t;

    states_fsm_t current_state, next_state;

    // State register
    always_ff @(posedge clk or negedge reset_n) begin
        if (!reset_n) current_state <= S0;
        else          current_state <= next_state;
    end

    // Next-state and output logic (combinatorial)
    always_comb begin
        next_state = S0;
        state0     = 1'b0;
        state1     = 1'b0;
        state2     = 1'b0;
        case (current_state)
            S0: begin
                next_state = input_signal ? S1 : S0;
                state0     = 1'b1;
            end
            S1: begin
                next_state = input_signal ? S2 : S0;
                state1     = 1'b1;
            end
            S2: begin
                next_state = input_signal ? S3 : S0;
                state2     = 1'b1;
            end
            S3: begin
                next_state = S0;
            end
            default: begin
                next_state = S0;
            end
        endcase
    end

endmodule : MealyFSM_4State

///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
// Sync FIFO — flag interface (write_en / read_en, empty / full)
///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
module SyncFIFO_Flags #(
    parameter int DEPTH      = 8,
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

endmodule : SyncFIFO_Flags

///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
// Sync FIFO — handshake interface (valid / ready)
///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
module SyncFIFO_Hsk #(
    parameter int DEPTH      = 8,
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

endmodule : SyncFIFO_Hsk

///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
// Round-Robin Arbiter
///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
module rr_arbiter #(
    parameter int N = 4
) (
    input  logic         clk,
    input  logic         rst_n,
    input  logic [N-1:0] req,
    output logic [N-1:0] gnt
);

    logic [N-1:0] mask;
    logic [N-1:0] gnt_masked, gnt_unmasked;

    // Lowest set bit within the masked window; fall back to unmasked if no masked request
    assign gnt_masked   = req & mask  & ~((req & mask)  - 1'b1);
    assign gnt_unmasked = req         & ~(req            - 1'b1);
    assign gnt          = |gnt_masked ? gnt_masked : gnt_unmasked;

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) mask <= '1;
        else if (|gnt) mask <= {gnt[N-2:0], gnt[N-1]}; // rotate left past last grant
    end

endmodule : rr_arbiter

///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
// Generate: conditional always_comb vs always_ff
//
// USE_FLOP selects at elaboration time between a registered and combinatorial path.
// Both branches share the same port signature — useful for pipeline stage templates.
///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
module gen_blocks #(
    parameter int  WIDTH    = 8,
    parameter bit  USE_FLOP = 1  // 1 = registered, 0 = combinatorial pass-through
) (
    input  logic             clk,
    input  logic             reset_n,
    input  logic [WIDTH-1:0] d,
    output logic [WIDTH-1:0] q
);

    generate
        if (USE_FLOP) begin : g_registered
            always_ff @(posedge clk or negedge reset_n) begin
                if (!reset_n) q <= '0;
                else          q <= d;
            end
        end else begin : g_combinatorial
            always_comb q = d;
        end
    endgenerate

endmodule : gen_blocks

///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
// Generate: replicate always_ff across a vector dimension
//
// Each channel gets an independent enable and its own reset-to-zero flop bank.
// The packed 2-D port style [CHANNELS-1:0][WIDTH-1:0] keeps the port list flat.
///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
module gen_ff_array #(
    parameter int CHANNELS = 4,
    parameter int WIDTH    = 8
) (
    input  logic                           clk,
    input  logic                           reset_n,
    input  logic [CHANNELS-1:0]            en,
    input  logic [CHANNELS-1:0][WIDTH-1:0] d,
    output logic [CHANNELS-1:0][WIDTH-1:0] q
);

    generate
        for (genvar i = 0; i < CHANNELS; i++) begin : g_ch
            always_ff @(posedge clk or negedge reset_n) begin
                if (!reset_n)  q[i] <= '0;
                else if (en[i]) q[i] <= d[i];
            end
        end
    endgenerate

endmodule : gen_ff_array

///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
// Generate: instantiate a parameterized sub-module N times
//
// Classic pattern for a bank of identical units (FIFO lanes, ALU lanes, channel engines).
// genvar is scope-local to the generate block.
///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
module gen_module_array #(
    parameter int NUM_LANES  = 4,
    parameter int DATA_WIDTH = 16,
    parameter int FIFO_DEPTH = 8
) (
    input  logic                                  clk,
    input  logic                                  reset_n,
    input  logic [NUM_LANES-1:0]                  wr_valid,
    output logic [NUM_LANES-1:0]                  wr_ready,
    input  logic [NUM_LANES-1:0][DATA_WIDTH-1:0]  wr_data,
    output logic [NUM_LANES-1:0]                  rd_valid,
    input  logic [NUM_LANES-1:0]                  rd_ready,
    output logic [NUM_LANES-1:0][DATA_WIDTH-1:0]  rd_data
);

    generate
        for (genvar i = 0; i < NUM_LANES; i++) begin : g_lane
            SyncFIFO_Hsk #(
                .DEPTH      (FIFO_DEPTH),
                .DATA_WIDTH (DATA_WIDTH)
            ) u_fifo (
                .clk      (clk),
                .reset_n  (reset_n),
                .wr_valid (wr_valid[i]),
                .wr_ready (wr_ready[i]),
                .wr_data  (wr_data[i]),
                .rd_valid (rd_valid[i]),
                .rd_ready (rd_ready[i]),
                .rd_data  (rd_data[i])
            );
        end
    endgenerate

endmodule : gen_module_array

///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
// Interface and modport
//
// Cleans up port lists dramatically; essential for AXI, APB, and custom buses.
// modport restricts which signals a given module can drive vs. observe.
///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
interface handshake_if #(
    parameter int DATA_WIDTH = 8
) (
    input logic clk,
    input logic reset_n
);
    logic                  valid;
    logic                  ready;
    logic [DATA_WIDTH-1:0] data;

    // Producer drives valid + data, consumer drives ready
    modport producer (
        input  clk, reset_n, ready,
        output valid, data
    );

    modport consumer (
        input  clk, reset_n, valid, data,
        output ready
    );

    // Monitor: read-only, used in assertions and coverage collectors
    modport monitor (
        input clk, reset_n, valid, ready, data
    );

endinterface : handshake_if

// Example: module consuming a handshake_if via producer modport
module hs_producer #(
    parameter int DATA_WIDTH = 8
) (
    handshake_if.producer    hs,
    input logic [DATA_WIDTH-1:0] src_data,
    input logic                  src_valid
);
    always_comb begin
        hs.valid = src_valid;
        hs.data  = src_data;
    end
endmodule : hs_producer

///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
// Packed struct
//
// Names the fields inside a logic vector; synthesizes to the same hardware as
// a plain bit-vector but is far more readable at use sites.
// Fields are packed MSB-first in declaration order.
///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
typedef struct packed {
    logic        valid;    // [31]
    logic [2:0]  opcode;   // [30:28]
    logic [11:0] addr;     // [27:16]
    logic [15:0] data;     // [15:0]
} cmd_pkt_t;               // 32 bits total

module struct_example (
    input  logic     clk,
    input  logic     reset_n,
    input  cmd_pkt_t cmd_in,
    output cmd_pkt_t cmd_out
);
    cmd_pkt_t cmd_q;

    always_ff @(posedge clk or negedge reset_n) begin
        if (!reset_n) cmd_q <= '0;
        else          cmd_q <= cmd_in;
    end

    // Field access is self-documenting vs. raw bit-slicing
    always_comb begin
        cmd_out        = cmd_q;
        cmd_out.valid  = cmd_q.valid & (cmd_q.opcode != 3'b111); // example gate
    end

endmodule : struct_example

///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
// Function and Task
//
// function : combinatorial, returns a value, synthesizable, no time advance
// task     : can consume simulation time (delays / events), not synthesizable,
//            used in testbenches and UVM sequences
///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
module func_task_demo #(
    parameter int WIDTH = 8
) (
    input  logic [WIDTH-1:0] a, b,
    output logic [WIDTH-1:0] max_val,
    output logic             parity_ok
);

    // Synthesizable function: pick the larger of two values
    function automatic logic [WIDTH-1:0] f_max (
        input logic [WIDTH-1:0] x, y
    );
        return (x > y) ? x : y;
    endfunction

    // Synthesizable function: even-parity check (1 = even parity)
    function automatic logic f_parity (
        input logic [WIDTH-1:0] vec
    );
        return ~^vec;
    endfunction

    assign max_val   = f_max(a, b);
    assign parity_ok = f_parity(a);

    // Simulation-only task: drive a single valid/ready handshake beat
    // Call from an initial or always block in a testbench
    task automatic t_send_beat (
        ref   logic             valid,
        ref   logic             ready,
        ref   logic [WIDTH-1:0] data,
        input logic [WIDTH-1:0] payload,
        input int               clk_period_ns = 10
    );
        data  = payload;
        valid = 1'b1;
        wait (ready);
        #(clk_period_ns);
        valid = 1'b0;
    endtask

endmodule : func_task_demo
