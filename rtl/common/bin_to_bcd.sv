`timescale 1ns / 1ps

///////////////////////////////////////////////////////////////////////////////
// File Downloaded from http://www.nandland.com
// lots and lots of fixes needed to get this clean and working
///////////////////////////////////////////////////////////////////////////////
module bin_to_bcd #(
    parameter int WIDTH  = 8,
    parameter int DIGITS = 3
) (
    input  logic                i_clk,     // Clock signal
    input  logic                i_rst_n,   // Active-low reset signal
    input  logic                i_start,
    input  logic [   WIDTH-1:0] i_binary,
    output logic [DIGITS*4-1:0] o_bcd,
    output logic                o_done
);

    // Define the FSM states
    parameter logic [2:0] S_IDLE = 3'b000;
    parameter logic [2:0] S_SHIFT = 3'b001;
    parameter logic [2:0] S_CHECK_SHIFT_INDEX = 3'b010;
    parameter logic [2:0] S_ADD = 3'b011;
    parameter logic [2:0] S_CHECK_DIGIT_INDEX = 3'b100;
    parameter logic [2:0] S_BCD_DONE = 3'b101;

    // FSM present and next state
    logic [2:0] r_SM_Main;
    logic [2:0] w_SM_Main;

    // The vector that contains the output BCD
    logic [DIGITS*4-1:0] r_BCD, w_BCD;

    // The vector that contains the input binary value being shifted.
    logic [WIDTH-1:0] r_Binary, w_Binary;

    // Keeps track of which Decimal Digit we are indexing
    logic [$clog2(DIGITS)-1:0] r_Digit_Index, w_Digit_Index;

    // Keeps track of which loop iteration we are on.
    // Number of loops performed = MaxDigits
    localparam int MaxDigits = 16;
    logic [$clog2(MaxDigits)-1:0] r_Loop_Count, w_Loop_Count;

    logic [3:0] w_BCD_Digit;
    logic r_DV, w_DV;

    // flop all of the registers
    always_ff @(posedge i_clk or negedge i_rst_n) begin
        if (!i_rst_n) begin
            r_SM_Main <= S_IDLE;
            r_BCD <= '0;
            r_Binary <= '0;
            r_Digit_Index <= '0;
            r_Loop_Count <= '0;
            r_DV <= '0;
        end else begin
            r_SM_Main <= w_SM_Main;
            r_BCD <= w_BCD;
            r_Binary <= w_Binary;
            r_Digit_Index <= w_Digit_Index;
            r_Loop_Count <= w_Loop_Count;
            r_DV <= w_DV;
        end
    end

    // Next State for the FSM and wire versions of the various control signals
    always_comb begin

        w_SM_Main = r_SM_Main;
        w_BCD = r_BCD;
        w_Binary = r_Binary;
        w_Digit_Index = r_Digit_Index;
        w_Loop_Count = r_Loop_Count;
        w_DV = 1'b0;

        case (r_SM_Main)

            // Stay in this state until i_start comes alonglogic [2:0]
            S_IDLE: begin
                if (i_start == 1'b1) begin
                    w_Binary = i_binary;
                    w_SM_Main = S_SHIFT;
                    w_BCD = 0;
                end else w_SM_Main = S_IDLE;
            end

            // Always shift the BCD Vector until we have shifted all bits through
            // Shift the most significant bit of r_Binary into r_BCD lowest bit.
            S_SHIFT: begin
                w_BCD = r_BCD << 1;
                w_BCD[0] = r_Binary[WIDTH-1];
                w_Binary = r_Binary << 1;
                w_SM_Main = S_CHECK_SHIFT_INDEX;
            end

            // Check if we are done with shifting in r_Binary vector
            S_CHECK_SHIFT_INDEX: begin
                if (r_Loop_Count == WIDTH - 1) begin
                    w_Loop_Count = 0;
                    w_SM_Main = S_BCD_DONE;
                end else begin
                    w_Loop_Count = r_Loop_Count + 1;
                    w_SM_Main = S_ADD;
                end
            end

            // Break down each BCD Digit individually. Check them one-by-one to
            // see if they are greater than 4. If they are, increment by 3.
            // Put the result back into r_BCD Vector.
            S_ADD: begin
                if (w_BCD_Digit > 4) w_BCD[(r_Digit_Index*4)+:4] = w_BCD_Digit + 3;
                w_SM_Main = S_CHECK_DIGIT_INDEX;
            end

            // Check if we are done incrementing all of the BCD Digits
            S_CHECK_DIGIT_INDEX: begin
                if (r_Digit_Index == DIGITS - 1) begin
                    w_Digit_Index = 0;
                    w_SM_Main = S_SHIFT;
                end else begin
                    w_Digit_Index = r_Digit_Index + 1;
                    w_SM_Main = S_ADD;
                end
            end

            S_BCD_DONE: begin
                w_DV = 1'b1;
                w_SM_Main = S_IDLE;
            end

            default: w_SM_Main = S_IDLE;

        endcase
    end

    assign w_BCD_Digit = r_BCD[r_Digit_Index*4+:4];

    assign o_bcd = r_BCD;
    assign o_done = r_DV;

    // synopsys translate_off
    initial begin
        $dumpfile("dump.vcd");
        $dumpvars(0, bin_to_bcd);
    end
    // synopsys translate_on

endmodule : bin_to_bcd
