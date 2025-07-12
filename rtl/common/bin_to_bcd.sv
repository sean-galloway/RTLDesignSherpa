`timescale 1ns / 1ps

///////////////////////////////////////////////////////////////////////////////
// File Downloaded from http://www.nandland.com
// lots and lots of fixes needed to get this clean and working
///////////////////////////////////////////////////////////////////////////////
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
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
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
    end

    assign w_bcd_digit = r_bcd[r_digit_index*4+:4];

    assign bcd = r_bcd;
    assign done = r_dv;

endmodule : bin_to_bcd