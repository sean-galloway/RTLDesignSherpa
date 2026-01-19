// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: pwm
// Purpose: //   Multi-channel Pulse Width Modulation (PWM) generator with independent control
//
// Documentation: rtl/common/PRD.md
// Subsystem: common
//
// Author: sean galloway
// Created: 2025-10-18

`timescale 1ns / 1ps

//==============================================================================
// Module: pwm
//==============================================================================
// Description:
//   Multi-channel Pulse Width Modulation (PWM) generator with independent control
//   per channel. Each channel has configurable duty cycle, period, and repeat count
//   with start/done handshake. Uses state machine per channel for lifecycle management
//   (IDLE → RUNNING → DONE). Supports 0% and 100% duty cycle edge cases, continuous
//   mode (repeat=0), and finite repeat counts. Generate-based instantiation of N
//   independent PWM channels.
//
// Features:
//   - Multi-channel (1 to 16+ channels)
//   - Independent duty, period, repeat per channel
//   - Start/done handshake per channel
//   - Continuous or finite repeat modes
//   - 0% and 100% duty cycle support
//   - Synchronous and asynchronous reset
//   - State machine-based control
//
//------------------------------------------------------------------------------
// Parameters:
//------------------------------------------------------------------------------
//   WIDTH:
//     Description: Counter bit width (resolution)
//     Type: int
//     Range: 4 to 16
//     Default: 8
//     Constraints: Determines max period (2^WIDTH - 1)
//                  For WIDTH=8: max period = 255 clocks
//                  For WIDTH=16: max period = 65535 clocks
//
//   CHANNELS:
//     Description: Number of independent PWM channels
//     Type: int
//     Range: 1 to 16
//     Default: 4
//     Constraints: duty/period/repeat are CHANNELS*WIDTH wide
//                  Area scales linearly with CHANNELS
//
//------------------------------------------------------------------------------
// Ports:
//------------------------------------------------------------------------------
//   Inputs:
//     clk:                           Clock input
//     rst_n:                         Asynchronous active-low reset
//     sync_rst_n:                    Synchronous active-low reset
//     start[CHANNELS-1:0]:           Start PWM for each channel (edge triggered)
//     duty[CHANNELS*WIDTH-1:0]:      Duty cycle count (packed per channel)
//     period[CHANNELS*WIDTH-1:0]:    Period count (packed per channel)
//     repeat_count[CHANNELS*WIDTH-1:0]: Repeat count (packed per channel)
//
//   Outputs:
//     done[CHANNELS-1:0]:            Done flag per channel (high when complete)
//     pwm_out[CHANNELS-1:0]:         PWM output signals
//
//------------------------------------------------------------------------------
// Timing:
//------------------------------------------------------------------------------
//   Latency:        1 cycle from start to first PWM assertion
//   Period:         Configurable per channel (1 to 2^WIDTH - 1 clocks)
//   Duty Cycle:     Configurable per channel (0 to period clocks)
//   Reset:          Asynchronous + synchronous (returns to IDLE)
//   Start:          Edge-triggered (rising edge detection)
//
//------------------------------------------------------------------------------
// Behavior:
//------------------------------------------------------------------------------
//   Per-Channel State Machine:
//   - IDLE:    Waiting for start edge, outputs inactive
//   - RUNNING: Generating PWM pulses, counting periods
//   - DONE:    All repeats complete, done=1, waiting for restart
//
//   Duty Cycle Calculation:
//   - pwm_out = (count < duty) during RUNNING state
//   - 0% duty: pwm_out always 0 (duty=0)
//   - 100% duty: pwm_out always 1 (duty >= period)
//   - Normal: pwm_out high for first 'duty' clocks of each period
//
//   Period Counter:
//   - Counts from 0 to (period - 1) during RUNNING state
//   - Wraps to 0 when reaching period
//   - Increments repeat counter on each wrap
//
//   Repeat Counter:
//   - Counts completed periods
//   - repeat_count=0: Continuous mode (never done)
//   - repeat_count>0: Stops after 'repeat_count' periods
//
//   Start Edge Detection:
//   - Detects rising edge of start signal
//   - Starts new PWM sequence from IDLE or DONE state
//   - Resets counters on start
//
//   State Transitions:
//   IDLE → RUNNING:  Start edge detected AND period > 0
//   RUNNING → DONE:  Period complete AND repeat count reached
//   DONE → RUNNING:  Start edge detected (restart)
//
//   Example Waveform (WIDTH=8, duty=50, period=100, repeat=2):
//   Clock:    |‾|_|‾|_|‾|_|‾|_|‾|_|...|‾|_|‾|_|‾|_|‾|_|
//   start:    __|‾‾|_____________________________
//   count:    0 1 2...49 50...99 0 1...49 50...99 0
//   pwm_out:  ____|‾‾‾‾‾‾‾‾‾‾‾‾‾‾|___|‾‾‾‾‾‾‾‾‾‾|___
//   repeat:   0               1               2
//   done:     ________________________________________|‾‾
//
//   Duty Cycle Edge Cases:
//   - duty=0:          pwm_out always 0 (0% duty)
//   - duty=period:     pwm_out always 1 (100% duty)
//   - duty=1:          pwm_out high for 1 clock per period
//   - duty>=period:    Treated as 100% duty cycle
//
//   Continuous Mode (repeat_count=0):
//   - Never transitions to DONE state
//   - Runs indefinitely until reset or stopped
//   - done signal never asserts
//
//   Packed Parameter Format:
//   duty[CHANNELS*WIDTH-1:0] contains all channel duty values:
//     duty[WIDTH-1:0]         = Channel 0 duty
//     duty[2*WIDTH-1:WIDTH]   = Channel 1 duty
//     duty[3*WIDTH-1:2*WIDTH] = Channel 2 duty
//     ... and so on
//
//------------------------------------------------------------------------------
// Usage Example:
//------------------------------------------------------------------------------
//   // 4-channel PWM with 8-bit resolution
//   localparam int PWM_WIDTH = 8;
//   localparam int NUM_CHANNELS = 4;
//
//   logic clk, rst_n, sync_rst_n;
//   logic [NUM_CHANNELS-1:0] pwm_start, pwm_done, pwm_output;
//   logic [NUM_CHANNELS*PWM_WIDTH-1:0] pwm_duty, pwm_period, pwm_repeats;
//
//   pwm #(
//       .WIDTH(PWM_WIDTH),
//       .CHANNELS(NUM_CHANNELS)
//   ) u_pwm (
//       .clk        (clk),
//       .rst_n      (rst_n),
//       .sync_rst_n (sync_rst_n),
//       .start      (pwm_start),
//       .duty       (pwm_duty),
//       .period     (pwm_period),
//       .repeat_count(pwm_repeats),
//       .done       (pwm_done),
//       .pwm_out    (pwm_output)
//   );
//
//   // Configure channel 0: 25% duty, period=100, continuous
//   assign pwm_duty[7:0]         = 8'd25;     // 25 clocks high
//   assign pwm_period[7:0]       = 8'd100;    // 100 clock period
//   assign pwm_repeats[7:0]      = 8'd0;      // Continuous mode
//
//   // Configure channel 1: 50% duty, period=200, repeat 10 times
//   assign pwm_duty[15:8]        = 8'd100;
//   assign pwm_period[15:8]      = 8'd200;
//   assign pwm_repeats[15:8]     = 8'd10;
//
//   // Configure channel 2: 75% duty, period=80, single shot
//   assign pwm_duty[23:16]       = 8'd60;
//   assign pwm_period[23:16]     = 8'd80;
//   assign pwm_repeats[23:16]    = 8'd1;      // Run once
//
//   // Configure channel 3: 100% duty, period=50, repeat 5 times
//   assign pwm_duty[31:24]       = 8'd50;     // duty=period → 100%
//   assign pwm_period[31:24]     = 8'd50;
//   assign pwm_repeats[31:24]    = 8'd5;
//
//   // Start all channels
//   always_ff @(posedge clk) begin
//       if (!rst_n) begin
//           pwm_start <= 4'b0000;
//       end else begin
//           pwm_start <= 4'b1111;  // Pulse high to start all
//       end
//   end
//
//   // Motor control example (single channel)
//   logic [7:0] motor_speed;  // 0-255
//   assign pwm_duty[7:0]    = motor_speed;
//   assign pwm_period[7:0]  = 8'd255;
//   assign pwm_repeats[7:0] = 8'd0;  // Continuous
//   // motor_speed=0   → 0% duty (stopped)
//   // motor_speed=128 → 50% duty (half speed)
//   // motor_speed=255 → 100% duty (full speed)
//
//   // LED dimming example
//   logic [7:0] brightness;
//   assign pwm_duty[15:8]    = brightness;
//   assign pwm_period[15:8]  = 8'd100;
//   assign pwm_repeats[15:8] = 8'd0;  // Continuous
//
//------------------------------------------------------------------------------
// Notes:
//------------------------------------------------------------------------------
//   - **Multi-channel:** Each channel is independent (separate state machine)
//   - Generate-based implementation (one FSM per channel)
//   - **Start edge detection:** Uses registered start signal to detect rising edge
//   - Start is edge-sensitive (not level-sensitive)
//   - **Dual reset:** Both asynchronous (rst_n) and synchronous (sync_rst_n)
//   - All states return to IDLE on reset
//   - **Repeat count 0:** Special case for continuous/infinite operation
//   - repeat_count > 0: Finite operation, transitions to DONE
//   - **Duty cycle range:** 0 to period (inclusive)
//   - duty=0: Always low (0% duty cycle)
//   - duty>=period: Always high (100% duty cycle)
//   - **PWM frequency:** fclk / period (per channel)
//   - Resolution: WIDTH bits (2^WIDTH possible duty values)
//   - **Area:** Linear scaling with CHANNELS (each channel has FSM + 3 counters)
//   - Typical use: WIDTH=8-16, CHANNELS=1-8
//   - **Packed inputs:** duty/period/repeat are concatenated vectors
//   - Extract per-channel: duty[EndIdx-:WIDTH] syntax
//   - Output pwm_out[i] is combinational (from r_count comparison)
//   - **Done signal:** Asserted when in DONE state, cleared on restart
//   - Use done to chain operations or trigger interrupts
//   - **Period=0 handling:** Prevents transition to RUNNING (stays IDLE)
//   - Period must be >0 for operation
//   - **Applications:** Motor control, LED dimming, servo control, audio DAC
//
//------------------------------------------------------------------------------
// Test:
//------------------------------------------------------------------------------
//   Location: val/common/test_pwm.py
//   Run: pytest val/common/test_pwm.py -v
//   Coverage: 95%
//   Key Test Scenarios:
//     - Basic PWM generation with various duty cycles
//     - 0% and 100% duty cycle edge cases
//     - Repeat count functionality (finite and continuous)
//     - Multi-channel independence
//     - Start/done handshake
//     - Reset behavior (async and sync)
//     - Period and duty parameter variations
//
//==============================================================================

`include "reset_defs.svh"
module pwm #(
    parameter int WIDTH = 8,  // Counter Width
    parameter int CHANNELS = 4  // Number of PWM channels
) (
    input  logic                      clk,
    input  logic                      rst_n,
    input  logic                      sync_rst_n,     // Synchronous reset
    input  logic [      CHANNELS-1:0] start,         // Start the PWM for each channel
    input  logic [CHANNELS*WIDTH-1:0] duty,          // Max count for keeping PWM high per channel
    input  logic [CHANNELS*WIDTH-1:0] period,        // Max total count per channel
    input  logic [CHANNELS*WIDTH-1:0] repeat_count,  // Repeat the counter for each channel
    output logic [      CHANNELS-1:0] done,
    output logic [      CHANNELS-1:0] pwm_out        // Done and the PWM signal for each channel
);

    // State machine states
    typedef enum logic [1:0] {
        IDLE = 2'b00,
        RUNNING = 2'b01,
        DONE = 2'b10
    } state_t;

    // Loop over each channel
    genvar i;
    generate
        for (i = 0; i < CHANNELS; i++) begin : gen_channel
            localparam int EndIdx = (i + 1) * WIDTH - 1;

            state_t           r_state;
            logic [WIDTH-1:0] r_count;
            logic [WIDTH-1:0] r_repeat_value;
            logic [WIDTH-1:0] local_duty;
            logic [WIDTH-1:0] local_period;
            logic [WIDTH-1:0] local_repeat;

            // Extract per-channel parameters
            assign local_duty = duty[EndIdx-:WIDTH];
            assign local_period = period[EndIdx-:WIDTH];
            assign local_repeat = repeat_count[EndIdx-:WIDTH];

            // Internal control signals
            logic w_period_complete;
            logic w_all_repeats_done;
            logic w_start_edge;
            logic r_start_prev;

            // Edge detection for start signal
            `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
                    r_start_prev <= 1'b0;
                end else if (!sync_rst_n) begin
                    r_start_prev <= 1'b0;
                end else begin
                    r_start_prev <= start[i];
                end
            )

            assign w_start_edge = start[i] && !r_start_prev;

            // Period completion detection
            assign w_period_complete = (r_count == local_period - 1) && (r_state == RUNNING);

            // All repeats done detection
            assign w_all_repeats_done = (local_repeat == 0) ? 1'b0 :  // 0 means infinite/continuous
                                        (r_repeat_value >= local_repeat);

            // State machine
            `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
                    r_state <= IDLE;
                end else if (!sync_rst_n) begin
                    r_state <= IDLE;
                end else begin
                    case (r_state)
                        IDLE: begin
                            if (w_start_edge && local_period > 0) begin
                                r_state <= RUNNING;
                            end
                        end

                        RUNNING: begin
                            if (w_period_complete && w_all_repeats_done) begin
                                r_state <= DONE;
                            end
                        end

                        DONE: begin
                            if (w_start_edge) begin
                                r_state <= RUNNING;
                            end
                        end

                        // verilator coverage_off
                        // DEFENSIVE: Illegal FSM state recovery
                        default: r_state <= IDLE;
                        // verilator coverage_on
                    endcase
                end
            )


            // Counter logic
            `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
                    r_count <= '0;
                end else if (!sync_rst_n) begin
                    r_count <= '0;
                end else begin
                    case (r_state)
                        IDLE: begin
                            r_count <= '0;
                        end

                        RUNNING: begin
                            if (w_period_complete) begin
                                r_count <= '0;
                            end else begin
                                r_count <= r_count + 1;
                            end
                        end

                        DONE: begin
                            if (w_start_edge) begin
                                r_count <= '0;
                            end
                        end

                        // verilator coverage_off
                        // DEFENSIVE: Illegal FSM state recovery
                        default: r_count <= '0;
                        // verilator coverage_on
                    endcase
                end
            )


            // Repeat counter logic
            `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
                    r_repeat_value <= '0;
                end else if (!sync_rst_n) begin
                    r_repeat_value <= '0;
                end else begin
                    case (r_state)
                        IDLE: begin
                            r_repeat_value <= '0;
                        end

                        RUNNING: begin
                            if (w_period_complete) begin
                                r_repeat_value <= r_repeat_value + 1;
                            end
                        end

                        DONE: begin
                            if (w_start_edge) begin
                                r_repeat_value <= '0;
                            end
                        end

                        // verilator coverage_off
                        // DEFENSIVE: Illegal FSM state recovery
                        default: r_repeat_value <= '0;
                        // verilator coverage_on
                    endcase
                end
            )


            // PWM output logic
            always_comb begin
                case (r_state)
                    RUNNING: begin
                        if (local_duty == 0) begin
                            // 0% duty cycle
                            pwm_out[i] = 1'b0;
                        end else if (local_duty >= local_period) begin
                            // 100% duty cycle (duty >= period)
                            pwm_out[i] = 1'b1;
                        end else begin
                            // Normal case: PWM high for first 'duty' cycles
                            pwm_out[i] = (r_count < local_duty);
                        end
                    end

                    default: begin
                        pwm_out[i] = 1'b0;
                    end
                endcase
            end

            // Done output
            assign done[i] = (r_state == DONE);

        end
    endgenerate

endmodule : pwm
