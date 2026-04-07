// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// Formal wrapper for pwm (yosys-compatible)
// Instantiates DUT and properties together.
// Properties use only port-level signals (no hierarchical internal access).
// Run with: sby pwm.sby

module formal_pwm #(
    parameter int WIDTH    = 4,
    parameter int CHANNELS = 2
) (
    input logic                       clk,
    input logic                       rst_n,
    input logic                       sync_rst_n,
    input logic [CHANNELS-1:0]        start,
    input logic [CHANNELS*WIDTH-1:0]  duty,
    input logic [CHANNELS*WIDTH-1:0]  period,
    input logic [CHANNELS*WIDTH-1:0]  repeat_count
);

    // DUT outputs
    logic [CHANNELS-1:0] done;
    logic [CHANNELS-1:0] pwm_out;

    // Instantiate DUT
    pwm #(
        .WIDTH   (WIDTH),
        .CHANNELS(CHANNELS)
    ) dut (
        .clk         (clk),
        .rst_n       (rst_n),
        .sync_rst_n  (sync_rst_n),
        .start       (start),
        .duty        (duty),
        .period      (period),
        .repeat_count(repeat_count),
        .done        (done),
        .pwm_out     (pwm_out)
    );

    // =========================================================================
    // Formal infrastructure
    // =========================================================================
    reg [7:0] f_past_valid = 0;
    always @(posedge clk)
        f_past_valid <= f_past_valid + (f_past_valid < 8'hFF);

    // Assumptions: start in reset for at least 3 cycles, then release
    initial assume (!rst_n);
    always @(posedge clk) begin
        if (f_past_valid >= 3) assume (rst_n);
    end

    // Keep sync_rst_n deasserted after initial reset
    always @(posedge clk) begin
        if (f_past_valid >= 3) assume (sync_rst_n);
    end

    // Extract channel 0 parameters
    wire [WIDTH-1:0] ch0_period = period[WIDTH-1:0];
    wire [WIDTH-1:0] ch0_duty   = duty[WIDTH-1:0];
    wire [WIDTH-1:0] ch0_repeat = repeat_count[WIDTH-1:0];

    // Constrain: period > 0 for meaningful operation
    always @(*) begin
        assume (ch0_period > 0);
        assume (ch0_duty <= ch0_period);
    end

    // Keep duty/period/repeat stable after reset release
    always @(posedge clk) begin
        if (f_past_valid > 0 && rst_n && $past(rst_n)) begin
            assume (duty == $past(duty));
            assume (period == $past(period));
            assume (repeat_count == $past(repeat_count));
        end
    end

    // =========================================================================
    // Shadow FSM model for channel 0 (tracks expected state from outputs)
    // =========================================================================
    // We mirror the PWM state machine to verify output correctness
    // without accessing internal signals.

    // Track start edge for channel 0
    reg f_start_prev;
    always @(posedge clk) begin
        if (!rst_n || !sync_rst_n)
            f_start_prev <= 1'b0;
        else
            f_start_prev <= start[0];
    end
    wire f_start_edge = start[0] && !f_start_prev;

    // Shadow state for channel 0
    localparam [1:0] F_IDLE    = 2'b00;
    localparam [1:0] F_RUNNING = 2'b01;
    localparam [1:0] F_DONE    = 2'b10;

    reg [1:0]       f_state;
    reg [WIDTH-1:0] f_count;
    reg [WIDTH-1:0] f_repeat;

    wire f_period_complete = (f_count == ch0_period - 1) && (f_state == F_RUNNING);
    wire f_all_done        = (ch0_repeat == 0) ? 1'b0 : (f_repeat >= ch0_repeat);

    always @(posedge clk) begin
        if (!rst_n || !sync_rst_n) begin
            f_state  <= F_IDLE;
            f_count  <= '0;
            f_repeat <= '0;
        end else begin
            case (f_state)
                F_IDLE: begin
                    f_count <= '0;
                    f_repeat <= '0;
                    if (f_start_edge && ch0_period > 0)
                        f_state <= F_RUNNING;
                end
                F_RUNNING: begin
                    if (f_period_complete && f_all_done) begin
                        f_state <= F_DONE;
                    end
                    if (f_period_complete) begin
                        f_count  <= '0;
                        f_repeat <= f_repeat + 1;
                    end else begin
                        f_count <= f_count + 1;
                    end
                end
                F_DONE: begin
                    if (f_start_edge)  begin
                        f_state  <= F_RUNNING;
                        f_count  <= '0;
                        f_repeat <= '0;
                    end
                end
                default: begin
                    f_state <= F_IDLE;
                    f_count <= '0;
                    f_repeat <= '0;
                end
            endcase
        end
    end

    // =========================================================================
    // Safety properties
    // =========================================================================

    // After reset, pwm_out is zero
    always @(posedge clk) begin
        if (f_past_valid > 0 && $past(!rst_n))
            ap_reset_pwm: assert (pwm_out == '0);
    end

    // After reset, done is deasserted
    always @(posedge clk) begin
        if (f_past_valid > 0 && $past(!rst_n))
            ap_reset_done: assert (done == '0);
    end

    // done and pwm_out are mutually exclusive for channel 0
    // (done only in DONE state, pwm only in RUNNING state)
    always @(posedge clk) begin
        if (rst_n && f_past_valid >= 4)
            ap_done_pwm_mutex: assert (!(done[0] && pwm_out[0]));
    end

    // Shadow FSM matches DUT done output
    // After sufficient reset settling, shadow should track actual output
    always @(posedge clk) begin
        if (rst_n && f_past_valid >= 5)
            ap_done_matches_shadow: assert (done[0] == (f_state == F_DONE));
    end

    // Shadow FSM matches DUT pwm output
    always @(posedge clk) begin
        if (rst_n && f_past_valid >= 5 && f_state == F_RUNNING) begin
            if (ch0_duty == 0)
                ap_duty_zero: assert (pwm_out[0] == 1'b0);
            else if (ch0_duty >= ch0_period)
                ap_duty_full: assert (pwm_out[0] == 1'b1);
            else
                ap_duty_normal: assert (pwm_out[0] == (f_count < ch0_duty));
        end
    end

    // In shadow IDLE state, outputs should be inactive
    always @(posedge clk) begin
        if (rst_n && f_past_valid >= 5 && f_state == F_IDLE) begin
            ap_idle_no_pwm: assert (pwm_out[0] == 1'b0);
            ap_idle_no_done: assert (done[0] == 1'b0);
        end
    end

    // In shadow DONE state, pwm should be zero
    always @(posedge clk) begin
        if (rst_n && f_past_valid >= 5 && f_state == F_DONE)
            ap_done_no_pwm: assert (pwm_out[0] == 1'b0);
    end

    // =========================================================================
    // Cover properties
    // =========================================================================

    // Cover: start triggers running (pwm goes high)
    always @(posedge clk) begin
        if (f_past_valid > 0 && rst_n && $past(rst_n))
            cp_start_running: cover (pwm_out[0] && !$past(pwm_out[0]));
    end

    // Cover: running state with pwm high
    always @(posedge clk) begin
        if (rst_n)
            cp_running: cover (pwm_out[0]);
    end

    // Cover: done asserted
    always @(posedge clk) begin
        if (rst_n)
            cp_done: cover (done[0]);
    end

    // Cover: pwm_out toggles
    always @(posedge clk) begin
        if (f_past_valid > 0 && rst_n && $past(rst_n))
            cp_pwm_toggle: cover (pwm_out[0] != $past(pwm_out[0]));
    end

    // Cover: done transitions from 0 to 1
    always @(posedge clk) begin
        if (f_past_valid > 0 && rst_n && $past(rst_n))
            cp_done_assert: cover (done[0] && !$past(done[0]));
    end

endmodule
