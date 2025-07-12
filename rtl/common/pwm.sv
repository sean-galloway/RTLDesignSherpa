`timescale 1ns / 1ps

module pwm #(
    parameter int WIDTH = 8,  // Counter Width
    parameter int CHANNELS = 4  // Number of PWM channels
) (
    input  logic                      clk,
    input  logic                      rst_n,
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
            always_ff @(posedge clk or negedge rst_n) begin
                if (!rst_n) r_start_prev <= 1'b0;
                else r_start_prev <= start[i];
            end
            assign w_start_edge = start[i] && !r_start_prev;

            // Period completion detection
            assign w_period_complete = (r_count == local_period - 1) && (r_state == RUNNING);

            // All repeats done detection
            assign w_all_repeats_done = (local_repeat == 0) ? 1'b0 :  // 0 means infinite/continuous
                                        (r_repeat_value >= local_repeat);

            // State machine
            always_ff @(posedge clk or negedge rst_n) begin
                if (!rst_n) begin
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

                        default: r_state <= IDLE;
                    endcase
                end
            end

            // Counter logic
            always_ff @(posedge clk or negedge rst_n) begin
                if (!rst_n) begin
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

                        default: r_count <= '0;
                    endcase
                end
            end

            // Repeat counter logic
            always_ff @(posedge clk or negedge rst_n) begin
                if (!rst_n) begin
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

                        default: r_repeat_value <= '0;
                    endcase
                end
            end

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
