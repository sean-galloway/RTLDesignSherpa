`timescale 1ns / 1ps

module pwm #(
    parameter int WIDTH = 8,  // Counter Width
    parameter int CHANNELS = 4  // Number of PWM channels
) (
    input  logic                      i_clk,
    input  logic                      i_rst_n,
    input  logic [      CHANNELS-1:0] i_start,         // Start the PWM for each channel
    input  logic [CHANNELS*WIDTH-1:0] i_duty,          // Max count for keeping PWM high per channel
    input  logic [CHANNELS*WIDTH-1:0] i_period,        // Max total count per channel
    input  logic [CHANNELS*WIDTH-1:0] i_repeat_count,  // Repeat the counter for each channel
    output logic [      CHANNELS-1:0] ow_done,
    output logic [      CHANNELS-1:0] o_pwm            // Done and the PWM signal for each channel
);

    // Loop over each channel
    genvar i;
    generate
        for (i = 0; i < CHANNELS; i++) begin : gen_channel
            localparam int EndIdx = (i + 1) * WIDTH - 1;

            logic [WIDTH-1:0] r_count;
            logic [WIDTH-1:0] r_repeat_value;
            logic w_count_met, w_counting, w_done_repeat;

            assign w_count_met = (r_count == i_period[EndIdx-:WIDTH] - 1);
            assign w_counting = (i_start[i] && !ow_done[i]);
            assign w_done_repeat = (i_repeat_count[EndIdx -: WIDTH] != 'b0) &&
                                    (r_repeat_value == i_repeat_count[EndIdx -: WIDTH]);
            assign ow_done[i] = w_done_repeat;

            // Count handling
            always_ff @(posedge i_clk or negedge i_rst_n) begin
                if (!i_rst_n) r_count <= 'b0;
                else if (w_count_met) r_count <= 'b0;
                else if (w_counting) r_count <= r_count + 1;
            end

            // Repeat counting
            always_ff @(posedge i_clk or negedge i_rst_n) begin
                if (!i_rst_n) r_repeat_value <= 'b0;
                else if (w_counting && w_count_met) r_repeat_value <= r_repeat_value + 'b1;
            end

            // PWM signal handling
            always_comb begin
                if (i_duty[EndIdx-:WIDTH] >= i_period[EndIdx-:WIDTH])
                    o_pwm[i] = 1;  // Handle 100% duty cycle
                else if (r_count < i_duty[EndIdx-:WIDTH] && !ow_done[i]) o_pwm[i] = 1;
                else o_pwm[i] = 0;
            end
        end
    endgenerate

    // Synopsys translate_off
    // Synopsys translate_on

endmodule : pwm
