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
    output logic [      CHANNELS-1:0] pwm            // Done and the PWM signal for each channel
);

    // Loop over each channel
    genvar i;
    generate
        for (i = 0; i < CHANNELS; i++) begin : gen_channel
            localparam int EndIdx = (i + 1) * WIDTH - 1;

            logic [WIDTH-1:0] r_count;
            logic [WIDTH-1:0] r_repeat_value;
            logic w_count_met, w_counting, w_done_repeat;

            assign w_count_met = (r_count == period[EndIdx-:WIDTH] - 1);
            assign w_counting = (start[i] && !done[i]);
            assign w_done_repeat = (repeat_count[EndIdx -: WIDTH] != 'b0) &&
                                    (r_repeat_value == repeat_count[EndIdx -: WIDTH]);
            assign done[i] = w_done_repeat;

            // Count handling
            always_ff @(posedge clk or negedge rst_n) begin
                if (!rst_n) r_count <= 'b0;
                else if (w_count_met) r_count <= 'b0;
                else if (w_counting) r_count <= r_count + 1;
            end

            // Repeat counting
            always_ff @(posedge clk or negedge rst_n) begin
                if (!rst_n) r_repeat_value <= 'b0;
                else if (w_counting && w_count_met) r_repeat_value <= r_repeat_value + 'b1;
            end

            // PWM signal handling
            always_comb begin
                if (duty[EndIdx-:WIDTH] >= period[EndIdx-:WIDTH])
                    pwm[i] = 1;  // Handle 100% duty cycle
                else if (r_count < duty[EndIdx-:WIDTH] && !done[i]) pwm[i] = 1;
                else pwm[i] = 0;
            end
        end
    endgenerate

    // Synopsys translate_off
    // Synopsys translate_on

endmodule : pwm
