`timescale 1ns / 1ps

module debounce #(
    parameter int N              = 4,  // Number of buttons (input signals)
    parameter int DEBOUNCE_DELAY = 4,  // Debounce delay in tick cycles
    parameter int PRESSED_STATE  = 1   // State when the button is pressed (1 for NO, 0 for NC)
) (
    input  logic         i_clk,        // Clock signal
    input  logic         i_rst_n,      // Active low reset signal
    input  logic         i_long_tick,  // A ~10ms tick to delay between sampling the buttons
    input  logic [N-1:0] i_button,     // Input button signals to be debounced
    output logic [N-1:0] o_button      // Debounced output signals
);

    logic [DEBOUNCE_DELAY-1:0] r_shift_regs        [N-1];  // Shift registers for each button
    logic [             N-1:0] w_debounced_signals;

    // Debounce logic for each button
    always_ff @(posedge i_clk or negedge i_rst_n) begin
        if (!i_rst_n) begin
            for (int i = 0; i < N; i++) begin
                r_shift_regs[i] <= {DEBOUNCE_DELAY{1'b0}};
            end
        end else if (i_long_tick) begin
            for (int i = 0; i < N; i++) begin
                r_shift_regs[i] <= {
                    r_shift_regs[i][DEBOUNCE_DELAY-2:0], PRESSED_STATE ? i_button[i] : ~i_button[i]
                };
            end
        end
    end

    // Check if the signal is stable (either all 1s or all 0s)
    always_comb begin
        for (int i = 0; i < N; i++) begin
            w_debounced_signals[i] = (&r_shift_regs[i]) | (~|r_shift_regs[i]);
        end
    end

    // Update output signals
    always_ff @(posedge i_clk or negedge i_rst_n) begin
        if (!i_rst_n) begin
            o_button <= {N{1'b0}};
        end else begin
            o_button <= w_debounced_signals;
        end
    end

endmodule : debounce
