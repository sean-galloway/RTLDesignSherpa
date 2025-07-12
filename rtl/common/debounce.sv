`timescale 1ns / 1ps

module debounce #(
    parameter int N              = 4,  // Number of buttons (input signals)
    parameter int DEBOUNCE_DELAY = 4,  // Debounce delay in tick cycles
    /* verilator lint_off WIDTHTRUNC */
    parameter bit PRESSED_STATE  = 1   // State when the button is pressed (1 for NO, 0 for NC)
    /* verilator lint_on WIDTHTRUNC */
) (
    input  logic         clk,           // Clock signal
    input  logic         rst_n,         // Active low reset signal
    input  logic         long_tick,     // A ~10ms tick to delay between sampling the buttons
    input  logic [N-1:0] button_in,     // Input button signals to be debounced
    output logic [N-1:0] button_out     // Debounced output signals
);

    logic [DEBOUNCE_DELAY-1:0] r_shift_regs        [N-1:0];  // Shift registers for each button
    logic [             N-1:0] w_debounced_signals;

    // Debounce logic for each button
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            for (int i = 0; i < N; i++) begin
                r_shift_regs[i] <= {DEBOUNCE_DELAY{1'b0}};
            end
        end else if (long_tick) begin
            for (int i = 0; i < N; i++) begin
                r_shift_regs[i] <= {
                    r_shift_regs[i][DEBOUNCE_DELAY-2:0], PRESSED_STATE ? button_in[i] : ~button_in[i]
                };
            end
        end
    end

    // Generate debounced output based on shift register state
    // For both NO and NC, all 1s in shift register means button is pressed
    always_comb begin
        for (int i = 0; i < N; i++) begin
            // Output 1 when shift register shows stable pressed state (all 1s)
            // This works for both NO and NC due to the inversion in the shift logic
            w_debounced_signals[i] = &r_shift_regs[i];
        end
    end

    // Update output signals
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            button_out <= {N{1'b0}};
        end else begin
            button_out <= w_debounced_signals;
        end
    end

endmodule : debounce
