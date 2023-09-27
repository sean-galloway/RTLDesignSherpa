`timescale 1ns / 1ps

module debounce #(
    parameter int N              = 4,  // Number of buttons (input signals)
    parameter int DEBOUNCE_DELAY = 3   // Debounce delay in clock cycles
) (
    input  logic         i_clk,     // Clock signal
    input  logic         i_rst_n,   // Active low reset signal
    input  logic [N-1:0] i_button,  // Input button signals to be debounced
    output logic [N-1:0] o_button   // Debounced output signals
);

    logic [DEBOUNCE_DELAY-1:0] r_regs     [N];
    logic [             N-1:0] w_flop_out;

    // Flop the button(s) coming in
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) for (int i = 0; i < N; i++) r_regs[i] <= {DEBOUNCE_DELAY{1'b0}};
        else for (int i = 0; i < N; i++) r_regs[i] <= {r_regs[i][DEBOUNCE_DELAY-2:0], i_button[i]};
    end

    // AND the signals together
    always_comb begin
        for (int i = 0; i < N; i++) w_flop_out[i] = &r_regs[i][DEBOUNCE_DELAY-1:0];
    end

    // Final flop stage
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) o_button <= 'b0;
        else o_button <= w_flop_out;
    end

endmodule : debounce
