`timescale 1ns / 1ps

module debounce #(
    parameter N = 4,                // Number of buttons (input signals)
    parameter DEBOUNCE_DELAY = 3    // Debounce delay in clock cycles
) (
    input wire clk,                 // Clock signal
    input wire rst_n,               // Active low reset signal
    input wire [N-1:0] button_in,   // Input button signals to be debounced
    output wire [N-1:0] button_out  // Debounced output signals
);

    logic [DEBOUNCE_DELAY-1:0]   regs[N];
    logic [N-1:0]                flop_out;

    always_ff (posedge clk or negedge rst_n) begin
        if (!rst_n)
            for (int i = 0; i < N; i++)
                regs[i] <= {DEBOUNCE_DELAY{1'b0}};
        else
            for (int i = 0; i < N; i++)
                regs[i] <= {regs[i][DEBOUNCE_DELAY-2:0], button_in[i]};
        end

    always_comb begin
        for (int i = 0; i < N; i++)
            flop_out[i] = &regs[i][DEBOUNCE_DELAY-1:0];
        end

    always_ff (posedge clk) begin
        button_out <= flop_out;
    end

endmodule : debounce