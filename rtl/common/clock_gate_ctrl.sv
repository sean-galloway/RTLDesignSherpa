module clock_gate_ctrl #(
    parameter int IDLE_CNTR_WIDTH = 4, // Default width of idle counter
    parameter int N = IDLE_CNTR_WIDTH
) (
    // Inputs
    input logic          clk_in,
    input logic          aresetn,
    input logic          i_cfg_cg_enable,     // Global clock gate enable
    input logic  [N-1:0] i_cfg_cg_idle_count, // Idle countdown value
    input logic          i_wakeup,            // Signal to wake up the block

    // Outputs
    output logic         clk_out,
    output logic         o_gating          // clock gating indicator
);

    // Internal signals
    logic [N-1:0] r_idle_counter;

    // Counter logic
    always_ff @(posedge clk_in or negedge aresetn) begin
        if (!aresetn) begin
            r_idle_counter <= i_cfg_cg_idle_count;
        end else begin
            if (i_wakeup || !i_cfg_cg_enable) begin
                // On wakeup or global disable, reset counter
                r_idle_counter <= i_cfg_cg_idle_count;
            end else if (r_idle_counter != 'h0) begin
                // Normal counting operation - decrement when not zero
                r_idle_counter <= r_idle_counter - 1'b1;
            end
            // When counter reaches zero, it stays at zero
        end
    end

    // Simple gating condition: gate when not in wakeup, globally enabled, and counter is zero
    wire w_gate_enable = i_cfg_cg_enable && !i_wakeup && (r_idle_counter == 'h0);

    // Instantiate the ICG cell
    icg u_icg (
        .clk(clk_in),
        .en(~w_gate_enable),  // Enable is active high in our logic
        .gclk(clk_out)
    );

    assign o_gating = w_gate_enable;

endmodule : clock_gate_ctrl
