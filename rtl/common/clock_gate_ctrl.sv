`timescale 1ns / 1ps

module clock_gate_ctrl #(
    parameter int N = 4  // Default width of idle counter
) (
    // Inputs
    input logic          clk_in,
    input logic          aresetn,
    input logic          i_cfg_cg_enable,  // Global clock gate enable
    input logic  [N-1:0] i_cfg_idle_count, // Idle countdown value
    input logic          i_wakeup,         // Signal to wake up the block

    // Outputs
    output logic         clk_out,
    output logic         o_gating          // clock gating indicator
);

    // Internal signals
    logic [N-1:0] r_idle_counter;
    logic         w_counter_active;
    logic         w_gate_enable;
    logic         w_idle_timer_done;
    logic         w_begin_clock_gating;

    // Counter is active when sleep is asserted but wakeup is not
    assign w_counter_active = ~i_wakeup;

    // Idle counter logic
    always_ff @(posedge clk_in or negedge aresetn) begin
        if (!aresetn)
            r_idle_counter <= 'h0;
        else
            if (i_wakeup || ~i_cfg_cg_enable) begin
                r_idle_counter <= i_cfg_idle_count;
            end else if (w_counter_active && r_idle_counter != 'h0) begin
                r_idle_counter <= r_idle_counter - 1'b1;
        end
    end

    // Clock gating enable logic
    // Keep clock enabled if:
    // 1. Clock gating is globally disabled (cg_enable = 0)
    // 2. Block is in wakeup state
    // 3. Counter is still running (not zero) during sleep
    assign w_idle_timer_done = (r_idle_counter == 'h0);
    assign w_begin_gating    = (i_wakeup) ? 1'b0 : w_idle_timer_done;
    assign w_gate_enable     = (~i_cfg_cg_enable) ? 1'b0 : w_begin_gating;

    // Instantiate the ICG cell
    icg u_icg (
        .clk(clk_in),
        .en(~w_gate_enable),  // Enable is active high in our logic
        .gclk(clk_out)
    );

    assign o_gating = w_gate_enable;

endmodule : clock_gate_ctrl
