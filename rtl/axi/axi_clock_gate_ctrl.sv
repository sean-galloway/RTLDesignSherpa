`timescale 1ns / 1ps

module axi_clock_gate_ctrl #(
    parameter int N = 4             // Default width of idle counter
) (
    // Clock and Reset
    input  logic                    clk_in,
    input  logic                    aresetn,

    // Configuration Interface
    input  logic                    i_cfg_cg_enable,     // Global clock gate enable
    input  logic [N-1:0]            i_cfg_cg_idle_count,    // Idle countdown value

    // Activity Monitoring
    input  logic                    i_user_valid,        // Any user-side valid signal
    input  logic                    i_axi_valid,         // Any AXI-side valid signal

    // Clock Gating Control Outputs
    output logic                    clk_out,             // Gated clock
    output logic                    o_gating,            // Active gating indicator
    output logic                    o_idle               // All buffers empty indicator
);

    // Internal signals
    logic r_wakeup;

    // Combine activity signals
    // flop the wakeup signal
    always_ff @(posedge clk_in or negedge aresetn) begin
        if (!aresetn)
            r_wakeup <= 'h1;
        else
            r_wakeup <= i_user_valid || i_axi_valid;
    end

    // Generate idle signal when no activity
    assign o_idle = ~r_wakeup;

    // Instantiate the base clock gate control
    clock_gate_ctrl #(
        .N(N)
    ) u_clock_gate_ctrl (
        .clk_in              (clk_in),
        .aresetn             (aresetn),
        .i_cfg_cg_enable     (i_cfg_cg_enable),
        .i_cfg_cg_idle_count (i_cfg_cg_idle_count),
        .i_wakeup            (w_wakeup),
        .clk_out             (clk_out),
        .o_gating            (o_gating)
    );

endmodule : axi_clock_gate_ctrl
