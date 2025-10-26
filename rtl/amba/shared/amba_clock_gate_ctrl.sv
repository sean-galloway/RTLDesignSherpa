// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: amba_clock_gate_ctrl
// Purpose: Amba Clock Gate Ctrl module
//
// Documentation: rtl/amba/PRD.md
// Subsystem: amba
//
// Author: sean galloway
// Created: 2025-10-18

`timescale 1ns / 1ps

`include "reset_defs.svh"

module amba_clock_gate_ctrl #(
    parameter int CG_IDLE_COUNT_WIDTH = 4,                   // Default width of idle counter
    parameter int ICW                 = CG_IDLE_COUNT_WIDTH

) (
    // Clock and Reset
    input logic clk_in,
    input logic aresetn,

    // Configuration Interface
    input logic         cfg_cg_enable,     // Global clock gate enable
    input logic [ICW-1:0] cfg_cg_idle_count, // Idle countdown value

    // Activity Monitoring
    input logic user_valid,  // Any user-side valid signal
    input logic axi_valid,   // Any AXI-side valid signal

    // Clock Gating Control Outputs
    output logic clk_out,   // Gated clock
    output logic gating,  // Active gating indicator
    output logic idle     // All buffers empty indicator
);

    // Internal signals
    logic r_wakeup;

    // Combine activity signals
    // flop the wakeup signal
    `ALWAYS_FF_RST(clk_in, aresetn,
        if (!aresetn) r_wakeup <= 'h1;
        else r_wakeup <= user_valid || axi_valid;
    )


    // Generate idle signal when no activity
    assign idle = ~r_wakeup;

    // Instantiate the base clock gate control
    clock_gate_ctrl #(
        .IDLE_CNTR_WIDTH    (ICW)
    ) u_clock_gate_ctrl (
        .clk_in             (clk_in),
        .aresetn            (aresetn),
        .cfg_cg_enable      (cfg_cg_enable),
        .cfg_cg_idle_count  (cfg_cg_idle_count),
        .wakeup             (r_wakeup),
        .clk_out            (clk_out),
        .gating             (gating)
    );

endmodule : amba_clock_gate_ctrl
