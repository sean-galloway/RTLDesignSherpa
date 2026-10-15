// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: amba_clock_gate_ctrl
// Purpose: Amba Clock Gate Ctrl module
//
// Documentation: docs/markdown/rtl-amba/index.md
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

    // ---------------------------------------------------------------
    // Boundary reset synchronization. The port aresetn is treated as an
    // asynchronous-assert input of unknown deassert quality: an N=3
    // reset_sync (rtl/cdc, formally proven) produces the internal reset
    // every block below sees.
    // ---------------------------------------------------------------
    logic w_aresetn;
    reset_sync #(
        .N             (3),
        .KEEP_ATTRS    (1'b1),
        .IN_ACTIVE_LOW (1'b1),
        .OUT_ACTIVE_LOW(1'b1),
        .ASYNC_ASSERT  (1'b1)
    ) u_reset_sync (
        .clk        (clk_in),
        .rst_n      (aresetn),
        .sync_rst_n (w_aresetn)
    );

    // Internal signals
    logic r_wakeup;

    // Combine activity signals
    // flop the wakeup signal
    `ALWAYS_FF_RST(clk_in, w_aresetn,
        if (`RST_ASSERTED(w_aresetn)) r_wakeup <= 'h1;
        else r_wakeup <= user_valid || axi_valid;
    )


    // Generate idle signal when no activity
    assign idle = ~r_wakeup;

    // Instantiate the base clock gate control
    clock_gate_ctrl #(
        .IDLE_CNTR_WIDTH    (ICW)
    ) u_clock_gate_ctrl (
        .clk_in             (clk_in),
        .aresetn            (w_aresetn),
        .cfg_cg_enable      (cfg_cg_enable),
        .cfg_cg_idle_count  (cfg_cg_idle_count),
        .wakeup             (r_wakeup),
        .clk_out            (clk_out),
        .gating             (gating)
    );

endmodule : amba_clock_gate_ctrl
