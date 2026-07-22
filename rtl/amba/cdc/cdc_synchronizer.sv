// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: cdc_synchronizer
// Purpose: Multi-bit synchronizer for clock domain crossing
//
// This module provides a simple CDC synchronizer interface that wraps
// the glitch_free_n_dff_arn module for consistent naming across the
// AMBA infrastructure.
//
// Documentation: rtl/amba/PRD.md
// Subsystem: amba
//
// Author: sean galloway
// Created: 2025-12-23

`timescale 1ns / 1ps

module cdc_synchronizer #(
    parameter int WIDTH      = 1,   // Bus width to synchronize
    parameter int FLOP_COUNT = 3    // Number of synchronizer stages (2-5)
) (
    input  logic             clk,       // Destination clock
    input  logic             rst_n,     // Asynchronous active-low reset
    input  logic [WIDTH-1:0] async_in,  // Asynchronous input from source domain
    output logic [WIDTH-1:0] sync_out   // Synchronized output in destination domain
);

    // Use the glitch_free_n_dff_arn module for the actual synchronization
    glitch_free_n_dff_arn #(
        .FLOP_COUNT (FLOP_COUNT),
        .WIDTH      (WIDTH)
    ) u_sync (
        .clk   (clk),
        .rst_n (rst_n),
        .d     (async_in),
        .q     (sync_out)
    );

endmodule : cdc_synchronizer
