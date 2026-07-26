// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// Yosys-compatible copy of cdc_synchronizer.sv for formal verification.
// Identical to original -- just reads without the original include path.

`timescale 1ns / 1ps

module cdc_synchronizer #(
    parameter int WIDTH      = 1,
    parameter int FLOP_COUNT = 3
) (
    input  logic             clk,
    input  logic             rst_n,
    input  logic [WIDTH-1:0] async_in,
    output logic [WIDTH-1:0] sync_out
);

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
