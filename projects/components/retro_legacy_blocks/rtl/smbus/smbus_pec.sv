// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: smbus_pec
// Purpose: SMBus Packet Error Checking (PEC) Calculator
//
// Implements CRC-8 calculation for SMBus PEC:
// - Polynomial: x^8 + x^2 + x + 1 (0x07)
// - Initial value: 0x00
// - Calculated over all bytes in transaction except PEC itself
// - Provides running CRC during transaction
//
// Usage:
// - Assert enable to start/continue CRC calculation
// - Provide data_in with data_valid pulse
// - Read crc_out for current PEC value
// - Assert clear to reset CRC to 0x00

`timescale 1ns / 1ps

`include "reset_defs.svh"

module smbus_pec (
    input  wire       clk,
    input  wire       rst,          // Active-high reset

    // Control
    input  wire       enable,       // Enable CRC calculation
    input  wire       clear,        // Clear CRC to initial value

    // Data input
    input  wire [7:0] data_in,      // Input data byte
    input  wire       data_valid,   // Data valid pulse

    // CRC output
    output wire [7:0] crc_out       // Current CRC value
);

    //========================================================================
    // CRC-8 Calculation
    //========================================================================
    // Polynomial: x^8 + x^2 + x + 1 = 0x07
    // This is the SMBus PEC polynomial

    logic [7:0] r_crc;

    // CRC-8 calculation function
    function automatic logic [7:0] crc8_update(input logic [7:0] crc, input logic [7:0] data);
        logic [7:0] temp;
        integer i;
        
        temp = crc ^ data;
        
        for (i = 0; i < 8; i = i + 1) begin
            if (temp[7]) begin
                temp = (temp << 1) ^ 8'h07;  // Polynomial 0x07
            end else begin
                temp = temp << 1;
            end
        end
        
        crc8_update = temp;
    endfunction

    //========================================================================
    // CRC Register
    //========================================================================

    always_ff @(posedge clk) begin
        if (rst || clear) begin
            r_crc <= 8'h00;  // Initial CRC value
        end else if (enable && data_valid) begin
            r_crc <= crc8_update(r_crc, data_in);
        end
    end

    //========================================================================
    // Output
    //========================================================================

    assign crc_out = r_crc;

endmodule
