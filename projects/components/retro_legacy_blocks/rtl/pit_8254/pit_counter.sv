// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: pit_counter
// Purpose: Single 8254 PIT counter with mode 0 (interrupt on terminal count)
//
// Based on Intel 8254 Programmable Interval Timer specification
// Implements one of three independent 16-bit counters with:
// - Binary or BCD counting
// - Load and latch operations
// - GATE input control
// - OUT signal generation

`timescale 1ns / 1ps

`include "reset_defs.svh"

module pit_counter (
    input wire clk,
    input wire rst,  // Active-high reset

    // Configuration inputs (from control register)
    input wire        cfg_bcd,           // 0=binary, 1=BCD counting
    input wire [2:0]  cfg_mode,          // Counter mode (0-5)
    input wire [1:0]  cfg_rw_mode,       // Read/Write mode
    input wire        cfg_control_wr,    // Control word written pulse

    // Counter data interface
    input wire [15:0] count_reg_in,      // Count value from register file
    input wire        count_reg_wr,      // Write strobe from CPU
    output reg [15:0] count_reg_out,     // Current count for readback

    // Hardware interface
    input wire        i_gate,            // GATE input (external control)
    input wire        i_clk_en,          // Clock enable (from clock select)
    output reg        o_out,             // OUT signal

    // Status outputs (for status register)
    output wire       o_null_count,      // NULL COUNT flag (no value loaded)
    output wire [1:0] o_status_rw_mode,  // Current RW mode for status
    output wire [2:0] o_status_mode,     // Current mode for status
    output wire       o_status_bcd       // Current BCD setting for status
);

    //========================================================================
    // Internal State
    //========================================================================

    // Counter value
    logic [15:0] r_count;          // Current count value
    logic [15:0] r_count_latch;    // Latched count for readback
    logic        r_count_latched;  // Latch active flag

    // Counting control
    logic        r_null_count;     // 1 = no value loaded yet
    logic        r_counting;       // 1 = counting in progress
    logic        r_out;            // OUT signal state

    // Configuration shadow (latches control word)
    logic        r_cfg_bcd;
    logic [2:0]  r_cfg_mode;
    logic [1:0]  r_cfg_rw_mode;

    // Load/reload value
    logic [15:0] r_reload_value;   // Value to load on reload
    logic        r_reload_pending; // Reload requested

    // Byte access state machine (for RW_MODE = 1,2,3)
    typedef enum logic [1:0] {
        BYTE_IDLE = 2'b00,
        BYTE_LSB  = 2'b01,
        BYTE_MSB  = 2'b10
    } byte_state_t;

    byte_state_t r_wr_byte_state;
    byte_state_t r_rd_byte_state;
    logic [7:0]  r_wr_lsb;         // Temporary storage for LSB during 2-byte write

    // Read source mux
    logic [15:0] w_read_source;

    //========================================================================
    // Status Outputs
    //========================================================================

    assign o_null_count       = r_null_count;
    assign o_status_rw_mode   = r_cfg_rw_mode;
    assign o_status_mode      = r_cfg_mode;
    assign o_status_bcd       = r_cfg_bcd;
    assign o_out              = r_out;

    // Read source mux: select between current count and latched count
    assign w_read_source = r_count_latched ? r_count_latch : r_count;

    //========================================================================
    // Configuration Latch (Control Word Write)
    //========================================================================

    `ALWAYS_FF_RST(clk, ~rst,
        if (`RST_ASSERTED(~rst)) begin
            r_cfg_bcd     <= 1'b0;
            r_cfg_mode    <= 3'h0;
            r_cfg_rw_mode <= 2'h0;
        end else begin
            if (cfg_control_wr) begin
                r_cfg_bcd     <= cfg_bcd;
                r_cfg_mode    <= cfg_mode;
                r_cfg_rw_mode <= cfg_rw_mode;
            end
        end
    )

    //========================================================================
    // Write Logic (Count Register Load)
    //========================================================================

    `ALWAYS_FF_RST(clk, ~rst,
        if (`RST_ASSERTED(~rst)) begin
            r_reload_value   <= 16'h0;
            r_reload_pending <= 1'b0;
            r_wr_byte_state  <= BYTE_IDLE;
            r_wr_lsb         <= 8'h0;
        end else begin
            r_reload_pending <= 1'b0;  // Default: clear pending

            if (count_reg_wr) begin
                case (r_cfg_rw_mode)
                    2'b00: begin  // Counter latch command
                        if (!r_count_latched) begin
                            r_count_latch   <= r_count;
                            r_count_latched <= 1'b1;
                        end
                    end

                    2'b01: begin  // LSB only
                        r_reload_value   <= {8'h00, count_reg_in[7:0]};
                        r_reload_pending <= 1'b1;
                        r_wr_byte_state  <= BYTE_IDLE;
                    end

                    2'b10: begin  // MSB only
                        r_reload_value   <= {count_reg_in[7:0], 8'h00};
                        r_reload_pending <= 1'b1;
                        r_wr_byte_state  <= BYTE_IDLE;
                    end

                    2'b11: begin  // LSB then MSB
                        // For APB register interface: accept full 16-bit write immediately
                        // (The register wrapper already handles byte access at APB level)
                        // Byte-by-byte mode would be used for true 8254 port I/O interface
                        r_reload_value   <= count_reg_in;
                        r_reload_pending <= 1'b1;
                        r_wr_byte_state  <= BYTE_IDLE;
                    end
                endcase
            end
        end
    )

    //========================================================================
    // Read Logic (Count Register Readback)
    //========================================================================

    `ALWAYS_FF_RST(clk, ~rst,
        if (`RST_ASSERTED(~rst)) begin
            count_reg_out    <= 16'h0;
            r_count_latched  <= 1'b0;
            r_rd_byte_state  <= BYTE_IDLE;
        end else begin
            case (r_cfg_rw_mode)
                2'b00: begin  // Latch command (handled in write logic)
                    count_reg_out <= w_read_source;
                end

                2'b01: begin  // LSB only
                    count_reg_out <= {8'h00, w_read_source[7:0]};
                    r_count_latched <= 1'b0;  // Clear latch after read
                end

                2'b10: begin  // MSB only
                    count_reg_out <= {8'h00, w_read_source[15:8]};
                    r_count_latched <= 1'b0;
                end

                2'b11: begin  // LSB then MSB
                    // For APB register interface: return full 16-bit value
                    // (Byte-by-byte reads would be used for true 8254 port I/O interface)
                    count_reg_out <= w_read_source;
                    r_count_latched <= 1'b0;  // Clear latch after read
                end
            endcase
        end
    )

    //========================================================================
    // Counter Core - Mode 0: Interrupt on Terminal Count
    //========================================================================

    // Decrement function (binary or BCD)
    function automatic [15:0] decrement_count(input [15:0] count, input bcd_mode);
        logic [15:0] result;
        if (bcd_mode) begin
            // BCD decrement (4 digits, 0000-9999)
            result = count;
            // Digit 0 (ones)
            if (result[3:0] == 4'h0) begin
                result[3:0] = 4'h9;
                // Digit 1 (tens)
                if (result[7:4] == 4'h0) begin
                    result[7:4] = 4'h9;
                    // Digit 2 (hundreds)
                    if (result[11:8] == 4'h0) begin
                        result[11:8] = 4'h9;
                        // Digit 3 (thousands)
                        if (result[15:12] == 4'h0)
                            result[15:12] = 4'h9;
                        else
                            result[15:12] = result[15:12] - 4'h1;
                    end else begin
                        result[11:8] = result[11:8] - 4'h1;
                    end
                end else begin
                    result[7:4] = result[7:4] - 4'h1;
                end
            end else begin
                result[3:0] = result[3:0] - 4'h1;
            end
        end else begin
            // Binary decrement
            result = count - 16'h1;
        end
        return result;
    endfunction

    // Mode 0 counter logic
    `ALWAYS_FF_RST(clk, ~rst,
        if (`RST_ASSERTED(~rst)) begin
            r_count      <= 16'h0;
            r_null_count <= 1'b1;
            r_counting   <= 1'b0;
            r_out        <= 1'b0;
        end else begin
            // Handle reload (new count loaded)
            // Per Intel 8254 spec: After loading, counting begins on next clock pulse
            if (r_reload_pending) begin
                r_count      <= r_reload_value;    // Load counter immediately
                r_null_count <= 1'b0;              // Clear NULL_COUNT flag
                r_counting   <= (i_gate && i_clk_en) ? 1'b1 : 1'b0;  // Start if GATE high AND clock enabled
                r_out        <= 1'b0;              // OUT goes low on load (mode 0)
            end
            // Count down on each enabled clock cycle
            else if (r_counting && i_clk_en) begin
                if (r_count == 16'h0) begin
                    // Terminal count reached
                    r_out      <= 1'b1;            // OUT goes high
                    r_counting <= 1'b0;            // Stop counting
                end else begin
                    // Decrement counter
                    r_count <= decrement_count(r_count, r_cfg_bcd);
                end
            end
            // Handle GATE transitions when not actively reloading or counting
            else if (!r_null_count && !r_counting) begin
                // If GATE goes high and clock enabled, start counting
                if (i_gate && i_clk_en) begin
                    r_counting <= 1'b1;
                end
            end
        end
    )

endmodule
