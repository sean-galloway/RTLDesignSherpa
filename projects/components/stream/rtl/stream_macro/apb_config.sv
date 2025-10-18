// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: apb_config
// Purpose: Apb Config module
//
// Documentation: projects/components/stream_macro/PRD.md
// Subsystem: stream_macro
//
// Author: sean galloway
// Created: 2025-10-18

`timescale 1ns / 1ps

// Import common STREAM and monitor packages
`include "stream_imports.svh"

module apb_config #(
    parameter int NUM_CHANNELS = 8,
    parameter int ADDR_WIDTH = 32,
    parameter int DATA_WIDTH = 32
) (
    // Clock and Reset
    input  logic                        pclk,
    input  logic                        presetn,

    // APB Slave Interface
    input  logic [ADDR_WIDTH-1:0]       paddr,
    input  logic                        psel,
    input  logic                        penable,
    input  logic                        pwrite,
    input  logic [DATA_WIDTH-1:0]       pwdata,
    input  logic [3:0]                  pstrb,
    output logic                        pready,
    output logic [DATA_WIDTH-1:0]       prdata,
    output logic                        pslverr,

    // Channel Configuration Outputs (per channel)
    output logic [NUM_CHANNELS-1:0]     ch_enable,              // Channel enable
    output logic [NUM_CHANNELS-1:0]     ch_reset,               // Channel reset
    output logic [NUM_CHANNELS-1:0][63:0] ch_desc_addr,         // Descriptor address
    output logic [NUM_CHANNELS-1:0][7:0]  ch_read_burst_len,    // Read burst length
    output logic [NUM_CHANNELS-1:0][7:0]  ch_write_burst_len,   // Write burst length

    // Channel Status Inputs (per channel)
    input  logic [NUM_CHANNELS-1:0]     ch_idle,                // Channel idle
    input  logic [NUM_CHANNELS-1:0]     ch_error,               // Channel error
    input  logic [NUM_CHANNELS-1:0][31:0] ch_bytes_xfered       // Bytes transferred
);

    //=========================================================================
    // Register Map Constants
    //=========================================================================

    // Global registers
    localparam logic [ADDR_WIDTH-1:0] ADDR_GLOBAL_CTRL   = 32'h00;
    localparam logic [ADDR_WIDTH-1:0] ADDR_GLOBAL_STATUS = 32'h04;

    // Channel register offsets (16 bytes per channel)
    localparam logic [ADDR_WIDTH-1:0] CH_BASE = 32'h10;
    localparam logic [ADDR_WIDTH-1:0] CH_STRIDE = 32'h10;
    localparam logic [ADDR_WIDTH-1:0] CH_CTRL_OFFSET = 32'h00;
    localparam logic [ADDR_WIDTH-1:0] CH_STATUS_OFFSET = 32'h04;
    localparam logic [ADDR_WIDTH-1:0] CH_RD_BURST_OFFSET = 32'h08;
    localparam logic [ADDR_WIDTH-1:0] CH_WR_BURST_OFFSET = 32'h0C;

    //=========================================================================
    // Internal Registers
    //=========================================================================

    // Global configuration
    logic r_global_enable;
    logic [NUM_CHANNELS-1:0] r_ch_reset;

    // Per-channel configuration
    logic [NUM_CHANNELS-1:0][63:0] r_ch_desc_addr;
    logic [NUM_CHANNELS-1:0][7:0] r_ch_read_burst_len;
    logic [NUM_CHANNELS-1:0][7:0] r_ch_write_burst_len;
    logic [NUM_CHANNELS-1:0] r_ch_enable;

    // APB FSM
    typedef enum logic [1:0] {
        APB_IDLE   = 2'b00,
        APB_SETUP  = 2'b01,
        APB_ACCESS = 2'b10
    } apb_state_t;

    apb_state_t r_apb_state, w_apb_next_state;

    // Transaction tracking
    logic w_apb_read;
    logic w_apb_write;
    logic [ADDR_WIDTH-1:0] r_apb_addr;
    logic [DATA_WIDTH-1:0] r_apb_wdata;

    // Decoded channel and offset
    logic [3:0] w_channel_id;
    logic [3:0] w_reg_offset;
    logic w_valid_channel;
    logic w_global_reg;

    //=========================================================================
    // APB State Machine
    //=========================================================================

    always_ff @(posedge pclk or negedge presetn) begin
        if (!presetn) begin
            r_apb_state <= APB_IDLE;
        end else begin
            r_apb_state <= w_apb_next_state;
        end
    end

    always_comb begin
        w_apb_next_state = r_apb_state;

        case (r_apb_state)
            APB_IDLE: begin
                if (psel) begin
                    w_apb_next_state = APB_SETUP;
                end
            end

            APB_SETUP: begin
                if (penable) begin
                    w_apb_next_state = APB_ACCESS;
                end
            end

            APB_ACCESS: begin
                // Transaction completes
                w_apb_next_state = APB_IDLE;
            end

            default: begin
                w_apb_next_state = APB_IDLE;
            end
        endcase
    end

    // APB transaction detection
    assign w_apb_read = (r_apb_state == APB_ACCESS) && !pwrite;
    assign w_apb_write = (r_apb_state == APB_ACCESS) && pwrite;

    //=========================================================================
    // Address Decoding
    //=========================================================================

    // Latch address and data during SETUP phase
    always_ff @(posedge pclk or negedge presetn) begin
        if (!presetn) begin
            r_apb_addr <= '0;
            r_apb_wdata <= '0;
        end else if (r_apb_state == APB_SETUP) begin
            r_apb_addr <= paddr;
            r_apb_wdata <= pwdata;
        end
    end

    // Decode channel ID and register offset
    always_comb begin
        w_global_reg = (r_apb_addr < CH_BASE);
        w_channel_id = 4'h0;
        w_reg_offset = 4'h0;
        w_valid_channel = 1'b0;

        if (!w_global_reg) begin
            // Channel register access
            logic [ADDR_WIDTH-1:0] ch_offset;
            ch_offset = r_apb_addr - CH_BASE;
            w_channel_id = ch_offset[7:4];  // Which channel (bits 7:4)
            w_reg_offset = ch_offset[3:0];  // Which register within channel (bits 3:0)
            w_valid_channel = (w_channel_id < NUM_CHANNELS);
        end
    end

    //=========================================================================
    // Register Writes
    //=========================================================================

    always_ff @(posedge pclk or negedge presetn) begin
        if (!presetn) begin
            r_global_enable <= 1'b0;
            r_ch_reset <= '0;
            r_ch_desc_addr <= '0;
            r_ch_read_burst_len <= '0;
            r_ch_write_burst_len <= '0;
            r_ch_enable <= '0;

            // Default burst lengths (8 beats for reads, 16 beats for writes)
            for (int i = 0; i < NUM_CHANNELS; i++) begin
                r_ch_read_burst_len[i] <= 8'd8;
                r_ch_write_burst_len[i] <= 8'd16;
            end
        end else if (w_apb_write) begin
            if (w_global_reg) begin
                // Global register write
                case (r_apb_addr)
                    ADDR_GLOBAL_CTRL: begin
                        r_global_enable <= r_apb_wdata[0];
                        r_ch_reset <= r_apb_wdata[NUM_CHANNELS+15:16];
                    end

                    default: begin
                        // Unknown global register
                    end
                endcase
            end else if (w_valid_channel) begin
                // Channel register write
                case (w_reg_offset)
                    CH_CTRL_OFFSET: begin
                        // Write to CHx_CTRL kicks off channel
                        r_ch_desc_addr[w_channel_id] <= {32'h0, r_apb_wdata};
                        r_ch_enable[w_channel_id] <= 1'b1;  // Auto-enable on kick-off
                    end

                    CH_RD_BURST_OFFSET: begin
                        // Configure read burst length
                        r_ch_read_burst_len[w_channel_id] <= r_apb_wdata[7:0];
                    end

                    CH_WR_BURST_OFFSET: begin
                        // Configure write burst length
                        r_ch_write_burst_len[w_channel_id] <= r_apb_wdata[7:0];
                    end

                    default: begin
                        // Unknown channel register
                    end
                endcase
            end
        end else begin
            // Auto-clear channel enable when channel goes idle
            for (int i = 0; i < NUM_CHANNELS; i++) begin
                if (ch_idle[i]) begin
                    r_ch_enable[i] <= 1'b0;
                end
            end

            // Auto-clear reset after one cycle
            r_ch_reset <= '0;
        end
    end

    //=========================================================================
    // Register Reads
    //=========================================================================

    logic [DATA_WIDTH-1:0] w_read_data;

    always_comb begin
        w_read_data = 32'h0;

        if (w_global_reg) begin
            // Global register read
            case (r_apb_addr)
                ADDR_GLOBAL_CTRL: begin
                    w_read_data[0] = r_global_enable;
                    w_read_data[NUM_CHANNELS+15:16] = r_ch_reset;
                end

                ADDR_GLOBAL_STATUS: begin
                    w_read_data[NUM_CHANNELS-1:0] = ch_idle;
                    w_read_data[NUM_CHANNELS+15:16] = ch_error;
                end

                default: begin
                    w_read_data = 32'h0;
                end
            endcase
        end else if (w_valid_channel) begin
            // Channel register read
            case (w_reg_offset)
                CH_CTRL_OFFSET: begin
                    w_read_data = r_ch_desc_addr[w_channel_id][31:0];
                end

                CH_STATUS_OFFSET: begin
                    w_read_data[0] = r_ch_enable[w_channel_id];
                    w_read_data[1] = ch_idle[w_channel_id];
                    w_read_data[2] = ch_error[w_channel_id];
                end

                CH_RD_BURST_OFFSET: begin
                    w_read_data[7:0] = r_ch_read_burst_len[w_channel_id];
                end

                CH_WR_BURST_OFFSET: begin
                    w_read_data[7:0] = r_ch_write_burst_len[w_channel_id];
                end

                default: begin
                    w_read_data = 32'h0;
                end
            endcase
        end
    end

    // APB read data output
    always_ff @(posedge pclk or negedge presetn) begin
        if (!presetn) begin
            prdata <= 32'h0;
        end else if (w_apb_read) begin
            prdata <= w_read_data;
        end
    end

    //=========================================================================
    // APB Response Signals
    //=========================================================================

    // Ready after ACCESS phase
    assign pready = (r_apb_state == APB_ACCESS);

    // Error on invalid channel or address
    assign pslverr = (r_apb_state == APB_ACCESS) &&
                     (!w_global_reg && !w_valid_channel);

    //=========================================================================
    // Configuration Outputs
    //=========================================================================

    assign ch_enable = r_ch_enable & {NUM_CHANNELS{r_global_enable}};
    assign ch_reset = r_ch_reset;
    assign ch_desc_addr = r_ch_desc_addr;
    assign ch_read_burst_len = r_ch_read_burst_len;
    assign ch_write_burst_len = r_ch_write_burst_len;

endmodule : apb_config
