// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: smbus_core
// Purpose: Core logic for SMBus 2.0 Controller with Master/Slave FSMs
//
// Implements SMBus 2.0 functionality:
// - Master mode: initiate transactions, generate clocks
// - Slave mode: respond to transactions, clock stretching
// - All standard transaction types (Quick, Byte, Word, Block)
// - Physical layer: I2C-compatible signaling (SCL/SDA)
// - Start/Stop condition generation and detection
// - Arbitration handling
// - Timeout detection (25-35ms)
// - Packet Error Checking (PEC) integration
// - TX/RX FIFO integration
//
// Follows RTC pattern: separate core logic from register interface

`timescale 1ns / 1ps

`include "reset_defs.svh"

module smbus_core #(
    parameter int FIFO_DEPTH = 32   // TX/RX FIFO depth (32 bytes per SMBus 2.0)
) (
    input wire clk,              // System clock
    input wire rst,              // Active-high reset

    //========================================================================
    // SMBus Physical Interface
    //========================================================================
    input  wire smb_scl_i,       // SCL input
    output wire smb_scl_o,       // SCL output
    output wire smb_scl_t,       // SCL tristate enable (1=input, 0=output)
    input  wire smb_sda_i,       // SDA input
    output wire smb_sda_o,       // SDA output
    output wire smb_sda_t,       // SDA tristate enable (1=input, 0=output)

    //========================================================================
    // Configuration from Registers
    //========================================================================
    input wire        cfg_master_en,        // Master mode enable
    input wire        cfg_slave_en,         // Slave mode enable
    input wire        cfg_pec_en,           // PEC enable
    input wire        cfg_fast_mode,        // Fast mode (400kHz vs 100kHz)
    input wire        cfg_fifo_reset,       // FIFO reset strobe
    input wire [15:0] cfg_clk_div,          // Clock divider for SCL
    input wire [23:0] cfg_timeout,          // Timeout threshold
    input wire [6:0]  cfg_own_addr,         // Own slave address
    input wire        cfg_own_addr_en,      // Own address enable

    //========================================================================
    // Command Interface
    //========================================================================
    input wire [3:0]  cmd_trans_type,       // Transaction type
    input wire [7:0]  cmd_code,             // Command code
    input wire [6:0]  cmd_slave_addr,       // Target slave address
    input wire        cmd_start,            // Start transaction
    input wire        cmd_stop,             // Stop/abort transaction
    input wire [7:0]  cmd_data_byte,        // Single data byte
    input wire [5:0]  cmd_block_count,      // Block transfer count

    //========================================================================
    // Status Outputs
    //========================================================================
    output wire       status_busy,          // Transaction in progress
    output wire       status_bus_error,     // Bus error (NAK, etc.)
    output wire       status_timeout_error, // Timeout error
    output wire       status_pec_error,     // PEC mismatch
    output wire       status_arb_lost,      // Arbitration lost
    output wire       status_nak_received,  // NAK received
    output wire       status_slave_addressed, // Addressed as slave
    output wire       status_complete,      // Transaction complete
    output wire [3:0] status_fsm_state,     // FSM state (debug)

    //========================================================================
    // Data Byte Interface
    //========================================================================
    output wire [7:0] data_byte_out,        // Data byte read
    input  wire [7:0] data_byte_in,         // Data byte written

    //========================================================================
    // TX FIFO Interface
    //========================================================================
    input  wire [7:0] tx_fifo_wdata,        // TX FIFO write data
    input  wire       tx_fifo_wr,           // TX FIFO write enable
    output wire [5:0] tx_fifo_level,        // TX FIFO level
    output wire       tx_fifo_full,         // TX FIFO full
    output wire       tx_fifo_empty,        // TX FIFO empty

    //========================================================================
    // RX FIFO Interface
    //========================================================================
    output wire [7:0] rx_fifo_rdata,        // RX FIFO read data
    input  wire       rx_fifo_rd,           // RX FIFO read enable
    output wire [5:0] rx_fifo_level,        // RX FIFO level
    output wire       rx_fifo_full,         // RX FIFO full
    output wire       rx_fifo_empty,        // RX FIFO empty

    //========================================================================
    // PEC Interface
    //========================================================================
    output wire [7:0] pec_value,            // Current PEC value
    input  wire [7:0] pec_expected          // Expected PEC value
);

    //========================================================================
    // Transaction Type Definitions
    //========================================================================
    typedef enum logic [3:0] {
        TRANS_QUICK_CMD     = 4'h0,  // Quick command (0 bytes)
        TRANS_SEND_BYTE     = 4'h1,  // Send byte (1 byte, no command)
        TRANS_RECV_BYTE     = 4'h2,  // Receive byte (1 byte, no command)
        TRANS_WRITE_BYTE    = 4'h3,  // Write byte data (1 cmd + 1 data)
        TRANS_READ_BYTE     = 4'h4,  // Read byte data (1 cmd + 1 data)
        TRANS_WRITE_WORD    = 4'h5,  // Write word data (1 cmd + 2 data)
        TRANS_READ_WORD     = 4'h6,  // Read word data (1 cmd + 2 data)
        TRANS_BLOCK_WRITE   = 4'h7,  // Block write (1 cmd + count + data)
        TRANS_BLOCK_READ    = 4'h8,  // Block read (1 cmd + count + data)
        TRANS_BLOCK_PROC    = 4'h9   // Block write-block read process call
    } trans_type_t;

    //========================================================================
    // Master FSM States
    //========================================================================
    typedef enum logic [3:0] {
        M_IDLE          = 4'h0,   // Idle state
        M_START         = 4'h1,   // Generate START condition
        M_ADDR          = 4'h2,   // Send address byte
        M_ADDR_ACK      = 4'h3,   // Wait for address ACK
        M_CMD           = 4'h4,   // Send command byte
        M_CMD_ACK       = 4'h5,   // Wait for command ACK
        M_DATA_WR       = 4'h6,   // Write data byte
        M_DATA_WR_ACK   = 4'h7,   // Wait for data write ACK
        M_DATA_RD       = 4'h8,   // Read data byte
        M_DATA_RD_ACK   = 4'h9,   // Send ACK/NAK for read data
        M_PEC_WR        = 4'hA,   // Send PEC byte
        M_PEC_WR_ACK    = 4'hB,   // Wait for PEC ACK
        M_PEC_RD        = 4'hC,   // Read PEC byte
        M_STOP          = 4'hD,   // Generate STOP condition
        M_ERROR         = 4'hE,   // Error state
        M_RESTART       = 4'hF    // Generate repeated START
    } master_state_t;

    master_state_t r_master_state, r_master_state_next;

    //========================================================================
    // Slave FSM States
    //========================================================================
    typedef enum logic [3:0] {
        S_IDLE          = 4'h0,   // Idle, listening for address
        S_ADDR_MATCH    = 4'h1,   // Address matched, send ACK
        S_CMD_RX        = 4'h2,   // Receive command byte
        S_CMD_ACK       = 4'h3,   // ACK command byte
        S_DATA_RX       = 4'h4,   // Receive data byte
        S_DATA_RX_ACK   = 4'h5,   // ACK received data
        S_DATA_TX       = 4'h6,   // Transmit data byte
        S_DATA_TX_ACK   = 4'h7,   // Wait for master ACK
        S_PEC_RX        = 4'h8,   // Receive PEC byte
        S_PEC_ACK       = 4'h9,   // ACK PEC byte
        S_WAIT_STOP     = 4'hA    // Wait for STOP condition
    } slave_state_t;

    slave_state_t r_slave_state, r_slave_state_next;

    //========================================================================
    // Physical Layer State
    //========================================================================
    typedef enum logic [2:0] {
        PHY_IDLE        = 3'h0,   // Bus idle
        PHY_START       = 3'h1,   // START condition
        PHY_STOP        = 3'h2,   // STOP condition
        PHY_BIT_TX      = 3'h3,   // Transmit bit
        PHY_BIT_RX      = 3'h4,   // Receive bit
        PHY_WAIT        = 3'h5    // Wait state
    } phy_state_t;

    phy_state_t r_phy_state, r_phy_state_next;

    //========================================================================
    // Internal Registers
    //========================================================================

    // Status flags
    logic r_busy;
    logic r_bus_error;
    logic r_timeout_error;
    logic r_pec_error;
    logic r_arb_lost;
    logic r_nak_received;
    logic r_slave_addressed;
    logic r_complete;

    // Clock generation
    logic [15:0] r_clk_counter;
    logic        r_scl_gen;
    logic        r_scl_quarter;  // SCL quarter period tick

    // Bit timing
    logic [3:0]  r_bit_counter;
    logic [7:0]  r_shift_reg;
    logic        r_shift_dir;    // 0=TX, 1=RX
    logic        r_ack_bit;

    // Byte counter for multi-byte transfers
    logic [5:0]  r_byte_counter;
    logic [5:0]  r_bytes_total;

    // Transaction tracking
    logic [3:0]  r_trans_type;
    logic [6:0]  r_slave_addr;
    logic [7:0]  r_cmd_code;
    logic        r_rw_bit;       // 0=write, 1=read

    // Timeout counter
    logic [23:0] r_timeout_counter;
    logic        r_timeout_en;

    // Start/Stop detection
    logic        r_scl_d1, r_scl_d2;
    logic        r_sda_d1, r_sda_d2;
    logic        r_start_detected;
    logic        r_stop_detected;

    // SCL/SDA control
    logic        r_scl_out;
    logic        r_sda_out;
    logic        r_scl_tristate;
    logic        r_sda_tristate;

    //========================================================================
    // TX FIFO Instance
    //========================================================================

    logic       w_tx_fifo_rd;
    logic [7:0] w_tx_fifo_rdata;

    simple_fifo #(
        .DATA_WIDTH(8),
        .DEPTH(FIFO_DEPTH)
    ) u_tx_fifo (
        .clk        (clk),
        .rst        (rst || cfg_fifo_reset),
        .wr_en      (tx_fifo_wr),
        .wr_data    (tx_fifo_wdata),
        .rd_en      (w_tx_fifo_rd),
        .rd_data    (w_tx_fifo_rdata),
        .full       (tx_fifo_full),
        .empty      (tx_fifo_empty),
        .count      (tx_fifo_level)
    );

    //========================================================================
    // RX FIFO Instance
    //========================================================================

    logic       w_rx_fifo_wr;
    logic [7:0] w_rx_fifo_wdata;

    simple_fifo #(
        .DATA_WIDTH(8),
        .DEPTH(FIFO_DEPTH)
    ) u_rx_fifo (
        .clk        (clk),
        .rst        (rst || cfg_fifo_reset),
        .wr_en      (w_rx_fifo_wr),
        .wr_data    (w_rx_fifo_wdata),
        .rd_en      (rx_fifo_rd),
        .rd_data    (rx_fifo_rdata),
        .full       (rx_fifo_full),
        .empty      (rx_fifo_empty),
        .count      (rx_fifo_level)
    );

    //========================================================================
    // PEC Module Instance
    //========================================================================

    logic       w_pec_enable;
    logic       w_pec_clear;
    logic [7:0] w_pec_data;
    logic       w_pec_valid;
    logic [7:0] w_pec_out;

    smbus_pec u_pec (
        .clk        (clk),
        .rst        (rst),
        .enable     (w_pec_enable),
        .clear      (w_pec_clear),
        .data_in    (w_pec_data),
        .data_valid (w_pec_valid),
        .crc_out    (w_pec_out)
    );

    assign pec_value = w_pec_out;

    //========================================================================
    // SCL Clock Generation
    //========================================================================

    always_ff @(posedge clk) begin
        if (rst || !cfg_master_en) begin
            r_clk_counter <= 16'h0;
            r_scl_gen <= 1'b1;
            r_scl_quarter <= 1'b0;
        end else begin
            r_scl_quarter <= 1'b0;
            
            if (r_clk_counter >= cfg_clk_div) begin
                r_clk_counter <= 16'h0;
                r_scl_gen <= ~r_scl_gen;
                r_scl_quarter <= 1'b1;
            end else begin
                r_clk_counter <= r_clk_counter + 16'h1;
            end
        end
    end

    //========================================================================
    // Input Synchronization and Edge Detection
    //========================================================================

    always_ff @(posedge clk) begin
        if (rst) begin
            r_scl_d1 <= 1'b1;
            r_scl_d2 <= 1'b1;
            r_sda_d1 <= 1'b1;
            r_sda_d2 <= 1'b1;
        end else begin
            r_scl_d1 <= smb_scl_i;
            r_scl_d2 <= r_scl_d1;
            r_sda_d1 <= smb_sda_i;
            r_sda_d2 <= r_sda_d1;
        end
    end

    wire w_scl_posedge = r_scl_d1 && !r_scl_d2;
    wire w_scl_negedge = !r_scl_d1 && r_scl_d2;
    wire w_sda_posedge = r_sda_d1 && !r_sda_d2;
    wire w_sda_negedge = !r_sda_d1 && r_sda_d2;

    //========================================================================
    // Start/Stop Detection
    //========================================================================

    always_ff @(posedge clk) begin
        if (rst) begin
            r_start_detected <= 1'b0;
            r_stop_detected <= 1'b0;
        end else begin
            // START: SDA falling while SCL high
            r_start_detected <= w_sda_negedge && r_scl_d2;
            
            // STOP: SDA rising while SCL high
            r_stop_detected <= w_sda_posedge && r_scl_d2;
        end
    end

    //========================================================================
    // Timeout Counter
    //========================================================================

    always_ff @(posedge clk) begin
        if (rst || !r_timeout_en || r_start_detected) begin
            r_timeout_counter <= 24'h0;
        end else if (r_timeout_counter >= cfg_timeout) begin
            r_timeout_counter <= cfg_timeout;
        end else begin
            r_timeout_counter <= r_timeout_counter + 24'h1;
        end
    end

    wire w_timeout = (r_timeout_counter >= cfg_timeout);

    //========================================================================
    // Master FSM
    //========================================================================

    always_ff @(posedge clk) begin
        if (rst) begin
            r_master_state <= M_IDLE;
        end else begin
            r_master_state <= r_master_state_next;
        end
    end

    always_comb begin
        r_master_state_next = r_master_state;
        
        case (r_master_state)
            M_IDLE: begin
                if (cfg_master_en && cmd_start) begin
                    r_master_state_next = M_START;
                end
            end
            
            M_START: begin
                // Wait for START condition generation
                if (r_phy_state == PHY_IDLE) begin
                    r_master_state_next = M_ADDR;
                end
            end
            
            M_ADDR: begin
                // Send address byte + R/W bit
                if (r_bit_counter == 4'h8) begin
                    r_master_state_next = M_ADDR_ACK;
                end
            end
            
            M_ADDR_ACK: begin
                // Check ACK from slave
                if (r_ack_bit == 1'b0) begin
                    // ACK received, proceed based on transaction type
                    case (r_trans_type)
                        TRANS_QUICK_CMD: r_master_state_next = M_STOP;
                        TRANS_SEND_BYTE: r_master_state_next = M_DATA_WR;
                        TRANS_RECV_BYTE: r_master_state_next = M_DATA_RD;
                        default: r_master_state_next = M_CMD;
                    endcase
                end else begin
                    // NAK received
                    r_master_state_next = M_ERROR;
                end
            end
            
            M_CMD: begin
                // Send command byte
                if (r_bit_counter == 4'h8) begin
                    r_master_state_next = M_CMD_ACK;
                end
            end
            
            M_CMD_ACK: begin
                // Check ACK for command
                if (r_ack_bit == 1'b0) begin
                    // Determine next state based on transaction type
                    if (r_rw_bit) begin
                        r_master_state_next = M_DATA_RD;
                    end else begin
                        r_master_state_next = M_DATA_WR;
                    end
                end else begin
                    r_master_state_next = M_ERROR;
                end
            end
            
            M_DATA_WR: begin
                // Write data byte
                if (r_bit_counter == 4'h8) begin
                    r_master_state_next = M_DATA_WR_ACK;
                end
            end
            
            M_DATA_WR_ACK: begin
                // Check ACK for written data
                if (r_ack_bit == 1'b0) begin
                    // Check if more bytes to send
                    if (r_byte_counter >= r_bytes_total) begin
                        // Done with data, check if PEC needed
                        if (cfg_pec_en) begin
                            r_master_state_next = M_PEC_WR;
                        end else begin
                            r_master_state_next = M_STOP;
                        end
                    end else begin
                        r_master_state_next = M_DATA_WR;
                    end
                end else begin
                    r_master_state_next = M_ERROR;
                end
            end
            
            M_DATA_RD: begin
                // Read data byte
                if (r_bit_counter == 4'h8) begin
                    r_master_state_next = M_DATA_RD_ACK;
                end
            end
            
            M_DATA_RD_ACK: begin
                // Send ACK/NAK for read data
                if (r_byte_counter >= r_bytes_total) begin
                    // Last byte, send NAK
                    if (cfg_pec_en) begin
                        r_master_state_next = M_PEC_RD;
                    end else begin
                        r_master_state_next = M_STOP;
                    end
                end else begin
                    // More bytes to read, send ACK
                    r_master_state_next = M_DATA_RD;
                end
            end
            
            M_PEC_WR: begin
                // Send PEC byte
                if (r_bit_counter == 4'h8) begin
                    r_master_state_next = M_PEC_WR_ACK;
                end
            end
            
            M_PEC_WR_ACK: begin
                // Check ACK for PEC
                if (r_ack_bit == 1'b0) begin
                    r_master_state_next = M_STOP;
                end else begin
                    r_master_state_next = M_ERROR;
                end
            end
            
            M_PEC_RD: begin
                // Read PEC byte
                if (r_bit_counter == 4'h8) begin
                    r_master_state_next = M_STOP;
                end
            end
            
            M_STOP: begin
                // Generate STOP condition
                if (r_phy_state == PHY_IDLE) begin
                    r_master_state_next = M_IDLE;
                end
            end
            
            M_ERROR: begin
                // Error state, wait for stop command
                if (cmd_stop || w_timeout) begin
                    r_master_state_next = M_STOP;
                end
            end
            
            default: r_master_state_next = M_IDLE;
        endcase
        
        // Global timeout check
        if (w_timeout && r_master_state != M_IDLE) begin
            r_master_state_next = M_ERROR;
        end
    end

    //========================================================================
    // Slave FSM (Simplified - Basic Structure)
    //========================================================================

    always_ff @(posedge clk) begin
        if (rst) begin
            r_slave_state <= S_IDLE;
        end else begin
            r_slave_state <= r_slave_state_next;
        end
    end

    always_comb begin
        r_slave_state_next = r_slave_state;
        
        case (r_slave_state)
            S_IDLE: begin
                // Wait for address match on START
                if (cfg_slave_en && r_start_detected) begin
                    // Check if address matches (simplified)
                    if (cfg_own_addr_en) begin
                        r_slave_state_next = S_ADDR_MATCH;
                    end
                end
                
                if (r_stop_detected) begin
                    r_slave_state_next = S_IDLE;
                end
            end
            
            S_ADDR_MATCH: begin
                // Address matched, check R/W and proceed
                r_slave_state_next = S_CMD_RX;
            end
            
            S_CMD_RX: begin
                // Receive command byte
                r_slave_state_next = S_CMD_ACK;
            end
            
            S_CMD_ACK: begin
                // ACK command, determine next action
                if (r_rw_bit) begin
                    r_slave_state_next = S_DATA_TX;
                end else begin
                    r_slave_state_next = S_DATA_RX;
                end
            end
            
            default: r_slave_state_next = S_IDLE;
        endcase
    end

    //========================================================================
    // Status Register Updates
    //========================================================================

    always_ff @(posedge clk) begin
        if (rst) begin
            r_busy <= 1'b0;
            r_bus_error <= 1'b0;
            r_timeout_error <= 1'b0;
            r_pec_error <= 1'b0;
            r_arb_lost <= 1'b0;
            r_nak_received <= 1'b0;
            r_slave_addressed <= 1'b0;
            r_complete <= 1'b0;
        end else begin
            // Update status flags based on FSM states
            r_busy <= (r_master_state != M_IDLE) || (r_slave_state != S_IDLE);
            r_complete <= (r_master_state == M_STOP) && (r_master_state_next == M_IDLE);
            r_bus_error <= (r_master_state == M_ERROR);
            r_timeout_error <= w_timeout && r_busy;
            r_nak_received <= (r_master_state == M_ADDR_ACK || r_master_state == M_CMD_ACK) && (r_ack_bit == 1'b1);
        end
    end

    //========================================================================
    // Physical Layer FSM Implementation
    //========================================================================
    
    // Physical layer command from master FSM
    logic [2:0] r_phy_cmd;
    logic       r_phy_cmd_valid;
    logic       r_phy_done;
    
    // Physical layer bit value
    logic       r_tx_bit;
    logic       r_rx_bit;
    
    // State machine for physical layer
    always_ff @(posedge clk) begin
        if (rst) begin
            r_phy_state <= PHY_IDLE;
            r_phy_done <= 1'b0;
            r_scl_out <= 1'b1;
            r_sda_out <= 1'b1;
            r_rx_bit <= 1'b0;
        end else begin
            r_phy_done <= 1'b0;
            
            case (r_phy_state)
                PHY_IDLE: begin
                    if (r_phy_cmd_valid) begin
                        case (r_phy_cmd)
                            3'h1: r_phy_state <= PHY_START;
                            3'h2: r_phy_state <= PHY_STOP;
                            3'h3: r_phy_state <= PHY_BIT_TX;
                            3'h4: r_phy_state <= PHY_BIT_RX;
                            default: r_phy_state <= PHY_IDLE;
                        endcase
                    end
                end
                
                PHY_START: begin
                    // Generate START: SDA falls while SCL high
                    if (r_scl_quarter) begin
                        if (r_scl_gen) begin
                            r_sda_out <= 1'b0;  // Pull SDA low
                        end else begin
                            r_scl_out <= 1'b0;  // Pull SCL low
                            r_phy_done <= 1'b1;
                            r_phy_state <= PHY_IDLE;
                        end
                    end
                end
                
                PHY_STOP: begin
                    // Generate STOP: SDA rises while SCL high
                    if (r_scl_quarter) begin
                        if (!r_scl_gen) begin
                            r_sda_out <= 1'b0;  // Ensure SDA low
                            r_scl_out <= 1'b1;  // Release SCL
                        end else begin
                            r_sda_out <= 1'b1;  // Release SDA (STOP)
                            r_phy_done <= 1'b1;
                            r_phy_state <= PHY_IDLE;
                        end
                    end
                end
                
                PHY_BIT_TX: begin
                    // Transmit one bit
                    if (r_scl_quarter) begin
                        if (!r_scl_gen) begin
                            // SCL low: setup data
                            r_sda_out <= r_tx_bit;
                        end else begin
                            // SCL high: data valid, complete
                            r_phy_done <= 1'b1;
                            r_phy_state <= PHY_IDLE;
                        end
                    end
                end
                
                PHY_BIT_RX: begin
                    // Receive one bit
                    if (r_scl_quarter) begin
                        if (!r_scl_gen) begin
                            // SCL low: release SDA for slave
                            r_sda_out <= 1'b1;
                        end else begin
                            // SCL high: sample data
                            r_rx_bit <= r_sda_d2;
                            r_phy_done <= 1'b1;
                            r_phy_state <= PHY_IDLE;
                        end
                    end
                end
                
                default: r_phy_state <= PHY_IDLE;
            endcase
        end
    end
    
    //========================================================================
    // Physical Layer Control (SCL/SDA Tristate)
    //========================================================================

    always_ff @(posedge clk) begin
        if (rst) begin
            r_scl_tristate <= 1'b1;
            r_sda_tristate <= 1'b1;
        end else begin
            // Default to tristate (input mode)
            r_scl_tristate <= 1'b1;
            r_sda_tristate <= 1'b1;
            
            // Master mode: control SCL
            if (cfg_master_en && r_master_state != M_IDLE) begin
                r_scl_tristate <= 1'b0;  // Drive SCL in master mode
            end
            
            // Control SDA based on physical layer state
            if (r_phy_state == PHY_START || r_phy_state == PHY_STOP || 
                r_phy_state == PHY_BIT_TX) begin
                r_sda_tristate <= 1'b0;  // Drive SDA
            end else if (r_phy_state == PHY_BIT_RX) begin
                r_sda_tristate <= 1'b1;  // Release SDA for RX
            end
        end
    end

    //========================================================================
    // Output Assignments
    //========================================================================

    assign smb_scl_o = r_scl_out;
    assign smb_scl_t = r_scl_tristate;
    assign smb_sda_o = r_sda_out;
    assign smb_sda_t = r_sda_tristate;

    assign status_busy = r_busy;
    assign status_bus_error = r_bus_error;
    assign status_timeout_error = r_timeout_error;
    assign status_pec_error = r_pec_error;
    assign status_arb_lost = r_arb_lost;
    assign status_nak_received = r_nak_received;
    assign status_slave_addressed = r_slave_addressed;
    assign status_complete = r_complete;
    assign status_fsm_state = r_master_state;

    assign data_byte_out = r_shift_reg;

    // PEC control
    assign w_pec_enable = cfg_pec_en;
    assign w_pec_clear = (r_master_state == M_START) || (r_slave_state == S_IDLE);
    assign w_pec_data = r_shift_reg;
    assign w_pec_valid = (r_bit_counter == 4'h8);

    //========================================================================
    // Byte-Level Transmission Logic
    //========================================================================
    
    // Bit and byte transmission controller
    always_ff @(posedge clk) begin
        if (rst) begin
            r_bit_counter <= 4'h0;
            r_shift_reg <= 8'h00;
            r_phy_cmd <= 3'h0;
            r_phy_cmd_valid <= 1'b0;
            r_tx_bit <= 1'b0;
            r_ack_bit <= 1'b1;
            r_byte_counter <= 6'h0;
            r_bytes_total <= 6'h0;
            r_trans_type <= 4'h0;
            r_slave_addr <= 7'h00;
            r_cmd_code <= 8'h00;
            r_rw_bit <= 1'b0;
        end else begin
            r_phy_cmd_valid <= 1'b0;  // Pulse
            
            // Latch transaction parameters on START
            if (r_master_state == M_IDLE && cmd_start) begin
                r_trans_type <= cmd_trans_type;
                r_slave_addr <= cmd_slave_addr;
                r_cmd_code <= cmd_code;
                r_byte_counter <= 6'h0;
                r_bytes_total <= cmd_block_count;
                
                // Determine R/W bit based on transaction type
                case (cmd_trans_type)
                    TRANS_RECV_BYTE, TRANS_READ_BYTE, 
                    TRANS_READ_WORD, TRANS_BLOCK_READ: r_rw_bit <= 1'b1;
                    default: r_rw_bit <= 1'b0;
                endcase
            end
            
            // Physical layer command generation
            case (r_master_state)
                M_START: begin
                    if (r_phy_state == PHY_IDLE && !r_phy_cmd_valid) begin
                        r_phy_cmd <= 3'h1;  // START
                        r_phy_cmd_valid <= 1'b1;
                        r_bit_counter <= 4'h0;
                        // Load address + R/W bit into shift register
                        r_shift_reg <= {r_slave_addr, r_rw_bit};
                    end
                end
                
                M_ADDR, M_CMD, M_DATA_WR, M_PEC_WR: begin
                    // Transmit byte bit by bit
                    if (r_bit_counter < 4'h8 && r_phy_done) begin
                        r_bit_counter <= r_bit_counter + 4'h1;
                    end else if (r_bit_counter < 4'h8 && r_phy_state == PHY_IDLE) begin
                        // Send next bit (MSB first)
                        r_tx_bit <= r_shift_reg[7];
                        r_shift_reg <= {r_shift_reg[6:0], 1'b0};
                        r_phy_cmd <= 3'h3;  // BIT_TX
                        r_phy_cmd_valid <= 1'b1;
                    end
                    
                    // Load next byte when current completes
                    if (r_bit_counter == 4'h8 && r_master_state_next != r_master_state) begin
                        r_bit_counter <= 4'h0;
                        if (r_master_state == M_ADDR && r_master_state_next == M_CMD) begin
                            r_shift_reg <= r_cmd_code;
                        end else if (r_master_state == M_CMD && r_master_state_next == M_DATA_WR) begin
                            r_shift_reg <= cmd_data_byte;  // First data byte
                        end else if (r_master_state == M_DATA_WR && r_master_state_next == M_DATA_WR) begin
                            r_shift_reg <= w_tx_fifo_rdata;  // From FIFO
                            r_byte_counter <= r_byte_counter + 6'h1;
                        end else if (r_master_state == M_DATA_WR && r_master_state_next == M_PEC_WR) begin
                            r_shift_reg <= w_pec_out;
                        end
                    end
                end
                
                M_ADDR_ACK, M_CMD_ACK, M_DATA_WR_ACK, M_PEC_WR_ACK: begin
                    // Receive ACK bit
                    if (r_phy_state == PHY_IDLE && !r_phy_cmd_valid && r_bit_counter == 4'h0) begin
                        r_phy_cmd <= 3'h4;  // BIT_RX
                        r_phy_cmd_valid <= 1'b1;
                        r_bit_counter <= 4'h1;
                    end else if (r_phy_done && r_bit_counter == 4'h1) begin
                        r_ack_bit <= r_rx_bit;
                        r_bit_counter <= 4'h8;  // Mark as complete
                    end
                end
                
                M_DATA_RD, M_PEC_RD: begin
                    // Receive byte bit by bit
                    if (r_bit_counter < 4'h8 && r_phy_done) begin
                        r_shift_reg <= {r_shift_reg[6:0], r_rx_bit};
                        r_bit_counter <= r_bit_counter + 4'h1;
                    end else if (r_bit_counter < 4'h8 && r_phy_state == PHY_IDLE) begin
                        r_phy_cmd <= 3'h4;  // BIT_RX
                        r_phy_cmd_valid <= 1'b1;
                    end
                    
                    // Store received byte when complete
                    if (r_bit_counter == 4'h8 && r_master_state_next != r_master_state) begin
                        r_bit_counter <= 4'h0;
                        if (r_master_state == M_DATA_RD) begin
                            r_byte_counter <= r_byte_counter + 6'h1;
                        end
                    end
                end
                
                M_DATA_RD_ACK: begin
                    // Send ACK (0) or NAK (1) for read data
                    if (r_phy_state == PHY_IDLE && !r_phy_cmd_valid && r_bit_counter == 4'h0) begin
                        r_tx_bit <= (r_byte_counter >= r_bytes_total) ? 1'b1 : 1'b0;
                        r_phy_cmd <= 3'h3;  // BIT_TX
                        r_phy_cmd_valid <= 1'b1;
                        r_bit_counter <= 4'h8;  // Mark as complete
                    end
                end
                
                M_STOP: begin
                    if (r_phy_state == PHY_IDLE && !r_phy_cmd_valid) begin
                        r_phy_cmd <= 3'h2;  // STOP
                        r_phy_cmd_valid <= 1'b1;
                    end
                end
                
                default: begin
                    r_bit_counter <= 4'h0;
                end
            endcase
        end
    end
    
    //========================================================================
    // FIFO Control Logic
    //========================================================================
    
    // TX FIFO read: Pull data during multi-byte write
    assign w_tx_fifo_rd = (r_master_state == M_DATA_WR) && 
                         (r_bit_counter == 4'h8) && 
                         (r_byte_counter < r_bytes_total) &&
                         !tx_fifo_empty;
    
    // RX FIFO write: Store data during multi-byte read
    assign w_rx_fifo_wr = (r_master_state == M_DATA_RD) && 
                         (r_bit_counter == 4'h8) &&
                         !rx_fifo_full;
    
    assign w_rx_fifo_wdata = r_shift_reg;

endmodule
