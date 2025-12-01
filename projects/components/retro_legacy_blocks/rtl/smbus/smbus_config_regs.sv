// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: smbus_config_regs
// Purpose: Configuration register wrapper for SMBus - PeakRDL Wrapper
//
// Wrapper that instantiates PeakRDL-generated register block and adapter,
// mapping between the generated hwif signals and the SMBus core interface.
//
// ARCHITECTURE:
//   cmd/rsp --> peakrdl_to_cmdrsp adapter --> smbus_regs (PeakRDL) --> hwif --> mapping --> SMBus core
//
// Follows HPET pattern exactly - uses existing peakrdl_to_cmdrsp from converters/rtl/

`timescale 1ns / 1ps

`include "reset_defs.svh"

module smbus_config_regs
    import smbus_regs_pkg::*;
(
    input logic clk,
    input logic rst_n,  // Active-low reset

    // Command/Response Interface (from apb_slave)
    input  logic        cmd_valid,
    output logic        cmd_ready,
    input  logic        cmd_pwrite,
    input  logic [11:0] cmd_paddr,
    input  logic [31:0] cmd_pwdata,
    input  logic [3:0]  cmd_pstrb,

    output logic        rsp_valid,
    input  logic        rsp_ready,
    output logic [31:0] rsp_prdata,
    output logic        rsp_pslverr,

    // SMBus Core Interface - Configuration Outputs
    output logic        cfg_master_en,
    output logic        cfg_slave_en,
    output logic        cfg_pec_en,
    output logic        cfg_fast_mode,
    output logic        cfg_fifo_reset,
    output logic [15:0] cfg_clk_div,
    output logic [23:0] cfg_timeout,
    output logic [6:0]  cfg_own_addr,
    output logic        cfg_own_addr_en,

    // Command interface outputs
    output logic [3:0]  cmd_trans_type,
    output logic [7:0]  cmd_code,
    output logic [6:0]  cmd_slave_addr,
    output logic        cmd_start,
    output logic        cmd_stop,
    output logic [7:0]  cmd_data_byte,
    output logic [5:0]  cmd_block_count,

    // Status inputs (from smbus_core)
    input  logic        status_busy,
    input  logic        status_bus_error,
    input  logic        status_timeout_error,
    input  logic        status_pec_error,
    input  logic        status_arb_lost,
    input  logic        status_nak_received,
    input  logic        status_slave_addressed,
    input  logic        status_complete,
    input  logic [3:0]  status_fsm_state,

    // Data byte interface
    input  logic [7:0]  data_byte_in,
    output logic [7:0]  data_byte_out,

    // TX FIFO interface
    output logic [7:0]  tx_fifo_wdata,
    output logic        tx_fifo_wr,
    input  logic [5:0]  tx_fifo_level,
    input  logic        tx_fifo_full,
    input  logic        tx_fifo_empty,

    // RX FIFO interface
    input  logic [7:0]  rx_fifo_rdata,
    output logic        rx_fifo_rd,
    input  logic [5:0]  rx_fifo_level,
    input  logic        rx_fifo_full,
    input  logic        rx_fifo_empty,

    // PEC interface
    input  logic [7:0]  pec_value,
    output logic [7:0]  pec_expected,

    // Interrupt enables
    output logic        int_complete_en,
    output logic        int_error_en,
    output logic        int_tx_thresh_en,
    output logic        int_rx_thresh_en,
    output logic        int_slave_addr_en
);

    //========================================================================
    // Internal Signals for PeakRDL Passthrough Interface
    //========================================================================

    logic                regblk_req;
    logic                regblk_req_is_wr;
    logic [11:0]         regblk_addr;
    logic [31:0]         regblk_wr_data;
    logic [31:0]         regblk_wr_biten;
    logic                regblk_req_stall_wr;
    logic                regblk_req_stall_rd;
    logic                regblk_rd_ack;
    logic                regblk_rd_err;
    logic [31:0]         regblk_rd_data;
    logic                regblk_wr_ack;
    logic                regblk_wr_err;

    //========================================================================
    // Hardware Interface Structs
    //========================================================================

    smbus_regs__in_t  hwif_in;
    smbus_regs__out_t hwif_out;

    //========================================================================
    // Instantiate Protocol Adapter (from converters/rtl/)
    //========================================================================

    peakrdl_to_cmdrsp #(
        .ADDR_WIDTH(12),
        .DATA_WIDTH(32)
    ) u_adapter (
        .aclk               (clk),
        .aresetn            (rst_n),

        // CMD/RSP interface (external)
        .cmd_valid          (cmd_valid),
        .cmd_ready          (cmd_ready),
        .cmd_pwrite         (cmd_pwrite),
        .cmd_paddr          (cmd_paddr),
        .cmd_pwdata         (cmd_pwdata),
        .cmd_pstrb          (cmd_pstrb),

        .rsp_valid          (rsp_valid),
        .rsp_ready          (rsp_ready),
        .rsp_prdata         (rsp_prdata),
        .rsp_pslverr        (rsp_pslverr),

        // PeakRDL passthrough interface (to register block)
        .regblk_req         (regblk_req),
        .regblk_req_is_wr   (regblk_req_is_wr),
        .regblk_addr        (regblk_addr),
        .regblk_wr_data     (regblk_wr_data),
        .regblk_wr_biten    (regblk_wr_biten),
        .regblk_req_stall_wr(regblk_req_stall_wr),
        .regblk_req_stall_rd(regblk_req_stall_rd),
        .regblk_rd_ack      (regblk_rd_ack),
        .regblk_rd_err      (regblk_rd_err),
        .regblk_rd_data     (regblk_rd_data),
        .regblk_wr_ack      (regblk_wr_ack),
        .regblk_wr_err      (regblk_wr_err)
    );

    //========================================================================
    // Instantiate PeakRDL-Generated Register Block
    //========================================================================

    smbus_regs u_smbus_regs (
        .clk                (clk),
        .rst                (~rst_n),  // PeakRDL uses active-high reset

        // Passthrough CPU interface
        .s_cpuif_req        (regblk_req),
        .s_cpuif_req_is_wr  (regblk_req_is_wr),
        .s_cpuif_addr       (regblk_addr[5:0]),  // Only lower 6 bits needed for SMBus
        .s_cpuif_wr_data    (regblk_wr_data),
        .s_cpuif_wr_biten   (regblk_wr_biten),
        .s_cpuif_req_stall_wr(regblk_req_stall_wr),
        .s_cpuif_req_stall_rd(regblk_req_stall_rd),
        .s_cpuif_rd_ack     (regblk_rd_ack),
        .s_cpuif_rd_err     (regblk_rd_err),
        .s_cpuif_rd_data    (regblk_rd_data),
        .s_cpuif_wr_ack     (regblk_wr_ack),
        .s_cpuif_wr_err     (regblk_wr_err),

        // Hardware interface
        .hwif_in            (hwif_in),
        .hwif_out           (hwif_out)
    );

    //========================================================================
    // Map PeakRDL hwif Outputs to SMBus Core Configuration Inputs
    //========================================================================

    // Control register
    assign cfg_master_en  = hwif_out.SMBUS_CONTROL.master_en.value;
    assign cfg_slave_en   = hwif_out.SMBUS_CONTROL.slave_en.value;
    assign cfg_pec_en     = hwif_out.SMBUS_CONTROL.pec_en.value;
    assign cfg_fast_mode  = hwif_out.SMBUS_CONTROL.fast_mode.value;
    assign cfg_fifo_reset = hwif_out.SMBUS_CONTROL.fifo_reset.value;

    // Clock and timeout
    assign cfg_clk_div    = hwif_out.SMBUS_CLK_DIV.clk_div.value;
    assign cfg_timeout    = hwif_out.SMBUS_TIMEOUT.timeout.value;

    // Slave address
    assign cfg_own_addr     = hwif_out.SMBUS_OWN_ADDR.own_addr.value;
    assign cfg_own_addr_en  = hwif_out.SMBUS_OWN_ADDR.addr_en.value;

    // Command interface
    assign cmd_trans_type  = hwif_out.SMBUS_COMMAND.trans_type.value;
    assign cmd_code        = hwif_out.SMBUS_COMMAND.cmd_code.value;
    assign cmd_start       = hwif_out.SMBUS_COMMAND.start.value;
    assign cmd_stop        = hwif_out.SMBUS_COMMAND.stop.value;
    assign cmd_slave_addr  = hwif_out.SMBUS_SLAVE_ADDR.slave_addr.value;
    assign cmd_data_byte   = hwif_out.SMBUS_DATA.data.value;
    assign cmd_block_count = hwif_out.SMBUS_BLOCK_COUNT.block_count.value;

    // Interrupt enables
    assign int_complete_en   = hwif_out.SMBUS_INT_ENABLE.complete_en.value;
    assign int_error_en      = hwif_out.SMBUS_INT_ENABLE.error_en.value;
    assign int_tx_thresh_en  = hwif_out.SMBUS_INT_ENABLE.tx_thresh_en.value;
    assign int_rx_thresh_en  = hwif_out.SMBUS_INT_ENABLE.rx_thresh_en.value;
    assign int_slave_addr_en = hwif_out.SMBUS_INT_ENABLE.slave_addr_en.value;

    // PEC expected value
    assign pec_expected = hwif_out.SMBUS_PEC.pec.value;

    //========================================================================
    // TX FIFO Write Detection and Data
    //========================================================================
    // Note: We detect TX FIFO writes by monitoring the cpuif signals directly
    // since the tx_data field doesn't have swmod enabled in the RDL.
    // TX_FIFO register is at offset 0x014 (byte address)

    logic r_tx_fifo_wr_prev;
    logic w_tx_fifo_write_req;

    // Detect write request to TX_FIFO register (address 0x014)
    assign w_tx_fifo_write_req = regblk_req && regblk_req_is_wr &&
                                  (regblk_addr[5:0] == 6'h14);

    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            r_tx_fifo_wr_prev <= 1'b0;
        end else begin
            r_tx_fifo_wr_prev <= w_tx_fifo_write_req;
        end
    )

    // Detect SW write to TX_FIFO register (rising edge of write request)
    assign tx_fifo_wr = w_tx_fifo_write_req && !r_tx_fifo_wr_prev;
    assign tx_fifo_wdata = hwif_out.SMBUS_TX_FIFO.tx_data.value;

    //========================================================================
    // RX FIFO Read Detection  
    //========================================================================

    logic r_rx_fifo_rd_prev;
    
    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            r_rx_fifo_rd_prev <= 1'b0;
        end else begin
            // Detect read of RX_FIFO register
            r_rx_fifo_rd_prev <= (regblk_req && !regblk_req_is_wr && 
                                 (regblk_addr[5:0] == 6'h18));
        end
    )

    assign rx_fifo_rd = (regblk_req && !regblk_req_is_wr && 
                        (regblk_addr[5:0] == 6'h18)) && !r_rx_fifo_rd_prev;

    //========================================================================
    // Data Byte Output
    //========================================================================
    assign data_byte_out = hwif_out.SMBUS_DATA.data.value;

    //========================================================================
    // Map SMBus Core Outputs to PeakRDL hwif Inputs
    //========================================================================

    // Status register inputs (hardware writes)
    assign hwif_in.SMBUS_STATUS.busy.next = status_busy;
    assign hwif_in.SMBUS_STATUS.bus_error.next = status_bus_error;
    assign hwif_in.SMBUS_STATUS.timeout_error.next = status_timeout_error;
    assign hwif_in.SMBUS_STATUS.pec_error.next = status_pec_error;
    assign hwif_in.SMBUS_STATUS.arb_lost.next = status_arb_lost;
    assign hwif_in.SMBUS_STATUS.nak_received.next = status_nak_received;
    assign hwif_in.SMBUS_STATUS.slave_addressed.next = status_slave_addressed;
    assign hwif_in.SMBUS_STATUS.complete.next = status_complete;
    assign hwif_in.SMBUS_STATUS.fsm_state.next = status_fsm_state;

    // RX FIFO data (hardware writes)
    assign hwif_in.SMBUS_RX_FIFO.rx_data.next = rx_fifo_rdata;

    // FIFO status (hardware writes)
    assign hwif_in.SMBUS_FIFO_STATUS.tx_level.next = tx_fifo_level;
    assign hwif_in.SMBUS_FIFO_STATUS.tx_full.next = tx_fifo_full;
    assign hwif_in.SMBUS_FIFO_STATUS.tx_empty.next = tx_fifo_empty;
    assign hwif_in.SMBUS_FIFO_STATUS.rx_level.next = rx_fifo_level;
    assign hwif_in.SMBUS_FIFO_STATUS.rx_full.next = rx_fifo_full;
    assign hwif_in.SMBUS_FIFO_STATUS.rx_empty.next = rx_fifo_empty;

    // PEC value (hardware writes)
    assign hwif_in.SMBUS_PEC.pec.next = pec_value;

    // Data byte input (hardware writes)
    assign hwif_in.SMBUS_DATA.data.next = data_byte_in;

    // Block count (hardware can update)
    assign hwif_in.SMBUS_BLOCK_COUNT.block_count.next = hwif_out.SMBUS_BLOCK_COUNT.block_count.value;

    //========================================================================
    // Interrupt Status Handling (W1C with edge detection)
    //========================================================================

    // Edge detection for interrupt status flags
    logic r_status_complete_prev;
    logic r_status_error_prev;
    logic w_complete_edge, w_error_edge;

    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            r_status_complete_prev <= 1'b0;
            r_status_error_prev <= 1'b0;
        end else begin
            r_status_complete_prev <= status_complete;
            r_status_error_prev <= (status_bus_error || status_timeout_error || 
                                   status_pec_error);
        end
    )

    // Rising edge detection
    assign w_complete_edge = status_complete && !r_status_complete_prev;
    assign w_error_edge = (status_bus_error || status_timeout_error || status_pec_error) && 
                         !r_status_error_prev;

    // Feed edge pulses to PeakRDL interrupt status (W1C fields)
    assign hwif_in.SMBUS_INT_STATUS.complete_int.next = w_complete_edge;
    assign hwif_in.SMBUS_INT_STATUS.error_int.next = w_error_edge;
    assign hwif_in.SMBUS_INT_STATUS.tx_thresh_int.next = tx_fifo_empty;
    assign hwif_in.SMBUS_INT_STATUS.rx_thresh_int.next = !rx_fifo_empty;
    assign hwif_in.SMBUS_INT_STATUS.slave_addr_int.next = status_slave_addressed;

    //========================================================================
    // Auto-Clear Fields (fifo_reset, soft_reset, start, stop)
    //========================================================================

    // These fields auto-clear after being set
    assign hwif_in.SMBUS_CONTROL.fifo_reset.next = 1'b0;
    assign hwif_in.SMBUS_CONTROL.soft_reset.next = 1'b0;
    assign hwif_in.SMBUS_COMMAND.start.next = 1'b0;
    assign hwif_in.SMBUS_COMMAND.stop.next = 1'b0;

endmodule
