// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: pit_config_regs
// Purpose: Configuration register wrapper for 8254 PIT - PeakRDL Wrapper
//
// This module wraps the PeakRDL-generated pit_regs module and adds:
// - CMD/RSP to PeakRDL adapter (peakrdl_to_cmdrsp)
// - Edge detection for control word writes (converts level to pulse)
// - Proper status register feedback from pit_core
// - Counter data bidirectional interface
//
// ARCHITECTURE:
//   cmd/rsp --> peakrdl_to_cmdrsp adapter --> pit_regs (PeakRDL) --> hwif --> mapping --> PIT core
//
// Follows HPET pattern: separate generated registers from integration logic

`timescale 1ns / 1ps

`include "reset_defs.svh"

module pit_config_regs
    import pit_regs_pkg::*;
(
    input wire clk,
    input wire rst_n,  // Active-low reset (changed from rst)

    // Command/Response Interface (from apb_slave)
    input  wire        cmd_valid,
    output wire        cmd_ready,
    input  wire        cmd_pwrite,
    input  wire [11:0] cmd_paddr,
    input  wire [31:0] cmd_pwdata,
    input  wire [3:0]  cmd_pstrb,

    output wire        rsp_valid,
    input  wire        rsp_ready,
    output wire [31:0] rsp_prdata,
    output wire        rsp_pslverr,

    // PIT Core Interface
    output wire        pit_enable,
    output wire        clock_select,

    output wire        control_wr,          // Pulse when control word written
    output wire        bcd,
    output wire [2:0]  mode,
    output wire [1:0]  rw_mode,
    output wire [1:0]  counter_select,

    output wire        counter0_data_wr,   // Pulse when counter 0 data written
    output wire [15:0] counter0_data,
    input  wire [15:0] counter0_readback,  // Current counter 0 value
    output wire        counter1_data_wr,   // Pulse when counter 1 data written
    output wire [15:0] counter1_data,
    input  wire [15:0] counter1_readback,  // Current counter 1 value
    output wire        counter2_data_wr,   // Pulse when counter 2 data written
    output wire [15:0] counter2_data,
    input  wire [15:0] counter2_readback,  // Current counter 2 value

    input  wire [7:0]  counter0_status,
    input  wire [7:0]  counter1_status,
    input  wire [7:0]  counter2_status
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
    // Instantiate CMD/RSP to PeakRDL Adapter
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
    // PeakRDL Register Interface Structures
    //========================================================================

    pit_regs__in_t  hwif_in;
    pit_regs__out_t hwif_out;

    // ========================================================================
    // Counter Data Write Detection and Capture (HPET Pattern)
    // ========================================================================
    //
    // Following HPET methodology: capture write data directly from regblk_wr_data
    // instead of relying on hwif_out (which has hw=rw conflict for read-back).
    //
    // The counter registers are hw=rw to allow hardware read-back of current count,
    // but this means we must capture SW writes before they get overridden by
    // hardware read-back values.
    //

    logic [15:0] last_sw_counter0_data;
    logic [15:0] last_sw_counter1_data;
    logic [15:0] last_sw_counter2_data;
    logic        counter0_data_written;
    logic        counter1_data_written;
    logic        counter2_data_written;

    // Detect writes based on address
    assign counter0_data_written = regblk_req && regblk_req_is_wr && (regblk_addr[11:0] == 12'h010);
    assign counter1_data_written = regblk_req && regblk_req_is_wr && (regblk_addr[11:0] == 12'h014);
    assign counter2_data_written = regblk_req && regblk_req_is_wr && (regblk_addr[11:0] == 12'h018);

    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            last_sw_counter0_data <= '0;
            last_sw_counter1_data <= '0;
            last_sw_counter2_data <= '0;
        end else begin
            // Capture SW-written values from write data bus
            if (counter0_data_written) begin
                last_sw_counter0_data <= regblk_wr_data[15:0];
            end
            if (counter1_data_written) begin
                last_sw_counter1_data <= regblk_wr_data[15:0];
            end
            if (counter2_data_written) begin
                last_sw_counter2_data <= regblk_wr_data[15:0];
            end
        end
    )

    // ========================================================================
    // Control Word Write Detection
    // ========================================================================
    //
    // Control word is write-only (sw=w, hw=r), so hwif_out works fine.
    // We still register the write acknowledge for timing consistency.
    //

    logic        r_control_wr_ack;

    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            r_control_wr_ack <= 1'b0;
        end else begin
            r_control_wr_ack <= regblk_wr_ack && regblk_req_is_wr && (regblk_addr[11:0] == 12'h004);
        end
    )

    //========================================================================
    // Status Register Inputs (from pit_core)
    //========================================================================

    assign hwif_in.PIT_STATUS.counter0_status.next = counter0_status;
    assign hwif_in.PIT_STATUS.counter1_status.next = counter1_status;
    assign hwif_in.PIT_STATUS.counter2_status.next = counter2_status;

    //========================================================================
    // Counter Data Bidirectional Interface
    //========================================================================
    //
    // Feed current counter values back to PeakRDL for readback
    // Per Intel 8254 spec: reading counter returns current count value
    //
    assign hwif_in.COUNTER0_DATA.counter0_data.next = counter0_readback;
    assign hwif_in.COUNTER1_DATA.counter1_data.next = counter1_readback;
    assign hwif_in.COUNTER2_DATA.counter2_data.next = counter2_readback;

    //========================================================================
    // PeakRDL Generated Register File
    //========================================================================

    pit_regs u_pit_regs (
        .clk                   (clk),
        .rst                   (~rst_n),  // Convert active-low to active-high
        .s_cpuif_req           (regblk_req),
        .s_cpuif_req_is_wr     (regblk_req_is_wr),
        .s_cpuif_addr          (regblk_addr[4:0]),  // Only lower 5 bits needed
        .s_cpuif_wr_data       (regblk_wr_data),
        .s_cpuif_wr_biten      (regblk_wr_biten),
        .s_cpuif_req_stall_wr  (regblk_req_stall_wr),
        .s_cpuif_req_stall_rd  (regblk_req_stall_rd),
        .s_cpuif_rd_ack        (regblk_rd_ack),
        .s_cpuif_rd_err        (regblk_rd_err),
        .s_cpuif_rd_data       (regblk_rd_data),
        .s_cpuif_wr_ack        (regblk_wr_ack),
        .s_cpuif_wr_err        (regblk_wr_err),
        .hwif_in               (hwif_in),
        .hwif_out              (hwif_out)
    );

    // ========================================================================
    // Output Assignments to PIT Core
    // ========================================================================

    // Configuration signals (simple passthrough from hwif_out)
    assign pit_enable   = hwif_out.PIT_CONFIG.pit_enable.value;
    assign clock_select = hwif_out.PIT_CONFIG.clock_select.value;

    // Control word signals (write-only registers, hwif_out is safe to use)
    assign bcd            = hwif_out.PIT_CONTROL.bcd.value;
    assign mode           = hwif_out.PIT_CONTROL.mode.value;
    assign rw_mode        = hwif_out.PIT_CONTROL.rw_mode.value;
    assign counter_select = hwif_out.PIT_CONTROL.counter_select.value;
    assign control_wr     = r_control_wr_ack;  // Registered write strobe

    // Counter data signals (captured from write bus, not hwif_out)
    // This prevents hw=rw read-back from overriding software writes
    assign counter0_data    = last_sw_counter0_data;
    assign counter1_data    = last_sw_counter1_data;
    assign counter2_data    = last_sw_counter2_data;
    assign counter0_data_wr = counter0_data_written;
    assign counter1_data_wr = counter1_data_written;
    assign counter2_data_wr = counter2_data_written;

endmodule
