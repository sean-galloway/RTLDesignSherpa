// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: pm_acpi_config_regs
// Purpose: Configuration register wrapper for PM_ACPI - PeakRDL Wrapper
//
// Wrapper that instantiates PeakRDL-generated register block and adapter,
// mapping between the generated hwif signals and the PM_ACPI core interface.
//
// ARCHITECTURE:
//   cmd/rsp --> peakrdl_to_cmdrsp adapter --> pm_acpi_regs (PeakRDL) --> hwif --> mapping --> PM_ACPI core
//
// Follows HPET/SMBus pattern exactly - uses existing peakrdl_to_cmdrsp from converters/rtl/

`timescale 1ns / 1ps

`include "reset_defs.svh"

module pm_acpi_config_regs
    import pm_acpi_regs_pkg::*;
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

    // PM_ACPI Core Interface - Configuration Outputs
    output logic        cfg_acpi_enable,
    output logic        cfg_pm_timer_enable,
    output logic        cfg_gpe_enable,
    output logic        cfg_low_power_req,
    output logic [2:0]  cfg_sleep_type,
    output logic        cfg_sleep_enable,
    output logic        cfg_pwrbtn_ovr,
    output logic        cfg_slpbtn_ovr,
    output logic        cfg_pm1_tmr_en,
    output logic        cfg_pm1_pwrbtn_en,
    output logic        cfg_pm1_slpbtn_en,
    output logic        cfg_pm1_rtc_en,
    output logic [15:0] cfg_pm_timer_div,
    output logic [31:0] cfg_gpe_enables,
    output logic [31:0] cfg_clk_gate_ctrl,
    output logic [7:0]  cfg_pwr_domain_ctrl,
    output logic        cfg_gpe_wake_en,
    output logic        cfg_pwrbtn_wake_en,
    output logic        cfg_rtc_wake_en,
    output logic        cfg_ext_wake_en,
    output logic        cfg_pme_enable,
    output logic        cfg_wake_enable,
    output logic        cfg_timer_ovf_enable,
    output logic        cfg_state_trans_enable,
    output logic        cfg_pm1_enable,
    output logic        cfg_gpe_int_enable,

    // Status inputs (from pm_acpi_core)
    input  logic [1:0]  status_current_state,
    input  logic        status_pme,
    input  logic        status_wake,
    input  logic        status_timer_overflow,
    input  logic        status_state_transition,
    input  logic        status_pm1_tmr,
    input  logic        status_pm1_pwrbtn,
    input  logic        status_pm1_slpbtn,
    input  logic        status_pm1_rtc,
    input  logic        status_pm1_wake,
    input  logic [31:0] status_pm_timer_value,
    input  logic [31:0] status_gpe_status,
    input  logic [31:0] status_clk_gate_status,
    input  logic [7:0]  status_pwr_domain_status,
    input  logic        status_gpe_wake,
    input  logic        status_pwrbtn_wake,
    input  logic        status_rtc_wake,
    input  logic        status_ext_wake,
    input  logic        status_por_reset,
    input  logic        status_wdt_reset,
    input  logic        status_sw_reset,
    input  logic        status_ext_reset
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

    pm_acpi_regs__in_t  hwif_in;
    pm_acpi_regs__out_t hwif_out;

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

    pm_acpi_regs u_pm_acpi_regs (
        .clk                (clk),
        .rst                (~rst_n),  // PeakRDL uses active-high reset

        // Passthrough CPU interface
        .s_cpuif_req        (regblk_req),
        .s_cpuif_req_is_wr  (regblk_req_is_wr),
        .s_cpuif_addr       (regblk_addr[8:0]),  // Lower 9 bits for PM_ACPI address space
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
    // Map PeakRDL hwif Outputs to PM_ACPI Core Configuration Inputs
    //========================================================================

    // ACPI Control register
    assign cfg_acpi_enable = hwif_out.ACPI_CONTROL.acpi_enable.value;
    assign cfg_pm_timer_enable = hwif_out.ACPI_CONTROL.pm_timer_enable.value;
    assign cfg_gpe_enable = hwif_out.ACPI_CONTROL.gpe_enable.value;
    assign cfg_low_power_req = hwif_out.ACPI_CONTROL.low_power_req.value;

    // PM1 Control register
    assign cfg_sleep_type = hwif_out.PM1_CONTROL.sleep_type.value;
    assign cfg_sleep_enable = hwif_out.PM1_CONTROL.sleep_enable.value;
    assign cfg_pwrbtn_ovr = hwif_out.PM1_CONTROL.pwrbtn_ovr.value;
    assign cfg_slpbtn_ovr = hwif_out.PM1_CONTROL.slpbtn_ovr.value;

    // PM1 Enable register
    assign cfg_pm1_tmr_en = hwif_out.PM1_ENABLE.tmr_en.value;
    assign cfg_pm1_pwrbtn_en = hwif_out.PM1_ENABLE.pwrbtn_en.value;
    assign cfg_pm1_slpbtn_en = hwif_out.PM1_ENABLE.slpbtn_en.value;
    assign cfg_pm1_rtc_en = hwif_out.PM1_ENABLE.rtc_en.value;

    // PM Timer configuration
    assign cfg_pm_timer_div = hwif_out.PM_TIMER_CONFIG.timer_div.value;

    // GPE enables (combine low and high)
    assign cfg_gpe_enables = {hwif_out.GPE0_ENABLE_HI.gpe_enable.value, 
                              hwif_out.GPE0_ENABLE_LO.gpe_enable.value};

    // Clock gate control
    assign cfg_clk_gate_ctrl = hwif_out.CLOCK_GATE_CTRL.clk_gate_ctrl.value;

    // Power domain control
    assign cfg_pwr_domain_ctrl = hwif_out.POWER_DOMAIN_CTRL.pwr_domain_ctrl.value;

    // Wake enables
    assign cfg_gpe_wake_en = hwif_out.WAKE_ENABLE.gpe_wake_en.value;
    assign cfg_pwrbtn_wake_en = hwif_out.WAKE_ENABLE.pwrbtn_wake_en.value;
    assign cfg_rtc_wake_en = hwif_out.WAKE_ENABLE.rtc_wake_en.value;
    assign cfg_ext_wake_en = hwif_out.WAKE_ENABLE.ext_wake_en.value;

    // Interrupt enables
    assign cfg_pme_enable = hwif_out.ACPI_INT_ENABLE.pme_enable.value;
    assign cfg_wake_enable = hwif_out.ACPI_INT_ENABLE.wake_enable.value;
    assign cfg_timer_ovf_enable = hwif_out.ACPI_INT_ENABLE.timer_ovf_enable.value;
    assign cfg_state_trans_enable = hwif_out.ACPI_INT_ENABLE.state_trans_enable.value;
    assign cfg_pm1_enable = hwif_out.ACPI_INT_ENABLE.pm1_enable.value;
    assign cfg_gpe_int_enable = hwif_out.ACPI_INT_ENABLE.gpe_int_enable.value;

    //========================================================================
    // Map PM_ACPI Core Outputs to PeakRDL hwif Inputs
    //========================================================================

    // ACPI Control - current state (hardware writes)
    assign hwif_in.ACPI_CONTROL.current_state.next = status_current_state;

    // ACPI Status - edge detection for W1C fields
    logic r_status_pme_prev;
    logic r_status_wake_prev;
    logic r_status_timer_ovf_prev;
    logic r_status_state_trans_prev;
    
    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            r_status_pme_prev <= 1'b0;
            r_status_wake_prev <= 1'b0;
            r_status_timer_ovf_prev <= 1'b0;
            r_status_state_trans_prev <= 1'b0;
        end else begin
            r_status_pme_prev <= status_pme;
            r_status_wake_prev <= status_wake;
            r_status_timer_ovf_prev <= status_timer_overflow;
            r_status_state_trans_prev <= status_state_transition;
        end
    )

    // Edge detection for sticky status bits
    logic w_pme_edge, w_wake_edge, w_timer_ovf_edge, w_state_trans_edge;
    assign w_pme_edge = status_pme && !r_status_pme_prev;
    assign w_wake_edge = status_wake && !r_status_wake_prev;
    assign w_timer_ovf_edge = status_timer_overflow && !r_status_timer_ovf_prev;
    assign w_state_trans_edge = status_state_transition && !r_status_state_trans_prev;

    // Feed edges to PeakRDL W1C status fields
    assign hwif_in.ACPI_STATUS.pme_status.hwset = w_pme_edge;
    assign hwif_in.ACPI_STATUS.wake_status.hwset = w_wake_edge;
    assign hwif_in.ACPI_STATUS.timer_overflow.hwset = w_timer_ovf_edge;
    assign hwif_in.ACPI_STATUS.state_transition.hwset = w_state_trans_edge;

    // ACPI Interrupt Status - edge detection for W1C fields
    assign hwif_in.ACPI_INT_STATUS.pme_int.hwset = w_pme_edge;
    assign hwif_in.ACPI_INT_STATUS.wake_int.hwset = w_wake_edge;
    assign hwif_in.ACPI_INT_STATUS.timer_ovf_int.hwset = w_timer_ovf_edge;
    assign hwif_in.ACPI_INT_STATUS.state_trans_int.hwset = w_state_trans_edge;
    
    // PM1 status also sets interrupt bits
    logic r_status_pm1_prev;
    logic r_status_gpe_prev;
    
    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            r_status_pm1_prev <= 1'b0;
            r_status_gpe_prev <= 1'b0;
        end else begin
            r_status_pm1_prev <= status_pm1_tmr || status_pm1_pwrbtn || status_pm1_slpbtn;
            r_status_gpe_prev <= |status_gpe_status;
        end
    )

    logic w_pm1_edge, w_gpe_edge;
    assign w_pm1_edge = (status_pm1_tmr || status_pm1_pwrbtn || status_pm1_slpbtn) && !r_status_pm1_prev;
    assign w_gpe_edge = (|status_gpe_status) && !r_status_gpe_prev;

    assign hwif_in.ACPI_INT_STATUS.pm1_int.hwset = w_pm1_edge;
    assign hwif_in.ACPI_INT_STATUS.gpe_int.hwset = w_gpe_edge;

    // PM1 Status - edge detection for W1C fields
    logic r_pm1_tmr_prev, r_pm1_pwrbtn_prev, r_pm1_slpbtn_prev, r_pm1_rtc_prev, r_pm1_wake_prev;
    
    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            r_pm1_tmr_prev <= 1'b0;
            r_pm1_pwrbtn_prev <= 1'b0;
            r_pm1_slpbtn_prev <= 1'b0;
            r_pm1_rtc_prev <= 1'b0;
            r_pm1_wake_prev <= 1'b0;
        end else begin
            r_pm1_tmr_prev <= status_pm1_tmr;
            r_pm1_pwrbtn_prev <= status_pm1_pwrbtn;
            r_pm1_slpbtn_prev <= status_pm1_slpbtn;
            r_pm1_rtc_prev <= status_pm1_rtc;
            r_pm1_wake_prev <= status_pm1_wake;
        end
    )

    assign hwif_in.PM1_STATUS.tmr_sts.hwset = status_pm1_tmr && !r_pm1_tmr_prev;
    assign hwif_in.PM1_STATUS.pwrbtn_sts.hwset = status_pm1_pwrbtn && !r_pm1_pwrbtn_prev;
    assign hwif_in.PM1_STATUS.slpbtn_sts.hwset = status_pm1_slpbtn && !r_pm1_slpbtn_prev;
    assign hwif_in.PM1_STATUS.rtc_sts.hwset = status_pm1_rtc && !r_pm1_rtc_prev;
    assign hwif_in.PM1_STATUS.wak_sts.hwset = status_pm1_wake && !r_pm1_wake_prev;

    // PM Timer value (hardware writes, read-only from SW)
    assign hwif_in.PM_TIMER_VALUE.timer_value.next = status_pm_timer_value;

    // GPE Status - Edge detection on the sticky status from pm_acpi_core.
    // When hwset is asserted, the PeakRDL register latches the 'next' value as a SET
    // (not a replace), so we pass the edge bits to 'next'. The W1C behavior in PeakRDL
    // handles clearing. We don't want to continuously re-assert from the sticky status.
    logic [31:0] r_gpe_status_prev;
    logic [31:0] w_gpe_status_edge;

    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            r_gpe_status_prev <= 32'h0;
        end else begin
            r_gpe_status_prev <= status_gpe_status;
        end
    )

    // Detect new bits being set in the sticky status from pm_acpi_core
    assign w_gpe_status_edge = status_gpe_status & ~r_gpe_status_prev;

    // GPE status to registers (split into low and high)
    // hwset triggers when any new bit is set in edge detection
    // next provides the specific edge bits (not the full sticky status)
    // This allows W1C to clear bits that aren't being newly set
    assign hwif_in.GPE0_STATUS_LO.gpe_status.hwset = |w_gpe_status_edge[15:0];
    assign hwif_in.GPE0_STATUS_LO.gpe_status.next = w_gpe_status_edge[15:0];

    assign hwif_in.GPE0_STATUS_HI.gpe_status.hwset = |w_gpe_status_edge[31:16];
    assign hwif_in.GPE0_STATUS_HI.gpe_status.next = w_gpe_status_edge[31:16];

    // Clock gate status (read-only)
    assign hwif_in.CLOCK_GATE_STATUS.clk_gate_status.next = status_clk_gate_status;

    // Power domain status (read-only)
    assign hwif_in.POWER_DOMAIN_STATUS.pwr_domain_status.next = status_pwr_domain_status;

    // Wake Status - edge detection for W1C fields
    logic r_gpe_wake_prev, r_pwrbtn_wake_prev, r_rtc_wake_prev, r_ext_wake_prev;
    
    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            r_gpe_wake_prev <= 1'b0;
            r_pwrbtn_wake_prev <= 1'b0;
            r_rtc_wake_prev <= 1'b0;
            r_ext_wake_prev <= 1'b0;
        end else begin
            r_gpe_wake_prev <= status_gpe_wake;
            r_pwrbtn_wake_prev <= status_pwrbtn_wake;
            r_rtc_wake_prev <= status_rtc_wake;
            r_ext_wake_prev <= status_ext_wake;
        end
    )

    assign hwif_in.WAKE_STATUS.gpe_wake.hwset = status_gpe_wake && !r_gpe_wake_prev;
    assign hwif_in.WAKE_STATUS.pwrbtn_wake.hwset = status_pwrbtn_wake && !r_pwrbtn_wake_prev;
    assign hwif_in.WAKE_STATUS.rtc_wake.hwset = status_rtc_wake && !r_rtc_wake_prev;
    assign hwif_in.WAKE_STATUS.ext_wake.hwset = status_ext_wake && !r_ext_wake_prev;

    // Reset Status (read-only)
    assign hwif_in.RESET_STATUS.por_reset.next = status_por_reset;
    assign hwif_in.RESET_STATUS.wdt_reset.next = status_wdt_reset;
    assign hwif_in.RESET_STATUS.sw_reset.next = status_sw_reset;
    assign hwif_in.RESET_STATUS.ext_reset.next = status_ext_reset;

    //========================================================================
    // Auto-Clear Fields (soft_reset, low_power_req, sleep_enable)
    //========================================================================

    // These fields auto-clear after being set
    assign hwif_in.ACPI_CONTROL.soft_reset.next = 1'b0;
    assign hwif_in.ACPI_CONTROL.low_power_req.next = 1'b0;
    assign hwif_in.PM1_CONTROL.sleep_enable.next = 1'b0;
    assign hwif_in.RESET_CTRL.sys_reset.next = 1'b0;
    assign hwif_in.RESET_CTRL.periph_reset.next = 1'b0;

endmodule
