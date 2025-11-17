// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: pic_8259_config_regs
// Purpose: Configuration register wrapper for 8259 PIC - PeakRDL Wrapper
//
// This module wraps the PeakRDL-generated pic_8259_regs module and adds:
// - CMD/RSP to PeakRDL adapter (peakrdl_to_cmdrsp)
// - Edge detection for ICW/OCW writes (converts level to pulse)
// - Status register feedback from pic_8259_core
// - IMR bidirectional interface
//
// ARCHITECTURE:
//   cmd/rsp --> peakrdl_to_cmdrsp adapter --> pic_8259_regs (PeakRDL) --> hwif --> mapping --> PIC core
//
// Follows HPET/PIT pattern: separate generated registers from integration logic

`timescale 1ns / 1ps

`include "reset_defs.svh"

module pic_8259_config_regs
    import pic_8259_regs_pkg::*;
(
    input wire clk,
    input wire rst_n,  // Active-low reset

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

    // PIC Core Interface
    output wire        pic_enable,
    output wire        init_mode,
    output wire        auto_reset_init,

    // ICW configuration
    output wire        ic4,
    output wire        sngl,
    output wire        ltim,
    output wire [7:0]  vector_base,
    output wire [7:0]  cascade,
    output wire        aeoi,
    output wire [1:0]  buf_mode,
    output wire        sfnm,

    // ICW/OCW write strobes
    output wire        icw1_wr,
    output wire        icw2_wr,
    output wire        icw3_wr,
    output wire        icw4_wr,
    output wire        ocw2_wr,
    output wire        ocw3_wr,

    // OCW2/OCW3 command values
    output wire [2:0]  ocw2_irq_level,
    output wire [2:0]  ocw2_eoi_cmd,
    output wire [1:0]  ocw3_read_reg_cmd,
    output wire        ocw3_poll_cmd,
    output wire [1:0]  ocw3_smm_cmd,

    // IMR (OCW1) bidirectional interface
    output wire        imr_reg_wr,
    output wire [7:0]  imr_reg_out,
    input  wire [7:0]  imr_reg_in,

    // Status inputs (from pic_8259_core)
    input  wire [7:0]  irr_in,
    input  wire [7:0]  isr_in,
    input  wire        init_complete,
    input  wire [2:0]  icw_step,
    input  wire        int_output,
    input  wire [2:0]  highest_priority
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

    pic_8259_regs__in_t  hwif_in;
    pic_8259_regs__out_t hwif_out;

    //========================================================================
    // ICW/OCW Write Detection and Edge Generation
    //========================================================================

    logic r_icw1_wr_ack;
    logic r_icw2_wr_ack;
    logic r_icw3_wr_ack;
    logic r_icw4_wr_ack;
    logic r_ocw2_wr_ack;
    logic r_ocw3_wr_ack;
    logic r_imr_wr_ack;

    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            r_icw1_wr_ack <= 1'b0;
            r_icw2_wr_ack <= 1'b0;
            r_icw3_wr_ack <= 1'b0;
            r_icw4_wr_ack <= 1'b0;
            r_ocw2_wr_ack <= 1'b0;
            r_ocw3_wr_ack <= 1'b0;
            r_imr_wr_ack  <= 1'b0;
        end else begin
            r_icw1_wr_ack <= regblk_wr_ack && regblk_req_is_wr && (regblk_addr[11:0] == 12'h004);
            r_icw2_wr_ack <= regblk_wr_ack && regblk_req_is_wr && (regblk_addr[11:0] == 12'h008);
            r_icw3_wr_ack <= regblk_wr_ack && regblk_req_is_wr && (regblk_addr[11:0] == 12'h00C);
            r_icw4_wr_ack <= regblk_wr_ack && regblk_req_is_wr && (regblk_addr[11:0] == 12'h010);
            r_ocw2_wr_ack <= regblk_wr_ack && regblk_req_is_wr && (regblk_addr[11:0] == 12'h018);
            r_ocw3_wr_ack <= regblk_wr_ack && regblk_req_is_wr && (regblk_addr[11:0] == 12'h01C);
            r_imr_wr_ack  <= regblk_wr_ack && regblk_req_is_wr && (regblk_addr[11:0] == 12'h014);
        end
    )

    //========================================================================
    // Status Register Inputs (from pic_8259_core)
    //========================================================================

    assign hwif_in.PIC_IRR.irr.next = irr_in;
    assign hwif_in.PIC_ISR.isr.next = isr_in;
    assign hwif_in.PIC_STATUS.init_complete.next = init_complete;
    assign hwif_in.PIC_STATUS.icw_step.next = icw_step;
    assign hwif_in.PIC_STATUS.int_output.next = int_output;
    assign hwif_in.PIC_STATUS.highest_priority.next = highest_priority;

    //========================================================================
    // Auto-Reset Init Mode Logic
    //========================================================================
    // When auto_reset_init is set and ICW4 is written, automatically clear init_mode
    // The hwif_in.next value is automatically loaded when different from current value

    assign hwif_in.PIC_CONFIG.init_mode.next = (auto_reset_init && r_icw4_wr_ack) ? 1'b0 : hwif_out.PIC_CONFIG.init_mode.value;

    //========================================================================
    // IMR Bidirectional Interface
    //========================================================================

    assign hwif_in.PIC_OCW1.imr.next = imr_reg_in;

    //========================================================================
    // PeakRDL Generated Register File
    //========================================================================

    pic_8259_regs u_pic_8259_regs (
        .clk                   (clk),
        .rst                   (~rst_n),  // Convert active-low to active-high
        .s_cpuif_req           (regblk_req),
        .s_cpuif_req_is_wr     (regblk_req_is_wr),
        .s_cpuif_addr          (regblk_addr[5:0]),  // Only lower 6 bits needed
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

    //========================================================================
    // Output Assignments to PIC Core
    //========================================================================

    // Configuration signals (simple passthrough from hwif_out)
    assign pic_enable       = hwif_out.PIC_CONFIG.pic_enable.value;
    assign init_mode        = hwif_out.PIC_CONFIG.init_mode.value;
    assign auto_reset_init  = hwif_out.PIC_CONFIG.auto_reset_init.value;

    // ICW signals (write-only registers, hwif_out is safe to use)
    assign ic4          = hwif_out.PIC_ICW1.ic4.value;
    assign sngl         = hwif_out.PIC_ICW1.sngl.value;
    assign ltim         = hwif_out.PIC_ICW1.ltim.value;
    assign vector_base  = hwif_out.PIC_ICW2.vector_base.value;
    assign cascade      = hwif_out.PIC_ICW3.cascade.value;
    assign aeoi         = hwif_out.PIC_ICW4.aeoi.value;
    assign buf_mode     = hwif_out.PIC_ICW4.buf_mode.value;
    assign sfnm         = hwif_out.PIC_ICW4.sfnm.value;

    // ICW/OCW write strobes (registered)
    assign icw1_wr = r_icw1_wr_ack;
    assign icw2_wr = r_icw2_wr_ack;
    assign icw3_wr = r_icw3_wr_ack;
    assign icw4_wr = r_icw4_wr_ack;
    assign ocw2_wr = r_ocw2_wr_ack;
    assign ocw3_wr = r_ocw3_wr_ack;

    // OCW2/OCW3 command values
    assign ocw2_irq_level     = hwif_out.PIC_OCW2.irq_level.value;
    assign ocw2_eoi_cmd       = hwif_out.PIC_OCW2.eoi_cmd.value;
    assign ocw3_read_reg_cmd  = hwif_out.PIC_OCW3.read_reg_cmd.value;
    assign ocw3_poll_cmd      = hwif_out.PIC_OCW3.poll_cmd.value;
    assign ocw3_smm_cmd       = hwif_out.PIC_OCW3.smm_cmd.value;

    // IMR bidirectional signals
    assign imr_reg_wr  = r_imr_wr_ack;
    assign imr_reg_out = hwif_out.PIC_OCW1.imr.value;

endmodule
