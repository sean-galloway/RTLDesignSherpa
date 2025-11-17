// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: ioapic_config_regs
// Purpose: Configuration register wrapper for IOAPIC - PeakRDL Wrapper with Indirect Access
//
// Wrapper that instantiates PeakRDL-generated register block and implements
// Intel IOAPIC indirect register access mechanism (IOREGSEL/IOWIN).
//
// ARCHITECTURE:
//   cmd/rsp --> peakrdl_to_cmdrsp adapter --> IOREGSEL/IOWIN indirect access --> 
//   --> ioapic_regs (PeakRDL) --> hwif --> mapping --> IOAPIC core
//
// INDIRECT ACCESS METHOD:
//   Software accesses internal registers through two APB registers:
//   1. Write register offset to IOREGSEL (APB 0x00)
//   2. Read/write data via IOWIN (APB 0x04)
//
// This matches Intel 82093AA IOAPIC specification.

`timescale 1ns / 1ps

`include "reset_defs.svh"

module ioapic_config_regs
    import ioapic_regs_pkg::*;
#(
    parameter int NUM_IRQS = 24
)(
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

    // IOAPIC Core Interface - Configuration Outputs (per IRQ)
    output logic [7:0]  cfg_vector       [NUM_IRQS],
    output logic [2:0]  cfg_deliv_mode   [NUM_IRQS],
    output logic        cfg_dest_mode    [NUM_IRQS],
    output logic        cfg_polarity     [NUM_IRQS],
    output logic        cfg_trigger_mode [NUM_IRQS],
    output logic        cfg_mask         [NUM_IRQS],
    output logic [7:0]  cfg_destination  [NUM_IRQS],
    output logic [3:0]  cfg_ioapic_id,

    // Status inputs (from ioapic_core)
    input  logic        status_deliv_status [NUM_IRQS],
    input  logic        status_remote_irr   [NUM_IRQS],
    input  logic [3:0]  status_arb_id,

    // EOI interface pass-through
    output logic        eoi_out,
    output logic [7:0]  eoi_vector_out,
    input  logic        eoi_in,
    input  logic [7:0]  eoi_vector_in
);

    //========================================================================
    // Internal Signals for PeakRDL Passthrough Interface
    //========================================================================

    // From adapter (before indirect access translation)
    logic                adapter_req;
    logic                adapter_req_is_wr;
    logic [11:0]         adapter_addr;
    logic [31:0]         adapter_wr_data;
    logic [31:0]         adapter_wr_biten;
    logic                adapter_req_stall_wr;
    logic                adapter_req_stall_rd;
    logic                adapter_rd_ack;
    logic                adapter_rd_err;
    logic [31:0]         adapter_rd_data;
    logic                adapter_wr_ack;
    logic                adapter_wr_err;

    // To register block (after indirect access translation)
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

    // IOREGSEL register for indirect access
    logic [7:0]          ioregsel_value;

    //========================================================================
    // Hardware Interface Structs
    //========================================================================

    ioapic_regs__in_t  hwif_in;
    ioapic_regs__out_t hwif_out;

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

        // PeakRDL passthrough interface (to indirect access logic)
        .regblk_req         (adapter_req),
        .regblk_req_is_wr   (adapter_req_is_wr),
        .regblk_addr        (adapter_addr),
        .regblk_wr_data     (adapter_wr_data),
        .regblk_wr_biten    (adapter_wr_biten),
        .regblk_req_stall_wr(adapter_req_stall_wr),
        .regblk_req_stall_rd(adapter_req_stall_rd),
        .regblk_rd_ack      (adapter_rd_ack),
        .regblk_rd_err      (adapter_rd_err),
        .regblk_rd_data     (adapter_rd_data),
        .regblk_wr_ack      (adapter_wr_ack),
        .regblk_wr_err      (adapter_wr_err)
    );

    //========================================================================
    // IOREGSEL/IOWIN Indirect Access Logic
    //========================================================================

    // IOREGSEL register - stores the offset of the internal register to access
    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            ioregsel_value <= 8'h00;
        end else begin
            // Write to IOREGSEL (APB address 0x00)
            if (adapter_req && adapter_req_is_wr && (adapter_addr == 12'h000)) begin
                ioregsel_value <= adapter_wr_data[7:0];
            end
        end
    )

    // Address translation: convert IOWIN access to internal register access
    always_comb begin
        regblk_req = adapter_req;
        regblk_req_is_wr = adapter_req_is_wr;
        regblk_wr_data = adapter_wr_data;
        regblk_wr_biten = adapter_wr_biten;

        // Default: pass through address unchanged
        regblk_addr = adapter_addr;

        // If accessing IOWIN (APB address 0x04), translate to internal register
        if (adapter_addr == 12'h004) begin
            // Map internal offset to actual APB address
            // Internal offset 0x00 (IOAPICID) → APB 0x08
            // Internal offset 0x01 (IOAPICVER) → APB 0x0C
            // Internal offset 0x02 (IOAPICARB) → APB 0x10
            // Internal offset 0x10-0x3F (IOREDTBL) → APB 0x14 + (offset-0x10)*4

            case (ioregsel_value)
                8'h00: regblk_addr = 12'h008;  // IOAPICID
                8'h01: regblk_addr = 12'h00C;  // IOAPICVER
                8'h02: regblk_addr = 12'h010;  // IOAPICARB
                default: begin
                    // Redirection table: offset 0x10-0x3F
                    // Each IRQ has 2 registers (LO at even, HI at odd)
                    // IRQ N: LO at 0x10+N*2, HI at 0x11+N*2
                    // APB mapping: base 0x14, stride 8 bytes per IRQ
                    if (ioregsel_value >= 8'h10 && ioregsel_value <= 8'h3F) begin
                        logic [5:0] redir_offset;
                        redir_offset = ioregsel_value[5:0] - 6'h10;  // 0x00-0x2F
                        // LO/HI alternates: LO at even offset, HI at odd offset
                        regblk_addr = 12'h014 + {6'h00, redir_offset[5:1], 3'b000} +
                                     {11'h000, redir_offset[0], 2'b00};
                        // Explanation:
                        // redir_offset[5:1] = IRQ number (0-23)
                        // redir_offset[0] = 0 for LO, 1 for HI
                        // Base 0x14 + IRQ*8 + (LO/HI)*4
                    end else begin
                        regblk_addr = 12'h000;  // Invalid offset, access IOREGSEL
                    end
                end
            endcase
        end
    end

    // Response path: pass through unchanged
    assign adapter_req_stall_wr = regblk_req_stall_wr;
    assign adapter_req_stall_rd = regblk_req_stall_rd;
    assign adapter_rd_ack = regblk_rd_ack;
    assign adapter_rd_err = regblk_rd_err;
    assign adapter_rd_data = regblk_rd_data;
    assign adapter_wr_ack = regblk_wr_ack;
    assign adapter_wr_err = regblk_wr_err;

    //========================================================================
    // Instantiate PeakRDL-Generated Register Block
    //========================================================================

    ioapic_regs u_ioapic_regs (
        .clk                (clk),
        .rst                (~rst_n),  // PeakRDL uses active-high reset

        // Passthrough CPU interface
        .s_cpuif_req        (regblk_req),
        .s_cpuif_req_is_wr  (regblk_req_is_wr),
        .s_cpuif_addr       (regblk_addr[8:0]),
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
    // Map PeakRDL hwif Outputs to IOAPIC Core Configuration Inputs
    //========================================================================

    // IOAPIC ID
    assign cfg_ioapic_id = hwif_out.IOAPICID.apic_id.value;

    // Redirection table entries - map array to core
    genvar g;
    generate
        for (g = 0; g < NUM_IRQS; g++) begin : g_redir_cfg
            assign cfg_vector[g]       = hwif_out.IOREDTBL[g].REDIR_LO.vector.value;
            assign cfg_deliv_mode[g]   = hwif_out.IOREDTBL[g].REDIR_LO.deliv_mode.value;
            assign cfg_dest_mode[g]    = hwif_out.IOREDTBL[g].REDIR_LO.dest_mode.value;
            assign cfg_polarity[g]     = hwif_out.IOREDTBL[g].REDIR_LO.polarity.value;
            assign cfg_trigger_mode[g] = hwif_out.IOREDTBL[g].REDIR_LO.trigger_mode.value;
            assign cfg_mask[g]         = hwif_out.IOREDTBL[g].REDIR_LO.mask.value;
            assign cfg_destination[g]  = hwif_out.IOREDTBL[g].REDIR_HI.destination.value;
        end
    endgenerate

    //========================================================================
    // Map IOAPIC Core Outputs to PeakRDL hwif Inputs
    //========================================================================

    // Arbitration ID (read-only, from core)
    assign hwif_in.IOAPICARB.arb_id.next = status_arb_id;

    // Delivery status and Remote IRR (read-only fields, from core)
    generate
        for (g = 0; g < NUM_IRQS; g++) begin : g_redir_status
            assign hwif_in.IOREDTBL[g].REDIR_LO.deliv_status.next = status_deliv_status[g];
            assign hwif_in.IOREDTBL[g].REDIR_LO.remote_irr.next = status_remote_irr[g];
        end
    endgenerate

    //========================================================================
    // EOI Pass-Through (for future external EOI mechanism)
    //========================================================================
    
    // For MVP, EOI comes from external CPU interface
    assign eoi_out = eoi_in;
    assign eoi_vector_out = eoi_vector_in;

    //========================================================================
    // IOREGSEL/IOWIN Indirect Access Notes
    //========================================================================
    
    // Note: The indirect access mechanism (IOREGSEL at 0x00, IOWIN at 0x04)
    // is handled by the PeakRDL-generated logic. Software writes to IOREGSEL
    // to select the internal register, then accesses IOWIN to read/write the
    // selected register's data.
    //
    // The PeakRDL generator creates the necessary multiplexing logic based on
    // the register definitions in ioapic_regs.rdl. The IOREGSEL.regsel field
    // controls which internal register is visible through IOWIN.data.
    //
    // Internal register offsets (accessed via IOREGSEL):
    //   0x00: IOAPICID
    //   0x01: IOAPICVER
    //   0x02: IOAPICARB
    //   0x10: IOREDTBL[0].LO
    //   0x11: IOREDTBL[0].HI
    //   0x12: IOREDTBL[1].LO
    //   0x13: IOREDTBL[1].HI
    //   ...
    //   0x3E: IOREDTBL[23].LO
    //   0x3F: IOREDTBL[23].HI

endmodule
