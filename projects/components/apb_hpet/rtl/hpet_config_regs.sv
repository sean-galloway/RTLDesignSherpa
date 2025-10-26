// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: hpet_config_regs
// Purpose: Hpet Config Regs module
//
// Documentation: projects/components/hpet_config_regs.sv/PRD.md
// Subsystem: hpet_config_regs.sv
//
// Author: sean galloway
// Created: 2025-10-18

/**
* ============================================================================
* HPET Configuration Registers - PeakRDL Wrapper
* ============================================================================
*
* DESCRIPTION:
*   Wrapper that instantiates PeakRDL-generated register block and adapter,
*   mapping between the generated hwif signals and the existing HPET core
*   interface.
*
* ARCHITECTURE:
*   cmd/rsp --> peakrdl_to_cmdrsp adapter --> hpet_regs (PeakRDL) --> hwif --> mapping --> HPET core
*
* KEY FEATURES:
*   - Drop-in replacement for hand-coded hpet_config_regs.sv
*   - Preserves exact external interface
*   - Single source of truth: hpet_regs.rdl SystemRDL definition
*   - Maps PeakRDL LO/HI register splits to combined 64-bit interfaces
*
* ============================================================================
*/

`timescale 1ns / 1ps

/* verilator lint_off SYNCASYNCNET */
// Note: rst_n connects to both async reset (line 203) and peakrdl_to_cmdrsp (sync reset via macros).
// This is intentional - both uses are in the same clock domain.

`include "reset_defs.svh"
module hpet_config_regs #(
    parameter int VENDOR_ID = 1,
    parameter int REVISION_ID = 1,
    parameter int NUM_TIMERS = 2
)(
    // Clock and Reset
    input  logic                    clk,
    input  logic                    rst_n,

    // Command/Response Interface
    input  logic                    cmd_valid,
    output logic                    cmd_ready,
    input  logic                    cmd_pwrite,
    input  logic [11:0]             cmd_paddr,
    input  logic [31:0]             cmd_pwdata,
    input  logic [3:0]              cmd_pstrb,

    output logic                    rsp_valid,
    input  logic                    rsp_ready,
    output logic [31:0]             rsp_prdata,
    output logic                    rsp_pslverr,

    // HPET Core Interface
    output logic                    hpet_enable,
    output logic                    legacy_replacement,

    output logic                    counter_write,
    output logic [63:0]             counter_wdata,
    input  logic [63:0]             counter_rdata,

    output logic [NUM_TIMERS-1:0]   timer_enable,
    output logic [NUM_TIMERS-1:0]   timer_int_enable,
    output logic [NUM_TIMERS-1:0]   timer_type,
    output logic [NUM_TIMERS-1:0]   timer_size,
    output logic [NUM_TIMERS-1:0]   timer_value_set,

    output logic [NUM_TIMERS-1:0]   timer_comp_write,
    output logic [63:0]             timer_comp_wdata [NUM_TIMERS],  // Per-timer data bus
    output logic                    timer_comp_write_high,
    input  logic [63:0]             timer_comp_rdata [NUM_TIMERS],

    input  logic [NUM_TIMERS-1:0]   timer_int_status,
    output logic [NUM_TIMERS-1:0]   timer_int_clear
);

    // ========================================================================
    // Internal Signals
    // ========================================================================

    // PeakRDL passthrough interface
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

    // Hardware interface structs
    hpet_regs_pkg::hpet_regs__in_t  hwif_in;
    hpet_regs_pkg::hpet_regs__out_t hwif_out;

    // Previous register values for edge detection
    logic [31:0] prev_counter_lo;
    logic [31:0] prev_counter_hi;
    logic [31:0] prev_timer_comp_lo [NUM_TIMERS];
    logic [31:0] prev_timer_comp_hi [NUM_TIMERS];

    // ========================================================================
    // Instantiate Protocol Adapter
    // ========================================================================

    peakrdl_to_cmdrsp #(
        .ADDR_WIDTH(12),
        .DATA_WIDTH(32)
    ) u_adapter (
        .aclk               (clk),
        .aresetn            (rst_n),

        // cmd/rsp interface (external)
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
        .regblk_addr        (regblk_addr),  // Full 12-bit address
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

    // ========================================================================
    // Instantiate PeakRDL-Generated Register Block
    // ========================================================================
    // Note: VENDOR_ID, REVISION_ID, NUM_TIMERS are baked into the generated
    // code at generation time (localparams in hpet_regs_pkg). Cannot be
    // overridden at instantiation.

    hpet_regs u_hpet_regs (
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

    // ========================================================================
    // Map PeakRDL hwif Outputs to HPET Core Inputs
    // ========================================================================

    // Global config signals - direct mapping
    assign hpet_enable = hwif_out.HPET_CONFIG.hpet_enable.value;
    assign legacy_replacement = hwif_out.HPET_CONFIG.legacy_replacement.value;

    // Counter write detection - use swmod signal to detect SW writes
    assign counter_write = hwif_out.HPET_COUNTER_LO.counter_lo.swmod ||
                          hwif_out.HPET_COUNTER_HI.counter_hi.swmod;

    // Counter write data - capture from adapter write data bus
    // swmod pulses when SW writes, and regblk_wr_data contains the written value
    logic [31:0] last_sw_counter_lo, last_sw_counter_hi;
    logic        counter_lo_written, counter_hi_written;

    // Detect which register was written based on address and write strobe
    assign counter_lo_written = regblk_req && regblk_req_is_wr && (regblk_addr[8:0] == 9'h010);
    assign counter_hi_written = regblk_req && regblk_req_is_wr && (regblk_addr[8:0] == 9'h014);

    `ALWAYS_FF_RST(clk, rst_n,
if (`RST_ASSERTED(rst_n)) begin
            last_sw_counter_lo <= '0;
            last_sw_counter_hi <= '0;
        end else begin
            // Capture SW-written values from write data bus
            if (counter_lo_written) begin
                last_sw_counter_lo <= regblk_wr_data;
            end
            if (counter_hi_written) begin
                last_sw_counter_hi <= regblk_wr_data;
            end
        end
    )


    assign counter_wdata = {last_sw_counter_hi, last_sw_counter_lo};

    // Timer config signals - array mapping
    generate
        for (genvar i = 0; i < NUM_TIMERS; i++) begin : g_timer_mapping
            assign timer_enable[i]     = hwif_out.TIMER[i].TIMER_CONFIG.timer_enable.value;
            assign timer_int_enable[i] = hwif_out.TIMER[i].TIMER_CONFIG.timer_int_enable.value;
            assign timer_type[i]       = hwif_out.TIMER[i].TIMER_CONFIG.timer_type.value;
            assign timer_size[i]       = hwif_out.TIMER[i].TIMER_CONFIG.timer_size.value;
            assign timer_value_set[i]  = hwif_out.TIMER[i].TIMER_CONFIG.timer_value_set.value;

            // Comparator write detection
            `ALWAYS_FF_RST(clk, rst_n,
if (`RST_ASSERTED(rst_n)) begin
                    prev_timer_comp_lo[i] <= '0;
                    prev_timer_comp_hi[i] <= '0;
                end else begin
                    prev_timer_comp_lo[i] <= hwif_out.TIMER[i].TIMER_COMPARATOR_LO.timer_comp_lo.value;
                    prev_timer_comp_hi[i] <= hwif_out.TIMER[i].TIMER_COMPARATOR_HI.timer_comp_hi.value;
                end
            )


            assign timer_comp_write[i] = (hwif_out.TIMER[i].TIMER_COMPARATOR_LO.timer_comp_lo.value != prev_timer_comp_lo[i]) ||
                                        (hwif_out.TIMER[i].TIMER_COMPARATOR_HI.timer_comp_hi.value != prev_timer_comp_hi[i]);
        end
    endgenerate

    // Comparator data - Per-timer buses (no sharing, no corruption)
    // Each timer gets its own dedicated 64-bit data bus from its PeakRDL register
    generate
        for (genvar i = 0; i < NUM_TIMERS; i++) begin : g_timer_wdata
            assign timer_comp_wdata[i] = {
                hwif_out.TIMER[i].TIMER_COMPARATOR_HI.timer_comp_hi.value,
                hwif_out.TIMER[i].TIMER_COMPARATOR_LO.timer_comp_lo.value
            };
        end
    endgenerate

    // Detect if writing to high half (if HI changed but not LO)
    logic [NUM_TIMERS-1:0] timer_comp_hi_write;
    generate
        for (genvar i = 0; i < NUM_TIMERS; i++) begin : g_hi_write_detect
            assign timer_comp_hi_write[i] = (hwif_out.TIMER[i].TIMER_COMPARATOR_HI.timer_comp_hi.value != prev_timer_comp_hi[i]) &&
                                           (hwif_out.TIMER[i].TIMER_COMPARATOR_LO.timer_comp_lo.value == prev_timer_comp_lo[i]);
        end
    endgenerate
    assign timer_comp_write_high = |timer_comp_hi_write;

    // ========================================================================
    // Map HPET Core Outputs to PeakRDL hwif Inputs
    // ========================================================================

    // HPET_ID register - drive num_tim_cap field with parameter value
    // This allows single generated RTL (NUM_TIMERS=8) to report correct timer count
    // when instantiated with different NUM_TIMERS values (2, 3, 8)
    assign hwif_in.HPET_ID.num_tim_cap.next = 5'(NUM_TIMERS - 1);

    // Counter readback - continuously write live counter value to PeakRDL registers
    // With hw=w and precedence=sw, hardware writes every cycle, but SW writes take priority
    assign hwif_in.HPET_COUNTER_LO.counter_lo.next = counter_rdata[31:0];
    assign hwif_in.HPET_COUNTER_HI.counter_hi.next = counter_rdata[63:32];

    // Interrupt status - edge detection for proper sticky interrupt handling
    // PeakRDL hwset expects a pulse, not a level, for sticky interrupt fields
    logic [NUM_TIMERS-1:0] prev_timer_int_status;
    logic [NUM_TIMERS-1:0] timer_int_rising_edge;

    `ALWAYS_FF_RST(clk, rst_n,
if (`RST_ASSERTED(rst_n)) begin
            prev_timer_int_status <= '0;
        end else begin
            prev_timer_int_status <= timer_int_status;
        end
    )


    // Detect rising edge (0->1 transition) for hwset pulse
    assign timer_int_rising_edge = timer_int_status & ~prev_timer_int_status;

    // Feed edge-detected pulse to PeakRDL hwset (sticky will latch it)
    assign hwif_in.HPET_STATUS.timer_int_status.hwset = |timer_int_rising_edge;

    // Feed current level to next (for multi-bit sticky logic)
    assign hwif_in.HPET_STATUS.timer_int_status.next = {{(8-NUM_TIMERS){1'b0}}, timer_int_status};

    // Interrupt clear - detect when software writes W1C to HPET_STATUS
    // PeakRDL swmod signal pulses when SW modifies the field
    // When SW writes 1 to clear (W1C), we need to tell HPET core to deassert its status
    assign timer_int_clear = {NUM_TIMERS{hwif_out.HPET_STATUS.timer_int_status.swmod}} & timer_int_status;

/* verilator lint_on SYNCASYNCNET */
endmodule
