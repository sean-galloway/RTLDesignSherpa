// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: gpio_config_regs
// Purpose: GPIO Configuration Registers - Connects PeakRDL to Core
//
// Description:
//   Wrapper connecting PeakRDL-generated registers to GPIO core.
//   Handles the hwif (hardware interface) signal mapping.
//
// Architecture:
//   APB -> apb_slave -> CMD/RSP -> peakrdl_to_cmdrsp -> regblk_* -> gpio_regs (PeakRDL) -> hwif -> gpio_core
//
// Documentation: projects/components/retro_legacy_blocks/rtl/gpio/README.md
// Created: 2025-11-29
// Updated: 2025-11-30 - Changed to 32-bit data width

`timescale 1ns / 1ps

`include "reset_defs.svh"

module gpio_config_regs
    import gpio_regs_pkg::*;
#(
    parameter int GPIO_WIDTH = 32,
    parameter int SYNC_STAGES = 2,
    parameter int ADDR_WIDTH = 12,
    parameter int DATA_WIDTH = 32
) (
    // Clock and Reset
    input  logic                    clk,
    input  logic                    rst_n,

    // PeakRDL regblock interface (from peakrdl_to_cmdrsp)
    input  logic                    regblk_req,
    input  logic                    regblk_req_is_wr,
    input  logic [ADDR_WIDTH-1:0]   regblk_addr,
    input  logic [DATA_WIDTH-1:0]   regblk_wr_data,
    input  logic [DATA_WIDTH-1:0]   regblk_wr_biten,
    output logic                    regblk_req_stall_wr,
    output logic                    regblk_req_stall_rd,
    output logic                    regblk_rd_ack,
    output logic                    regblk_rd_err,
    output logic [DATA_WIDTH-1:0]   regblk_rd_data,
    output logic                    regblk_wr_ack,
    output logic                    regblk_wr_err,

    // GPIO Pins Interface
    input  logic [GPIO_WIDTH-1:0]   gpio_in,
    output logic [GPIO_WIDTH-1:0]   gpio_out,
    output logic [GPIO_WIDTH-1:0]   gpio_oe,

    // Interrupt Output
    output logic                    irq
);

    // PeakRDL hardware interface signals
    gpio_regs_pkg::gpio_regs__in_t  hwif_in;
    gpio_regs_pkg::gpio_regs__out_t hwif_out;

    // Internal signals to/from core
    logic [GPIO_WIDTH-1:0] w_sts_input_data;
    logic [GPIO_WIDTH-1:0] w_sts_raw_int;
    logic [GPIO_WIDTH-1:0] w_sts_int_pending;

    // Atomic operation pulse generation
    logic [31:0] r_set_prev;
    logic [31:0] r_clr_prev;
    logic [31:0] r_tgl_prev;
    logic [GPIO_WIDTH-1:0] w_output_set;
    logic [GPIO_WIDTH-1:0] w_output_clr;
    logic [GPIO_WIDTH-1:0] w_output_tgl;

    // ========================================================================
    // PeakRDL Register Block
    // ========================================================================
    gpio_regs u_gpio_regs (
        .clk        (clk),
        .rst        (~rst_n),  // PeakRDL uses active-high reset

        // PeakRDL cpuif interface (from peakrdl_to_cmdrsp)
        .s_cpuif_req            (regblk_req),
        .s_cpuif_req_is_wr      (regblk_req_is_wr),
        .s_cpuif_addr           (regblk_addr[5:0]),  // 6-bit address (64 bytes)
        .s_cpuif_wr_data        (regblk_wr_data),
        .s_cpuif_wr_biten       (regblk_wr_biten),
        .s_cpuif_req_stall_wr   (regblk_req_stall_wr),
        .s_cpuif_req_stall_rd   (regblk_req_stall_rd),
        .s_cpuif_rd_ack         (regblk_rd_ack),
        .s_cpuif_rd_err         (regblk_rd_err),
        .s_cpuif_rd_data        (regblk_rd_data),
        .s_cpuif_wr_ack         (regblk_wr_ack),
        .s_cpuif_wr_err         (regblk_wr_err),

        // Hardware interface
        .hwif_in    (hwif_in),
        .hwif_out   (hwif_out)
    );

    // ========================================================================
    // Atomic Operation Pulse Generation
    // ========================================================================
    // These registers need ONE-SHOT behavior: when software writes a value,
    // generate a pulse for each bit that's written as 1, then auto-clear.
    //
    // Solution: Track when the register value changes (any change), and use
    // the NEW value as the pulse when the register changes.

    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            r_set_prev <= '0;
            r_clr_prev <= '0;
            r_tgl_prev <= '0;
        end else begin
            r_set_prev <= hwif_out.GPIO_OUTPUT_SET.set_bits.value;
            r_clr_prev <= hwif_out.GPIO_OUTPUT_CLR.clear_bits.value;
            r_tgl_prev <= hwif_out.GPIO_OUTPUT_TGL.toggle_bits.value;
        end
    )

    // Generate pulses when register value CHANGES
    logic w_set_changed;
    logic w_clr_changed;
    logic w_tgl_changed;

    assign w_set_changed = (hwif_out.GPIO_OUTPUT_SET.set_bits.value != r_set_prev);
    assign w_clr_changed = (hwif_out.GPIO_OUTPUT_CLR.clear_bits.value != r_clr_prev);
    assign w_tgl_changed = (hwif_out.GPIO_OUTPUT_TGL.toggle_bits.value != r_tgl_prev);

    assign w_output_set = w_set_changed ? hwif_out.GPIO_OUTPUT_SET.set_bits.value : '0;
    assign w_output_clr = w_clr_changed ? hwif_out.GPIO_OUTPUT_CLR.clear_bits.value : '0;
    assign w_output_tgl = w_tgl_changed ? hwif_out.GPIO_OUTPUT_TGL.toggle_bits.value : '0;

    // ========================================================================
    // GPIO Core Instance
    // ========================================================================
    gpio_core #(
        .GPIO_WIDTH     (GPIO_WIDTH),
        .SYNC_STAGES    (SYNC_STAGES)
    ) u_gpio_core (
        .clk            (clk),
        .rst_n          (rst_n),

        // GPIO Pins
        .gpio_in        (gpio_in),
        .gpio_out       (gpio_out),
        .gpio_oe        (gpio_oe),

        // Configuration (now single 32-bit registers)
        .cfg_gpio_enable    (hwif_out.GPIO_CONTROL.gpio_enable.value),
        .cfg_int_enable     (hwif_out.GPIO_CONTROL.int_enable.value),
        .cfg_direction      (hwif_out.GPIO_DIRECTION.direction.value),
        .cfg_output_data    (hwif_out.GPIO_OUTPUT.output_data.value),
        .cfg_int_enable_pins(hwif_out.GPIO_INT_ENABLE.int_enable.value),
        .cfg_int_type       (hwif_out.GPIO_INT_TYPE.int_type.value),
        .cfg_int_polarity   (hwif_out.GPIO_INT_POLARITY.int_polarity.value),
        .cfg_int_both       (hwif_out.GPIO_INT_BOTH.int_both.value),

        // Atomic operations
        .cfg_output_set     (w_output_set),
        .cfg_output_clr     (w_output_clr),
        .cfg_output_tgl     (w_output_tgl),

        // Status
        .sts_input_data     (w_sts_input_data),
        .sts_raw_int        (w_sts_raw_int),
        .sts_int_pending    (w_sts_int_pending),

        // Interrupt output (from core - unused, we generate IRQ here)
        .irq                ()  // Not connected, IRQ generated from sticky register
    );

    // ========================================================================
    // IRQ Generation - Mode-Dependent (Edge=Sticky, Level=Live)
    // ========================================================================
    // IRQ is asserted when:
    // 1. Global interrupt enable is set (in GPIO_CONTROL)
    // 2. For EDGE mode: sticky status register bit is set (W1C behavior)
    // 3. For LEVEL mode: live raw interrupt is active (follows input level)
    //
    // This ensures:
    // - Edge interrupts latch and require explicit W1C to clear
    // - Level interrupts de-assert automatically when input level changes

    logic [GPIO_WIDTH-1:0] w_sticky_int_status;
    assign w_sticky_int_status = hwif_out.GPIO_INT_STATUS.int_status.value;

    // Get interrupt type configuration (1=level, 0=edge)
    logic [GPIO_WIDTH-1:0] w_int_type;
    assign w_int_type = hwif_out.GPIO_INT_TYPE.int_type.value;

    // Get per-pin interrupt enable
    logic [GPIO_WIDTH-1:0] w_int_enable_pins;
    assign w_int_enable_pins = hwif_out.GPIO_INT_ENABLE.int_enable.value;

    // Effective interrupt status per bit:
    // - Edge mode (type=0): use sticky register
    // - Level mode (type=1): use live raw interrupt status
    logic [GPIO_WIDTH-1:0] w_effective_int_status;
    always_comb begin
        for (int i = 0; i < GPIO_WIDTH; i++) begin
            if (w_int_type[i]) begin
                // Level mode: use live signal (AND with enable)
                w_effective_int_status[i] = w_sts_raw_int[i] & w_int_enable_pins[i];
            end else begin
                // Edge mode: use sticky register (already gated by enable when set)
                w_effective_int_status[i] = w_sticky_int_status[i];
            end
        end
    end

    assign irq = hwif_out.GPIO_CONTROL.int_enable.value && (|w_effective_int_status);

    // ========================================================================
    // Connect Status to hwif_in
    // ========================================================================
    // Input data register (read-only)
    assign hwif_in.GPIO_INPUT.input_data.next = w_sts_input_data;

    // Raw interrupt status (read-only)
    assign hwif_in.GPIO_RAW_INT.raw_status.next = w_sts_raw_int;

    // Interrupt status (W1C with stickybit - set by hardware via next)
    // stickybit: when next[i] is high, bit i is set in the register
    assign hwif_in.GPIO_INT_STATUS.int_status.next = w_sts_int_pending;

endmodule : gpio_config_regs
