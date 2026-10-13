// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: gpio_core
// Purpose: GPIO Core Logic - FPGA Friendly
//
// Description:
//   Core GPIO logic with input synchronization, interrupt detection,
//   and atomic output operations. Designed to be technology-agnostic
//   with FPGA I/O buffer instantiation at the top level.
//
// Features:
//   - 32-bit GPIO port
//   - 2-stage input synchronization (metastability protection)
//   - Edge detection for interrupts (rising, falling, both)
//   - Level-sensitive interrupt support
//   - Atomic set/clear/toggle operations
//   - Per-bit direction control
//
// Output Latch Contract (issue #44):
//   r_output_data is the single output latch. A direct software write to
//   GPIO_OUTPUT is signalled by cfg_output_wr_stb, a one-cycle STROBE aligned
//   with cfg_output_data by gpio_config_regs -- it is not derived from
//   cfg_output_data changing value, so writing the same value twice writes
//   twice. Priority within a cycle is direct write > toggle > set > clear.
//   gpio_config_regs writes r_output_data back into the GPIO_OUTPUT register
//   after an atomic op, so the register and this latch stay in agreement.
//
// Interrupt Aggregation:
//   This module does NOT produce the aggregate irq. It exports sts_raw_int and
//   sts_int_pending; gpio_config_regs builds irq from the STICKY status
//   register for edge pins and the live level for level pins. A local
//   `raw & pin_enable` irq used to exist here, was never connected, and
//   diverged from the wrapper's edge semantics -- it was removed rather than
//   left as a trap for a future integrator (issue #44).
//
// I/O Buffer Notes:
//   This module does NOT instantiate FPGA I/O primitives.
//   The top-level wrapper (apb4_gpio.sv) or FPGA top-level should:
//   - Connect gpio_out to IOBUF/OBUFT data input
//   - Connect gpio_oe to IOBUF/OBUFT tristate control
//   - Connect gpio_in from IOBUF/IBUF output
//
// Documentation: projects/components/retro_legacy_blocks/rtl/gpio/README.md
// Created: 2025-11-29
// Updated: 2026-09-08 - issue #44: strobe-driven direct write, unconnected
//                       irq output removed

`timescale 1ns / 1ps

`include "reset_defs.svh"

module gpio_core #(
    parameter int GPIO_WIDTH = 32,              // GPIO port width
    parameter int SYNC_STAGES = 2               // Input synchronizer stages
) (
    // Clock and Reset
    input  logic                    clk,
    input  logic                    rst_n,

    // GPIO Pins Interface
    input  logic [GPIO_WIDTH-1:0]   gpio_in,    // From I/O buffers (after IBUF)
    output logic [GPIO_WIDTH-1:0]   gpio_out,   // To I/O buffers (before OBUF)
    output logic [GPIO_WIDTH-1:0]   gpio_oe,    // Output enable (1=output, 0=tristate)

    // Configuration Interface (from registers)
    input  logic                    cfg_gpio_enable,    // Global enable
    input  logic [GPIO_WIDTH-1:0]   cfg_direction,      // 1=output, 0=input
    input  logic [GPIO_WIDTH-1:0]   cfg_output_data,    // Output data (GPIO_OUTPUT)
    input  logic                    cfg_output_wr_stb,  // 1-cycle strobe: software
                                                        // wrote GPIO_OUTPUT
    input  logic [GPIO_WIDTH-1:0]   cfg_int_enable_pins,// Per-pin interrupt enable
    input  logic [GPIO_WIDTH-1:0]   cfg_int_type,       // 1=level, 0=edge
    input  logic [GPIO_WIDTH-1:0]   cfg_int_polarity,   // 1=high/rising, 0=low/falling
    input  logic [GPIO_WIDTH-1:0]   cfg_int_both,       // 1=both edges

    // Atomic Operations (active high, one-cycle strobe-driven pulses built in
    // gpio_config_regs from each register's swmod write strobe)
    input  logic [GPIO_WIDTH-1:0]   cfg_output_set,     // Set output bits
    input  logic [GPIO_WIDTH-1:0]   cfg_output_clr,     // Clear output bits
    input  logic [GPIO_WIDTH-1:0]   cfg_output_tgl,     // Toggle output bits

    // Status Interface (to registers)
    output logic [GPIO_WIDTH-1:0]   sts_input_data,     // Synchronized input data
    output logic [GPIO_WIDTH-1:0]   sts_raw_int,        // Raw interrupt status
    output logic [GPIO_WIDTH-1:0]   sts_int_pending     // Interrupt pending (for IRQ)
);

    // ========================================================================
    // Input Synchronization
    // ========================================================================
    logic [GPIO_WIDTH-1:0] r_sync_stage [SYNC_STAGES];  // index 0 = first stage
    logic [GPIO_WIDTH-1:0] w_gpio_sync;

    // Multi-stage synchronizer for metastability protection
    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            for (int i = 0; i < SYNC_STAGES; i++) begin
                r_sync_stage[i] <= '0;
            end
        end else begin
            r_sync_stage[0] <= gpio_in;
            for (int i = 1; i < SYNC_STAGES; i++) begin
                r_sync_stage[i] <= r_sync_stage[i-1];
            end
        end
    )

    assign w_gpio_sync = r_sync_stage[SYNC_STAGES-1];
    assign sts_input_data = w_gpio_sync;

    // ========================================================================
    // Output Data with Atomic Operations
    // ========================================================================
    logic [GPIO_WIDTH-1:0] r_output_data;

    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            r_output_data <= '0;
        end else begin
            // Priority: Direct write (strobe) > Toggle > Set > Clear
            // When software writes to output register, ALL bits are updated from that write.
            // Atomic ops only apply when there's no direct register write happening.
            if (cfg_output_wr_stb) begin
                // Software wrote to output register - update ALL bits from new value
                r_output_data <= cfg_output_data;
            end else begin
                // No direct write - apply atomic operations
                for (int i = 0; i < GPIO_WIDTH; i++) begin
                    if (cfg_output_tgl[i]) begin
                        r_output_data[i] <= ~r_output_data[i];
                    end else if (cfg_output_set[i]) begin
                        r_output_data[i] <= 1'b1;
                    end else if (cfg_output_clr[i]) begin
                        r_output_data[i] <= 1'b0;
                    end
                    // else: retain previous value
                end
            end
        end
    )

    // Output assignments
    assign gpio_out = r_output_data;
    assign gpio_oe  = cfg_gpio_enable ? cfg_direction : '0;

    // ========================================================================
    // Edge Detection
    // ========================================================================
    logic [GPIO_WIDTH-1:0] r_gpio_prev;
    logic [GPIO_WIDTH-1:0] w_rising_edge;
    logic [GPIO_WIDTH-1:0] w_falling_edge;
    logic [GPIO_WIDTH-1:0] w_any_edge;

    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            r_gpio_prev <= '0;
        end else begin
            r_gpio_prev <= w_gpio_sync;
        end
    )

    assign w_rising_edge  = w_gpio_sync & ~r_gpio_prev;
    assign w_falling_edge = ~w_gpio_sync & r_gpio_prev;
    assign w_any_edge     = w_rising_edge | w_falling_edge;

    // ========================================================================
    // Interrupt Generation
    // ========================================================================
    logic [GPIO_WIDTH-1:0] w_edge_int;
    logic [GPIO_WIDTH-1:0] w_level_int;
    logic [GPIO_WIDTH-1:0] w_raw_int;

    // Edge interrupt logic
    always_comb begin
        for (int i = 0; i < GPIO_WIDTH; i++) begin
            if (cfg_int_both[i]) begin
                // Both edges
                w_edge_int[i] = w_any_edge[i];
            end else if (cfg_int_polarity[i]) begin
                // Rising edge
                w_edge_int[i] = w_rising_edge[i];
            end else begin
                // Falling edge
                w_edge_int[i] = w_falling_edge[i];
            end
        end
    end

    // Level interrupt logic
    always_comb begin
        for (int i = 0; i < GPIO_WIDTH; i++) begin
            if (cfg_int_polarity[i]) begin
                // Active high
                w_level_int[i] = w_gpio_sync[i];
            end else begin
                // Active low
                w_level_int[i] = ~w_gpio_sync[i];
            end
        end
    end

    // Select edge or level based on type
    // For edge: raw interrupt is pulse, status in register is sticky (hwset)
    // For level: raw interrupt is live level, status in register follows level
    always_comb begin
        for (int i = 0; i < GPIO_WIDTH; i++) begin
            if (cfg_int_type[i]) begin
                w_raw_int[i] = w_level_int[i];
            end else begin
                w_raw_int[i] = w_edge_int[i];
            end
        end
    end

    // Raw interrupt output (to PeakRDL for hwset/hwwrite)
    assign sts_raw_int = w_raw_int;

    // Interrupt pending output (raw & enable - for IRQ generation)
    // Note: The W1C sticky behavior is handled by PeakRDL gpio_regs, and the
    // aggregate irq is built in gpio_config_regs (see the header).
    assign sts_int_pending = w_raw_int & cfg_int_enable_pins;

endmodule : gpio_core
