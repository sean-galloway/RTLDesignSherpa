// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: ioapic_core
// Purpose: Core I/O APIC interrupt controller logic
//
// Documentation: projects/components/retro_legacy_blocks/rtl/ioapic/README.md
// Subsystem: ioapic
//
// Author: sean galloway
// Created: 2025-11-16

/**
 * ============================================================================
 * IOAPIC Core Logic
 * ============================================================================
 *
 * DESCRIPTION:
 *   Core I/O Advanced Programmable Interrupt Controller logic implementing
 *   Intel 82093AA-compatible interrupt routing and distribution:
 *   - 24 interrupt input pins with programmable redirection
 *   - Edge and level trigger detection
 *   - Active high/low polarity handling
 *   - Priority-based arbitration
 *   - Interrupt delivery state machine
 *   - Remote IRR tracking for level-triggered interrupts
 *
 * INTERRUPT ROUTING:
 *   Each IRQ input has a redirection table entry that configures:
 *   - Vector: Interrupt vector number to deliver (0x00-0xFF)
 *   - Delivery Mode: Fixed, LowestPri, SMI, NMI, INIT, ExtINT
 *   - Destination: Target CPU APIC ID
 *   - Trigger Mode: Edge or Level
 *   - Polarity: Active High or Active Low
 *   - Mask: Enable/Disable this IRQ
 *
 * PRIORITY ARBITRATION (MVP):
 *   - Static priority: Lower IRQ number = higher priority
 *   - Only one interrupt delivered at a time
 *   - Pending interrupts wait until current delivery completes
 *
 * EDGE vs LEVEL HANDLING:
 *   - Edge: Latch on trigger edge, clear after delivery
 *   - Level: Track input level, set Remote IRR when delivered,
 *            clear Remote IRR on EOI, re-trigger if still asserted
 *
 * ============================================================================
 */

`timescale 1ns / 1ps

`include "reset_defs.svh"

module ioapic_core #(
    parameter int NUM_IRQS = 24  // Number of IRQ inputs (typically 24)
)(
    // ========================================================================
    // Clock and Reset
    // ========================================================================
    input  logic        clk,
    input  logic        rst_n,

    // ========================================================================
    // Configuration Interface (from config_regs) - Per IRQ
    // ========================================================================
    
    // Redirection table entries (per IRQ)
    input  logic [7:0]  cfg_vector       [NUM_IRQS],  // Interrupt vector
    input  logic [2:0]  cfg_deliv_mode   [NUM_IRQS],  // Delivery mode
    input  logic        cfg_dest_mode    [NUM_IRQS],  // 0=Physical, 1=Logical
    input  logic        cfg_polarity     [NUM_IRQS],  // 0=Active high, 1=Active low
    input  logic        cfg_trigger_mode [NUM_IRQS],  // 0=Edge, 1=Level
    input  logic        cfg_mask         [NUM_IRQS],  // 0=Enabled, 1=Masked
    input  logic [7:0]  cfg_destination  [NUM_IRQS],  // Target CPU APIC ID
    
    // IOAPIC ID configuration
    input  logic [3:0]  cfg_ioapic_id,

    // ========================================================================
    // Status Interface (to config_regs) - Per IRQ
    // ========================================================================
    
    // Read-only status fields
    output logic        status_deliv_status [NUM_IRQS],  // 0=Idle, 1=Pending
    output logic        status_remote_irr   [NUM_IRQS],  // Level-triggered state
    
    // Arbitration ID (read-only, typically same as IOAPIC ID)
    output logic [3:0]  status_arb_id,

    // ========================================================================
    // External Interfaces
    // ========================================================================
    
    // IRQ inputs from system (24 interrupt sources)
    input  logic [NUM_IRQS-1:0]  irq_in,
    
    // Interrupt output to CPU (MSI-style message interface)
    // Simplified for MVP: single wire interrupt with vector/destination
    output logic        irq_out_valid,      // Interrupt delivery request
    output logic [7:0]  irq_out_vector,     // Vector to deliver
    output logic [7:0]  irq_out_dest,       // Destination APIC ID
    output logic [2:0]  irq_out_deliv_mode, // Delivery mode
    input  logic        irq_out_ready,      // CPU acknowledge (EOI)
    
    // EOI (End of Interrupt) input from CPU
    input  logic        eoi_in,             // EOI strobe
    input  logic [7:0]  eoi_vector          // Vector being EOI'd
);

    // ========================================================================
    // Internal Signals
    // ========================================================================
    
    // IRQ synchronization
    logic [NUM_IRQS-1:0] irq_sync [2:0];
    logic [NUM_IRQS-1:0] irq_level;
    
    // Polarity-adjusted IRQ levels
    logic [NUM_IRQS-1:0] irq_active;
    
    // Edge detection
    logic [NUM_IRQS-1:0] irq_edge_rising;
    logic [NUM_IRQS-1:0] irq_edge_falling;
    logic [NUM_IRQS-1:0] irq_edge_trigger;
    
    // Interrupt pending status (latched for edge, tracked for level)
    logic [NUM_IRQS-1:0] irq_pending;
    logic irq_remote_irr [NUM_IRQS];  // Remote IRR per IRQ (unpacked array)
    
    // Priority arbitration
    logic [NUM_IRQS-1:0] irq_eligible;      // Unmasked and pending
    logic [4:0]          selected_irq;       // 0-23 (need 5 bits)
    logic                irq_selected_valid;
    
    // Delivery state machine
    typedef enum logic [1:0] {
        IDLE,
        DELIVER,
        WAIT_EOI
    } delivery_state_t;
    
    delivery_state_t delivery_state, next_delivery_state;
    logic [4:0]      current_irq;            // Currently being delivered
    logic [7:0]      current_vector;
    logic            current_is_level;

    // ========================================================================
    // IRQ Input Synchronization (Avoid Metastability)
    // ========================================================================
    
    genvar i;
    generate
        for (i = 0; i < NUM_IRQS; i++) begin : g_irq_sync
            `ALWAYS_FF_RST(clk, rst_n,
                if (`RST_ASSERTED(rst_n)) begin
                    irq_sync[0][i] <= 1'b0;
                    irq_sync[1][i] <= 1'b0;
                    irq_sync[2][i] <= 1'b0;
                end else begin
                    irq_sync[0][i] <= irq_in[i];
                    irq_sync[1][i] <= irq_sync[0][i];
                    irq_sync[2][i] <= irq_sync[1][i];
                end
            )
        end
    endgenerate
    
    assign irq_level = irq_sync[2];

    // ========================================================================
    // Polarity Handling
    // ========================================================================
    
    // Invert input if active-low configured
    generate
        for (i = 0; i < NUM_IRQS; i++) begin : g_polarity
            assign irq_active[i] = cfg_polarity[i] ? ~irq_level[i] : irq_level[i];
        end
    endgenerate

    // ========================================================================
    // Edge Detection
    // ========================================================================
    
    logic [NUM_IRQS-1:0] irq_active_prev;
    
    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            irq_active_prev <= '0;
        end else begin
            irq_active_prev <= irq_active;
        end
    )
    
    // Rising and falling edges
    assign irq_edge_rising = irq_active & ~irq_active_prev;
    assign irq_edge_falling = ~irq_active & irq_active_prev;
    
    // Trigger edge based on configuration (most edge-triggered IRQs use rising)
    // For active-low edge-triggered: rising edge of inverted signal = falling edge of input
    assign irq_edge_trigger = irq_edge_rising;  // Simplified: always rising edge of active signal

    // ========================================================================
    // Interrupt Pending Logic
    // ========================================================================
    
    generate
        for (i = 0; i < NUM_IRQS; i++) begin : g_pending
            `ALWAYS_FF_RST(clk, rst_n,
                if (`RST_ASSERTED(rst_n)) begin
                    irq_pending[i] <= 1'b0;
                end else begin
                    if (cfg_trigger_mode[i] == 1'b0) begin
                        // Edge-triggered: Set on edge, clear when delivery completes
                        if (irq_edge_trigger[i]) begin
                            irq_pending[i] <= 1'b1;
                        end else if ((delivery_state == DELIVER) && (current_irq == i[4:0]) &&
                                   irq_out_ready) begin
                            irq_pending[i] <= 1'b0;  // Clear when delivery acknowledged
                        end
                    end else begin
                        // Level-triggered: Pending = active level AND not masked by Remote IRR
                        irq_pending[i] <= irq_active[i] && !irq_remote_irr[i];
                    end
                end
            )
        end
    endgenerate

    // ========================================================================
    // Remote IRR Management (Level-Triggered Only)
    // ========================================================================
    
    generate
        for (i = 0; i < NUM_IRQS; i++) begin : g_remote_irr
            `ALWAYS_FF_RST(clk, rst_n,
                if (`RST_ASSERTED(rst_n)) begin
                    irq_remote_irr[i] <= 1'b0;
                end else begin
                    if (cfg_trigger_mode[i] == 1'b1) begin  // Level-triggered only
                        // Set when interrupt accepted for delivery
                        if (irq_selected_valid && (selected_irq == i) && 
                           (delivery_state == IDLE)) begin
                            irq_remote_irr[i] <= 1'b1;
                        end
                        // Clear on EOI for this vector
                        else if (eoi_in && (eoi_vector == cfg_vector[i])) begin
                            irq_remote_irr[i] <= 1'b0;
                        end
                    end else begin
                        irq_remote_irr[i] <= 1'b0;  // Always 0 for edge-triggered
                    end
                end
            )
        end
    endgenerate
    
    // Export Remote IRR status
    assign status_remote_irr = irq_remote_irr;
    
    // Export arbitration ID (same as IOAPIC ID)
    assign status_arb_id = cfg_ioapic_id;

    // ========================================================================
    // Priority Arbitration - Find Highest Priority Pending IRQ
    // ========================================================================
    
    // Find eligible interrupts (unmasked and pending)
    generate
        for (i = 0; i < NUM_IRQS; i++) begin : g_eligible
            assign irq_eligible[i] = irq_pending[i] && !cfg_mask[i];
        end
    endgenerate
    
    // Static priority: lowest IRQ number wins
    always_comb begin
        selected_irq = '0;
        irq_selected_valid = 1'b0;
        
        for (int j = 0; j < NUM_IRQS; j++) begin
            if (irq_eligible[j]) begin
                selected_irq = j[4:0];
                irq_selected_valid = 1'b1;
                break;  // Stop at first match (lowest number)
            end
        end
    end

    // ========================================================================
    // Interrupt Delivery State Machine
    // ========================================================================
    
    // State register
    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            delivery_state <= IDLE;
            current_irq <= '0;
            current_vector <= '0;
            current_is_level <= 1'b0;
        end else begin
            delivery_state <= next_delivery_state;
            
            // Latch current IRQ info when starting delivery
            if (delivery_state == IDLE && next_delivery_state == DELIVER) begin
                current_irq <= selected_irq;
                current_vector <= cfg_vector[selected_irq];
                current_is_level <= cfg_trigger_mode[selected_irq];
            end
        end
    )
    
    // Next state logic
    always_comb begin
        next_delivery_state = delivery_state;
        
        case (delivery_state)
            IDLE: begin
                // Start delivery if eligible interrupt exists
                if (irq_selected_valid) begin
                    next_delivery_state = DELIVER;
                end
            end
            
            DELIVER: begin
                // Wait for CPU to accept interrupt
                if (irq_out_ready) begin
                    if (current_is_level) begin
                        next_delivery_state = WAIT_EOI;  // Level needs EOI
                    end else begin
                        next_delivery_state = IDLE;      // Edge done immediately
                    end
                end
            end
            
            WAIT_EOI: begin
                // Wait for EOI for current vector
                if (eoi_in && (eoi_vector == current_vector)) begin
                    next_delivery_state = IDLE;
                end
            end
            
            default: begin
                next_delivery_state = IDLE;
            end
        endcase
    end
    
    // ========================================================================
    // Interrupt Output Interface
    // ========================================================================
    
    assign irq_out_valid = (delivery_state == DELIVER);
    assign irq_out_vector = (delivery_state == DELIVER) ? cfg_vector[current_irq] : 8'h00;
    assign irq_out_dest = (delivery_state == DELIVER) ? cfg_destination[current_irq] : 8'h00;
    assign irq_out_deliv_mode = (delivery_state == DELIVER) ? cfg_deliv_mode[current_irq] : 3'h0;

    // ========================================================================
    // Delivery Status (Per IRQ)
    // ========================================================================
    
    // Delivery status = 1 when this IRQ is currently being delivered
    generate
        for (i = 0; i < NUM_IRQS; i++) begin : g_deliv_status
            assign status_deliv_status[i] = (delivery_state == DELIVER || 
                                            delivery_state == WAIT_EOI) && 
                                           (current_irq == i[4:0]);
        end
    endgenerate

    // ========================================================================
    // Assertions for Design Verification
    // ========================================================================
    
    // synthesis translate_off
    // Ensure only one IRQ is in delivery at a time
    always @(posedge clk) begin
        if (rst_n) begin
            assert ($countones(status_deliv_status) <= 1) 
                else $error("IOAPIC: Multiple IRQs in delivery state!");
        end
    end
    
    // Ensure selected IRQ is within range
    always @(posedge clk) begin
        if (rst_n && irq_selected_valid) begin
            assert (selected_irq < NUM_IRQS) 
                else $error("IOAPIC: Selected IRQ %0d out of range!", selected_irq);
        end
    end
    // synthesis translate_on

endmodule : ioapic_core
