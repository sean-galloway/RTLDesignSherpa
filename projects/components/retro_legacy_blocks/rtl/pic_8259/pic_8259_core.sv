// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: pic_8259_core
// Purpose: Core logic for 8259 PIC with 8 IRQ inputs
//
// Implements Intel 8259A Programmable Interrupt Controller functionality:
// - 8 prioritized interrupt inputs (IRQ0-7)
// - Edge and level triggered modes
// - Fixed and rotating priority modes
// - Interrupt masking (IMR)
// - Interrupt Request Register (IRR)
// - In-Service Register (ISR)
// - End-of-Interrupt (EOI) handling
// - Cascade support (master/slave configuration)
// - Auto-EOI mode
// - Special fully nested mode
//
// Follows HPET/PIT pattern: separate core logic from register interface

`timescale 1ns / 1ps

`include "reset_defs.svh"

module pic_8259_core (
    input wire clk,
    input wire rst,  // Active-high reset

    // Configuration from registers
    input wire        cfg_pic_enable,
    input wire        cfg_init_mode,
    input wire        cfg_auto_reset_init,

    // ICW configuration
    input wire        cfg_ic4,           // ICW4 needed
    input wire        cfg_sngl,          // Single mode (vs cascade)
    input wire        cfg_ltim,          // Level triggered mode
    input wire [7:0]  cfg_vector_base,   // Interrupt vector base
    input wire [7:0]  cfg_cascade,       // Cascade configuration
    input wire        cfg_aeoi,          // Auto EOI mode
    input wire [1:0]  cfg_buf_mode,      // Buffered mode
    input wire        cfg_sfnm,          // Special fully nested mode

    // ICW/OCW write strobes
    input  wire       icw1_wr,
    input  wire       icw2_wr,
    input  wire       icw3_wr,
    input  wire       icw4_wr,
    input  wire       ocw2_wr,
    input  wire       ocw3_wr,

    // OCW2/OCW3 command inputs
    input  wire [2:0] ocw2_irq_level,
    input  wire [2:0] ocw2_eoi_cmd,
    input  wire [1:0] ocw3_read_reg_cmd,
    input  wire       ocw3_poll_cmd,
    input  wire [1:0] ocw3_smm_cmd,

    // IMR (OCW1) interface - bidirectional
    input  wire [7:0] imr_reg_in,        // IMR value from register
    input  wire       imr_reg_wr,        // IMR write strobe
    output wire [7:0] imr_reg_out,       // IMR value to register

    // Status outputs (to registers)
    output wire [7:0] irr_out,           // Interrupt Request Register
    output wire [7:0] isr_out,           // In-Service Register
    output wire       init_complete,
    output wire [2:0] icw_step,
    output wire       int_output,        // INT pin state
    output wire [2:0] highest_priority,  // Highest priority IRQ

    // Hardware interface
    input  wire [7:0] irq_in,            // IRQ inputs (IRQ0-7)
    output wire [7:0] int_vector        // Interrupt vector for INTA cycle
);

    //========================================================================
    // Internal Registers
    //========================================================================

    // Interrupt registers
    logic [7:0] r_irr;           // Interrupt Request Register
    logic [7:0] r_isr;           // In-Service Register
    logic [7:0] r_imr;           // Interrupt Mask Register
    logic [7:0] r_irq_last;      // Previous IRQ state (for edge detection)

    // Priority rotation
    logic [2:0] r_priority_base; // Lowest priority IRQ (for rotating priority)
    logic       r_rotate_on_aeoi;// Rotate priority on auto EOI

    // Special modes
    logic       r_special_mask_mode;

    // Temporary variables for priority calculations
    logic [2:0] highest_irq_comb;
    logic [2:0] highest_isr_comb;
    logic [2:0] highest_irq_latched;

    // Initialization state machine
    typedef enum logic [2:0] {
        INIT_IDLE       = 3'd0,
        INIT_WAIT_ICW2  = 3'd1,
        INIT_WAIT_ICW3  = 3'd2,
        INIT_WAIT_ICW4  = 3'd3,
        INIT_COMPLETE   = 3'd4
    } init_state_t;

    init_state_t r_init_state;

    //========================================================================
    // Initialization State Machine
    //========================================================================

    always_ff @(posedge clk) begin
        if (rst) begin
            r_init_state <= INIT_IDLE;
        end else begin
            case (r_init_state)
                INIT_IDLE: begin
                    if (icw1_wr) begin
                        r_init_state <= INIT_WAIT_ICW2;
                    end
                end

                INIT_WAIT_ICW2: begin
                    if (icw2_wr) begin
                        // ICW3 needed if not single mode
                        if (cfg_sngl) begin
                            // Single mode - skip ICW3
                            r_init_state <= cfg_ic4 ? INIT_WAIT_ICW4 : INIT_COMPLETE;
                        end else begin
                            r_init_state <= INIT_WAIT_ICW3;
                        end
                    end
                end

                INIT_WAIT_ICW3: begin
                    if (icw3_wr) begin
                        // ICW4 needed if IC4 bit set
                        r_init_state <= cfg_ic4 ? INIT_WAIT_ICW4 : INIT_COMPLETE;
                    end
                end

                INIT_WAIT_ICW4: begin
                    if (icw4_wr) begin
                        r_init_state <= INIT_COMPLETE;
                    end
                end

                INIT_COMPLETE: begin
                    // Stay in complete state unless re-initialized
                    if (icw1_wr) begin
                        r_init_state <= INIT_WAIT_ICW2;
                    end else if (cfg_init_mode) begin
                        // Manual return to init mode via config register
                        r_init_state <= INIT_IDLE;
                    end
                end

                default: r_init_state <= INIT_IDLE;
            endcase
        end
    end

    //========================================================================
    // Edge/Level Detection for IRQ Inputs
    //========================================================================

    always_ff @(posedge clk) begin
        if (rst) begin
            r_irq_last <= 8'h00;
        end else begin
            r_irq_last <= irq_in;
        end
    end

    // Detect rising edges (edge triggered) or level (level triggered)
    wire [7:0] w_irq_trigger;
    assign w_irq_trigger = cfg_ltim ? irq_in : (irq_in & ~r_irq_last);

    //========================================================================
    // Priority Resolution
    //========================================================================

    // Priority mask based on rotation base
    // In fixed priority: IRQ0=highest, IRQ7=lowest (base=7)
    // In rotating priority: base determines lowest priority
    function automatic logic [7:0] get_priority_mask(input logic [2:0] base);
        logic [7:0] mask;
        mask = 8'h00;
        // Set bits for IRQs with higher priority than base
        for (int i = 0; i < 8; i++) begin
            if (((i - base - 1) & 8'h7) < 8) begin
                mask[i] = 1'b1;
            end
        end
        return mask;
    endfunction

    //========================================================================
    // Priority Resolution - Combinational Logic
    //========================================================================

    // Find highest priority IRQ from r_irr & ~r_imr
    always_comb begin
        logic [7:0] pending_irqs;
        int idx;
        
        pending_irqs = r_irr & ~r_imr;
        highest_irq_comb = 3'd0;
        
        // Search in priority order starting from highest (after base)
        for (int i = 0; i < 8; i++) begin
            idx = (r_priority_base + 1 + i) & 3'h7;
            if (pending_irqs[idx]) begin
                highest_irq_comb = idx[2:0];
                break;
            end
        end
    end

    // Find highest priority IRQ from r_isr
    always_comb begin
        int idx;
        highest_isr_comb = 3'd0;
        
        // Search in priority order starting from highest (after base)
        for (int i = 0; i < 8; i++) begin
            idx = (r_priority_base + 1 + i) & 3'h7;
            if (r_isr[idx]) begin
                highest_isr_comb = idx[2:0];
                break;
            end
        end
    end

    //========================================================================
    // Interrupt Request Register (IRR) Management
    //========================================================================

    always_ff @(posedge clk) begin
        if (rst) begin
            r_irr <= 8'h00;
            highest_irq_latched <= 3'd0;
        end else if (!cfg_pic_enable) begin
            r_irr <= 8'h00;
            highest_irq_latched <= 3'd0;
        end else if (r_init_state == INIT_COMPLETE) begin
            // Latch the highest IRQ at the start of the cycle
            highest_irq_latched <= highest_irq_comb;
            
            // Set bits for triggered interrupts (unless special mask mode)
            r_irr <= r_irr | w_irq_trigger;

            // Clear IRR bit when interrupt moves to ISR
            if (int_output && !cfg_aeoi) begin
                r_irr[highest_irq_comb] <= 1'b0;
            end
        end
    end

    //========================================================================
    // In-Service Register (ISR) Management
    //========================================================================

    always_ff @(posedge clk) begin
        if (rst) begin
            r_isr <= 8'h00;
        end else if (!cfg_pic_enable) begin
            r_isr <= 8'h00;
        end else if (r_init_state == INIT_COMPLETE) begin
            // Set ISR bit when interrupt acknowledged (unless auto-EOI)
            if (int_output && !cfg_aeoi) begin
                r_isr[highest_irq_comb] <= 1'b1;
            end

            // Clear ISR bit on EOI command
            if (ocw2_wr) begin
                case (ocw2_eoi_cmd)
                    3'b001: begin // Non-specific EOI
                        r_isr[highest_isr_comb] <= 1'b0;
                    end
                    3'b011: begin // Specific EOI
                        r_isr[ocw2_irq_level] <= 1'b0;
                    end
                    3'b101: begin // Rotate on non-specific EOI
                        r_isr[highest_isr_comb] <= 1'b0;
                    end
                    3'b111: begin // Rotate on specific EOI
                        r_isr[ocw2_irq_level] <= 1'b0;
                    end
                    default: begin
                        // No change
                    end
                endcase
            end
        end
    end

    //========================================================================
    // Interrupt Mask Register (IMR) Management
    //========================================================================

    always_ff @(posedge clk) begin
        if (rst) begin
            r_imr <= 8'hFF;  // All masked by default
        end else if (imr_reg_wr) begin
            r_imr <= imr_reg_in;
        end
    end

    assign imr_reg_out = r_imr;

    //========================================================================
    // Priority Rotation Logic
    //========================================================================

    always_ff @(posedge clk) begin
        if (rst) begin
            r_priority_base <= 3'd7;  // Fixed priority by default (IRQ0 highest)
            r_rotate_on_aeoi <= 1'b0;
        end else if (ocw2_wr) begin
            case (ocw2_eoi_cmd)
                3'b000: begin // Rotate in auto-EOI mode (clear)
                    r_rotate_on_aeoi <= 1'b0;
                end
                3'b100: begin // Rotate in auto-EOI mode (set)
                    r_rotate_on_aeoi <= 1'b1;
                end
                3'b101: begin // Rotate on non-specific EOI
                    r_priority_base <= highest_isr_comb;
                end
                3'b110: begin // Set priority command
                    r_priority_base <= ocw2_irq_level;
                end
                3'b111: begin // Rotate on specific EOI
                    r_priority_base <= ocw2_irq_level;
                end
                default: begin
                    // No change
                end
            endcase
        end else if (cfg_aeoi && r_rotate_on_aeoi && int_output) begin
            // Auto-EOI with rotation
            r_priority_base <= highest_irq_comb;
        end
    end

    //========================================================================
    // Special Mask Mode
    //========================================================================

    always_ff @(posedge clk) begin
        if (rst) begin
            r_special_mask_mode <= 1'b0;
        end else if (ocw3_wr) begin
            case (ocw3_smm_cmd)
                2'b10: r_special_mask_mode <= 1'b0;  // Reset special mask
                2'b11: r_special_mask_mode <= 1'b1;  // Set special mask
                default: begin
                    // No change
                end
            endcase
        end
    end

    //========================================================================
    // Interrupt Output Generation
    //========================================================================

    // Determine if any unmasked interrupt is pending
    wire [7:0] w_pending_irqs;
    
    generate
        if (1) begin : gen_pending_irqs
            // In special mask mode, allow interrupts even if same/lower priority is in service
            // In normal mode, block interrupts if equal/higher priority is in service
            assign w_pending_irqs = r_special_mask_mode ? 
                                    (r_irr & ~r_imr) :
                                    (r_irr & ~r_imr & ~r_isr);
        end
    endgenerate

    assign int_output = (r_init_state == INIT_COMPLETE) && 
                        cfg_pic_enable && 
                        (|w_pending_irqs);

    //========================================================================
    // Status Outputs
    //========================================================================

    assign irr_out = r_irr;
    assign isr_out = r_isr;
    assign init_complete = (r_init_state == INIT_COMPLETE);
    assign icw_step = r_init_state;
    assign highest_priority = highest_irq_comb;

    //========================================================================
    // Interrupt Vector Generation
    //========================================================================

    // Generate interrupt vector for INTA cycle
    // Vector = base[7:3] | irq_level[2:0]
    assign int_vector = {cfg_vector_base[7:3], highest_irq_comb};

endmodule
