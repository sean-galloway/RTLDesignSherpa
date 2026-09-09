// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: apb4_ioapic
// Purpose: APB IOAPIC Top Level Integration
//
// Documentation: projects/components/retro_legacy_blocks/rtl/ioapic/README.md
// Subsystem: ioapic
//
// Author: sean galloway
// Created: 2025-11-16
// Updated: 2026-09-09 - issue #48: EOI crosses pclk -> ioapic_clk through a
//                       pulse synchronizer when CDC_ENABLE=1. Review round:
//                       idle LAPIC payload gated (L3), CDC_ENABLE treated as
//                       an enum not a bit field (L5), clock-domain and EOI
//                       rate comments corrected (M2/L6/L7)

/**
 * ============================================================================
 * APB IOAPIC Top Level Integration
 * ============================================================================
 *
 * DESCRIPTION:
 *   Top-level module that integrates APB slave with CDC, configuration
 *   registers, and IOAPIC core. Provides complete I/O APIC functionality
 *   with Intel 82093AA compatibility.
 *
 * ARCHITECTURE:
 *   - APB Slave CDC: Handles APB interface with optional clock crossing
 *   - Config Registers: Implements indirect register access (IOREGSEL/IOWIN)
 *   - IOAPIC Core: Interrupt routing and arbitration logic
 *
 * CLOCK DOMAINS:
 *   - pclk: APB interface clock, and the whole CPU/LAPIC-facing interface
 *           (irq_out_valid/ready/payload and eoi_in/eoi_vector)
 *   - ioapic_clk: IOAPIC controller clock
 *   - irq_in is the only asynchronous port; ioapic_core synchronizes it
 *   - CDC_ENABLE=0: Single clock (pclk == ioapic_clk, no CDC)
 *   - CDC_ENABLE=1: Dual clock (pclk != ioapic_clk, CDC enabled)
 *
 * LAPIC INTERFACE CROSSING (issue #48 qc round_3, item 2)
 *   irq_in is asynchronous and is synchronized inside ioapic_core, but
 *   eoi_in/eoi_vector used to reach the core combinationally: with an async
 *   LAPIC a one-cycle EOI pulse could be missed entirely or drive the
 *   Remote-IRR flops metastable, and a missed EOI leaves a level pin blocked.
 *   With CDC_ENABLE=1 the delivery handshake AND the EOI strobe are presented
 *   in pclk and cross into ioapic_clk through identical pulse synchronizers -
 *   see the long note at the crossing itself for why synchronizing the EOI
 *   alone is worse than not synchronizing it at all.
 *
 *   RATE CONTRACT: consecutive EOI strobes must be at least
 *   3*T_ioapic_clk + 2*T_pclk apart (sync_pulse's spacing requirement), and an
 *   EOI must be at least one pclk cycle away from the delivery accept it is
 *   ordered against.
 *
 *   Violating the spacing does NOT cost one EOI - it costs BOTH, silently.
 *   sync_pulse is toggle-based: each source pulse flips a toggle that the
 *   destination edge-detects. Two EOIs inside one destination sample window
 *   flip that toggle twice, the destination sees the same level it sampled
 *   last time, and NEITHER pulse produces an output. Nothing anywhere reports
 *   it, and the visible symptom is two level pins stuck with Remote IRR set.
 *   (An earlier version of this note said one of the two survived. It does
 *   not; a toggle synchronizer has no way to carry a second event.)
 *
 *   One EOI per delivered interrupt, and a delivery round trip costs far more
 *   than the spacing, so software cannot legitimately hit either limit.
 *
 *   TIMING CONSTRAINTS: the payload buses across this crossing are
 *   quasi-static behind a handshake and are NOT synchronized bit by bit - the
 *   core's vector/dest/deliv_mode sampled into pclk, and r_eoi_vector_p
 *   sampled into ioapic_clk. Any build that instantiates this block with
 *   CDC_ENABLE=1 must constrain those paths, with
 *   `set_max_delay -datapath_only` (one destination clock period is the usual
 *   choice) or `set_false_path`. Without a constraint the tool either fails
 *   an inter-clock path it should never have analysed, or - worse - reports
 *   timing met on a path it never analysed at all.
 *
 * REGISTER ACCESS METHOD (Intel IOAPIC Indirect Access):
 *   1. Write register offset to IOREGSEL (APB address 0x00)
 *   2. Read/write data via IOWIN (APB address 0x04)
 *
 * REGISTER MAP:
 *   APB Direct Access:
 *     0x00: IOREGSEL - Register select for indirect access
 *     0x04: IOWIN    - Data window for selected register
 *
 *   Internal Registers (via IOREGSEL/IOWIN):
 *     0x00: IOAPICID  - IOAPIC identification
 *     0x01: IOAPICVER - Version and capabilities
 *     0x02: IOAPICARB - Arbitration priority
 *     0x10-0x3F: IOREDTBL - Redirection table (24 IRQs × 2 regs)
 *
 * INTERRUPT FEATURES:
 *   - 24 IRQ inputs with programmable redirection
 *   - Edge and level trigger modes
 *   - Active high/low polarity
 *   - Interrupt masking per IRQ
 *   - Delivery mode support (Fixed for MVP)
 *   - Remote IRR for level-triggered interrupts
 *   - Priority-based arbitration
 *
 * ============================================================================
 */

`timescale 1ns / 1ps

`include "reset_defs.svh"

/* verilator lint_off SYNCASYNCNET */
// Note: presetn and ioapic_resetn connect to modules with different reset styles.
// ioapic_config_regs uses async reset, peakrdl_to_cmdrsp uses sync reset.
// This is intentional - both modules are in same clock domain.
module apb4_ioapic #(
    parameter int NUM_IRQS = 24,       // Number of IRQ inputs (typically 24)
    parameter int CDC_ENABLE = 0, // 0=same clock (apb4_slave), 1=different clocks (apb4_slave_cdc)
    // Async-FIFO pointer encoding, forwarded to the CDC block: 0 = Gray
    // (power-of-2 depth only), 1 = Johnson (any depth, DEPTH-bit pointers).
    // Gray by default -- Johnson is opt-in.
    parameter int USE_JOHNSON = 0
)(
    // ========================================================================
    // Clock and Reset - Dual Domain
    // ========================================================================
    input  logic                    pclk,          // APB clock domain
    input  logic                    presetn,       // APB reset (active low)
    input  logic                    ioapic_clk,    // IOAPIC clock domain
    input  logic                    ioapic_resetn, // IOAPIC reset (active low)

    // ========================================================================
    // APB4 Slave Interface (APB Clock Domain)
    // ========================================================================
    input  logic                    s_apb_PSEL,
    input  logic                    s_apb_PENABLE,
    output logic                    s_apb_PREADY,
    input  logic [11:0]             s_apb_PADDR,   // Fixed 12-bit addressing
    input  logic                    s_apb_PWRITE,
    input  logic [31:0]             s_apb_PWDATA,
    input  logic [3:0]              s_apb_PSTRB,
    input  logic [2:0]              s_apb_PPROT,
    output logic [31:0]             s_apb_PRDATA,
    output logic                    s_apb_PSLVERR,

    // ========================================================================
    // External Interrupt Interfaces
    //
    // NOT one clock domain, despite what this banner said before issue #48's
    // review round (item M2): irq_in is the ONLY asynchronous port here - it
    // is free-running and ioapic_core synchronizes it. Everything below it,
    // irq_out_valid/vector/dest/deliv_mode, irq_out_ready and eoi_in/
    // eoi_vector, is in the PCLK domain in both CDC configurations, because
    // the LAPIC that drives and consumes them is the same agent that drives
    // the APB programming interface. At CDC_ENABLE=1 the crossing into
    // ioapic_clk happens inside this module, not at these pins.
    // ========================================================================

    // IRQ inputs from system (24 interrupt sources) - ASYNCHRONOUS
    input  logic [NUM_IRQS-1:0]     irq_in,

    // Interrupt output to CPU/LAPIC (pclk domain)
    output logic                    irq_out_valid,      // Interrupt delivery request
    output logic [7:0]              irq_out_vector,     // Vector to deliver
    output logic [7:0]              irq_out_dest,       // Destination APIC ID
    output logic [2:0]              irq_out_deliv_mode, // Delivery mode
    input  logic                    irq_out_ready,      // CPU acknowledge

    // EOI (End of Interrupt) from CPU (pclk domain)
    input  logic                    eoi_in,             // EOI strobe
    input  logic [7:0]              eoi_vector          // Vector being EOI'd
);

`ifndef SYNTHESIS
    // Simulation-time parameter guard. CDC_ENABLE selects between two whole
    // structures, not a bit field: only 0 and 1 are defined, and a stray 2
    // used to pick the single-clock build silently through `CDC_ENABLE[0]`.
    initial begin : param_check
        if ((CDC_ENABLE != 0) && (CDC_ENABLE != 1)) begin
            $error({"apb4_ioapic: CDC_ENABLE=%0d but only 0 (single clock) ",
                    "and 1 (dual clock) are defined"}, CDC_ENABLE);
        end
    end
`endif

    // ========================================================================
    // CDC Command/Response Interface Signals
    // ========================================================================
    logic                    w_cmd_valid;
    logic                    w_cmd_ready;
    logic                    w_cmd_pwrite;
    logic [11:0]             w_cmd_paddr;
    logic [31:0]             w_cmd_pwdata;
    logic [3:0]              w_cmd_pstrb;
    logic [2:0]              w_cmd_pprot;

    logic                    w_rsp_valid;
    logic                    w_rsp_ready;
    logic [31:0]             w_rsp_prdata;
    logic                    w_rsp_pslverr;

    // ========================================================================
    // Configuration Interface Signals (per IRQ arrays)
    // ========================================================================
    logic [7:0]  w_cfg_vector       [NUM_IRQS];
    logic [2:0]  w_cfg_deliv_mode   [NUM_IRQS];
    logic        w_cfg_dest_mode    [NUM_IRQS];
    logic        w_cfg_polarity     [NUM_IRQS];
    logic        w_cfg_trigger_mode [NUM_IRQS];
    logic        w_cfg_mask         [NUM_IRQS];
    logic [7:0]  w_cfg_destination  [NUM_IRQS];
    logic [3:0]  w_cfg_ioapic_id;

    // Status signals from core
    logic        w_status_deliv_status [NUM_IRQS];
    logic        w_status_remote_irr   [NUM_IRQS];
    logic [3:0]  w_status_arb_id;

    // LAPIC-facing delivery, on the ioapic_clk side of the crossing
    logic        w_core_irq_valid;
    logic [7:0]  w_core_irq_vector;
    logic [7:0]  w_core_irq_dest;
    logic [2:0]  w_core_irq_deliv_mode;
    logic        w_core_irq_ready;   // accept strobe back into the core

    // EOI, in the ioapic_clk domain (synchronized when CDC_ENABLE=1)
    logic        w_eoi_strobe;
    logic [7:0]  w_eoi_vector;

    // ========================================================================
    // APB Slave - CDC or Non-CDC based on parameter
    // ========================================================================
    generate
        if (CDC_ENABLE != 0) begin : g_apb4_slave_cdc
            // Clock Domain Crossing version for async clocks
            apb4_slave_cdc #(
                .ADDR_WIDTH(12),
                .DATA_WIDTH(32),
                .STRB_WIDTH(4),
                .PROT_WIDTH(3),
                .DEPTH     (2),
                .USE_JOHNSON (USE_JOHNSON)
            ) u_apb4_slave_cdc (
                // APB Clock Domain
                .pclk                 (pclk),
                .presetn              (presetn),

                // IOAPIC Clock Domain
                .aclk                 (ioapic_clk),
                .aresetn              (ioapic_resetn),

                // APB Interface (pclk domain)
                .s_apb_PSEL           (s_apb_PSEL),
                .s_apb_PENABLE        (s_apb_PENABLE),
                .s_apb_PREADY         (s_apb_PREADY),
                .s_apb_PADDR          (s_apb_PADDR),
                .s_apb_PWRITE         (s_apb_PWRITE),
                .s_apb_PWDATA         (s_apb_PWDATA),
                .s_apb_PSTRB          (s_apb_PSTRB),
                .s_apb_PPROT          (s_apb_PPROT),
                .s_apb_PRDATA         (s_apb_PRDATA),
                .s_apb_PSLVERR        (s_apb_PSLVERR),

                // Command Interface (ioapic_clk domain)
                .cmd_valid            (w_cmd_valid),
                .cmd_ready            (w_cmd_ready),
                .cmd_pwrite           (w_cmd_pwrite),
                .cmd_paddr            (w_cmd_paddr),
                .cmd_pwdata           (w_cmd_pwdata),
                .cmd_pstrb            (w_cmd_pstrb),
                .cmd_pprot            (w_cmd_pprot),

                // Response Interface (ioapic_clk domain)
                .rsp_valid            (w_rsp_valid),
                .rsp_ready            (w_rsp_ready),
                .rsp_prdata           (w_rsp_prdata),
                .rsp_pslverr          (w_rsp_pslverr)
            );
        end else begin : g_apb4_slave_no_cdc
            // Non-CDC version for same clock domain (pclk == ioapic_clk)
            apb4_slave #(
                .ADDR_WIDTH(12),
                .DATA_WIDTH(32),
                .STRB_WIDTH(4),
                .PROT_WIDTH(3)
            ) u_apb4_slave (
                // Single clock domain (use pclk for both APB and cmd/rsp)
                .pclk                 (pclk),
                .presetn              (presetn),

                // APB Interface
                .s_apb_PSEL           (s_apb_PSEL),
                .s_apb_PENABLE        (s_apb_PENABLE),
                .s_apb_PREADY         (s_apb_PREADY),
                .s_apb_PADDR          (s_apb_PADDR),
                .s_apb_PWRITE         (s_apb_PWRITE),
                .s_apb_PWDATA         (s_apb_PWDATA),
                .s_apb_PSTRB          (s_apb_PSTRB),
                .s_apb_PPROT          (s_apb_PPROT),
                .s_apb_PRDATA         (s_apb_PRDATA),
                .s_apb_PSLVERR        (s_apb_PSLVERR),

                // Command Interface (same pclk domain)
                .cmd_valid            (w_cmd_valid),
                .cmd_ready            (w_cmd_ready),
                .cmd_pwrite           (w_cmd_pwrite),
                .cmd_paddr            (w_cmd_paddr),
                .cmd_pwdata           (w_cmd_pwdata),
                .cmd_pstrb            (w_cmd_pstrb),
                .cmd_pprot            (w_cmd_pprot),

                // Response Interface (same pclk domain)
                .rsp_valid            (w_rsp_valid),
                .rsp_ready            (w_rsp_ready),
                .rsp_prdata           (w_rsp_prdata),
                .rsp_pslverr          (w_rsp_pslverr)
            );
        end
    endgenerate

    // ========================================================================
    // IOAPIC Configuration Registers
    // CDC_ENABLE=0: Uses pclk (same clock as APB)
    // CDC_ENABLE=1: Uses ioapic_clk (async clock)
    // ========================================================================
    ioapic_config_regs #(
        .NUM_IRQS        (NUM_IRQS)
    ) u_ioapic_config_regs (
        // Clock and Reset - conditional based on CDC_ENABLE
        .clk               ((CDC_ENABLE != 0) ? ioapic_clk : pclk),
        .rst_n             ((CDC_ENABLE != 0) ? ioapic_resetn : presetn),

        // Command/Response Interface
        .cmd_valid         (w_cmd_valid),
        .cmd_ready         (w_cmd_ready),
        .cmd_pwrite        (w_cmd_pwrite),
        .cmd_paddr         (w_cmd_paddr),
        .cmd_pwdata        (w_cmd_pwdata),
        .cmd_pstrb         (w_cmd_pstrb),

        .rsp_valid         (w_rsp_valid),
        .rsp_ready         (w_rsp_ready),
        .rsp_prdata        (w_rsp_prdata),
        .rsp_pslverr       (w_rsp_pslverr),

        // Configuration outputs to core (per IRQ)
        .cfg_vector        (w_cfg_vector),
        .cfg_deliv_mode    (w_cfg_deliv_mode),
        .cfg_dest_mode     (w_cfg_dest_mode),
        .cfg_polarity      (w_cfg_polarity),
        .cfg_trigger_mode  (w_cfg_trigger_mode),
        .cfg_mask          (w_cfg_mask),
        .cfg_destination   (w_cfg_destination),
        .cfg_ioapic_id     (w_cfg_ioapic_id),

        // Status inputs from core
        .status_deliv_status(w_status_deliv_status),
        .status_remote_irr  (w_status_remote_irr),
        .status_arb_id      (w_status_arb_id)
    );

    // ========================================================================
    // LAPIC Interface Clock Domain Crossing
    // ========================================================================
    //
    // The CPU/LAPIC side of this block is ONE interface: the delivery
    // handshake (irq_out_valid/ready + payload) and the EOI strobe are driven
    // and consumed by the same agent, in the same clock domain as the APB
    // programming interface. It is therefore presented in pclk, and the two
    // events cross into ioapic_clk through IDENTICAL sync_pulse instances so
    // their pclk ORDER survives the crossing.
    //
    // That ordering is the whole point (issue #48 qc round_2 item 3 /
    // round_3 item 2). ioapic_core drops an EOI that arrives while the pin's
    // Remote IRR is still clear - i.e. before the delivery was accepted -
    // which is what stops a spurious EOI from pre-clearing an in-flight
    // delivery. If the EOI were synchronized while the accept was sampled
    // straight off irq_out_ready in ioapic_clk, the synchronizer's latency
    // would re-order them: an EOI issued a cycle BEFORE the accept would
    // arrive several cycles AFTER it, clear a Remote IRR it never saw set,
    // and a level pin would be redelivered on a spurious EOI. Measured, not
    // theorised - that is exactly how the EOI-during-DELIVER test failed with
    // the delivery still presented in ioapic_clk.
    //
    // Second consequence, equally load-bearing: irq_out_valid is a pclk
    // signal, so a delivery accepted with irq_out_ready held high is visible
    // for exactly one pclk cycle - one handshake, countable. Presented in
    // ioapic_clk it was one ioapic_clk cycle wide, which a faster ioapic_clk
    // can slip entirely between two pclk edges.
    //
    // RESET: both domains are expected to be reset together. A reset of one
    // side alone can make sync_pulse fabricate one edge; both consumers
    // qualify it with their own state (an accept needs a valid delivery, an
    // EOI needs a set Remote IRR), so a fabricated pulse after reset is a
    // no-op rather than a lost or duplicated interrupt.
    generate
        if (CDC_ENABLE != 0) begin : g_lapic_cdc
            // ---------------------------------------------------------------
            // Delivery request: ioapic_clk -> pclk, classic four-phase.
            //
            //   A: idle                      r_i_req=0, r_i_busy=0
            //   B: request out, awaiting ack r_i_req=1, r_i_busy=1
            //   C: request withdrawn,        r_i_req=0, r_i_busy=1
            //      awaiting ack withdrawal
            //
            // The return-to-zero phase C is not optional: ioapic_core holds
            // irq_out_valid across an accept whenever the next interrupt is
            // already waiting, so "the core dropped its valid" is NOT a usable
            // end-of-transfer marker. A first cut used it and deadlocked the
            // moment two interrupts arrived back to back - the stress and
            // mask-all tests stopped delivering entirely.
            logic       r_i_req;
            logic       r_i_busy;
            logic       w_i_ack;
            logic       w_p_req;
            logic       r_p_valid;
            logic       r_p_ack;
            logic [7:0] r_p_vector;
            logic [7:0] r_p_dest;
            logic [2:0] r_p_deliv_mode;
            logic       r_eoi_in_d;
            logic       w_eoi_pulse_p;
            logic [7:0] r_eoi_vector_p;

            `ALWAYS_FF_RST(ioapic_clk, ioapic_resetn,
                if (`RST_ASSERTED(ioapic_resetn)) begin
                    r_i_req  <= 1'b0;
                    r_i_busy <= 1'b0;
                end else if (!r_i_busy) begin
                    if (w_core_irq_valid) begin           // A -> B
                        r_i_req  <= 1'b1;
                        r_i_busy <= 1'b1;
                    end
                end else if (r_i_req) begin
                    if (w_i_ack) begin                    // B -> C (accepted)
                        r_i_req <= 1'b0;
                    end
                end else begin
                    if (!w_i_ack) begin                   // C -> A
                        r_i_busy <= 1'b0;
                    end
                end
            )

            // One-cycle accept strobe into the core: exactly the cycle the
            // request is withdrawn. ioapic_core treats a one-cycle ready with
            // its valid high as one transfer, which is what this is.
            assign w_core_irq_ready = r_i_busy && r_i_req && w_i_ack;

            cdc_synchronizer #(
                .WIDTH      (1),
                .FLOP_COUNT (3)
            ) u_ack_sync (
                .clk       (ioapic_clk),
                .rst_n     (ioapic_resetn),
                .async_in  (r_p_ack),
                .sync_out  (w_i_ack)
            );

            cdc_synchronizer #(
                .WIDTH      (1),
                .FLOP_COUNT (3)
            ) u_req_sync (
                .clk       (pclk),
                .rst_n     (presetn),
                .async_in  (r_i_req),
                .sync_out  (w_p_req)
            );

            // pclk side of the four-phase, and the LAPIC-facing register.
            // The payload is sampled straight out of ioapic_core's output
            // registers: it has been stable since at least one ioapic_clk
            // cycle before r_i_req rose (the flop above) plus the three pclk
            // synchronizer stages, and the core cannot change it until this
            // side acks. Quasi-static data behind a handshake, the standard
            // multi-cycle-path crossing.
            `ALWAYS_FF_RST(pclk, presetn,
                if (`RST_ASSERTED(presetn)) begin
                    r_p_valid      <= 1'b0;
                    r_p_ack        <= 1'b0;
                    r_p_vector     <= 8'h00;
                    r_p_dest       <= 8'h00;
                    r_p_deliv_mode <= 3'h0;
                end else if (!r_p_ack) begin
                    if (w_p_req && !r_p_valid) begin
                        r_p_vector     <= w_core_irq_vector;
                        r_p_dest       <= w_core_irq_dest;
                        r_p_deliv_mode <= w_core_irq_deliv_mode;
                        r_p_valid      <= 1'b1;
                    end else if (r_p_valid && irq_out_ready) begin
                        r_p_valid <= 1'b0;      // the LAPIC accepted
                        r_p_ack   <= 1'b1;
                    end
                end else begin
                    if (!w_p_req) begin
                        r_p_ack <= 1'b0;
                    end
                end
            )

            // Gated on r_p_valid so the idle payload is zero, matching what
            // ioapic_core presents at CDC_ENABLE=0 (issue #48 review round,
            // item L3). Ungated, these held the last delivered interrupt
            // between deliveries and the two configurations disagreed on the
            // idle bus - a difference that only ever shows up as a testbench
            // or an integrator reading a stale vector and believing it.
            assign irq_out_valid      = r_p_valid;
            assign irq_out_vector     = r_p_valid ? r_p_vector     : 8'h00;
            assign irq_out_dest       = r_p_valid ? r_p_dest       : 8'h00;
            assign irq_out_deliv_mode = r_p_valid ? r_p_deliv_mode : 3'h0;

            // ---------------------------------------------------------------
            // EOI: pclk -> ioapic_clk
            //
            // Edge-detected first, because sync_pulse requires a single-cycle
            // input pulse and eoi_in is only specified as a strobe - a level
            // held for several pclk cycles would toggle the handshake once per
            // cycle and violate its spacing requirement.
            //
            // Latency matters as much as safety here: the accept crosses back
            // through a 3-stage cdc_synchronizer and the EOI through a 3-stage
            // sync_pulse, so both land the same number of ioapic_clk edges
            // after their pclk event and their ORDER survives. That is what
            // makes "an EOI seen before the accept is spurious" a property of
            // the pclk timeline rather than of the synchronizer depth.
            `ALWAYS_FF_RST(pclk, presetn,
                if (`RST_ASSERTED(presetn)) begin
                    r_eoi_in_d     <= 1'b0;
                    r_eoi_vector_p <= 8'h00;
                end else begin
                    r_eoi_in_d <= eoi_in;
                    if (eoi_in && !r_eoi_in_d) begin
                        r_eoi_vector_p <= eoi_vector;
                    end
                end
            )

            assign w_eoi_pulse_p = eoi_in && !r_eoi_in_d;

            sync_pulse #(
                .SYNC_STAGES (3)
            ) u_eoi_sync (
                .i_src_clk   (pclk),
                .i_src_rst_n (presetn),
                .i_pulse     (w_eoi_pulse_p),
                .i_dst_clk   (ioapic_clk),
                .i_dst_rst_n (ioapic_resetn),
                .o_pulse     (w_eoi_strobe)
            );

            // Quasi-static across the crossing: it only changes on a new EOI,
            // which the rate contract keeps far away from this arrival.
            assign w_eoi_vector = r_eoi_vector_p;
        end else begin : g_lapic_direct
            // Same clock - the core drives the LAPIC interface directly and
            // eoi_in is consumed as-is (a multi-cycle strobe is harmless, the
            // Remote IRR clear is idempotent).
            assign irq_out_valid      = w_core_irq_valid;
            assign irq_out_vector     = w_core_irq_vector;
            assign irq_out_dest       = w_core_irq_dest;
            assign irq_out_deliv_mode = w_core_irq_deliv_mode;
            assign w_core_irq_ready   = irq_out_ready;
            assign w_eoi_strobe       = eoi_in;
            assign w_eoi_vector       = eoi_vector;
        end
    endgenerate

    // ========================================================================
    // IOAPIC Core Logic
    // CDC_ENABLE=0: Uses pclk (same clock as APB)
    // CDC_ENABLE=1: Uses ioapic_clk (async clock)
    // ========================================================================
    ioapic_core #(
        .NUM_IRQS(NUM_IRQS)
    ) u_ioapic_core (
        // Clock and Reset - conditional based on CDC_ENABLE
        .clk                  ((CDC_ENABLE != 0) ? ioapic_clk : pclk),
        .rst_n                ((CDC_ENABLE != 0) ? ioapic_resetn : presetn),

        // Configuration inputs (per IRQ)
        .cfg_vector           (w_cfg_vector),
        .cfg_deliv_mode       (w_cfg_deliv_mode),
        .cfg_dest_mode        (w_cfg_dest_mode),
        .cfg_polarity         (w_cfg_polarity),
        .cfg_trigger_mode     (w_cfg_trigger_mode),
        .cfg_mask             (w_cfg_mask),
        .cfg_destination      (w_cfg_destination),
        .cfg_ioapic_id        (w_cfg_ioapic_id),

        // Status outputs
        .status_deliv_status  (w_status_deliv_status),
        .status_remote_irr    (w_status_remote_irr),
        .status_arb_id        (w_status_arb_id),

        // External IRQ inputs
        .irq_in               (irq_in),

        // Interrupt output to CPU (through the LAPIC crossing above)
        .irq_out_valid        (w_core_irq_valid),
        .irq_out_vector       (w_core_irq_vector),
        .irq_out_dest         (w_core_irq_dest),
        .irq_out_deliv_mode   (w_core_irq_deliv_mode),
        .irq_out_ready        (w_core_irq_ready),

        // EOI input from CPU (pclk-synchronized when CDC_ENABLE=1)
        .eoi_in               (w_eoi_strobe),
        .eoi_vector           (w_eoi_vector)
    );

/* verilator lint_on SYNCASYNCNET */
endmodule : apb4_ioapic
