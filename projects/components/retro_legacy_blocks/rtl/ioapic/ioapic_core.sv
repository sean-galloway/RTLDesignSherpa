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
// Updated: 2026-09-09 - issue #48: per-pin level blocking, single-delivery
//                       edge semantics, EOI matched against the DELIVERED
//                       vector; the delivery FSM is gone. Review round: the
//                       live trigger mode arms Remote IRR (L1) and a polarity
//                       rewrite no longer fabricates an edge (L8)

/**
 * ============================================================================
 * IOAPIC Core Logic
 * ============================================================================
 *
 * DESCRIPTION:
 *   Core I/O Advanced Programmable Interrupt Controller logic implementing
 *   Intel 82093AA-compatible interrupt routing and distribution:
 *   - NUM_IRQS interrupt input pins with programmable redirection
 *   - Edge and level trigger detection
 *   - Active high/low polarity handling
 *   - Arbitration: static priority (lowest IRQ number wins) or, behind
 *     IOAPICARBCFG.rr_enable, round robin from the last accepted pin
 *   - One outstanding delivery, presented on a valid/ready handshake
 *   - Per-pin Remote IRR tracking for level-triggered interrupts
 *
 * DELIVERY (issue #48, C1 and qc round_2/round_3)
 *   There is NO delivery state machine. The delivery path is a one-entry
 *   valid/ready pipeline stage ([[streaming-no-fsm]]): the arbiter picks the
 *   highest-priority eligible pin, the pick is registered into the output
 *   stage, and the stage empties on `irq_out_valid && irq_out_ready`. The
 *   three states that used to exist (IDLE / DELIVER / WAIT_EOI) carried no
 *   information the handshake does not:
 *
 *     - IDLE vs DELIVER is `r_out_valid`.
 *     - WAIT_EOI was a GLOBAL block. It is now a PER-PIN block: accepting a
 *       level interrupt sets that pin's Remote IRR and the stage is free
 *       again on the same cycle, so a lost or wrong-vector EOI stalls only
 *       the pin it belongs to. A real 82093AA blocks only the affected pin;
 *       the old engine froze every IRQ in the block until reset.
 *
 *   The pending bit is cleared on the NON-delayed accept strobe
 *   (`r_out_valid && irq_out_ready && r_out_irq == i`). The old one-cycle
 *   delay left the pin eligible for one extra arbitration round and every
 *   edge interrupt was therefore delivered twice (issue #48 C1). A new edge
 *   landing in the clear cycle SETS - a fresh event is not swallowed by the
 *   retirement of the previous one.
 *
 *   The accepted pin is masked from arbitration for the accept cycle itself
 *   (`w_irq_eligible` below). Without that term the pin is still requesting
 *   in the cycle its pending bit is being cleared, which is exactly the
 *   re-arbitration window C1 describes - the fix is the same for edge (the
 *   latch clears next cycle) and level (Remote IRR sets next cycle).
 *
 * EOI MATCHING (issue #48 qc round_1)
 *   Remote IRR is cleared when an EOI arrives whose vector equals the vector
 *   that was actually DELIVERED for that pin (`r_delivered_vector[i]`, latched
 *   at accept), NOT the live RTE vector. Software may legally re-point an RTE
 *   between delivery and EOI; comparing against the live vector permanently
 *   blocked the pin. The next delivery uses the current RTE vector.
 *
 *   EOI is honoured in any state - there is no WAIT_EOI to wedge - and an EOI
 *   for a pin whose Remote IRR is clear is a no-op (a spurious EOI cannot
 *   pre-clear an in-flight delivery). A delivery accepted in the same cycle as
 *   a matching EOI wins: the pin has just re-entered service.
 *
 *   ONE EOI CLEARS EVERY MATCHING PIN. The comparison is per pin and runs on
 *   all pins at once, so a single EOI clears Remote IRR on EVERY pin whose
 *   delivered vector equals eoi_vector - not just the pin that was delivered
 *   most recently. That is 82093AA behaviour rather than an artefact of this
 *   implementation: an EOI carries a vector, not a pin number, and the IOAPIC
 *   has nothing else to match on. Software that programs one vector into
 *   several RTEs is choosing to have those pins share an EOI.
 *
 * REMOTE IRR SET ARM (issue #48 review round, item L1)
 *   The set is gated on the LIVE cfg_trigger_mode[i] and on nothing else - in
 *   particular NOT on a copy of the trigger mode sampled when the delivery was
 *   loaded. With the sampled copy, rewriting an RTE from edge to level while a
 *   delivery was in flight livelocked the pin: the accept saw the stale "edge"
 *   copy and did not set Remote IRR, the pin was now level and still asserted,
 *   so it re-delivered forever and no EOI could ever stop it (Remote IRR never
 *   set, so there was nothing for an EOI to clear).
 *
 * POLARITY CHANGES (issue #48 review round, item L8)
 *   `w_irq_active` is the polarity-adjusted level, so writing cfg_polarity
 *   inverts it in one cycle with the pin itself idle - and the edge detector,
 *   which compares this cycle's active level against last cycle's, sees a
 *   textbook rising edge and latches an interrupt that no device ever raised.
 *   The edge detector is therefore SUPPRESSED for a pin in the cycle its own
 *   polarity bit changes (`w_polarity_changed`), which is exactly the cycle
 *   the fabricated edge would appear: one cycle later `r_irq_active_prev`
 *   already holds the re-polarised level and the comparison is honest again.
 *   The cost is that a genuine edge landing in the same cycle as a polarity
 *   rewrite is dropped - the right trade, since the pin's meaning is changing
 *   in that cycle and the two are indistinguishable at the detector.
 *
 * EDGE vs LEVEL HANDLING:
 *   - Edge : rising edge of the polarity-adjusted, synchronized input latches
 *            `r_irq_pending`; cleared when the delivery is accepted.
 *   - Level: the request IS the synchronized level (no latch), gated by
 *            Remote IRR. Still asserted after EOI -> delivered again, exactly
 *            once per EOI, because Remote IRR re-asserts on the next accept.
 *
 * CLOCK DOMAIN:
 *   Everything here is in `clk`. `irq_in` is asynchronous and crosses through
 *   SYNC_STAGES flops. `eoi_in` must be a single-cycle strobe IN THIS DOMAIN
 *   with `eoi_vector` stable around it - apb4_ioapic does the pclk crossing.
 *
 * CHECK BY INSPECTION (these were assertions; properties belong in external
 * formal bindings, not inside the module)
 *   - At most one pin is in delivery at a time: status_deliv_status[] is set
 *     only by the single output stage, which holds one r_out_irq index.
 *   - w_sel_valid implies w_sel_irq < NUM_IRQS: the selector is a priority
 *     scan over an NUM_IRQS-wide request vector and is only valid when that
 *     vector is non-zero.
 *   - An accept retires an edge pin's pending bit (issue #48 C1, half one).
 *     A coincident new edge is allowed to re-arm it: set wins. Guarded by
 *     ioapic_tests_medium.py::test_c1_edge_double_delivery_count.
 *   - irq_out_valid is never parked for an edge pin whose pending bit is
 *     already clear (issue #48 C1, half two), EXCEPT while software has
 *     rewritten the pin's trigger mode since this delivery was loaded. That
 *     exception is legal and is why the removed assertion carried two
 *     sim-only bookkeeping flops with no counterpart in the design: an
 *     edge->level->edge rewrite clears r_irq_pending[i] through the level
 *     branch of g_pending while r_out_valid is still up. L1 removed the
 *     synthesized copy of the load-time trigger mode because gating on it
 *     livelocks. Guarded by
 *     ioapic_tests_medium.py::test_c1_no_park_after_single_ready_pulse and
 *     ::test_rte_vector_rewrite_mid_delivery.
 *   - Accepting a LEVEL interrupt sets that pin's Remote IRR the next cycle,
 *     which is what makes in-service state per-pin rather than global.
 *     Guarded by ioapic_tests_medium.py::test_per_pin_block_level_b_and_eoi_clears
 *     and ioapic_tests_basic.py::test_remote_irr_status.
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
    // 0 = static priority (82093AA: lowest eligible IRQ number wins),
    // 1 = round robin (the scan starts above the last accepted pin).
    input  logic        cfg_rr_enable,

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

    // IRQ inputs from system (asynchronous, synchronized below)
    input  logic [NUM_IRQS-1:0]  irq_in,

    // Interrupt output to CPU (MSI-style message interface)
    output logic        irq_out_valid,      // Interrupt delivery request
    output logic [7:0]  irq_out_vector,     // Vector to deliver
    output logic [7:0]  irq_out_dest,       // Destination APIC ID or logical mask
    // How the receiver must READ irq_out_dest: 0 = physical, a single
    // APIC ID; 1 = logical, a bitmask matched against each local APIC's
    // logical destination register. An IOAPIC does not decode logical
    // destinations itself - it forwards the field and the mode, and the
    // local APICs match. Forwarding the mode is what makes logical
    // delivery usable at all (RLB-008).
    output logic        irq_out_dest_mode,
    output logic [2:0]  irq_out_deliv_mode, // Delivery mode
    input  logic        irq_out_ready,      // CPU accepts the delivery

    // EOI (End of Interrupt) input from CPU - single-cycle strobe in `clk`
    input  logic        eoi_in,             // EOI strobe
    input  logic [7:0]  eoi_vector          // Vector being EOI'd
);

    // ========================================================================
    // Local Parameters
    // ========================================================================

    localparam int SYNC_STAGES = 3;                        // irq_in metastability filter
    localparam int IRQ_IDX_W   = (NUM_IRQS > 1) ? $clog2(NUM_IRQS) : 1;

    // ========================================================================
    // Internal Signals
    // ========================================================================

    // IRQ synchronization and polarity
    logic [NUM_IRQS-1:0] r_irq_sync [SYNC_STAGES];
    logic [NUM_IRQS-1:0] w_irq_level;
    logic [NUM_IRQS-1:0] w_irq_active;       // polarity-adjusted level
    logic [NUM_IRQS-1:0] r_irq_active_prev;
    logic [NUM_IRQS-1:0] r_polarity_prev;    // per-pin cfg_polarity, delayed
    logic [NUM_IRQS-1:0] w_polarity_changed; // ...and its change detect
    logic [NUM_IRQS-1:0] w_irq_edge_rising;

    // Request tracking
    logic [NUM_IRQS-1:0] r_irq_pending;      // edge-triggered latch only
    logic [NUM_IRQS-1:0] w_irq_request;      // edge latch or live level
    logic [NUM_IRQS-1:0] w_irq_eligible;     // requesting, unmasked, not in service
    logic [NUM_IRQS-1:0] r_remote_irr;       // level in-service, per pin
    logic [7:0]          r_delivered_vector [NUM_IRQS];

    // Arbitration
    logic [IRQ_IDX_W-1:0] w_sel_irq;
    logic                 w_sel_valid;
    // Round-robin start pointer: the pin AFTER the last accepted one.
    logic [IRQ_IDX_W-1:0] r_rr_ptr;

    // Delivery output stage (one entry, valid/ready)
    logic                 r_out_valid;
    logic [IRQ_IDX_W-1:0] r_out_irq;
    logic [7:0]           r_out_vector;
    logic [7:0]           r_out_dest;
    logic                 r_out_dest_mode;
    logic [2:0]           r_out_deliv_mode;
    logic                 w_deliv_accept;    // the delivery handshake
    logic                 w_out_load;

    // ========================================================================
    // IRQ Input Synchronization (Avoid Metastability)
    // ========================================================================

    genvar i;
    generate
        for (i = 0; i < NUM_IRQS; i++) begin : g_irq_sync
            `ALWAYS_FF_RST(clk, rst_n,
                if (`RST_ASSERTED(rst_n)) begin
                    for (int s = 0; s < SYNC_STAGES; s++) begin
                        r_irq_sync[s][i] <= 1'b0;
                    end
                end else begin
                    r_irq_sync[0][i] <= irq_in[i];
                    for (int s = 1; s < SYNC_STAGES; s++) begin
                        r_irq_sync[s][i] <= r_irq_sync[s-1][i];
                    end
                end
            )
        end
    endgenerate

    assign w_irq_level = r_irq_sync[SYNC_STAGES-1];

    // ========================================================================
    // Polarity Handling
    // ========================================================================

    // Invert input if active-low configured
    generate
        for (i = 0; i < NUM_IRQS; i++) begin : g_polarity
            assign w_irq_active[i] = cfg_polarity[i] ? ~w_irq_level[i] : w_irq_level[i];

            // Per-pin polarity change detect. cfg_polarity is a register-block
            // output, so it steps on a clock edge exactly as w_irq_active does;
            // this flop trails it by one cycle and the XOR below is high for
            // precisely the cycle in which the inversion took effect.
            `ALWAYS_FF_RST(clk, rst_n,
                if (`RST_ASSERTED(rst_n)) begin
                    r_polarity_prev[i] <= 1'b0;
                end else begin
                    r_polarity_prev[i] <= cfg_polarity[i];
                end
            )

            assign w_polarity_changed[i] = cfg_polarity[i] ^ r_polarity_prev[i];
        end
    endgenerate

    // ========================================================================
    // Edge Detection
    // ========================================================================

    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            r_irq_active_prev <= '0;
        end else begin
            r_irq_active_prev <= w_irq_active;
        end
    )

    // Edge-triggered pins trigger on the rising edge of the ACTIVE signal, so
    // an active-low pin triggers on the falling edge of the pin itself. There
    // is no falling-edge trigger mode in the 82093AA and no consumer for one:
    // the unused irq_edge_falling term was removed with issue #48.
    //
    // ...masked, per pin, in the cycle that pin's polarity bit changed: the
    // inversion moves w_irq_active without the pin itself moving, and that is
    // a fabricated edge rather than an interrupt (POLARITY CHANGES, header).
    assign w_irq_edge_rising = w_irq_active & ~r_irq_active_prev & ~w_polarity_changed;

    // ========================================================================
    // Delivery Accept Strobe
    // ========================================================================

    // The single retirement event for a delivery. Everything that has to
    // happen exactly once per delivered interrupt - pending clear, Remote IRR
    // set, delivered-vector latch - hangs off this one term, in the SAME cycle
    // the handshake happens (issue #48 C1: the old one-cycle-delayed copy of
    // this condition is what delivered every edge interrupt twice).
    assign w_deliv_accept = r_out_valid && irq_out_ready;

    // ========================================================================
    // Interrupt Pending Logic
    // ========================================================================

    generate
        for (i = 0; i < NUM_IRQS; i++) begin : g_pending
            `ALWAYS_FF_RST(clk, rst_n,
                if (`RST_ASSERTED(rst_n)) begin
                    r_irq_pending[i] <= 1'b0;
                end else if (cfg_trigger_mode[i] == 1'b0) begin
                    // Edge: set on the edge, clear when the delivery is
                    // accepted. SET WINS - an edge coincident with the clear
                    // is a new event and must not be lost.
                    if (w_irq_edge_rising[i]) begin
                        r_irq_pending[i] <= 1'b1;
                    end else if (w_deliv_accept && (r_out_irq == IRQ_IDX_W'(i))) begin
                        r_irq_pending[i] <= 1'b0;
                    end
                end else begin
                    // Level: the request is the live level (w_irq_request),
                    // the latch is unused and held clear so that switching a
                    // pin back to edge mode starts from a clean state.
                    r_irq_pending[i] <= 1'b0;
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
                    r_remote_irr[i] <= 1'b0;
                end else if (cfg_trigger_mode[i] == 1'b1) begin
                    // Set when the CPU ACCEPTS the delivery (not when it is
                    // presented): an EOI that arrives while the delivery is
                    // still unaccepted finds Remote IRR clear and is dropped,
                    // instead of pre-clearing the in-service state.
                    // Armed by the LIVE trigger mode - this branch - and NOT
                    // by a mode sampled at load: see REMOTE IRR SET ARM in the
                    // header, where the sampled copy livelocked an edge->level
                    // rewrite during an in-flight delivery.
                    if (w_deliv_accept && (r_out_irq == IRQ_IDX_W'(i))) begin
                        r_remote_irr[i] <= 1'b1;
                    end else if (eoi_in && (eoi_vector == r_delivered_vector[i])) begin
                        // Matched against the DELIVERED vector, not cfg_vector.
                        r_remote_irr[i] <= 1'b0;
                    end
                end else begin
                    r_remote_irr[i] <= 1'b0;  // Always 0 for edge-triggered
                end
            )

            // Vector actually delivered on this pin. Latched for every trigger
            // mode; it only gates anything while Remote IRR is set, and Remote
            // IRR is level-only.
            `ALWAYS_FF_RST(clk, rst_n,
                if (`RST_ASSERTED(rst_n)) begin
                    r_delivered_vector[i] <= 8'h00;
                end else if (w_deliv_accept && (r_out_irq == IRQ_IDX_W'(i))) begin
                    r_delivered_vector[i] <= r_out_vector;
                end
            )
        end
    endgenerate

    // Export Remote IRR status
    generate
        for (i = 0; i < NUM_IRQS; i++) begin : g_status
            assign status_remote_irr[i]   = r_remote_irr[i];
            assign status_deliv_status[i] = r_out_valid && (r_out_irq == IRQ_IDX_W'(i));
        end
    endgenerate

    // Export arbitration ID (same as IOAPIC ID)
    assign status_arb_id = cfg_ioapic_id;

    // ========================================================================
    // Priority Arbitration - Find Highest Priority Pending IRQ
    // ========================================================================

    generate
        for (i = 0; i < NUM_IRQS; i++) begin : g_eligible
            // Edge pins request from the latch, level pins from the live
            // synchronized level - so a level pin re-requests by itself the
            // cycle after Remote IRR clears, with no edge needed.
            assign w_irq_request[i] = cfg_trigger_mode[i] ? w_irq_active[i]
                                                          : r_irq_pending[i];

            // Per-pin blocking: Remote IRR masks ONLY its own pin. The accept
            // term covers the one cycle in which the retiring pin still shows
            // as requesting (its latch clears / its Remote IRR sets on the
            // next edge) - without it the same interrupt is delivered twice.
            assign w_irq_eligible[i] = w_irq_request[i]
                                     && !cfg_mask[i]
                                     && !r_remote_irr[i]
                                     && !(w_deliv_accept && (r_out_irq == IRQ_IDX_W'(i)));
        end
    endgenerate

    // ROUND-ROBIN POINTER. Parked at the pin after the last accepted one, so
    // that pin is the LAST the rotated scan reaches rather than the first.
    // It advances only on an accept: a pick that is never taken must not move
    // the rotation, or a stalled consumer would walk it round the ring.
    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            r_rr_ptr <= '0;
        end else if (w_deliv_accept) begin
            r_rr_ptr <= (r_out_irq == IRQ_IDX_W'(NUM_IRQS-1)) ? '0
                                                             : (r_out_irq + 1'b1);
        end
    )

    // TWO SCANS, ONE SELECTOR. Static priority is the 82093AA scheme: scan up
    // from pin 0, lowest eligible number wins. Its weakness is stated in the
    // datasheet's own terms - a level pin that is eligible again the cycle
    // after software EOIs it holds the low ground forever, and every pin above
    // it starves.
    //
    // Round robin scans from r_rr_ptr and wraps, so the pin just served is the
    // last one reached. Priority becomes position in the rotation rather than
    // IRQ number, and every eligible pin is served before any pin is served
    // twice. The scan is written as a single pass over an offset because a
    // wrapped scan and a pair of scans are the same thing, and one loop is
    // one piece of logic to be right about.
    always_comb begin
        w_sel_irq   = '0;
        w_sel_valid = 1'b0;

        for (int j = 0; j < NUM_IRQS; j++) begin
            // The wrap is a compare-and-subtract rather than a modulo: it is
            // what a synthesiser builds for `%` by a non-power-of-two anyway,
            // and NUM_IRQS is not required to be a power of two.
            automatic int unsigned raw = cfg_rr_enable ? (int'(r_rr_ptr) + j) : j;
            automatic int unsigned k   = (raw >= NUM_IRQS) ? (raw - NUM_IRQS) : raw;
            if (w_irq_eligible[k] && !w_sel_valid) begin
                w_sel_irq   = IRQ_IDX_W'(k);
                w_sel_valid = 1'b1;
            end
        end
    end

    // ========================================================================
    // Delivery Output Stage (one entry, valid/ready)
    // ========================================================================

    // Load when the stage is empty or emptying this cycle. Registered payload,
    // so the outputs are Moore and stable for the whole handshake.
    assign w_out_load = w_sel_valid && (!r_out_valid || irq_out_ready);

    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            r_out_valid      <= 1'b0;
            r_out_irq        <= '0;
            r_out_vector     <= 8'h00;
            r_out_dest       <= 8'h00;
            r_out_dest_mode  <= 1'b0;
            r_out_deliv_mode <= 3'h0;
        end else if (w_out_load) begin
            r_out_valid      <= 1'b1;
            r_out_irq        <= w_sel_irq;
            r_out_vector     <= cfg_vector[w_sel_irq];
            r_out_dest       <= cfg_destination[w_sel_irq];
            r_out_dest_mode  <= cfg_dest_mode[w_sel_irq];
            r_out_deliv_mode <= cfg_deliv_mode[w_sel_irq];
        end else if (irq_out_ready) begin
            r_out_valid      <= 1'b0;
        end
    )

    // ========================================================================
    // Interrupt Output Interface
    // ========================================================================

    assign irq_out_valid      = r_out_valid;
    assign irq_out_vector     = r_out_valid ? r_out_vector     : 8'h00;
    assign irq_out_dest       = r_out_valid ? r_out_dest       : 8'h00;
    assign irq_out_dest_mode  = r_out_valid ? r_out_dest_mode  : 1'b0;
    assign irq_out_deliv_mode = r_out_valid ? r_out_deliv_mode : 3'h0;

endmodule : ioapic_core
