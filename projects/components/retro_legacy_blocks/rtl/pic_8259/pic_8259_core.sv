// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: pic_8259_core
// Purpose: Intel 8259A-compatible interrupt controller core, 8 IRQ inputs
//
// Parameters:
//   - SYNC_STAGES: irq_in synchronizer depth, >= 2. Default 2.
//
// ============================================================================
// ACKNOWLEDGE BY READ  (GitHub #50, C3/C4)
// ============================================================================
// The 8259A moves a request from the IRR to the ISR during the CPU's INTA bus
// cycle. APB has no INTA cycle, and this block used to have no substitute at
// all: nothing set the ISR, so EOI, nesting and special mask mode were all
// no-ops on dead state (C3), and an edge-triggered IRR bit had no clear path
// at all, so int_out latched high forever after the first edge (C4).
//
// The substitute is a READ of the PIC_INTA register (APB 0x02C), the way the
// ARM PL190 VIC acknowledges through a read of VICVectAddr.
// pic_8259_config_regs turns that read into a ONE-CYCLE `inta_ack` strobe.
// On that strobe, if a request is eligible (see PRIORITY below):
//
//   - inta_vector / inta_valid present the vector BEFORE the acknowledge; they
//     are combinational, and PIC_INTA is a wire in the register block, so the
//     value the bridge captures in the strobe cycle is the pre-acknowledge one.
//   - ISR[irq] sets.
//   - IRR[irq] clears in EDGE mode. In LEVEL mode IRR follows the pin, so the
//     acknowledge does not touch it and the pin holding high re-requests as
//     soon as the level is EOI'd - which is what a level-triggered input means.
//   - In AEOI mode the same cycle also clears ISR[irq] (the set and the clear
//     collapse, so the bit is never observable), and if rotate-on-AEOI is armed
//     the priority base rotates ONCE, to the acknowledged level.
//
// With nothing eligible the read returns valid = 0 and the spurious vector
// base[7:3] | 7 (the 8259A spurious-IRQ7 convention) and has NO side effects.
//
// ============================================================================
// PRIORITY
// ============================================================================
// r_priority_base names the LOWEST-priority level. The resolver scans k = 0..7
// visiting level
//
//     idx = (r_priority_base + 1 + k) mod 8
//
// in DESCENDING priority: k = 0 is the highest-priority level and k = 7 is the
// base itself. That is a ROTATION of the level index, not a reflection. Checked
// at an asymmetric point rather than at the default base = 7, where the order
// degenerates to 0,1,...,7 and a reflection would look identical: with
// base = 3 the visit order must be 4,5,6,7,0,1,2,3 - i.e. IRQ4 outranks IRQ2.
// (The starving round-robin arbiter in the handbook's escape-analysis note is
// exactly this mistake made at the symmetric input.)
//
// A level is ELIGIBLE when it is requesting, unmasked, and NO level of equal or
// higher priority is in service. The scan expresses that directly: walk in
// priority order and stop at the first level that is either in service
// (-> blocked, nothing below it may interrupt) or requesting-and-unmasked
// (-> that is the winner). The ISR is tested FIRST at each level, so an
// in-service level blocks ITSELF as well as everything below it - the 8259A
// rule. A second edge on a level already in service still SETS its IRR bit
// (the request is remembered), it simply is not delivered until the EOI; then
// INT reasserts and the next acknowledge returns that level again.
//
// One predicate drives both the INT pin and the acknowledge, so they can never
// disagree.
//
// SPECIAL MASK MODE (OCW3 SMM) is IMR-GATED, not a blanket lift. The datasheet
// rule is that a mask bit set in OCW1 "inhibits further interrupts at that
// level and enables interrupts from all other levels that are not masked": a
// handler masks its OWN level and sets SMM, and only THAT level stops blocking.
// So under SMM an in-service level is removed from the blocking set exactly
// when its IMR bit is set; an in-service level that is still unmasked keeps
// blocking, precisely as in normal mode.
//
// The SAME gated set is what a NON-SPECIFIC EOI retires - the highest-priority
// in-service level among those not masked, per the datasheet's SMM note. A
// handler that masked its own level and enabled SMM so a lower level could run
// therefore has its own EOI retire ITS level, not the outer masked one.
//
// COMMAND STROBES. Every ICW/OCW write strobe reaching this core is one cycle
// wide, aligned with the register field it wrote, and only asserted for a write
// that actually carried byte enables - a PSTRB = 0 write cannot replay the
// stored command. pic_8259_config_regs owns all three properties; see its
// header.
//
// ============================================================================
// DEVIATIONS from a real 8259A (stated, not hidden)
// ============================================================================
//   - No cascade. ICW3 (cascade), ICW4 buffered-mode and ICW4 SFNM are
//     documented STORAGE in the register block. They are `sw = w`, so software
//     can write them and the regblock holds the value, but a READ returns ZERO
//     - they are not read back. Nothing consumes them, so they are not wired
//     into this core. SFNM in particular is not implemented - the ordinary
//     non-SFNM nesting rule above is what runs.
//   - OCW3 poll and read-register-select are likewise storage only; IRR and ISR
//     have their own read-only registers, which is why the command is moot.
//   - Re-initialization (an ICW1 write) clears IRR, ISR, special mask mode,
//     rotate-on-AEOI and returns the priority base to 7 (IRQ0 highest), which
//     is what ICW1 does on a real part. It does NOT reset the ICW4 storage.
//
// In-service blocking and special mask mode are NOT deviations: both follow the
// datasheet exactly - see PRIORITY above. An earlier revision of this fix let a
// level re-interrupt itself and made SMM lift blocking unconditionally; both
// were reverted once the tests encoding them were corrected.
//
// Follows the HPET/PIT pattern: core logic separate from the register wrapper.
//
// Documentation: projects/components/retro_legacy_blocks/rtl/pic_8259/README.md
// Subsystem: retro_legacy_blocks/pic_8259
//
// Created: 2025-11-16
// Updated: 2026-09-09 - GitHub #50: acknowledge-by-read, live ISR/IRR, gated
//                       OCW2/OCW3, one-shot AEOI rotation, init FSM hold,
//                       irq_in synchronizer, dead code removed
// Updated: 2026-09-09 - GitHub #50 follow-up: in-service self-block and
//                       IMR-gated special mask mode, both per the datasheet
// Updated: 2026-09-09 - GitHub #50 review: IMR-gated non-specific-EOI target,
//                       edge reference tracks unconditionally and the IRR
//                       observes while disabled (pic_enable gates delivery)

`timescale 1ns / 1ps

`include "reset_defs.svh"

module pic_8259_core #(
    parameter int SYNC_STAGES = 2   // irq_in metastability filter depth, >= 2
) (
    input  logic       clk,
    input  logic       rst_n,       // Active-low reset

    //========================================================================
    // Configuration (from pic_8259_config_regs)
    //========================================================================
    input  logic       cfg_pic_enable,
    input  logic       cfg_init_mode,      // start/allow init; consumed by ICW1
    input  logic       cfg_ic4,            // ICW1.IC4  - ICW4 needed
    input  logic       cfg_sngl,           // ICW1.SNGL - single (no ICW3)
    input  logic       cfg_ltim,           // ICW1.LTIM - level triggered
    input  logic [7:0] cfg_vector_base,    // ICW2 - only [7:3] reach the vector
    input  logic       cfg_aeoi,           // ICW4.AEOI
    input  logic [7:0] cfg_imr,            // OCW1 - the ONE copy of the mask

    //========================================================================
    // ICW/OCW write strobes - ONE cycle, aligned with the field storage
    //========================================================================
    input  logic       icw1_wr,
    input  logic       icw2_wr,
    input  logic       icw3_wr,
    input  logic       icw4_wr,
    input  logic       ocw2_wr,
    input  logic       ocw3_wr,

    input  logic [2:0] ocw2_irq_level,
    input  logic [2:0] ocw2_eoi_cmd,
    input  logic [1:0] ocw3_smm_cmd,

    //========================================================================
    // Acknowledge by read (PIC_INTA)
    //========================================================================
    input  logic       inta_ack,           // ONE cycle per PIC_INTA read
    output logic [7:0] inta_vector,        // pre-acknowledge vector
    output logic       inta_valid,         // pre-acknowledge valid

    //========================================================================
    // Status (to pic_8259_config_regs)
    //========================================================================
    output logic [7:0] irr_out,
    output logic [7:0] isr_out,
    output logic       init_complete,
    output logic [2:0] icw_step,
    output logic       int_output,
    output logic [2:0] highest_priority,

    //========================================================================
    // Hardware interface
    //========================================================================
    input  logic [7:0] irq_in              // asynchronous; synchronized below
);

    //========================================================================
    // Types
    //========================================================================

    typedef enum logic [2:0] {
        INIT_IDLE       = 3'd0,
        INIT_WAIT_ICW2  = 3'd1,
        INIT_WAIT_ICW3  = 3'd2,
        INIT_WAIT_ICW4  = 3'd3,
        INIT_COMPLETE   = 3'd4
    } init_state_t;

    //========================================================================
    // Internal Registers
    //========================================================================

    init_state_t r_init_state;
    logic        r_init_mode_d;       // cfg_init_mode, delayed, for edge detect
    logic        r_init_armed;        // init requested, not yet consumed by ICW1

    logic [7:0]  r_irq_sync [SYNC_STAGES];
    logic [7:0]  r_irq_last;          // for edge detection

    logic [7:0]  r_irr;
    logic [7:0]  r_isr;

    logic [2:0]  r_priority_base;     // LOWEST-priority level
    logic        r_rotate_on_aeoi;
    logic        r_special_mask_mode;

    //========================================================================
    // Combinational
    //========================================================================

    logic        w_running;           // initialized AND enabled
    logic [7:0]  w_irq;               // synchronized irq_in
    logic [7:0]  w_irq_trigger;
    logic [7:0]  w_req_unmasked;
    logic [7:0]  w_block_isr;

    logic        w_ack_valid;         // an eligible request exists
    logic [2:0]  w_ack_irq;
    logic        w_top_req_valid;
    logic [2:0]  w_top_req_irq;
    logic        w_top_isr_valid;
    logic [2:0]  w_top_isr_irq;

    logic        w_ack_now;           // this cycle's acknowledge takes effect
    logic [7:0]  w_ack_mask;
    logic        w_ocw2_exec;
    logic        w_ocw3_exec;
    logic [7:0]  w_isr_set;
    logic [7:0]  w_isr_clr;

`ifndef SYNTHESIS
    // Simulation-time parameter guard (same shape as the gpio/hpet guards). A
    // single-stage "synchronizer" is not one; the design point is 2.
    initial begin : param_check
        if (SYNC_STAGES < 2) begin
            $error("pic_8259_core: SYNC_STAGES=%0d but an input synchronizer needs >= 2",
                   SYNC_STAGES);
        end
    end
`endif

    //========================================================================
    // IRQ Input Synchronizer
    //========================================================================
    // irq_in comes from outside this clock domain (device pins, other blocks).
    // It used to be sampled directly, which is a metastability hazard on every
    // edge (GitHub #50 round_2 item 5 recorded the missing synchronizer as a
    // "synchronous input" ASSUMPTION; it is not one worth making for pins).
    // Cost is SYNC_STAGES cycles of latency on every IRQ, which the edge and
    // level timing in the test suite has ample margin for.

    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            for (int s = 0; s < SYNC_STAGES; s++) begin
                r_irq_sync[s] <= 8'h00;
            end
        end else begin
            r_irq_sync[0] <= irq_in;
            for (int s = 1; s < SYNC_STAGES; s++) begin
                r_irq_sync[s] <= r_irq_sync[s-1];
            end
        end
    )

    assign w_irq = r_irq_sync[SYNC_STAGES-1];

    //========================================================================
    // Initialization State Machine
    //========================================================================
    // cfg_init_mode is a START/ALLOW request, not a level that holds the core
    // out of INIT_COMPLETE. It used to be the latter, and with
    // auto_reset_init = 0 (nothing ever clears it) INIT_COMPLETE fell straight
    // back to INIT_IDLE on the very next cycle, making initialization
    // impossible - GitHub #50 round_2 item 3.
    //
    // It is now taken on its RISING EDGE into r_init_armed and CONSUMED by the
    // ICW1 write that starts the sequence. Writing PIC_CONFIG.init_mode 0 -> 1
    // requests a re-initialization; holding it at 1 afterwards does nothing,
    // which is what makes auto_reset_init = 0 a legal configuration. Taking the
    // LEVEL here instead of the edge reintroduces the same bounce one layer
    // down - measured, not assumed.

    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            r_init_mode_d <= 1'b0;
        end else begin
            r_init_mode_d <= cfg_init_mode;
        end
    )

    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            r_init_armed <= 1'b0;
        end else if (icw1_wr) begin
            r_init_armed <= 1'b0;                     // consumed by ICW1
        end else if (cfg_init_mode && !r_init_mode_d) begin
            r_init_armed <= 1'b1;                     // 0 -> 1 = "start init"
        end
    )

    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
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
                        // ICW3 is only needed in cascade mode
                        if (cfg_sngl) begin
                            r_init_state <= cfg_ic4 ? INIT_WAIT_ICW4 : INIT_COMPLETE;
                        end else begin
                            r_init_state <= INIT_WAIT_ICW3;
                        end
                    end
                end

                INIT_WAIT_ICW3: begin
                    if (icw3_wr) begin
                        r_init_state <= cfg_ic4 ? INIT_WAIT_ICW4 : INIT_COMPLETE;
                    end
                end

                INIT_WAIT_ICW4: begin
                    if (icw4_wr) begin
                        r_init_state <= INIT_COMPLETE;
                    end
                end

                INIT_COMPLETE: begin
                    // An ICW1 write restarts the sequence. A pending init
                    // request (r_init_armed) returns to IDLE to wait for it.
                    if (icw1_wr) begin
                        r_init_state <= INIT_WAIT_ICW2;
                    end else if (r_init_armed) begin
                        r_init_state <= INIT_IDLE;
                    end
                end

                default: r_init_state <= INIT_IDLE;
            endcase
        end
    )

    assign init_complete = (r_init_state == INIT_COMPLETE);
    assign icw_step      = r_init_state;
    assign w_running     = init_complete && cfg_pic_enable;

    //========================================================================
    // Edge / Level Detection
    //========================================================================

    // The edge reference tracks the synchronized pin UNCONDITIONALLY - while
    // the PIC is disabled and all the way through ICW1..ICW4, not only while
    // running. It used to be gated on `cfg_pic_enable && INIT_COMPLETE`, which
    // FROZE it: a line left high at disable time froze the reference at 1, so a
    // deassert-and-reassert inside the disabled window was invisible and the
    // new request was swallowed on re-enable. Tracking also guarantees the
    // converse - re-enabling never manufactures an edge from a line that was
    // already high, because the reference has followed it the whole time.
    //
    // The ICW1 resample this replaced is now the same assignment as every other
    // cycle, so it is gone rather than kept as a special case.
    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            r_irq_last <= 8'h00;
        end else begin
            r_irq_last <= w_irq;
        end
    )

    assign w_irq_trigger = cfg_ltim ? w_irq : (w_irq & ~r_irq_last);

    //========================================================================
    // Priority Resolution
    //========================================================================

    assign w_req_unmasked = r_irr & ~cfg_imr;
    // Levels whose in-service bit blocks. Under special mask mode an in-service
    // level stops blocking exactly when ITS OWN mask bit is set; an unmasked
    // in-service level keeps blocking, as in normal mode (see the header).
    assign w_block_isr    = r_isr & ~(r_special_mask_mode ? cfg_imr : 8'h00);

    // Eligible request: walk in DESCENDING priority from base+1. ISR FIRST,
    // request second - so an in-service level ends the scan at its own rank,
    // blocking itself and every lower-priority level until its EOI.
    always_comb begin
        logic [2:0] idx;
        logic       done;

        w_ack_valid = 1'b0;
        w_ack_irq   = 3'd0;
        done        = 1'b0;
        idx         = r_priority_base + 3'd1;    // highest priority level

        for (int k = 0; k < 8; k++) begin
            if (!done) begin
                if (w_block_isr[idx]) begin
                    done = 1'b1;                 // equal or higher level in service
                end else if (w_req_unmasked[idx]) begin
                    w_ack_valid = 1'b1;
                    w_ack_irq   = idx;
                    done        = 1'b1;
                end
            end
            idx = idx + 3'd1;
        end
    end

    // Highest-priority PENDING request, ignoring the ISR. This is what
    // PIC_STATUS.highest_priority reports - "which level would be next", not
    // "which level may interrupt now".
    always_comb begin
        logic [2:0] idx;

        w_top_req_valid = 1'b0;
        w_top_req_irq   = 3'd0;
        idx             = r_priority_base + 3'd1;

        for (int k = 0; k < 8; k++) begin
            if (!w_top_req_valid && w_req_unmasked[idx]) begin
                w_top_req_valid = 1'b1;
                w_top_req_irq   = idx;
            end
            idx = idx + 3'd1;
        end
    end

    // The level a non-specific EOI retires: the highest-priority level in
    // w_block_isr, i.e. the SAME IMR-gated set the blocking test uses, not raw
    // r_isr. Under special mask mode a handler masks its own level so lower
    // ones can run; the datasheet SMM note is that a non-specific EOI then
    // retires the highest-priority in-service level AMONG THOSE NOT MASKED -
    // otherwise the EOI issued by the lower-priority handler would retire the
    // outer, masked level instead of its own. Outside SMM the gate is empty and
    // this is exactly r_isr. w_top_isr_valid = 0 means nothing qualifies, and
    // the EOI is then a no-op rather than defaulting to level 0.
    always_comb begin
        logic [2:0] idx;

        w_top_isr_valid = 1'b0;
        w_top_isr_irq   = 3'd0;
        idx             = r_priority_base + 3'd1;

        for (int k = 0; k < 8; k++) begin
            if (!w_top_isr_valid && w_block_isr[idx]) begin
                w_top_isr_valid = 1'b1;
                w_top_isr_irq   = idx;
            end
            idx = idx + 3'd1;
        end
    end

    assign highest_priority = w_top_req_irq;

    //========================================================================
    // Interrupt Output and Acknowledge
    //========================================================================
    // ONE predicate for the INT pin and for the acknowledge, so a read can
    // never acknowledge something the pin did not offer.

    assign inta_valid  = w_ack_valid && w_running;
    assign int_output  = inta_valid;

    // ICW2[2:0] never reaches the vector: in 8086 mode the 8259A substitutes
    // the IRQ level for the low three bits. Spurious reads return level 7.
    assign inta_vector = inta_valid ? {cfg_vector_base[7:3], w_ack_irq}
                                    : {cfg_vector_base[7:3], 3'b111};

    assign w_ack_now  = inta_ack && inta_valid;
    assign w_ack_mask = w_ack_now ? (8'h01 << w_ack_irq) : 8'h00;

    //========================================================================
    // Interrupt Request Register (IRR)
    //========================================================================

    // cfg_pic_enable gates DELIVERY, not OBSERVATION: the IRR keeps tracking the
    // pins while the PIC is disabled, so a request that arrives during a
    // disabled window is delivered on re-enable instead of being dropped. It
    // used to be forced to zero every cycle while disabled, which lost that
    // request outright - and tracking the edge reference (above) alone does not
    // fix it, because the trigger pulse would arrive while this block was still
    // held at zero. INT and the acknowledge are still gated (see inta_valid).
    //
    // Initialization is different, deliberately: ICW1 clears the IRR and the
    // block does not observe again until INIT_COMPLETE, because mid-sequence
    // the trigger mode and vector base are still in flux. So an edge inside
    // ICW2..ICW4 is not latched - it is never MANUFACTURED either, which is
    // what the unconditional edge reference buys.
    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            r_irr <= 8'h00;
        end else if (icw1_wr) begin
            r_irr <= 8'h00;
        end else if (init_complete) begin
            if (cfg_ltim) begin
                // Level: IRR IS the pin. The acknowledge does not clear it.
                r_irr <= w_irq;
            end else begin
                // Edge: the acknowledge clears, a fresh edge re-sets. Set wins
                // over clear, so an edge arriving in the acknowledge cycle is
                // not swallowed.
                r_irr <= (r_irr & ~w_ack_mask) | w_irq_trigger;
            end
        end
    )

    //========================================================================
    // In-Service Register (ISR)
    //========================================================================
    // Set by the acknowledge, cleared by EOI (or immediately, in AEOI mode).
    // Clear wins over set: in AEOI the two masks are the same bit and collapse,
    // which is exactly "acknowledge then EOI in the same cycle".

    always_comb begin
        w_isr_set = w_ack_mask;
        w_isr_clr = (w_ack_now && cfg_aeoi) ? w_ack_mask : 8'h00;

        if (w_ocw2_exec) begin
            case (ocw2_eoi_cmd)
                3'b001,                                   // non-specific EOI
                3'b101: begin                             // rotate on non-spec EOI
                    // A non-specific EOI with nothing in service is a no-op -
                    // it must not retire (or rotate to) level 0 by default.
                    if (w_top_isr_valid) begin
                        w_isr_clr = w_isr_clr | (8'h01 << w_top_isr_irq);
                    end
                end
                3'b011,                                   // specific EOI
                3'b111: begin                             // rotate on specific EOI
                    w_isr_clr = w_isr_clr | (8'h01 << ocw2_irq_level);
                end
                default: begin
                    // 000/100 arm rotate-on-AEOI, 110 sets priority: no EOI
                end
            endcase
        end
    end

    // Cleared by reset and by ICW1 only - NOT by disabling the PIC, for the same
    // reason the IRR is not: pic_enable gates delivery, so a disable/enable
    // cycle in the middle of a handler must not silently retire its level.
    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            r_isr <= 8'h00;
        end else if (icw1_wr) begin
            r_isr <= 8'h00;
        end else if (init_complete) begin
            r_isr <= (r_isr | w_isr_set) & ~w_isr_clr;
        end
    )

    //========================================================================
    // OCW2 / OCW3 Command Gating
    //========================================================================
    // GitHub #50 round_3 item 1: rotation and special mask mode used to act on
    // the write strobe with no INIT_COMPLETE or pic_enable qualifier at all -
    // unlike IRR/ISR - so an OCW2 issued before initialization scrambled the
    // priority base and the state survived into normal operation.

    assign w_ocw2_exec = ocw2_wr && w_running;
    assign w_ocw3_exec = ocw3_wr && w_running;

    //========================================================================
    // Priority Rotation
    //========================================================================
    // ICW1 restores the power-on arbitration (fully nested, IRQ0 highest,
    // rotate-on-AEOI off) the way a real ICW1 does.

    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            r_priority_base  <= 3'd7;    // IRQ7 lowest => IRQ0 highest
            r_rotate_on_aeoi <= 1'b0;
        end else if (icw1_wr) begin
            r_priority_base  <= 3'd7;
            r_rotate_on_aeoi <= 1'b0;
        end else if (w_ocw2_exec) begin
            case (ocw2_eoi_cmd)
                3'b000: r_rotate_on_aeoi <= 1'b0;              // clear rotate-AEOI
                3'b100: r_rotate_on_aeoi <= 1'b1;              // set   rotate-AEOI
                3'b101: begin                                  // rotate on non-spec EOI
                    if (w_top_isr_valid) begin
                        r_priority_base <= w_top_isr_irq;      // base <= cleared level
                    end
                end
                3'b110: r_priority_base <= ocw2_irq_level;     // set priority
                3'b111: r_priority_base <= ocw2_irq_level;     // rotate on specific EOI
                default: begin
                    // 001 (non-specific EOI) and 011 (specific EOI) do not rotate
                end
            endcase
        end else if (w_ack_now && cfg_aeoi && r_rotate_on_aeoi) begin
            // ONE rotation per acknowledge. This used to be gated on
            // `cfg_aeoi && r_rotate_on_aeoi && int_output` with no strobe at
            // all, so with two or more pending requests the base alternated
            // EVERY clock forever (GitHub #50 round_2 item 1).
            r_priority_base <= w_ack_irq;
        end
    )

    //========================================================================
    // Special Mask Mode
    //========================================================================

    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            r_special_mask_mode <= 1'b0;
        end else if (icw1_wr) begin
            r_special_mask_mode <= 1'b0;      // ICW1 clears SMM
        end else if (w_ocw3_exec) begin
            case (ocw3_smm_cmd)
                2'b10:   r_special_mask_mode <= 1'b0;   // ESMM=1, SMM=0
                2'b11:   r_special_mask_mode <= 1'b1;   // ESMM=1, SMM=1
                default: begin
                    // ESMM=0: the SMM bit is ignored
                end
            endcase
        end
    )

    //========================================================================
    // Status Outputs
    //========================================================================

    assign irr_out = r_irr;
    assign isr_out = r_isr;

    //========================================================================
    // Simulation-only contract checks
    //========================================================================
`ifndef SYNTHESIS
`ifndef VERILATOR
    // The acknowledge may only retire a level the INT pin was actually
    // offering. If these ever diverge, software gets a vector for a level that
    // is masked or blocked - the C3/C4 class of defect, in the other direction.
    a_ack_implies_int: assert property (
        @(posedge clk) disable iff (`RST_ASSERTED(rst_n))
        w_ack_now |-> int_output
    ) else $error("pic_8259_core: acknowledge taken with INT deasserted");

    // An acknowledged level must be requesting, unmasked, and not blocked by
    // any in-service level - including its OWN in-service bit.
    a_ack_is_eligible: assert property (
        @(posedge clk) disable iff (`RST_ASSERTED(rst_n))
        w_ack_now |-> (r_irr[w_ack_irq] && !cfg_imr[w_ack_irq] && !w_block_isr[w_ack_irq])
    ) else $error("pic_8259_core: acknowledged IRQ%0d is masked, blocked or not requesting",
                  w_ack_irq);

    // inta_ack is a ONE-cycle strobe: pic_8259_config_regs rising-edge detects
    // the two-cycle swacc level. If a future bridge change lengthened it, the
    // acknowledge would fire twice per read and eat two interrupts.
    a_inta_ack_single_cycle: assert property (
        @(posedge clk) disable iff (`RST_ASSERTED(rst_n))
        inta_ack |=> !inta_ack
    ) else $error("pic_8259_core: inta_ack held for more than one cycle");
`endif
`endif

endmodule
