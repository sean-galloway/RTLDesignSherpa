// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: andesite_init_sequencer
// Purpose: DDR4 power-up initialization FSM (RESET#, CKE, MR3..MR0, ZQCL)
//
// Documentation:
//   projects/components/mem-ctrl-ip/research-ip/andesite-ddr4-lpddr4/docs/andesite_mas/
//   ch02_blocks/02_init_sequencer.md (Table 2.2.1 parameters; Table 2.2.2
//   ports; the DDR4 FSM state-list fence; sequencing rules)
//
// The MR order is a citation, not a design choice (pumice's EMRS3-first
// correction is the family precedent). Every wait counts a CSR-loaded value
// captured at state entry -- the reload-only rule; nothing is compiled in.
// P1 scope is the DDR4 branch: any other memtype latches init_err, an honest
// error rather than a half-built LPDDR4 branch (the breadth track owns it).
// Ordering checks live in DV (the HAS ch06 item-1 checker), not here -- the
// family rule: no assertions in RTL.
//
// Port names follow MAS Table 2.2.2 verbatim (the doc-instantiation gate
// diffs this module against that table). csr_mrN_image are the per-MR
// init payloads; the CSR map lands with the RDL (HAS Ch 5) and until then
// the TB drives them directly.
//
// Author: sean galloway
// Created: 2026-10-04

`timescale 1ns / 1ps

module andesite_init_sequencer #(
    parameter int TINIT_WIDTH = 16,
    parameter int ADDR_WIDTH  = 18,
    parameter int BANK_WIDTH  = 2,
    parameter int DATA_WIDTH  = 16
) (
    input  logic                     clk,
    input  logic                     reset_n,

    input  logic                     csr_init_trigger,
    input  logic [2:0]               csr_memtype,
    input  logic                     csr_geardown_en,
    input  logic                     csr_parity_en,
    input  logic [TINIT_WIDTH-1:0]   tinit1_csr,
    input  logic [TINIT_WIDTH-1:0]   tinit3_csr,
    input  logic [TINIT_WIDTH-1:0]   tinit4_csr,
    input  logic [TINIT_WIDTH-1:0]   tdllk_csr,
    input  logic [TINIT_WIDTH-1:0]   tzqinit_csr,
    input  logic [TINIT_WIDTH-1:0]   tmrd_csr,
    input  logic [TINIT_WIDTH-1:0]   tmod_csr,

    input  logic [DATA_WIDTH-1:0]    csr_mr0_image,
    input  logic [DATA_WIDTH-1:0]    csr_mr1_image,
    input  logic [DATA_WIDTH-1:0]    csr_mr2_image,
    input  logic [DATA_WIDTH-1:0]    csr_mr3_image,
    input  logic [DATA_WIDTH-1:0]    csr_mr4_image,
    input  logic [DATA_WIDTH-1:0]    csr_mr5_image,
    input  logic [DATA_WIDTH-1:0]    csr_mr6_image,

    output logic [DATA_WIDTH-1:0]    mr_image_out,
    output logic                     mr_load,

    output logic                     reset_n_out,
    output logic                     cke_out,

    output logic                     cmd_req,
    input  logic                     cmd_ack,
    output andesite_pkg::dram_op_e   cmd_op,
    // 3 bits: the DRAM bank address fits in BANK_WIDTH, but the MRS path
    // carries the MR index (0-6) here, which needs three.
    output logic [2:0]               cmd_bank,
    output logic [ADDR_WIDTH-1:0]    cmd_addr,

    output logic                     zq_cal_start,
    output logic                     gear_down_entry,
    output logic                     parity_enable_out,
    output logic                     init_done,
    output logic                     init_err,
    output logic                     ca_train_start,

    // ----- TASK-006: CA-parity error recovery (MAS 02 fence). The recovery
    // sub-FSM sits beside the init FSM and never enters the bank machine;
    // the formatter's logged alert pulse is its entry event.
    input  logic                     parity_alert_i,
    input  logic [15:0]              recovery_interval_i,  // runtime CSR
    input  logic                     csr_telem_clear_i,
    output logic                     retract_req_o,        // maintenance-class
    input  logic                     retract_ack_i,
    output logic [1:0]               obs_recovery_state_o,
    output logic [15:0]              obs_alerts_seen_o,
    output logic [15:0]              obs_cmds_dropped_o,
    output logic [15:0]              obs_cmds_resent_o
);

    import andesite_pkg::*;

    // The MR order is the anchor's citation: MR3 first, MR0 last.
    localparam logic [2:0] MR_ORDER [7] = '{3, 6, 5, 4, 2, 1, 0};

    typedef enum logic [4:0] {
        ST_POR,
        ST_RESET_ASSERT,
        ST_RESET_DEASSERT_WAIT,
        ST_CKE_ENABLE,
        ST_CKE_WAIT,
        ST_MRS_REQ,
        ST_MRS_GAP,
        ST_ZQCL_REQ,
        ST_DLLK_ZQINIT_WAIT,
        ST_GEARDOWN_ENTRY,
        ST_GEAR_SYNC_WAIT,
        ST_READY,
        ST_ERROR
    } state_e;

    state_e                     r_state;
    logic [TINIT_WIDTH-1:0]     r_cnt;
    logic [TINIT_WIDTH-1:0]     w_load;
    logic                       w_enter;
    logic [TINIT_WIDTH-1:0]     r_residency;
    logic                       w_timeout;
    logic [2:0]                 r_mr_idx;
    logic [2:0]                 w_mr;
    logic [DATA_WIDTH-1:0]      w_mr_image;

    assign w_mr = MR_ORDER[r_mr_idx];

    always_comb begin
        unique case (w_mr)
            3'd0:    w_mr_image = csr_mr0_image;
            3'd1:    w_mr_image = csr_mr1_image;
            3'd2:    w_mr_image = csr_mr2_image;
            3'd3:    w_mr_image = csr_mr3_image;
            3'd4:    w_mr_image = csr_mr4_image;
            3'd5:    w_mr_image = csr_mr5_image;
            3'd6:    w_mr_image = csr_mr6_image;
            default: w_mr_image = '0;
        endcase
    end

    // Next-state logic.
    state_e r_state_d;
    always_comb begin
        r_state_d = r_state;
        unique case (r_state)
            ST_POR: begin
                if (csr_memtype == 3'(MEMTYPE_DDR4))
                    r_state_d = ST_RESET_ASSERT;
                else
                    r_state_d = ST_ERROR;   // P1: DDR4 branch only, honest error
            end
            ST_RESET_ASSERT:       if (r_cnt == 0) r_state_d = ST_RESET_DEASSERT_WAIT;
            ST_RESET_DEASSERT_WAIT: if (r_cnt == 0) r_state_d = ST_CKE_ENABLE;
            ST_CKE_ENABLE:                          r_state_d = ST_CKE_WAIT;
            ST_CKE_WAIT:           if (r_cnt == 0) r_state_d = ST_MRS_REQ;
            ST_MRS_REQ:            if (cmd_ack)    r_state_d = ST_MRS_GAP;
            ST_MRS_GAP:            if (r_cnt == 0) begin
                // r_mr_idx already points at the NEXT MRS; 7 remains means
                // MR0 (index 6) is still to come, anything past it is ZQCL.
                if (r_mr_idx <= 3'd6)
                    r_state_d = ST_MRS_REQ;
                else
                    r_state_d = ST_ZQCL_REQ;
            end
            ST_ZQCL_REQ:           if (cmd_ack)    r_state_d = ST_DLLK_ZQINIT_WAIT;
            ST_DLLK_ZQINIT_WAIT:   if (r_cnt == 0) begin
                if (csr_geardown_en)
                    r_state_d = ST_GEARDOWN_ENTRY;
                else
                    r_state_d = ST_READY;
            end
            ST_GEARDOWN_ENTRY:                    r_state_d = ST_GEAR_SYNC_WAIT;
            ST_GEAR_SYNC_WAIT:     if (r_cnt == 0) r_state_d = ST_READY;
            ST_READY:              if (csr_init_trigger) r_state_d = ST_POR;
            ST_ERROR:              if (csr_init_trigger) r_state_d = ST_POR;
            default: ;
        endcase

        // Residency watchdog: any non-terminal state that holds past the
        // counter's all-ones residency (a withheld cmd_ack is the expected
        // trigger) latches the error state instead of blocking forever.
        // The cap is the counter width's property, not a JEDEC timing.
        if (r_state != ST_READY && r_state != ST_ERROR && w_timeout)
            r_state_d = ST_ERROR;
    end

    assign w_timeout = (r_residency == {TINIT_WIDTH{1'b1}});

    // Counter load value for the state being ENTERED (reload-only rule: the
    // value is captured at entry, so a CSR write mid-wait is inert).
    always_comb begin
        unique case (r_state_d)
            ST_RESET_ASSERT:        w_load = tinit1_csr;
            ST_RESET_DEASSERT_WAIT: w_load = tinit3_csr;
            ST_CKE_WAIT:            w_load = tinit4_csr;
            // Entered on the ack edge of an MRS; r_mr_idx still holds
            // the acknowledged index -- 6 (MR0) means the gap to ZQCL is tMOD,
            // every earlier MRS gaps by tMRD. Selecting here avoids the
            // race against the index increment that a registered gap value had.
            ST_MRS_GAP:             w_load = (r_mr_idx == 3'd6) ? tmod_csr : tmrd_csr;
            ST_DLLK_ZQINIT_WAIT:    w_load = (tdllk_csr > tzqinit_csr)
                                              ? tdllk_csr : tzqinit_csr;
            ST_GEAR_SYNC_WAIT:      w_load = tdllk_csr;  // sync bound; Q1 refines
            default:                w_load = '0;
        endcase
    end

    assign w_enter = (r_state_d != r_state);

    always_ff @(posedge clk or negedge reset_n) begin
        if (!reset_n) begin
            r_state     <= ST_POR;
            r_cnt       <= '0;
            r_residency <= '0;
            r_mr_idx    <= '0;
        end else begin
            r_state <= r_state_d;
            if (w_enter) begin
                r_cnt <= w_load;
                r_residency <= '0;
            end else begin
                if (r_cnt != 0)
                    r_cnt <= r_cnt - 1'b1;
                r_residency <= r_residency + 1'b1;
            end

            if (r_state == ST_POR) begin
                r_mr_idx  <= '0;
            end else if (r_state == ST_MRS_REQ && cmd_ack) begin
                r_mr_idx  <= r_mr_idx + 1'b1;
            end
        end
    end

    // Outputs (Moore where practical; the command bus is qualified by req).
    always_ff @(posedge clk or negedge reset_n) begin
        if (!reset_n) begin
            reset_n_out       <= 1'b0;
            cke_out           <= 1'b0;
            parity_enable_out <= 1'b0;
        end else begin
            if (r_state_d == ST_RESET_ASSERT && w_enter)
                reset_n_out <= 1'b0;
            else if (r_state == ST_RESET_ASSERT && r_cnt == 0)
                reset_n_out <= 1'b1;

            if (r_state_d == ST_CKE_ENABLE && w_enter)
                cke_out <= 1'b1;
            else if (r_state_d == ST_POR && w_enter)
                cke_out <= 1'b0;

            if (r_state == ST_MRS_REQ && cmd_ack && w_mr == 3'd5)
                parity_enable_out <= csr_parity_en;
            else if (r_state_d == ST_POR && w_enter)
                parity_enable_out <= 1'b0;
        end
    end

    always_comb begin
        cmd_req           = 1'b0;
        cmd_op            = OP_NOP;
        cmd_bank          = '0;
        cmd_addr          = '0;
        mr_image_out      = '0;
        mr_load           = 1'b0;
        zq_cal_start      = 1'b0;
        gear_down_entry   = 1'b0;
        ca_train_start    = 1'b0;
        init_done         = 1'b0;
        init_err          = 1'b0;

        unique case (r_state)
            ST_MRS_REQ: begin
                cmd_req      = 1'b1;
                cmd_op       = OP_MRS;
                cmd_bank     = w_mr;
                cmd_addr     = ADDR_WIDTH'(w_mr_image);
                mr_image_out = w_mr_image;
                mr_load      = 1'b1;
            end
            ST_ZQCL_REQ: begin
                cmd_req      = 1'b1;
                cmd_op       = OP_ZQCL;
                // A10=1 is what makes the command ZQCL rather than ZQCS
                // (kmap anchor: A10 is the long/short select input).
                cmd_addr     = 18'h000400;
                zq_cal_start = 1'b1;
            end
            ST_GEARDOWN_ENTRY: begin
                gear_down_entry = 1'b1;
            end
            ST_READY: begin
                init_done = 1'b1;
            end
            ST_ERROR: begin
                init_err = 1'b1;
            end
            default: ;
        endcase
    end

    //=========================================================================
    // TASK-006: CA-parity error recovery sub-FSM (MAS 02 fence).
    //
    // IDLE -> ALERT_SEEN -> RESENDING -> IDLE. The recovery FSM is
    // transparent in IDLE; normal scheduler grants pass through unchanged.
    // ALERT_SEEN marks the in-grant command suspect, drops it (telemetry),
    // and raises retract_req_o -- a maintenance-class request that waits
    // for the scheduler's grant like the init FSM's own cmd_req/cmd_ack
    // pair, preserving request-never-preempts. RESENDING holds the
    // recovery interval (runtime CSR), then releases the scheduler to
    // re-issue the dropped command from its request queue. No full
    // re-initialization here; escalation is HAS open question Q4.
    //=========================================================================
    typedef enum logic [1:0] {
        RCV_IDLE       = 2'd0,
        RCV_ALERT_SEEN = 2'd1,
        RCV_RESENDING  = 2'd2
    } rcv_state_e;

    rcv_state_e         r_rcv_state;
    logic [15:0]        r_rcv_cnt;
    logic [15:0]        r_alerts_seen, r_cmds_dropped, r_cmds_resent;

    assign obs_recovery_state_o = r_rcv_state;
    assign obs_alerts_seen_o    = r_alerts_seen;
    assign obs_cmds_dropped_o   = r_cmds_dropped;
    assign obs_cmds_resent_o    = r_cmds_resent;
    assign retract_req_o        = (r_rcv_state == RCV_ALERT_SEEN);

    always_ff @(posedge clk or negedge reset_n) begin
        if (!reset_n) begin
            r_rcv_state    <= RCV_IDLE;
            r_rcv_cnt      <= 16'd0;
            r_alerts_seen  <= 16'd0;
            r_cmds_dropped <= 16'd0;
            r_cmds_resent  <= 16'd0;
        end else begin
            unique case (r_rcv_state)
                RCV_IDLE: begin
                    if (parity_alert_i) begin
                        r_rcv_state <= RCV_ALERT_SEEN;
                        if (!csr_telem_clear_i && (r_alerts_seen != 16'hFFFF))
                            r_alerts_seen  <= r_alerts_seen + 16'd1;
                        if (!csr_telem_clear_i && (r_cmds_dropped != 16'hFFFF))
                            r_cmds_dropped <= r_cmds_dropped + 16'd1;
                    end
                end

                RCV_ALERT_SEEN: begin
                    if (retract_ack_i) begin
                        r_rcv_state <= RCV_RESENDING;
                        r_rcv_cnt   <= recovery_interval_i;
                    end
                end

                RCV_RESENDING: begin
                    if (r_rcv_cnt == 16'd0) begin
                        r_rcv_state <= RCV_IDLE;
                        if (!csr_telem_clear_i && (r_cmds_resent != 16'hFFFF))
                            r_cmds_resent <= r_cmds_resent + 16'd1;
                    end else begin
                        r_rcv_cnt <= r_rcv_cnt - 16'd1;
                    end
                end

                default: r_rcv_state <= RCV_IDLE;
            endcase

            // Explicit firmware clear zeroes the counters; it does not
            // disturb the FSM. Clear wins over a same-cycle count.
            if (csr_telem_clear_i) begin
                r_alerts_seen  <= 16'd0;
                r_cmds_dropped <= 16'd0;
                r_cmds_resent  <= 16'd0;
            end
        end
    end

endmodule : andesite_init_sequencer
