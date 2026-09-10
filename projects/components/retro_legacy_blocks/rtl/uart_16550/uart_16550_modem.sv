// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: uart_16550_modem
// Purpose: UART 16550 modem control and status
//
// Description:
//   Input synchronizers for the four modem inputs, the loopback substitution
//   (DTR->DSR, RTS->CTS, OUT1->RI, OUT2->DCD), the four MSR delta flags with
//   their read-clear, and the four active-low modem outputs.
//
//   Split out of uart_16550_core to keep that file under the 800-line cap.
//   It is a clean cut: nothing outside this block reads the synchronized
//   levels, and the core only consumes the four delta flags to form the
//   modem-status interrupt condition.
//
// Notes:
//   - The delta flags CLEAR ON READ OF MSR (clr_*), matching PC16550D. The
//     clear wins over a same-cycle set, so a change that happens exactly when
//     software reads MSR is reported by the level bits (sts_cts and friends)
//     rather than being latched twice.
//   - Auto flow control is NOT implemented (ledger RLB-013): cts does not
//     gate the transmitter and MCR[5] has no field at all.
//
// Documentation: projects/components/retro_legacy_blocks/rtl/uart_16550/README.md
// Created: 2026-09-10

`timescale 1ns / 1ps

`include "reset_defs.svh"

module uart_16550_modem #(
    parameter int SYNC_STAGES = 2  // Input synchronizer stages
) (
    input  logic clk,
    input  logic rst_n,

    // Modem inputs (active low, asynchronous)
    input  logic cts_n,
    input  logic dsr_n,
    input  logic ri_n,
    input  logic dcd_n,

    // Modem outputs (active low)
    output logic dtr_n,
    output logic rts_n,
    output logic out1_n,
    output logic out2_n,

    // MCR
    input  logic cfg_dtr,
    input  logic cfg_rts,
    // Auto flow control: with AFE set, RTS is driven from the receiver's
    // own occupancy rather than from MCR[1], so the far end is told to stop
    // before the FIFO overruns. MCR[1] still has to be set for RTS to be
    // asserted at all - AFE decides when to DEASSERT it, it does not
    // override a deliberate deassertion by software.
    input  logic cfg_afe,
    input  logic rx_hold_off,   // RX FIFO at or above the trigger level
    input  logic cfg_out1,
    input  logic cfg_out2,
    input  logic cfg_loopback,

    // Clear strobes (read of MSR)
    input  logic clr_delta_cts,
    input  logic clr_delta_dsr,
    input  logic clr_trailing_ri,
    input  logic clr_delta_dcd,

    // MSR status
    output logic sts_cts,
    output logic sts_dsr,
    output logic sts_ri,
    output logic sts_dcd,
    output logic sts_delta_cts,
    output logic sts_delta_dsr,
    output logic sts_trailing_ri,
    output logic sts_delta_dcd
);

    // Modem inputs synchronized
    logic r_cts_sync [SYNC_STAGES];
    logic r_dsr_sync [SYNC_STAGES];
    logic r_ri_sync  [SYNC_STAGES];
    logic r_dcd_sync [SYNC_STAGES];

    logic w_cts, w_dsr, w_ri, w_dcd;
    logic r_cts_prev, r_dsr_prev, r_ri_prev, r_dcd_prev;
    logic r_delta_cts, r_delta_dsr, r_trailing_ri, r_delta_dcd;

    // Synchronize modem inputs
    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            for (int i = 0; i < SYNC_STAGES; i++) begin
                r_cts_sync[i] <= 1'b0;
                r_dsr_sync[i] <= 1'b0;
                r_ri_sync[i]  <= 1'b0;
                r_dcd_sync[i] <= 1'b0;
            end
        end else begin
            r_cts_sync[0] <= ~cts_n;  // Invert active-low inputs
            r_dsr_sync[0] <= ~dsr_n;
            r_ri_sync[0]  <= ~ri_n;
            r_dcd_sync[0] <= ~dcd_n;
            for (int i = 1; i < SYNC_STAGES; i++) begin
                r_cts_sync[i] <= r_cts_sync[i-1];
                r_dsr_sync[i] <= r_dsr_sync[i-1];
                r_ri_sync[i]  <= r_ri_sync[i-1];
                r_dcd_sync[i] <= r_dcd_sync[i-1];
            end
        end
    )

    assign w_cts = cfg_loopback ? cfg_rts : r_cts_sync[SYNC_STAGES-1];
    assign w_dsr = cfg_loopback ? cfg_dtr : r_dsr_sync[SYNC_STAGES-1];
    assign w_ri  = cfg_loopback ? cfg_out1 : r_ri_sync[SYNC_STAGES-1];
    assign w_dcd = cfg_loopback ? cfg_out2 : r_dcd_sync[SYNC_STAGES-1];

    // Delta detection
    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            r_cts_prev    <= 1'b0;
            r_dsr_prev    <= 1'b0;
            r_ri_prev     <= 1'b0;
            r_dcd_prev    <= 1'b0;
            r_delta_cts   <= 1'b0;
            r_delta_dsr   <= 1'b0;
            r_trailing_ri <= 1'b0;
            r_delta_dcd   <= 1'b0;
        end else begin
            r_cts_prev <= w_cts;
            r_dsr_prev <= w_dsr;
            r_ri_prev  <= w_ri;
            r_dcd_prev <= w_dcd;

            // Set on change, clear on register read
            if (clr_delta_cts) r_delta_cts <= 1'b0;
            else if (w_cts != r_cts_prev) r_delta_cts <= 1'b1;

            if (clr_delta_dsr) r_delta_dsr <= 1'b0;
            else if (w_dsr != r_dsr_prev) r_delta_dsr <= 1'b1;

            if (clr_trailing_ri) r_trailing_ri <= 1'b0;
            else if (~w_ri && r_ri_prev) r_trailing_ri <= 1'b1;  // RI trailing edge

            if (clr_delta_dcd) r_delta_dcd <= 1'b0;
            else if (w_dcd != r_dcd_prev) r_delta_dcd <= 1'b1;
        end
    )

    // Modem outputs
    assign dtr_n  = ~cfg_dtr;
    assign rts_n  = ~(cfg_rts && !(cfg_afe && rx_hold_off));
    assign out1_n = ~cfg_out1;
    assign out2_n = ~cfg_out2;

    // Modem status outputs
    assign sts_cts = w_cts;
    assign sts_dsr = w_dsr;
    assign sts_ri  = w_ri;
    assign sts_dcd = w_dcd;
    assign sts_delta_cts   = r_delta_cts;
    assign sts_delta_dsr   = r_delta_dsr;
    assign sts_trailing_ri = r_trailing_ri;
    assign sts_delta_dcd   = r_delta_dcd;

endmodule : uart_16550_modem
