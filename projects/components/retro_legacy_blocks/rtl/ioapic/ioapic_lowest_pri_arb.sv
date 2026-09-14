// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: ioapic_lowest_pri_arb
// Purpose: The consumer half of LowestPriority delivery (RLB-008).
//
// Documentation: projects/components/retro_legacy_blocks/docs/ioapic_mas/
// Subsystem: retro_legacy_blocks/ioapic
//
// Created: 2026-09-14
//
//==============================================================================
// WHAT THIS IS, AND WHY IT IS NOT INSIDE ioapic_core
//==============================================================================
// An IOAPIC does not track CPU priority and never did. On the APIC bus it
// broadcast the message and the local APICs arbitrated among themselves using
// their Arbitration Priority Registers; one of them accepted. So the IOAPIC
// already forwards everything the choice needs -- vector, destination,
// destination mode, delivery mode -- and the only thing it lacked was being
// told the choice FAILED. `ioapic_core.irq_out_retry` is that half.
//
// This module is the OTHER half: the arbitration itself, which RLB-008 records
// as delegated to the consumer by design. It lives outside ioapic_core on
// purpose. The delivery channel is a payload plus a valid/ready handshake plus
// a status precisely so a bridge can carry that shape onto a bus (the retry
// becomes a response); a bundle of live per-CPU priority registers could not
// cross a bus at all without going stale. Putting this logic inside the core
// would grow exactly those inputs and break that property.
//
// It is therefore a COMPANION, instantiated by an integrator next to
// apb4_ioapic, not a change to the block. Nothing instantiates it by default,
// so adding it changes no existing configuration.
//
//==============================================================================
// BEHAVIOUR
//==============================================================================
// Destination set, per the 82093AA rules the core forwards unmodified:
//   dest_mode = 0 (physical): the CPU whose APIC ID equals deliv_dest.
//   dest_mode = 1 (logical):  every CPU whose logical destination shares a bit
//                             with deliv_dest.
//
// Within that set:
//   deliv_mode = 001 (LowestPriority): the single eligible CPU with the
//       numerically lowest cpu_priority wins. Ties go to the lowest index --
//       deterministic by choice, and stated here because "lowest priority"
//       does not define a tie-break.
//   every other mode (Fixed, SMI, NMI, INIT, ExtINT): every eligible CPU in
//       the set is signalled. The IOAPIC does not act on these modes and
//       neither does this module; it only routes them to the destination set.
//
// `cpu_can_accept` is the consumer's own refusal input -- a real local APIC
// refuses when its IRR slot for that vector is already set, or when its
// current priority blocks it. Modelling that belongs to the LAPIC, not here,
// so it arrives as a port rather than being invented.
//
// retry is asserted, qualified by the handshake, when the destination set is
// empty or nobody in it can accept. That is exactly the condition
// ioapic_core's w_deliv_accept tests, so the interrupt is offered again.
//
// The decision is combinational and the handshake completes in one cycle.
// A registered variant would add a cycle of latency to every delivery; the
// core already registers its output stage, so there is nothing to pipeline
// here.

`timescale 1ns / 1ps

`include "reset_defs.svh"

module ioapic_lowest_pri_arb #(
    parameter int NUM_CPUS = 4
) (
    // No clk/rst_n: the decision is combinational and nothing here holds
    // state. They were in an earlier draft for symmetry with the rest of the
    // block, which is not a reason a port should exist -- verilator -Wall said
    // so. A registered variant can add them back when it has something to
    // register.

    // Delivery channel in, from ioapic_core's irq_out_*
    input  logic                 deliv_valid,
    input  logic [7:0]           deliv_vector,
    input  logic [7:0]           deliv_dest,
    input  logic                 deliv_dest_mode,
    input  logic [2:0]           deliv_deliv_mode,
    output logic                 deliv_ready,
    output logic                 deliv_retry,

    // Per-CPU state, owned by the consumer
    input  logic [7:0]           cpu_apic_id      [NUM_CPUS],
    input  logic [7:0]           cpu_logical_dest [NUM_CPUS],
    input  logic [7:0]           cpu_priority     [NUM_CPUS],
    input  logic [NUM_CPUS-1:0]  cpu_can_accept,

    // Accept strobe to the chosen CPU(s)
    output logic [NUM_CPUS-1:0]  cpu_irq_valid,
    output logic [7:0]           cpu_irq_vector,
    output logic [2:0]           cpu_irq_deliv_mode
);

    localparam logic [2:0] DELIV_LOWEST_PRI = 3'b001;
    // Index width, derived the way ioapic_core derives IRQ_IDX_W.
    localparam int IDX_W = (NUM_CPUS > 1) ? $clog2(NUM_CPUS) : 1;

    logic [NUM_CPUS-1:0] w_in_set;
    logic [NUM_CPUS-1:0] w_eligible;
    logic [NUM_CPUS-1:0] w_grant;
    logic                w_have_lowest;
    logic [7:0]          w_best_pri;
    logic [IDX_W-1:0]    w_best_idx;

    // Destination match. Physical compares the APIC ID; logical intersects the
    // mask, which is why a logical destination can name several CPUs.
    always_comb begin
        for (int i = 0; i < NUM_CPUS; i++) begin
            w_in_set[i] = deliv_dest_mode
                        ? ((cpu_logical_dest[i] & deliv_dest) != 8'h00)
                        : (cpu_apic_id[i] == deliv_dest);
        end
    end

    assign w_eligible = w_in_set & cpu_can_accept;

    // argmin over the eligible set. Strict less-than, so the lowest index wins
    // a tie.
    always_comb begin
        w_have_lowest = 1'b0;
        w_best_pri    = 8'hFF;
        w_best_idx    = 0;
        for (int i = 0; i < NUM_CPUS; i++) begin
            if (w_eligible[i] && (!w_have_lowest || (cpu_priority[i] < w_best_pri))) begin
                w_have_lowest = 1'b1;
                w_best_pri    = cpu_priority[i];
                w_best_idx    = IDX_W'(i);
            end
        end
    end

    always_comb begin
        w_grant = '0;
        if (deliv_deliv_mode == DELIV_LOWEST_PRI) begin
            if (w_have_lowest) w_grant[w_best_idx] = 1'b1;
        end else begin
            w_grant = w_eligible;
        end
    end

    // The message is always consumed in one cycle; retry says nobody took it.
    assign deliv_ready        = deliv_valid;
    assign deliv_retry        = deliv_valid && (w_grant == '0);
    assign cpu_irq_valid      = deliv_valid ? w_grant : '0;
    assign cpu_irq_vector     = deliv_vector;
    assign cpu_irq_deliv_mode = deliv_deliv_mode;

`ifndef SYNTHESIS
    // Elaboration-time parameter guard (sim only). Not an assertion in the
    // house sense: see vault/handbook/design/no-assertions-in-rtl.md.
    initial begin : param_check
        if (NUM_CPUS < 1 || NUM_CPUS > 255) begin
            $error("ioapic_lowest_pri_arb: NUM_CPUS=%0d out of range [1,255]", NUM_CPUS);
        end
    end
`endif

endmodule : ioapic_lowest_pri_arb
