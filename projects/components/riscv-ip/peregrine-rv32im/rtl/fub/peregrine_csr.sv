// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: peregrine_csr
// Purpose: Machine-mode CSR file and trap state for peregrine (PRD P6).
//          One combinational read port (the CSR instruction in EX), one
//          write port and the trap-entry / mret updates (all three driven
//          by the MEM-stage commit, at most one per cycle), and the
//          interrupt-pending decision the commit point samples.
//
// Documentation: projects/components/riscv-ip/peregrine-rv32im/PRD.md
// Subsystem: riscv-ip/peregrine-rv32im
//
// Author: sean galloway
// Created: 2026-11-23
//
// Parameters:
//   - M_EXT: sets misa.M (bit 12).
//   - BUSERR_EN: 1 (the cached build) adds the bus-error report of
//     TASK-005: platform interrupt 16 (mip.16 from irq_buserr, mie.16
//     writable, mcause 0x8000_0010) and the custom CSR mbuserr (0x7C0),
//     which reads buserr_info and pulses buserr_clear on a write.  0 (the
//     cacheless build): neither exists, the CSR file is the stage-1 one.
//
// Notes:
//   - Implemented: mstatus (MIE, MPIE; MPP reads 11), misa (read-only,
//     writes ignored: WARL), mie (MSIE/MTIE/MEIE), mtvec (direct mode only:
//     bits 1:0 read 0), mstatush (reads 0), mscratch, mepc (bits 1:0 read
//     0: IALIGN=32), mcause, mtval, mip (MSIP/MTIP/MEIP from the pins,
//     writes ignored), and the read-only ID registers (mvendorid, marchid,
//     mimpid, mhartid, mconfigptr, all 0).  Anything else is r_exists = 0,
//     which the core turns into an illegal-instruction exception.
//   - PMP with zero entries: pmpcfg0-15 (0x3A0-0x3AF) and pmpaddr0-63
//     (0x3B0-0x3EF) exist, read 0 and ignore writes.  The privileged spec
//     makes every PMP field WARL and allows it to be read-only zero, so a
//     core without PMP must still accept the accesses (the riscv-tests
//     p-env writes pmpaddr0/pmpcfg0 unconditionally).
//   - No counters (PRD P6, no Zicntr).
//   - Interrupt priority when several are pending: BUSERR (16) > MEI > MSI
//     > MTI.  The privileged spec (3.1.9) orders the standard ones and lets
//     the platform place codes >= 16; spike also takes them first.
//
// Related Modules:
//   - peregrine_core (the only instance)

`timescale 1ns / 1ps

`include "reset_defs.svh"

module peregrine_csr #(
    parameter bit M_EXT     = 1'b0,
    parameter bit BUSERR_EN = 1'b0
) (
    input  logic        clk,
    input  logic        rst_n,
    // Read port (EX)
    input  logic [11:0] raddr,
    output logic [31:0] rdata,
    output logic        r_exists,
    // Write port (MEM commit)
    input  logic        wen,
    input  logic [11:0] waddr,
    input  logic [31:0] wdata,
    // Trap entry and return (MEM commit)
    input  logic        trap_take,
    input  logic [31:0] trap_cause,
    input  logic [31:0] trap_epc,
    input  logic [31:0] trap_tval,
    input  logic        mret_take,
    // Interrupt pins (level)
    input  logic        irq_software,
    input  logic        irq_timer,
    input  logic        irq_external,
    // Bus-error report (BUSERR_EN): the sticky write-back error (level, an
    // interrupt), the value mbuserr reads, and its clear (a write to it)
    input  logic        irq_buserr,
    input  logic [31:0] buserr_info,
    output logic        buserr_clear,
    // To the commit point and the PC mux
    output logic [31:0] mtvec,
    output logic [31:0] mepc,
    output logic        irq_pending,
    output logic [31:0] irq_cause
);

    import peregrine_pkg::*;

    localparam int MSTATUS_MIE  = 3;
    localparam int MSTATUS_MPIE = 7;
    localparam int IRQ_MSI      = 3;
    localparam int IRQ_MTI      = 7;
    localparam int IRQ_MEI      = 11;
    localparam int IRQ_BUSERR   = 16;

    localparam logic [31:0] MISA_VALUE = 32'h4000_0000              // MXL = 1
                                       | (32'h1 << 8)               // I
                                       | (M_EXT ? (32'h1 << 12) : 32'h0);
    localparam logic [11:0] CSR_PMPCFG0   = 12'h3A0;   // pmpcfg0..15  0x3A0-0x3AF
    localparam logic [11:0] CSR_PMPADDR63 = 12'h3EF;   // pmpaddr0..63 0x3B0-0x3EF
    localparam logic [31:0] MIE_MASK   = (32'h1 << IRQ_MSI) | (32'h1 << IRQ_MTI)
                                       | (32'h1 << IRQ_MEI)
                                       | (BUSERR_EN ? (32'h1 << IRQ_BUSERR) : 32'h0);

    logic        r_mie_bit;     // mstatus.MIE
    logic        r_mpie_bit;    // mstatus.MPIE
    logic [31:0] r_mie;
    logic [31:2] r_mtvec;
    logic [31:0] r_mscratch;
    logic [31:2] r_mepc;
    logic [31:0] r_mcause;
    logic [31:0] r_mtval;

    logic [31:0] w_mstatus;
    logic [31:0] w_mip;

    assign w_mstatus = (32'(r_mie_bit)  << MSTATUS_MIE)
                     | (32'(r_mpie_bit) << MSTATUS_MPIE)
                     | (32'h3 << 11);                               // MPP = M
    assign w_mip     = (32'(irq_software) << IRQ_MSI)
                     | (32'(irq_timer)    << IRQ_MTI)
                     | (32'(irq_external) << IRQ_MEI)
                     | (32'(BUSERR_EN & irq_buserr) << IRQ_BUSERR);

    assign mtvec = {r_mtvec, 2'b00};
    assign mepc  = {r_mepc, 2'b00};

    // Read port.
    always_comb begin
        rdata    = 32'd0;
        r_exists = 1'b1;
        unique case (raddr)
            CSR_MSTATUS:    rdata = w_mstatus;
            CSR_MISA:       rdata = MISA_VALUE;
            CSR_MIE:        rdata = r_mie;
            CSR_MTVEC:      rdata = mtvec;
            CSR_MSTATUSH:   rdata = 32'd0;
            CSR_MSCRATCH:   rdata = r_mscratch;
            CSR_MEPC:       rdata = mepc;
            CSR_MCAUSE:     rdata = r_mcause;
            CSR_MTVAL:      rdata = r_mtval;
            CSR_MIP:        rdata = w_mip;
            CSR_MVENDORID,
            CSR_MARCHID,
            CSR_MIMPID,
            CSR_MHARTID,
            CSR_MCONFIGPTR: rdata = 32'd0;
            CSR_MBUSERR: begin
                rdata    = BUSERR_EN ? buserr_info : 32'd0;
                r_exists = BUSERR_EN;
            end
            // pmpcfg0-15 and pmpaddr0-63: zero entries, read 0.
            default:        r_exists = (raddr >= CSR_PMPCFG0) && (raddr <= CSR_PMPADDR63);
        endcase
    end

    // Interrupt decision: globally enabled, individually enabled, pending.
    // Registered (peregrine TASK-006, the 75 MHz build): mie -> decision ->
    // the D request valid -> amber's accept cone was a critical path, so the
    // commit point sees the decision one cycle after the pins and enables
    // make it. A CSR write, a trap entry or an mret clears it for that one
    // cycle, so a write that disables interrupts (or the MIE clear of a trap
    // entry) is never followed by an interrupt taken on the old enables.
    logic [31:0] w_irq_en;
    logic        r_irq_pending;
    logic [31:0] r_irq_cause;
    assign w_irq_en    = r_mie & w_mip & {32{r_mie_bit}};
    assign irq_pending = r_irq_pending;
    assign irq_cause   = r_irq_cause;
    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            r_irq_pending <= 1'b0;
            r_irq_cause   <= '0;
        end else begin
            r_irq_pending <= (|w_irq_en) & ~wen & ~trap_take & ~mret_take;
            r_irq_cause   <= w_irq_en[IRQ_BUSERR] ? {1'b1, MCAUSE_BUSERR} :
                             w_irq_en[IRQ_MEI]    ? {1'b1, MCAUSE_MEI}    :
                             w_irq_en[IRQ_MSI]    ? {1'b1, MCAUSE_MSI}    :
                                                    {1'b1, MCAUSE_MTI};
        end
    )

    // State.  Trap entry, mret and a CSR write never coincide: each is the
    // commit of the one instruction in MEM.
    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            r_mie_bit  <= 1'b0;
            r_mpie_bit <= 1'b0;
            r_mie      <= '0;
            r_mtvec    <= '0;
            r_mscratch <= '0;
            r_mepc     <= '0;
            r_mcause   <= '0;
            r_mtval    <= '0;
        end else if (trap_take) begin
            r_mpie_bit <= r_mie_bit;
            r_mie_bit  <= 1'b0;
            r_mepc     <= trap_epc[31:2];
            r_mcause   <= trap_cause;
            r_mtval    <= trap_tval;
        end else if (mret_take) begin
            r_mie_bit  <= r_mpie_bit;
            r_mpie_bit <= 1'b1;
        end else if (wen) begin
            unique case (waddr)
                CSR_MSTATUS: begin
                    r_mie_bit  <= wdata[MSTATUS_MIE];
                    r_mpie_bit <= wdata[MSTATUS_MPIE];
                end
                CSR_MIE:      r_mie      <= wdata & MIE_MASK;
                CSR_MTVEC:    r_mtvec    <= wdata[31:2];
                CSR_MSCRATCH: r_mscratch <= wdata;
                CSR_MEPC:     r_mepc     <= wdata[31:2];
                CSR_MCAUSE:   r_mcause   <= wdata;
                CSR_MTVAL:    r_mtval    <= wdata;
                default: ;   // misa, mstatush, mip: writes ignored (WARL);
                             // mbuserr: the write is the clear (below)
            endcase
        end
    )

    // mbuserr: any write (the MEM commit of a CSR instruction that writes it)
    // clears amber's sticky status.  The pulse is the commit's own cycle, so
    // the status drops at the next edge, together with the write; the
    // interrupt decision is cleared for that cycle like for any CSR write,
    // and sees the dropped status from the cycle after.
    assign buserr_clear = BUSERR_EN & wen & (waddr == CSR_MBUSERR);

endmodule : peregrine_csr
