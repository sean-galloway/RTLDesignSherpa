// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: ioapic_deliv_merge_tb_top
// Purpose: DV wrapper putting ioapic_deliv_merge where it goes -- between TWO
//          real apb4_ioapic delivery channels and one receiver (RLB-008).
//
// The formal proof covers routing, retry routing and grant exclusivity at the
// merge's own ports, with free inputs. What it cannot show is that the merge
// fits between real producers: that src_ready actually closes each IOAPIC's
// handshake, that m_src_id names the IOAPIC the message truly came from, and
// that a refusal reaches ONLY the source whose message was refused.
//
// TWO APB PREFIXES. The IOAPICs are addressed independently as s0_apb_* and
// s1_apb_*. cocotb_bus composes `<prefix>_<SIGNAL>` (bus.py:58) rather than
// substring-searching, so these bind exactly and cannot capture each other's
// signals; a wrong prefix raises instead of binding loosely.
//
// WHO DRIVES WHAT. src_ready/src_retry are merge OUTPUTS wired straight back
// to each IOAPIC's irq_out_ready/irq_out_retry, so both producer handshakes
// close in RTL with exactly one driver per net. The testbench drives only
// m_ready/m_retry, on the merged side, where the receiver belongs.
`timescale 1ns / 1ps

module ioapic_deliv_merge_tb_top #(
    parameter int NUM_IRQS   = 24,
    parameter int CDC_ENABLE = 0,
    parameter int NUM_SRC    = 2
) (
    input  logic                    pclk,
    input  logic                    presetn,
    input  logic                    ioapic_clk,
    input  logic                    ioapic_resetn,

    // --- IOAPIC 0 APB ---
    input  logic                    s0_apb_PSEL,
    input  logic                    s0_apb_PENABLE,
    output logic                    s0_apb_PREADY,
    input  logic [11:0]             s0_apb_PADDR,
    input  logic                    s0_apb_PWRITE,
    input  logic [31:0]             s0_apb_PWDATA,
    input  logic [3:0]              s0_apb_PSTRB,
    input  logic [2:0]              s0_apb_PPROT,
    output logic [31:0]             s0_apb_PRDATA,
    output logic                    s0_apb_PSLVERR,

    // --- IOAPIC 1 APB ---
    input  logic                    s1_apb_PSEL,
    input  logic                    s1_apb_PENABLE,
    output logic                    s1_apb_PREADY,
    input  logic [11:0]             s1_apb_PADDR,
    input  logic                    s1_apb_PWRITE,
    input  logic [31:0]             s1_apb_PWDATA,
    input  logic [3:0]              s1_apb_PSTRB,
    input  logic [2:0]              s1_apb_PPROT,
    output logic [31:0]             s1_apb_PRDATA,
    output logic                    s1_apb_PSLVERR,

    // --- IRQ / EOI per IOAPIC ---
    input  logic [NUM_IRQS-1:0]     irq0_in,
    input  logic [NUM_IRQS-1:0]     irq1_in,
    input  logic                    eoi0_in,
    input  logic [7:0]              eoi0_vector,
    input  logic                    eoi1_in,
    input  logic [7:0]              eoi1_vector,

    // --- each source channel, OBSERVED (the merge drives ready/retry) ---
    output logic [NUM_SRC-1:0]      src_valid,
    output logic [NUM_SRC-1:0]      src_ready,
    output logic [NUM_SRC-1:0]      src_retry,
    output logic [7:0]              src0_vector,
    output logic [7:0]              src1_vector,

    // --- the merged channel; the testbench is the receiver here ---
    output logic                    m_valid,
    output logic [7:0]              m_vector,
    output logic [7:0]              m_dest,
    output logic                    m_dest_mode,
    output logic [2:0]              m_deliv_mode,
    output logic [((NUM_SRC > 1) ? $clog2(NUM_SRC) : 1)-1:0] m_src_id,
    input  logic                    m_ready,
    input  logic                    m_retry
);

    logic [7:0] w_src_vector     [NUM_SRC];
    logic [7:0] w_src_dest       [NUM_SRC];
    logic [2:0] w_src_deliv_mode [NUM_SRC];
    logic [NUM_SRC-1:0] w_src_dest_mode;

    assign src0_vector = w_src_vector[0];
    assign src1_vector = w_src_vector[1];

    apb4_ioapic #(.NUM_IRQS(NUM_IRQS), .CDC_ENABLE(CDC_ENABLE)) u_ioapic0 (
        .pclk(pclk), .presetn(presetn),
        .ioapic_clk(ioapic_clk), .ioapic_resetn(ioapic_resetn),
        .s_apb_PSEL(s0_apb_PSEL),       .s_apb_PENABLE(s0_apb_PENABLE),
        .s_apb_PREADY(s0_apb_PREADY),   .s_apb_PADDR(s0_apb_PADDR),
        .s_apb_PWRITE(s0_apb_PWRITE),   .s_apb_PWDATA(s0_apb_PWDATA),
        .s_apb_PSTRB(s0_apb_PSTRB),     .s_apb_PPROT(s0_apb_PPROT),
        .s_apb_PRDATA(s0_apb_PRDATA),   .s_apb_PSLVERR(s0_apb_PSLVERR),
        .irq_in(irq0_in),
        .irq_out_valid(src_valid[0]),       .irq_out_vector(w_src_vector[0]),
        .irq_out_dest(w_src_dest[0]),       .irq_out_dest_mode(w_src_dest_mode[0]),
        .irq_out_deliv_mode(w_src_deliv_mode[0]),
        .irq_out_ready(src_ready[0]),       .irq_out_retry(src_retry[0]),
        .eoi_in(eoi0_in), .eoi_vector(eoi0_vector),
        // MSI config outputs (RLB-008): this harness exercises the
        // delivery channel, not MSI. Explicit and open -- omitting them
        // entirely is PINMISSING.
        .cfg_msi_addr(), .cfg_msi_data()
    );

    apb4_ioapic #(.NUM_IRQS(NUM_IRQS), .CDC_ENABLE(CDC_ENABLE)) u_ioapic1 (
        .pclk(pclk), .presetn(presetn),
        .ioapic_clk(ioapic_clk), .ioapic_resetn(ioapic_resetn),
        .s_apb_PSEL(s1_apb_PSEL),       .s_apb_PENABLE(s1_apb_PENABLE),
        .s_apb_PREADY(s1_apb_PREADY),   .s_apb_PADDR(s1_apb_PADDR),
        .s_apb_PWRITE(s1_apb_PWRITE),   .s_apb_PWDATA(s1_apb_PWDATA),
        .s_apb_PSTRB(s1_apb_PSTRB),     .s_apb_PPROT(s1_apb_PPROT),
        .s_apb_PRDATA(s1_apb_PRDATA),   .s_apb_PSLVERR(s1_apb_PSLVERR),
        .irq_in(irq1_in),
        .irq_out_valid(src_valid[1]),       .irq_out_vector(w_src_vector[1]),
        .irq_out_dest(w_src_dest[1]),       .irq_out_dest_mode(w_src_dest_mode[1]),
        .irq_out_deliv_mode(w_src_deliv_mode[1]),
        .irq_out_ready(src_ready[1]),       .irq_out_retry(src_retry[1]),
        .eoi_in(eoi1_in), .eoi_vector(eoi1_vector),
        // MSI config outputs (RLB-008): this harness exercises the
        // delivery channel, not MSI. Explicit and open -- omitting them
        // entirely is PINMISSING.
        .cfg_msi_addr(), .cfg_msi_data()
    );

    ioapic_deliv_merge #(.NUM_SRC(NUM_SRC)) u_merge (
        .clk(pclk), .rst_n(presetn),
        .src_valid(src_valid),
        .src_vector(w_src_vector),
        .src_dest(w_src_dest),
        .src_dest_mode(w_src_dest_mode),
        .src_deliv_mode(w_src_deliv_mode),
        .src_ready(src_ready),
        .src_retry(src_retry),
        .m_valid(m_valid),       .m_vector(m_vector),
        .m_dest(m_dest),         .m_dest_mode(m_dest_mode),
        .m_deliv_mode(m_deliv_mode), .m_src_id(m_src_id),
        .m_ready(m_ready),       .m_retry(m_retry)
    );

endmodule : ioapic_deliv_merge_tb_top
