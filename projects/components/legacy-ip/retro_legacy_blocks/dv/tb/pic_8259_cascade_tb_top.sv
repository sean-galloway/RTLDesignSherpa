// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: pic_8259_cascade_tb_top
// Purpose: DV wrapper that puts two apb4_pic_8259 in the PC/AT cascade
//          arrangement, so the cascade RTL can be exercised at all
//          (RLB/pic_8259 TASK-001).
//
// The block's own DUT is a BARE apb4_pic_8259, so two PICs cannot be
// instantiated in the existing harness -- which is why the cascade path landed
// with no coverage. This wrapper is the harness.
//
// WHAT A PC/AT PAIR IS: the SLAVE's int_out drives one of the MASTER's IR
// lines (IR2 by convention), and the master's acknowledge is forwarded down so
// the master's PIC_INTA read returns the SLAVE's vector and retires the level
// in BOTH controllers. This block has no CAS[2:0] or SP/EN pins -- it
// acknowledges by an APB read of PIC_INTA -- so the cross-connect is the three
// signals below rather than a slave-ID broadcast.
//
// TWO PICs, ONE APB: PADDR[11] is a wrapper-level chip select -- clear selects
// the master, set selects the slave (+0x800). Bit 11 is MASKED OFF before the
// address reaches either block, because each decodes only 0x000-0x02C and
// would answer an unmasked 0x80C with PSLVERR instead of writing ICW3. This
// keeps ONE APB interface, so PIC8259TB binds unchanged rather than needing a
// second master BFM.
//
// The master's ports are re-exported under their EXACT original names --
// pclk, presetn, s_apb_*, irq_in, int_out -- which is every signal PIC8259TB
// touches, so the existing testbench class works against this wrapper as-is.

`timescale 1ns / 1ps

module pic_8259_cascade_tb_top #(
    parameter int SYNC_STAGES = 2
) (
    // --- apb4_pic_8259 (MASTER) ports, names preserved for PIC8259TB ---
    input  wire                    pclk,
    input  wire                    presetn,

    input  wire                    s_apb_PSEL,
    input  wire                    s_apb_PENABLE,
    output wire                    s_apb_PREADY,
    input  wire [11:0]             s_apb_PADDR,    // [11] selects master/slave
    input  wire                    s_apb_PWRITE,
    input  wire [31:0]             s_apb_PWDATA,
    input  wire [3:0]              s_apb_PSTRB,
    input  wire [2:0]              s_apb_PPROT,
    output wire [31:0]             s_apb_PRDATA,
    output wire                    s_apb_PSLVERR,

    // Master IR lines. IR2 is NOT taken from here -- it is driven by the
    // slave's int_out, exactly as a PC/AT pair wires it. A test that asserts
    // irq_in[2] is therefore asserting nothing, which is deliberate: it makes
    // "the slave raised the master" impossible to fake from the master side.
    input  wire [7:0]              irq_in,
    output wire                    int_out,        // MASTER INT pin

    // --- slave side ---
    input  wire [7:0]              slave_irq_in,   // IRQ8-15 in PC/AT terms

    // --- observability, so a test can prove the MECHANISM, not just the
    //     outcome: which of these three moved tells you where a failure is ---
    output wire                    slave_int,      // slave INT -> master IR2
    output wire                    cas_ack,        // master -> slave acknowledge
    output wire [7:0]              slave_vector    // slave's pre-ack vector
);

    //========================================================================
    // Chip select on PADDR[11], masked off before it reaches either block
    //========================================================================
    wire        w_sel_slave = s_apb_PADDR[11];
    wire [11:0] w_paddr     = {1'b0, s_apb_PADDR[10:0]};

    wire        w_m_PSEL = s_apb_PSEL & ~w_sel_slave;
    wire        w_s_PSEL = s_apb_PSEL &  w_sel_slave;

    wire        w_m_PREADY,  w_s_PREADY;
    wire [31:0] w_m_PRDATA,  w_s_PRDATA;
    wire        w_m_PSLVERR, w_s_PSLVERR;

    assign s_apb_PREADY  = w_sel_slave ? w_s_PREADY  : w_m_PREADY;
    assign s_apb_PRDATA  = w_sel_slave ? w_s_PRDATA  : w_m_PRDATA;
    assign s_apb_PSLVERR = w_sel_slave ? w_s_PSLVERR : w_m_PSLVERR;

    //========================================================================
    // Cascade cross-connect
    //========================================================================
    wire        w_cas_ack;       // master acknowledged a cascade level
    wire [7:0]  w_slave_vector;  // slave's pre-acknowledge vector

    assign cas_ack      = w_cas_ack;
    assign slave_vector = w_slave_vector;

    // PC/AT: the slave hangs off master IR2. Forcing the bit here rather than
    // OR-ing it keeps the source unambiguous.
    wire [7:0]  w_master_irq = {irq_in[7:3], slave_int, irq_in[1:0]};

    //========================================================================
    // MASTER
    //========================================================================
    apb4_pic_8259 #(
        .SYNC_STAGES   (SYNC_STAGES)
    ) u_master (
        .pclk          (pclk),
        .presetn       (presetn),
        .s_apb_PSEL    (w_m_PSEL),
        .s_apb_PENABLE (s_apb_PENABLE),
        .s_apb_PREADY  (w_m_PREADY),
        .s_apb_PADDR   (w_paddr),
        .s_apb_PWRITE  (s_apb_PWRITE),
        .s_apb_PWDATA  (s_apb_PWDATA),
        .s_apb_PSTRB   (s_apb_PSTRB),
        .s_apb_PPROT   (s_apb_PPROT),
        .s_apb_PRDATA  (w_m_PRDATA),
        .s_apb_PSLVERR (w_m_PSLVERR),
        .irq_in        (w_master_irq),
        .int_out       (int_out),
        // master: receives the slave's vector, emits the acknowledge
        .cas_ack       (w_cas_ack),
        .cas_vector    (w_slave_vector),
        .cas_ack_in    (1'b0),
        .inta_vector_o ()
    );

    //========================================================================
    // SLAVE
    //========================================================================
    apb4_pic_8259 #(
        .SYNC_STAGES   (SYNC_STAGES)
    ) u_slave (
        .pclk          (pclk),
        .presetn       (presetn),
        .s_apb_PSEL    (w_s_PSEL),
        .s_apb_PENABLE (s_apb_PENABLE),
        .s_apb_PREADY  (w_s_PREADY),
        .s_apb_PADDR   (w_paddr),
        .s_apb_PWRITE  (s_apb_PWRITE),
        .s_apb_PWDATA  (s_apb_PWDATA),
        .s_apb_PSTRB   (s_apb_PSTRB),
        .s_apb_PPROT   (s_apb_PPROT),
        .s_apb_PRDATA  (w_s_PRDATA),
        .s_apb_PSLVERR (w_s_PSLVERR),
        .irq_in        (slave_irq_in),
        .int_out       (slave_int),
        // slave: acknowledged by the MASTER's read, exports its vector upward
        .cas_ack       (),
        .cas_vector    (8'h00),
        .cas_ack_in    (w_cas_ack),
        .inta_vector_o (w_slave_vector)
    );

endmodule : pic_8259_cascade_tb_top
