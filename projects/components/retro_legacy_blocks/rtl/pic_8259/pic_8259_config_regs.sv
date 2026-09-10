// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: pic_8259_config_regs
// Purpose: Register wrapper for the 8259 PIC - PeakRDL block plus the strobe,
//          decode and acknowledge glue that does not belong in generated code
//
// ARCHITECTURE:
//   cmd/rsp --> peakrdl_to_cmdrsp --> strict decode --> pic_8259_regs (PeakRDL)
//                                                   --> hwif --> pic_8259_core
//
// ============================================================================
// DECODE CONTRACT (GitHub #50 round_2 item 2; same policy as ioapic #48)
// ============================================================================
// ONLY the twelve mapped registers 0x000-0x02C are software-visible in this
// block's 4 KB window. Every other address is DROPPED - the write is ignored,
// the read returns a defined zero - and answered with PSLVERR.
//
// The bug this closes: the generated block decodes six address bits
// (`cpuif_addr == 6'h4`), while the side-effect strobes in this file compared
// all twelve. A write to 0x044 therefore reached PIC_ICW1's storage (the 6-bit
// decode matched) but stepped no init FSM, and a write to 0x054 rewrote the
// IMR storage while the strobe that told the core about it never fired. There
// was no window check of any kind, and pic_8259_regs ties cpuif_wr_err to 0, so
// nothing in the block could ever raise PSLVERR.
//
// Now the strobes compare the SAME six bits the register block decodes, and
// regblk_req is gated so those six bits are only ever reached from a mapped
// address. Nothing in the RTL cross-checks the two decodes; see CHECK BY
// INSPECTION below for the DV guard if the RDL moves a register.
//
// Dropped accesses are acknowledged locally, combinationally, in the same shape
// the register block acks (peakrdl_to_cmdrsp HOLDS its request until an ack, so
// gating the request off without an ack would hang the APB).
//
// ============================================================================
// WRITE STROBES ARE ONE CYCLE, AND ALIGNED
// ============================================================================
// peakrdl_to_cmdrsp deliberately holds regblk_req from the accept cycle through
// CMD_WAIT_ACK, so the register-block decode - and every strobe derived from it
// - is a two-cycle LEVEL, not a pulse (handbook: generated-rtl-discipline,
// "swmod behind peakrdl_to_cmdrsp is a LEVEL"). Taking it at face value
// executes each command TWICE, which is invisible for a specific EOI and fatal
// for a non-specific one: the second cycle retires a SECOND in-service level,
// and a rotate-on-non-specific-EOI then rotates the base to whatever is left
// (or to 0 when nothing is). The old code registered the level, which just
// moved the two cycles later.
//
// So: rising-edge detect the level (one transaction, one event), then delay the
// pulse ONE flop. The delay matters - the field storage loads at the end of the
// first request cycle, so the edge cycle still presents the OLD OCW2 command.
// The delayed pulse lands exactly when the field holds the value just written.
//
// PIC_INTA's acknowledge is the ONE strobe that is NOT delayed, and it is the
// one case where that is right: it is a READ. The register block's readback is
// combinational and PIC_INTA is a wire (sw=r/hw=w, no storage), so in the edge
// cycle the bridge captures the PRE-acknowledge vector while the core registers
// the side effect at the end of that same cycle. Delaying it a flop would
// acknowledge one cycle after the data left, which is a race for no benefit.
//
// swacc for a read-only field is generated as the bare register strobe, NOT
// qualified by !req_is_wr, so the write qualifier is added here - a write to
// PIC_INTA must be ignored, not acknowledged as an interrupt.
//
// The write strobes carry the OTHER qualifier the bare decode lacks: a byte
// enable. `w_wr_byte0` requires the transaction to have actually enabled byte 0
// (where every ICW/OCW field lives). A PSTRB = 0 write changes nothing in the
// register - the regblock applies byte enables per bit - so a strobe fired on
// one would make the core REPLAY the stored command: a zero-strobe write to
// PIC_OCW2 would re-execute the previous EOI, retiring a second in-service
// level that nobody asked to retire. This is the same `|decoded_wr_biten` term
// PeakRDL itself puts on `swmod`.
//
// The edge detect assumes the level cannot run straight from one transaction
// into the next, because that would merge two reads into one acknowledge. It
// cannot: APB is strictly one-outstanding and apb4_slave issues a command on
// the IDLE -> BUSY edge and consumes its response in BUSY, so there is always
// an idle cycle at the cmd/rsp boundary. Nothing in the RTL checks it; see
// CHECK BY INSPECTION below for the DV guard.
//
// ============================================================================
// CHECK BY INSPECTION (these were assertions; properties belong in external
// formal bindings, not inside the module)
// ============================================================================
//   - Every address presented to the register block is one its own decode
//     recognises: ADDR_CONFIG, ADDR_ICW1..4, ADDR_OCW1..3, ADDR_IRR, ADDR_ISR,
//     ADDR_STATUS or ADDR_INTA. If the RDL moves or adds a register, the
//     access silently reads zero and writes nowhere - which is exactly how the
//     0x044 alias hid. The guard is
//     pic_8259_tests_medium.py::test_address_decode_aliases_dropped_with_pslverr
//     plus pic_8259_tests_basic.py::test_register_access, which touches every
//     mapped address.
//   - hwif_out.PIC_INTA.vector.swacc equals (regblk_req && regblk_addr ==
//     ADDR_INTA). swacc for a read-only field is generated WITHOUT the
//     !req_is_wr qualifier, which is why the qualifier is added locally; if
//     PeakRDL ever changes that, a write would silently start or stop
//     acknowledging. Guarded by
//     pic_8259_tests_medium.py::test_c4_edge_irr_clears_on_acknowledge.
//   - No register write level, and no PIC_INTA access level, ever runs for
//     three cycles. The bridge holds its request for exactly two, so a longer
//     level would mean the rising-edge detect is no longer enough: two writes
//     merge into one command, or - on PIC_INTA - the second read silently does
//     not acknowledge, handing out a vector with no ISR bit behind it.
//     Guarded by pic_8259_tests_basic.py::test_eoi_handling (a non-specific
//     EOI executed twice retires a second in-service level) and
//     pic_8259_tests_medium.py::test_c3_isr_set_by_acknowledge.
//
// Documentation: projects/components/retro_legacy_blocks/rtl/pic_8259/README.md
// Subsystem: retro_legacy_blocks/pic_8259
//
// Created: 2025-11-16
// Updated: 2026-09-09 - GitHub #50: strict decode with PSLVERR, one-cycle
//                       aligned strobes, PIC_INTA acknowledge, regblock-owned
//                       IMR, hwclr init_mode auto-clear
// Updated: 2026-09-09 - GitHub #50 review: write strobes qualified by the
//                       byte-0 enable, so a PSTRB = 0 write cannot replay the
//                       stored command

`timescale 1ns / 1ps

`include "reset_defs.svh"

module pic_8259_config_regs
    import pic_8259_regs_pkg::*;
(
    input  logic        clk,
    input  logic        rst_n,      // Active-low reset

    //========================================================================
    // Command/Response Interface (from apb4_slave)
    //========================================================================
    input  logic        cmd_valid,
    output logic        cmd_ready,
    input  logic        cmd_pwrite,
    input  logic [11:0] cmd_paddr,
    input  logic [31:0] cmd_pwdata,
    input  logic [3:0]  cmd_pstrb,

    output logic        rsp_valid,
    input  logic        rsp_ready,
    output logic [31:0] rsp_prdata,
    output logic        rsp_pslverr,

    //========================================================================
    // Configuration to pic_8259_core
    //========================================================================
    output logic        pic_enable,
    output logic        init_mode,
    output logic        ic4,
    output logic        sngl,
    output logic        ltim,
    output logic [7:0]  vector_base,
    output logic        aeoi,
    output logic [7:0]  imr,

    //========================================================================
    // ICW/OCW write strobes - one cycle, aligned with the field storage
    //========================================================================
    output logic        icw1_wr,
    output logic        icw2_wr,
    output logic        icw3_wr,
    output logic        icw4_wr,
    output logic        ocw2_wr,
    output logic        ocw3_wr,

    output logic [2:0]  ocw2_irq_level,
    output logic [2:0]  ocw2_eoi_cmd,
    output logic [1:0]  ocw3_smm_cmd,

    //========================================================================
    // Acknowledge by read (PIC_INTA)
    //========================================================================
    output logic        inta_ack,
    input  logic [7:0]  inta_vector,
    input  logic        inta_valid,

    //========================================================================
    // Status inputs (from pic_8259_core)
    //========================================================================
    input  logic [7:0]  irr_in,
    input  logic [7:0]  isr_in,
    input  logic        init_complete,
    input  logic [2:0]  icw_step,
    input  logic        int_output,
    input  logic [2:0]  highest_priority
);

    //========================================================================
    // Local Parameters - the register map, as the generated block decodes it
    //========================================================================
    // These MUST track pic_8259_regs.rdl. Nothing in the RTL cross-checks it;
    // see CHECK BY INSPECTION in the header for the DV guard.

    localparam logic [5:0] ADDR_CONFIG = 6'h00;
    localparam logic [5:0] ADDR_ICW1   = 6'h04;
    localparam logic [5:0] ADDR_ICW2   = 6'h08;
    localparam logic [5:0] ADDR_ICW3   = 6'h0C;
    localparam logic [5:0] ADDR_ICW4   = 6'h10;
    localparam logic [5:0] ADDR_OCW1   = 6'h14;
    localparam logic [5:0] ADDR_OCW2   = 6'h18;
    localparam logic [5:0] ADDR_OCW3   = 6'h1C;
    localparam logic [5:0] ADDR_IRR    = 6'h20;
    localparam logic [5:0] ADDR_ISR    = 6'h24;
    localparam logic [5:0] ADDR_STATUS = 6'h28;
    localparam logic [5:0] ADDR_INTA   = 6'h2C;

    // One strobe bit per register that has a write side effect
    localparam int STB_ICW1  = 0;
    localparam int STB_ICW2  = 1;
    localparam int STB_ICW3  = 2;
    localparam int STB_ICW4  = 3;
    localparam int STB_OCW2  = 4;
    localparam int STB_OCW3  = 5;
    localparam int STB_COUNT = 6;

    //========================================================================
    // Internal Signals
    //========================================================================

    // From the adapter, before the decode gate
    logic        adapter_req;
    logic        adapter_req_is_wr;
    logic [11:0] adapter_addr;
    logic [31:0] adapter_wr_data;
    logic [31:0] adapter_wr_biten;
    logic        adapter_req_stall_wr;
    logic        adapter_req_stall_rd;
    logic        adapter_rd_ack;
    logic        adapter_rd_err;
    logic [31:0] adapter_rd_data;
    logic        adapter_wr_ack;
    logic        adapter_wr_err;

    // To the register block, after the decode gate
    logic        regblk_req;
    logic [5:0]  regblk_addr;
    logic        regblk_req_stall_wr;
    logic        regblk_req_stall_rd;
    logic        regblk_rd_ack;
    logic        regblk_rd_err;
    logic [31:0] regblk_rd_data;
    logic        regblk_wr_ack;
    logic        regblk_wr_err;

    // Decode
    logic        w_addr_mapped;
    logic        w_drop;
    logic        w_drop_ack;

    // Write-strobe levels, their delayed copies, and the aligned pulses
    logic                 w_wr_byte0;   // the write carried byte-0 enables
    logic                 w_wr_sel;     // a byte-0-enabled write is in progress
    logic [STB_COUNT-1:0] w_wr_level;   // one bit per strobed register
    logic [STB_COUNT-1:0] r_wr_level_d;
    logic [STB_COUNT-1:0] w_wr_edge;
    logic [STB_COUNT-1:0] r_wr_stb;

    // PIC_INTA acknowledge
    logic        w_inta_acc;
    logic        r_inta_acc_d;

    // Hardware interface structs
    pic_8259_regs__in_t  hwif_in;
    pic_8259_regs__out_t hwif_out;

    //========================================================================
    // CMD/RSP to PeakRDL Adapter
    //========================================================================

    peakrdl_to_cmdrsp #(
        .ADDR_WIDTH(12),
        .DATA_WIDTH(32)
    ) u_adapter (
        .aclk               (clk),
        .aresetn            (rst_n),

        .cmd_valid          (cmd_valid),
        .cmd_ready          (cmd_ready),
        .cmd_pwrite         (cmd_pwrite),
        .cmd_paddr          (cmd_paddr),
        .cmd_pwdata         (cmd_pwdata),
        .cmd_pstrb          (cmd_pstrb),

        .rsp_valid          (rsp_valid),
        .rsp_ready          (rsp_ready),
        .rsp_prdata         (rsp_prdata),
        .rsp_pslverr        (rsp_pslverr),

        .regblk_req         (adapter_req),
        .regblk_req_is_wr   (adapter_req_is_wr),
        .regblk_addr        (adapter_addr),
        .regblk_wr_data     (adapter_wr_data),
        .regblk_wr_biten    (adapter_wr_biten),
        .regblk_req_stall_wr(adapter_req_stall_wr),
        .regblk_req_stall_rd(adapter_req_stall_rd),
        .regblk_rd_ack      (adapter_rd_ack),
        .regblk_rd_err      (adapter_rd_err),
        .regblk_rd_data     (adapter_rd_data),
        .regblk_wr_ack      (adapter_wr_ack),
        .regblk_wr_err      (adapter_wr_err)
    );

    //========================================================================
    // Strict Address Decode
    //========================================================================
    // Equality against the WHOLE 12-bit address, register by register - not a
    // window test and not a slice. An alias such as 0x044 shares the low six
    // bits with ICW1 and is exactly what this rejects.

    always_comb begin
        w_addr_mapped = (adapter_addr == {6'h00, ADDR_CONFIG}) ||
                        (adapter_addr == {6'h00, ADDR_ICW1})   ||
                        (adapter_addr == {6'h00, ADDR_ICW2})   ||
                        (adapter_addr == {6'h00, ADDR_ICW3})   ||
                        (adapter_addr == {6'h00, ADDR_ICW4})   ||
                        (adapter_addr == {6'h00, ADDR_OCW1})   ||
                        (adapter_addr == {6'h00, ADDR_OCW2})   ||
                        (adapter_addr == {6'h00, ADDR_OCW3})   ||
                        (adapter_addr == {6'h00, ADDR_IRR})    ||
                        (adapter_addr == {6'h00, ADDR_ISR})    ||
                        (adapter_addr == {6'h00, ADDR_STATUS}) ||
                        (adapter_addr == {6'h00, ADDR_INTA});
    end

    assign w_drop      = !w_addr_mapped;
    assign regblk_req  = adapter_req && !w_drop;
    assign regblk_addr = adapter_addr[5:0];

    // Local acknowledge for a dropped access, in the same combinational form
    // the register block uses. The adapter holds its request until acked.
    assign w_drop_ack = adapter_req && w_drop;

    assign adapter_req_stall_wr = regblk_req_stall_wr;
    assign adapter_req_stall_rd = regblk_req_stall_rd;
    assign adapter_rd_ack  = regblk_rd_ack | (w_drop_ack & ~adapter_req_is_wr);
    assign adapter_rd_err  = regblk_rd_err | (w_drop_ack & ~adapter_req_is_wr);
    assign adapter_rd_data = w_drop_ack ? 32'h0 : regblk_rd_data;
    assign adapter_wr_ack  = regblk_wr_ack | (w_drop_ack & adapter_req_is_wr);
    assign adapter_wr_err  = regblk_wr_err | (w_drop_ack & adapter_req_is_wr);

    //========================================================================
    // Write Strobes - mirror the regblock decode, edge-detect, then align
    //========================================================================

    // w_wr_byte0 is the byte-enable term. Every ICW/OCW field this block strobes
    // on lives in byte 0, and the regblock applies byte enables per bit, so a
    // PSTRB = 0 write leaves the stored command untouched. Without this term the
    // strobe would still fire and the core would REPLAY whatever command the
    // register already held - a zero-strobe write to PIC_OCW2 would re-execute
    // the previous EOI. This is the same `|decoded_wr_biten` qualifier PeakRDL
    // puts on `swmod`.
    assign w_wr_byte0 = |adapter_wr_biten[7:0];
    assign w_wr_sel   = regblk_req && adapter_req_is_wr && w_wr_byte0;

    always_comb begin
        w_wr_level = '0;
        w_wr_level[STB_ICW1] = w_wr_sel && (regblk_addr == ADDR_ICW1);
        w_wr_level[STB_ICW2] = w_wr_sel && (regblk_addr == ADDR_ICW2);
        w_wr_level[STB_ICW3] = w_wr_sel && (regblk_addr == ADDR_ICW3);
        w_wr_level[STB_ICW4] = w_wr_sel && (regblk_addr == ADDR_ICW4);
        w_wr_level[STB_OCW2] = w_wr_sel && (regblk_addr == ADDR_OCW2);
        w_wr_level[STB_OCW3] = w_wr_sel && (regblk_addr == ADDR_OCW3);
    end

    assign w_wr_edge = w_wr_level & ~r_wr_level_d;

    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            r_wr_level_d <= '0;
            r_wr_stb     <= '0;
        end else begin
            r_wr_level_d <= w_wr_level;
            r_wr_stb     <= w_wr_edge;
        end
    )

    assign icw1_wr = r_wr_stb[STB_ICW1];
    assign icw2_wr = r_wr_stb[STB_ICW2];
    assign icw3_wr = r_wr_stb[STB_ICW3];
    assign icw4_wr = r_wr_stb[STB_ICW4];
    assign ocw2_wr = r_wr_stb[STB_OCW2];
    assign ocw3_wr = r_wr_stb[STB_OCW3];

    //========================================================================
    // PIC_INTA Acknowledge Strobe
    //========================================================================
    // Rising edge of the two-cycle swacc level, NOT delayed - see the header.

    assign w_inta_acc = hwif_out.PIC_INTA.vector.swacc && !adapter_req_is_wr;

    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            r_inta_acc_d <= 1'b0;
        end else begin
            r_inta_acc_d <= w_inta_acc;
        end
    )

    assign inta_ack = w_inta_acc && !r_inta_acc_d;

    //========================================================================
    // Hardware Interface Inputs
    //========================================================================

    assign hwif_in.PIC_IRR.irr.next               = irr_in;
    assign hwif_in.PIC_ISR.isr.next               = isr_in;
    assign hwif_in.PIC_STATUS.init_complete.next  = init_complete;
    assign hwif_in.PIC_STATUS.icw_step.next       = icw_step;
    assign hwif_in.PIC_STATUS.int_output.next     = int_output;
    assign hwif_in.PIC_STATUS.highest_priority.next = highest_priority;
    assign hwif_in.PIC_INTA.vector.next           = inta_vector;
    assign hwif_in.PIC_INTA.valid.next            = inta_valid;

    // init_mode auto-clear after ICW4. `hwclr` with `precedence = hw` in the
    // RDL, so a software PIC_CONFIG write landing in the same cycle cannot
    // swallow the clear (GitHub #50 round_3 item 2). The previous form drove
    // the field's `.next` through a hw = rw mirror, where the generated
    // resolution takes the SW-write branch first and the clear was simply lost.
    assign hwif_in.PIC_CONFIG.init_mode.hwclr =
        hwif_out.PIC_CONFIG.auto_reset_init.value && r_wr_stb[STB_ICW4];

    //========================================================================
    // PeakRDL Generated Register File
    //========================================================================

    pic_8259_regs u_pic_8259_regs (
        .clk                  (clk),
        .rst                  (~rst_n),   // PeakRDL uses active-high reset
        .s_cpuif_req          (regblk_req),
        .s_cpuif_req_is_wr    (adapter_req_is_wr),
        .s_cpuif_addr         (regblk_addr),
        .s_cpuif_wr_data      (adapter_wr_data),
        .s_cpuif_wr_biten     (adapter_wr_biten),
        .s_cpuif_req_stall_wr (regblk_req_stall_wr),
        .s_cpuif_req_stall_rd (regblk_req_stall_rd),
        .s_cpuif_rd_ack       (regblk_rd_ack),
        .s_cpuif_rd_err       (regblk_rd_err),
        .s_cpuif_rd_data      (regblk_rd_data),
        .s_cpuif_wr_ack       (regblk_wr_ack),
        .s_cpuif_wr_err       (regblk_wr_err),
        .hwif_in              (hwif_in),
        .hwif_out             (hwif_out)
    );

    //========================================================================
    // Configuration Outputs
    //========================================================================
    // ICW3 cascade, ICW4 buffered-mode/SFNM and OCW3 poll/read-select are
    // software-visible STORAGE with no hardware effect in this implementation
    // (see the DEVIATIONS block in pic_8259_core.sv). They are deliberately not
    // exported: an output nobody drives anything with is worse documentation
    // than a stated deviation.

    assign pic_enable  = hwif_out.PIC_CONFIG.pic_enable.value;
    assign init_mode   = hwif_out.PIC_CONFIG.init_mode.value;

    assign ic4         = hwif_out.PIC_ICW1.ic4.value;
    assign sngl        = hwif_out.PIC_ICW1.sngl.value;
    assign ltim        = hwif_out.PIC_ICW1.ltim.value;
    assign vector_base = hwif_out.PIC_ICW2.vector_base.value;
    assign aeoi        = hwif_out.PIC_ICW4.aeoi.value;

    // The regblock field is the ONE copy of the IMR - no core mirror, so a
    // read-after-write can never see a stale value (GitHub #50 round_2 item 4).
    assign imr         = hwif_out.PIC_OCW1.imr.value;

    assign ocw2_irq_level = hwif_out.PIC_OCW2.irq_level.value;
    assign ocw2_eoi_cmd   = hwif_out.PIC_OCW2.eoi_cmd.value;
    assign ocw3_smm_cmd   = hwif_out.PIC_OCW3.smm_cmd.value;

endmodule
