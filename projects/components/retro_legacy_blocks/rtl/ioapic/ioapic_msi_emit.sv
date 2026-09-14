// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: ioapic_msi_emit
// Purpose: MSI delivery -- turn an IOAPIC delivery message into a posted
//          write on a bus (RLB-008).
//
// Documentation: projects/components/retro_legacy_blocks/docs/ioapic_mas/
// Subsystem: retro_legacy_blocks/ioapic
//
// Created: 2026-09-14
//
//==============================================================================
// WHY THIS IS A COMPANION AND NOT A PORT ON apb4_ioapic
//==============================================================================
// MSI is a posted memory WRITE of one data word to one address. RLB-008 called
// it blocked because apb4_ioapic is an APB SLAVE with no initiator -- true, but
// the wrong conclusion, and the entry's own text contained the right one in
// parentheses: "add a master port, OR BRIDGE THE EXISTING DELIVERY CHANNEL ONTO
// ONE".
//
// Sean's 2026-09-11 interface decision says the delivery channel stays a
// payload plus valid/ready plus a status precisely so "a bridge can carry that
// shape onto a bus (the retry becomes a response)". That sentence describes
// this module. So MSI needs no change to the block at all: apb4_ioapic's port
// list is untouched and apb4_ioapic.f does not reference this file, exactly as
// for ioapic_lowest_pri_arb and ioapic_deliv_merge.
//
//==============================================================================
// THE ENCODING IS A CHOICE, AND THIS IS WHICH ONE
//==============================================================================
// Nothing in the RTL, the RDL or the MAS commits to an MSI format --
// ioapic_core.sv:197 says only "MSI-style message interface". So the mapping
// below is a DEFAULT, not a derivation, and it is the x86 convention:
//
//   address[19:12] = destination  (APIC ID, or logical mask when dest_mode=1)
//   address[31:20] = msi_addr_base[31:20]   -- 0xFEE on a PC
//   address[11:0]  = msi_addr_base[11:0]    -- redirection/trigger hints live
//                                              here on x86; passed through
//   data[7:0]      = vector
//   data[10:8]     = delivery mode (Fixed/LowestPri/SMI/NMI/INIT/ExtINT,
//                                   forwarded unmodified as everywhere else)
//   data[11]       = destination mode (0 physical, 1 logical)
//   data[31:12]    = msi_data_template[31:12]
//
// A different fabric wants a different mapping and this is the one place to
// change it: the two assigns below are the whole format.
//
// msi_addr_base and msi_data_template arrive as PORTS, not registers. That
// keeps this a pure companion. Putting them in the register file is a separate
// change -- it needs new RDL at a reserved selector (the IOAPICARBCFG @ 0x03
// precedent), a peakrdl_generate.py cycle, and a decode change inside the
// block -- so it is deliberately not bundled here.
//
//==============================================================================
// RETRY IS THE BUS RESPONSE
//==============================================================================
// PSLVERR on the posted write becomes deliv_retry, qualified by the handshake
// exactly as ioapic_core expects: the message was taken and nobody accepted it,
// so the interrupt must be offered again. An OKAY response is an acceptance.
// Tie this module out and the channel behaves as it did before.

`timescale 1ns / 1ps

module ioapic_msi_emit #(
    parameter int ADDR_WIDTH = 32,
    parameter int DATA_WIDTH = 32,
    parameter int STRB_WIDTH = DATA_WIDTH / 8,
    // Derived, do not override: they size ports, so they live here rather than
    // as body localparams (same reason as ioapic_deliv_merge's SRC_IDX_W).
    parameter int CPW = ADDR_WIDTH + DATA_WIDTH + STRB_WIDTH + 3 + 1 + 1 + 1,
    parameter int RPW = DATA_WIDTH + 1 + 1 + 1
) (
    // No clk/rst_n: this module is combinational. The mapping assigns, the
    // command packing and the response decode hold no state, so a clock port
    // would exist only for symmetry with ioapic_deliv_merge -- which is not a
    // reason a port should exist, and verilator -Wall said so here just as it
    // did on ioapic_lowest_pri_arb. The apb4_master_stub next to it is the
    // sequential part and takes its own pclk/presetn.
    //
    // Delivery channel in, from ioapic_core's irq_out_*, or from
    // ioapic_deliv_merge's m_* -- the two are field-for-field identical, so a
    // multi-IOAPIC system chains merge -> emitter with no adapter.
    input  logic                    deliv_valid,
    input  logic [7:0]              deliv_vector,
    input  logic [7:0]              deliv_dest,
    input  logic                    deliv_dest_mode,
    input  logic [2:0]              deliv_deliv_mode,
    output logic                    deliv_ready,
    output logic                    deliv_retry,

    // Where the MSI write goes, and the fixed bits of what it carries
    input  logic [ADDR_WIDTH-1:0]   msi_addr_base,
    input  logic [DATA_WIDTH-1:0]   msi_data_template,

    // To apb4_master_stub
    output logic                    cmd_valid,
    input  logic                    cmd_ready,
    output logic [CPW-1:0]          cmd_data,
    input  logic                    rsp_valid,
    output logic                    rsp_ready,
    input  logic [RPW-1:0]          rsp_data
);

    // ------------------------------------------------------------------
    // The message -> write mapping. These two assigns ARE the MSI format.
    // ------------------------------------------------------------------
    logic [ADDR_WIDTH-1:0] w_msi_addr;
    logic [DATA_WIDTH-1:0] w_msi_data;

    always_comb begin
        w_msi_addr = msi_addr_base;
        w_msi_addr[19:12] = deliv_dest;
    end

    always_comb begin
        w_msi_data = msi_data_template;
        w_msi_data[7:0]  = deliv_vector;
        w_msi_data[10:8] = deliv_deliv_mode;
        w_msi_data[11]   = deliv_dest_mode;
    end

    // ------------------------------------------------------------------
    // Command: a single posted write, packed the way apb4_master_stub
    // unpacks it (apb4_master_stub.sv:70). first and last are both 1 --
    // an MSI is one beat, never part of a burst.
    // ------------------------------------------------------------------
    localparam logic [2:0] MSI_PPROT = 3'b010;   // non-secure, data, unpriv

    assign cmd_data = {1'b1,                       // last
                       1'b1,                       // first
                       1'b1,                       // pwrite
                       MSI_PPROT,                  // pprot
                       {STRB_WIDTH{1'b1}},         // pstrb: full word
                       w_msi_addr,
                       w_msi_data};

    assign cmd_valid = deliv_valid;
    // The delivery handshake completes when the write is ACCEPTED by the
    // master. The bus response arrives later and becomes retry, below.
    assign deliv_ready = cmd_ready;

    // ------------------------------------------------------------------
    // Response: PSLVERR is the refusal. rsp_data is
    // {last, first, pslverr, prdata} (apb4_master_stub.sv:149).
    // ------------------------------------------------------------------
    logic w_rsp_pslverr;
    assign w_rsp_pslverr = rsp_data[DATA_WIDTH];

    // Always able to take a response: a posted write's status must never be
    // able to back up into the delivery path.
    assign rsp_ready = 1'b1;

    // Qualified by the RESPONSE handshake -- which is NOT the handshake
    // ioapic_core samples. This comment used to claim they were the same, and
    // that error is the whole of RLB-008's posted-timing finding: deliv_ready
    // is cmd_ready, so the DELIVERY handshake closes when the write queues,
    // while this response arrives strictly later. ioapic_core evaluates
    // w_deliv_accept = w_deliv_done && !irq_out_retry AT the delivery
    // handshake, where retry is still low, so it retires the edge as accepted
    // and a refusal raised here can no longer be acted on.
    //
    // Accepted behaviour while the write is posted (Sean, 2026-09-14),
    // but it is not silent: ioapic_core counts every such late refusal into
    // IOAPICMSIDROP (IOWIN selector 0x06), so a dropped MSI is visible to
    // software. Two signals both being "qualified by a handshake" does not
    // make it the same handshake.
    assign deliv_retry = rsp_valid && w_rsp_pslverr;

    // ------------------------------------------------------------------
    // Elaboration-time parameter check ([[no-assertions-in-rtl]]: an
    // initial $error is the one sanctioned form, not an SVA).
    // ------------------------------------------------------------------
`ifndef SYNTHESIS
    initial begin : param_check
        if (DATA_WIDTH < 12)
            $error("ioapic_msi_emit: DATA_WIDTH must be >= 12 to carry vector, delivery mode and destination mode (got %0d)", DATA_WIDTH);
        if (ADDR_WIDTH < 20)
            $error("ioapic_msi_emit: ADDR_WIDTH must be >= 20 to carry the destination at [19:12] (got %0d)", ADDR_WIDTH);
    end
`endif

endmodule : ioapic_msi_emit
