// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: ioapic_config_regs
// Purpose: Configuration register wrapper for IOAPIC - PeakRDL wrapper with
//          the Intel IOREGSEL/IOWIN indirect access mechanism
//
// ARCHITECTURE:
//   cmd/rsp --> peakrdl_to_cmdrsp adapter --> IOREGSEL/IOWIN translation -->
//   --> ioapic_regs (PeakRDL) --> hwif --> mapping --> IOAPIC core
//
// INDIRECT ACCESS METHOD (Intel 82093AA):
//   1. Write the internal register offset to IOREGSEL (APB 0x000)
//   2. Read/write the selected register through IOWIN (APB 0x004)
//
//   The translation lives HERE, in the always_comb below - NOT in the
//   PeakRDL-generated block. (The generated block only ever sees a direct
//   address; it has no notion of a selector. The old "PeakRDL creates the
//   multiplexing logic based on IOREGSEL.regsel" comment was wrong and had
//   seeded the same wrong claim into two MAS chapters - issue #48 round_3.)
//
// ONE COPY OF THE SELECTOR (issue #48 qc round_2, item 2)
//   The selector is the regblock's IOREGSEL.regsel field and nothing else.
//   There used to be a second, functional copy here (ioregsel_value) that
//   drove the translation while the regblock field drove readback; the two
//   diverged, because an IOWIN access with an unmapped selector was routed to
//   regblk_addr 0x000 - the regblock's own IOREGSEL - so it rewrote the
//   readback copy and left the active selector alone. The shadow is gone;
//   readback and translation are now the same flop by construction.
//
// DECODE CONTRACT (issue #48 qc round_2 item 1, review round item M1)
//   ONLY APB 0x000 (IOREGSEL) and 0x004 (IOWIN) are software-visible in this
//   block's 4 KB window. The indirect selector/window pair is the ONLY path to
//   the register file; nothing else in the window is a register.
//
//   THREE classes of access therefore never reach the register block:
//     - APB address outside 0x000-0x0FF. The register file is 0xD4 bytes and
//       s_cpuif_addr is 8 bits, so without the upper-bit qualification every
//       address >= 0x100 aliased onto it modulo 0x100 and a stray write to
//       0x108 corrupted IOAPICID. These raise PSLVERR: the address is outside
//       the block's map and an error is the useful answer.
//     - APB address INSIDE 0x000-0x0FF that is neither IOREGSEL nor IOWIN.
//       Same treatment, same reason - the address is not a register here. This
//       used to be a backdoor: such an address fell through the old
//       `regblk_addr = adapter_addr[7:0]` default, reached the register block
//       AT ITS RAW OFFSET and answered with no error, so a direct APB write to
//       0x008 rewrote IOAPICID and one to 0x014 rewrote IOREDTBL[0].REDIR_LO,
//       bypassing the indirect mechanism entirely. There is no pass-through
//       default any more: the only direct access is IOREGSEL itself.
//     - An IOWIN access while the selector is unmapped (not 0x00-0x02 and not
//       0x10-0x3F). These do NOT raise PSLVERR: the address is legal, the
//       selector merely names a register the 82093AA does not implement, and
//       the architectural answer there is a read of zero. The selector itself
//       is unaffected - it keeps whatever software last wrote to IOREGSEL.
//   All three are acknowledged locally (w_drop_ack) with read data zero. The
//   upstream adapter HOLDS its request until an ack, so a dropped access that
//   is merely gated off the register block would hang the APB.
//
// CHECK BY INSPECTION (these were assertions and a simulation-time parameter
// guard; properties belong in external formal bindings, not inside the module)
//   - NUM_IRQS must be 24. The register map is generated from a fixed 24-entry
//     RDL, so this parameter is not free here even though ioapic_core scales.
//     Nothing in the RTL rejects another value.
//   - Every address this file presents to the register block is one the
//     generated decode recognises: IOREGSEL/IOAPICID/IOAPICVER/IOAPICARB, or
//     ADDR_REDIR + 8*n (+4) for n in [0,24). IOWIN's own regblock address
//     (0x04) is deliberately NOT in that set -- it is a window, never a
//     destination. If the RDL moves a register or changes the IOREDTBL stride,
//     the translation starts reading zero and writing nowhere rather than
//     failing. The guards are the DV tests
//     ioapic_tests_basic.py::test_full_redirection_table (every entry, both
//     halves, read back through IOWIN) and ::test_identification_registers.
//   - The DIRECT path reaches exactly one register, IOREGSEL at
//     ADDR_IOREGSEL: regblk_req with !w_is_iowin implies w_is_ioregsel and
//     regblk_addr == ADDR_IOREGSEL. Everything else in the register block is
//     reachable ONLY through an IOWIN translation, which is the whole content
//     of the decode contract above. Guarded by
//     ioapic_tests_medium.py::test_apb_backdoor_dropped_with_slverr and
//     ::test_address_decode_no_aliasing_above_0x100.
//   - An IOWIN access with an unmapped selector never presents a request to
//     the register block. That is what used to rewrite IOREGSEL through the
//     0x000 fallback. Guarded by
//     ioapic_tests_medium.py::test_ioregsel_invalid_selector_readback.
//
// Documentation: projects/components/retro_legacy_blocks/rtl/ioapic/README.md
// Subsystem: ioapic
//
// Created: 2025-11-16
// Updated: 2026-09-09 - issue #48: single selector copy, IOREGSEL/IOWIN-only
//                       decode, IOWIN tie-off, EOI moved to apb4_ioapic

`timescale 1ns / 1ps

`include "reset_defs.svh"

module ioapic_config_regs
    import ioapic_regs_pkg::*;
#(
    parameter int NUM_IRQS = 24
)(
    input logic clk,
    input logic rst_n,  // Active-low reset

    // Command/Response Interface (from apb4_slave)
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

    // IOAPIC Core Interface - Configuration Outputs (per IRQ)
    output logic [7:0]  cfg_vector       [NUM_IRQS],
    output logic [2:0]  cfg_deliv_mode   [NUM_IRQS],
    output logic        cfg_dest_mode    [NUM_IRQS],
    output logic        cfg_polarity     [NUM_IRQS],
    output logic        cfg_trigger_mode [NUM_IRQS],
    output logic        cfg_mask         [NUM_IRQS],
    output logic [7:0]  cfg_destination  [NUM_IRQS],
    output logic [3:0]  cfg_ioapic_id,

    // Status inputs (from ioapic_core)
    input  logic        status_deliv_status [NUM_IRQS],
    input  logic        status_remote_irr   [NUM_IRQS],
    input  logic [3:0]  status_arb_id
);

    //========================================================================
    // Local Parameters
    //========================================================================

    // Internal (IOREGSEL) offsets and their APB addresses in the generated
    // register block. These MUST track ioapic_regs.rdl - nothing in the RTL
    // cross-checks that; see CHECK BY INSPECTION in the header for the DV
    // guard against drift.
    localparam logic [7:0]  SEL_IOAPICID  = 8'h00;
    localparam logic [7:0]  SEL_IOAPICVER = 8'h01;
    localparam logic [7:0]  SEL_IOAPICARB = 8'h02;
    localparam logic [7:0]  SEL_REDIR_LO  = 8'h10;  // first redirection entry
    localparam logic [7:0]  SEL_REDIR_HI  = 8'h3F;  // last  redirection entry
    // Register-block addresses are 8 bits: the whole map is 0x00-0xD0 and the
    // decode below only ever presents a constant from this list, so there is
    // no truncation on the way into s_cpuif_addr.
    localparam logic [7:0]  ADDR_IOREGSEL = 8'h00;   // the ONE direct register
    localparam logic [7:0]  ADDR_IOAPICID = 8'h08;
    localparam logic [7:0]  ADDR_IOAPICVER= 8'h0C;
    localparam logic [7:0]  ADDR_IOAPICARB= 8'h10;
    localparam logic [7:0]  ADDR_REDIR    = 8'h14;   // IOREDTBL[0].REDIR_LO
    // The two software-visible APB addresses in the 4 KB window. Everything
    // else, in window or not, is dropped (see DECODE CONTRACT above).
    localparam logic [11:0] APB_IOREGSEL  = 12'h000;
    localparam logic [11:0] APB_IOWIN     = 12'h004;

    //========================================================================
    // Internal Signals for PeakRDL Passthrough Interface
    //========================================================================

    // From adapter (before indirect access translation)
    logic                adapter_req;
    logic                adapter_req_is_wr;
    logic [11:0]         adapter_addr;
    logic [31:0]         adapter_wr_data;
    logic [31:0]         adapter_wr_biten;
    logic                adapter_req_stall_wr;
    logic                adapter_req_stall_rd;
    logic                adapter_rd_ack;
    logic                adapter_rd_err;
    logic [31:0]         adapter_rd_data;
    logic                adapter_wr_ack;
    logic                adapter_wr_err;

    // To register block (after indirect access translation)
    logic                regblk_req;
    logic                regblk_req_is_wr;
    logic [7:0]          regblk_addr;
    logic [31:0]         regblk_wr_data;
    logic [31:0]         regblk_wr_biten;
    logic                regblk_req_stall_wr;
    logic                regblk_req_stall_rd;
    logic                regblk_rd_ack;
    logic                regblk_rd_err;
    logic [31:0]         regblk_rd_data;
    logic                regblk_wr_ack;
    logic                regblk_wr_err;

    // Indirect access decode
    logic [7:0]          w_regsel;        // the ONE selector copy
    logic                w_sel_mapped;    // selector names a real register
    logic                w_is_ioregsel;   // APB 0x000
    logic                w_is_iowin;      // APB 0x004
    logic                w_addr_visible;  // one of the two, and nothing else
    logic                w_drop;          // access does not reach the regblock
    logic                w_drop_err;      // ...and answers with PSLVERR
    logic                w_drop_ack;      // local acknowledge for a dropped access
    logic [5:0]          w_redir_off;
    logic [4:0]          w_redir_irq;

    //========================================================================
    // Hardware Interface Structs
    //========================================================================

    ioapic_regs__in_t  hwif_in;
    ioapic_regs__out_t hwif_out;

    //========================================================================
    // Instantiate Protocol Adapter (from converters/rtl/)
    //========================================================================

    peakrdl_to_cmdrsp #(
        .ADDR_WIDTH(12),
        .DATA_WIDTH(32)
    ) u_adapter (
        .aclk               (clk),
        .aresetn            (rst_n),

        // CMD/RSP interface (external)
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

        // PeakRDL passthrough interface (to indirect access logic)
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
    // IOREGSEL/IOWIN Indirect Access Logic
    //========================================================================

    // The selector, read straight out of the register block. Byte enables are
    // honoured because the regblock applies them (this file no longer has an
    // opinion about them).
    assign w_regsel = hwif_out.IOREGSEL.regsel.value;

    assign w_sel_mapped = (w_regsel == SEL_IOAPICID)  ||
                          (w_regsel == SEL_IOAPICVER) ||
                          (w_regsel == SEL_IOAPICARB) ||
                          ((w_regsel >= SEL_REDIR_LO) && (w_regsel <= SEL_REDIR_HI));

    // The software-visible decode, in full: IOREGSEL and IOWIN, nothing else.
    // Note this is an EQUALITY on the whole 12-bit APB address, not a window
    // test - an in-window address that is not one of these two is as invisible
    // as one above 0x0FF, and answers the same way.
    assign w_is_ioregsel  = (adapter_addr == APB_IOREGSEL);
    assign w_is_iowin     = (adapter_addr == APB_IOWIN);
    assign w_addr_visible = w_is_ioregsel || w_is_iowin;

    // Dropped: not a software-visible address at all, or IOWIN naming a
    // register the 82093AA does not implement. Only the first is an error -
    // an unmapped selector is a legal access to an unimplemented register and
    // reads zero.
    assign w_drop     = !w_addr_visible || (w_is_iowin && !w_sel_mapped);
    assign w_drop_err = !w_addr_visible;

    // Redirection entries: selector 0x10 + 2*N + hi  ->  0x014 + 8*N + 4*hi.
    // The mapping is monotonic in the selector, so check it at an asymmetric
    // point rather than at entry 0: selector 0x3F (entry 23, HI) must land on
    // 0x0D0, and 0x3E (entry 23, LO) on 0x0CC.
    assign w_redir_off = w_regsel[5:0] - SEL_REDIR_LO[5:0];
    assign w_redir_irq = w_redir_off[5:1];

    always_comb begin
        regblk_req       = adapter_req && !w_drop;
        regblk_req_is_wr = adapter_req_is_wr;
        regblk_wr_data   = adapter_wr_data;
        regblk_wr_biten  = adapter_wr_biten;

        // Default: IOREGSEL, the only register reachable directly. There is
        // no pass-through of adapter_addr - that default was the M1 backdoor,
        // and a constant here means an address can only reach the register
        // block by being named in this block.
        regblk_addr = ADDR_IOREGSEL;

        if (w_is_iowin) begin
            case (w_regsel)
                SEL_IOAPICID:  regblk_addr = ADDR_IOAPICID;
                SEL_IOAPICVER: regblk_addr = ADDR_IOAPICVER;
                SEL_IOAPICARB: regblk_addr = ADDR_IOAPICARB;
                default: begin
                    // Redirection table, or an unmapped selector - in which
                    // case regblk_req is already gated off and the address
                    // below is never presented.
                    regblk_addr = ADDR_REDIR
                                + {w_redir_irq, 3'b000}
                                + (w_redir_off[0] ? 8'h04 : 8'h00);
                end
            endcase
        end
    end

    // Local acknowledge for dropped accesses, in the SAME combinational form
    // the register block uses (issue #48 review round, item L4). peakrdl_to_-
    // cmdrsp HOLDS regblk_req until it is acked, and the generated block's own
    // ack is `decoded_req & decoded_req_is_wr` - combinational on that held
    // request, so it stands for as long as the request does. Mirroring it here
    // means a dropped access and a real one retire through identical adapter
    // timing. The previous form was a registered one-cycle pulse that had to
    // self-clear (`&& !r_drop_ack`) to avoid acking twice; a held request is
    // simpler to be right about than a pulse that has to be counted.
    assign w_drop_ack = adapter_req && w_drop;

    // Response path: the register block's, or the local drop response.
    assign adapter_req_stall_wr = regblk_req_stall_wr;
    assign adapter_req_stall_rd = regblk_req_stall_rd;
    assign adapter_rd_ack       = regblk_rd_ack | (w_drop_ack & ~adapter_req_is_wr);
    assign adapter_rd_err       = regblk_rd_err | (w_drop_ack & w_drop_err & ~adapter_req_is_wr);
    // A dropped read returns a defined zero, stated here rather than inherited
    // from "the regblock happens not to strobe anything".
    assign adapter_rd_data      = w_drop_ack ? 32'h0 : regblk_rd_data;
    assign adapter_wr_ack       = regblk_wr_ack | (w_drop_ack & adapter_req_is_wr);
    assign adapter_wr_err       = regblk_wr_err | (w_drop_ack & w_drop_err & adapter_req_is_wr);

    //========================================================================
    // Instantiate PeakRDL-Generated Register Block
    //========================================================================

    ioapic_regs u_ioapic_regs (
        .clk                (clk),
        .rst                (~rst_n),  // PeakRDL uses active-high reset

        // Passthrough CPU interface. regblk_addr is always one of the 8-bit
        // constants named above (top register is 0xD0), never a slice of the
        // APB address, so nothing is truncated on the way in.
        .s_cpuif_req        (regblk_req),
        .s_cpuif_req_is_wr  (regblk_req_is_wr),
        .s_cpuif_addr       (regblk_addr),
        .s_cpuif_wr_data    (regblk_wr_data),
        .s_cpuif_wr_biten   (regblk_wr_biten),
        .s_cpuif_req_stall_wr(regblk_req_stall_wr),
        .s_cpuif_req_stall_rd(regblk_req_stall_rd),
        .s_cpuif_rd_ack     (regblk_rd_ack),
        .s_cpuif_rd_err     (regblk_rd_err),
        .s_cpuif_rd_data    (regblk_rd_data),
        .s_cpuif_wr_ack     (regblk_wr_ack),
        .s_cpuif_wr_err     (regblk_wr_err),

        // Hardware interface
        .hwif_in            (hwif_in),
        .hwif_out           (hwif_out)
    );

    //========================================================================
    // Map PeakRDL hwif Outputs to IOAPIC Core Configuration Inputs
    //========================================================================

    // IOAPIC ID
    assign cfg_ioapic_id = hwif_out.IOAPICID.apic_id.value;

    // Redirection table entries - map array to core
    genvar g;
    generate
        for (g = 0; g < NUM_IRQS; g++) begin : g_redir_cfg
            assign cfg_vector[g]       = hwif_out.IOREDTBL[g].REDIR_LO.vector.value;
            assign cfg_deliv_mode[g]   = hwif_out.IOREDTBL[g].REDIR_LO.deliv_mode.value;
            assign cfg_dest_mode[g]    = hwif_out.IOREDTBL[g].REDIR_LO.dest_mode.value;
            assign cfg_polarity[g]     = hwif_out.IOREDTBL[g].REDIR_LO.polarity.value;
            assign cfg_trigger_mode[g] = hwif_out.IOREDTBL[g].REDIR_LO.trigger_mode.value;
            assign cfg_mask[g]         = hwif_out.IOREDTBL[g].REDIR_LO.mask.value;
            assign cfg_destination[g]  = hwif_out.IOREDTBL[g].REDIR_HI.destination.value;
        end
    endgenerate

    //========================================================================
    // Map IOAPIC Core Outputs to PeakRDL hwif Inputs
    //========================================================================

    // Arbitration ID (read-only, from core)
    assign hwif_in.IOAPICARB.arb_id.next = status_arb_id;

    // IOWIN is a window, not storage: every APB access to 0x004 is translated
    // to the selected register above, so the generated IOWIN field is never
    // read and never written through the bus. Its RDL declares hw = rw, which
    // makes the field load hwif_in every cycle it is not being written - so
    // leaving this input undriven parked X in the storage (issue #48 round_2,
    // item 4). Tied to zero: defined, and it keeps IOWIN in the RDL where it
    // documents the software-visible window.
    assign hwif_in.IOWIN.data.next = 32'h0;

    // Delivery status and Remote IRR (read-only fields, from core)
    generate
        for (g = 0; g < NUM_IRQS; g++) begin : g_redir_status
            assign hwif_in.IOREDTBL[g].REDIR_LO.deliv_status.next = status_deliv_status[g];
            assign hwif_in.IOREDTBL[g].REDIR_LO.remote_irr.next = status_remote_irr[g];
        end
    endgenerate


    // Elaboration-time parameter guard (sim only). Not an assertion in the
    // house sense: see vault/handbook/design/no-assertions-in-rtl.md.
`ifndef SYNTHESIS
    // Simulation-time parameter guard: the register map is generated from a
    // fixed 24-entry RDL, so NUM_IRQS is not free here even though the core
    // scales. Same shape as the gpio/hpet guards.
    initial begin : param_check
        if (NUM_IRQS != 24) begin
            $error("ioapic_config_regs: NUM_IRQS=%0d but ioapic_regs.rdl defines 24 entries",
                   NUM_IRQS);
        end
    end
`endif

endmodule
