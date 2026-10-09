// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: amber_ace_issue
// Purpose:
//   Combinational cache-event -> ACE-transaction map per MAS ch02/08
//   Table 2.8.1 (the onyx D2 coherent subset), sitting between
//   amber_control / amber_fill / amber_drain and the house
//   axi4ace_master_rd / axi4ace_master_wr transports. It lives only in the
//   amber_ace rig (the pair-rig amber_top does not instantiate it).
//
// Documentation: projects/components/cache-ip/amber-mesi-l1/docs/amber_mas/ch02_blocks/08_amber_ace_issue.md
// Subsystem: amber
//
// Author: sean galloway
// Created: 2026-10-09

`timescale 1ns / 1ps
`include "reset_defs.svh"

//==============================================================================
// Module: amber_ace_issue
//==============================================================================
// Description:
//   Three jobs, one per channel group it intercepts:
//
//   AR (fill): the engine's AR passes through untouched; this block stamps
//   fub_axi_arsnoop from the latched launch class. The fill engine raises
//   AR the cycle after the launch pulse, so the class register (set by
//   ace_rd_req) is already stable when the address handshake runs -- a
//   pure combinational map from the register to the pin (MAS "Timing":
//   no pipeline stage between control and the transport skid).
//
//   AW (drain + upgrades): two producers share the wrapper AW channel,
//   never concurrently (the blocking control FSM visits MISS_DRAIN and
//   the upgrade's MISS_FILL in separate transactions):
//     * amber_drain's WriteBack AW passes through with
//       fub_axi_awsnoop = WriteBack (drain only ever launches for dirty
//       victims -- the control never drains a clean line).
//     * CleanUnique / MakeUnique / Evict are AW-only transactions the
//       engines never generate: this block originates the AW itself from
//       the ace_wr_req pulse and holds fub_axi_awvalid under backpressure
//       until the transport skid accepts it. The generated AW carries
//       AWONLY_ID (the engines drive ID 0) so the B response -- which the
//       manager returns per the ACE contract even though no W data
//       exists -- can be retired by this block's BID mux instead of
//       leaking onto the drain engine's B channel (its bready is a D_B
//       state output; a stray AW-only credit would otherwise misretire
//       the next WriteBack by one transaction).
//
//   B (drain): fub_axi_bvalid/bready pass through except responses whose
//   ID equals AWONLY_ID, which are consumed here (fub_bready forced,
//   eng_bvalid suppressed). Engine responses (ID 0) reach the drain
//   engine unmodified, in skid order.
//
//   Table 2.8.1 maps (snoop-field encodings):
//     ReadShared  arsnoop[3:0] = 4'h1     ReadUnique arsnoop[3:0] = 4'h7
//     CleanUnique awsnoop[2:0] = 3'h6     MakeUnique awsnoop[2:0] = 3'h4
//     WriteBack   awsnoop[2:0] = 3'h3     Evict      awsnoop[2:0] = 3'h5
//   The values are the framework ACETransactionType encodings where they
//   fit the wire width (ReadShared 0x1, ReadUnique 0x7, WriteBack 0x3,
//   Evict 0x5, MakeUnique 0xC -> low-3 0x4); CleanUnique's framework value
//   (0xB) collides with WriteBack under 3-bit truncation, so the family
//   AWSNOOP assigns the next free code 0x6. RACK/WACK are auto-pulsed by
//   the wrapper transports, not here.
//
//------------------------------------------------------------------------------
// Parameters:
//------------------------------------------------------------------------------
//   ADDR_WIDTH / BUS_WIDTH: geometry per amber_pkg (HAS Table 5.0).
//   AXI_ID_WIDTH / AXI_USER_WIDTH: fub_axi id/user field widths.
//   AWONLY_ID: AWID tag for self-originated AW-only transactions; must
//     differ from the engines' ID (0).
//
//------------------------------------------------------------------------------
// Notes:
//   - Single clock / active-low reset (aclk / aresetn), MAS ch01/03.
//   - The only registers are the in-flight read class and the AW-only
//     hold -- skid semantics, not pipeline stages: every engine-driven
//     payload path (AR/AW/B through-data) is combinational.
//   - ace_rd_addr / ace_rd_len are observational contract inputs (MAS
//     ch02/08 interface table): the AR address/burst ride the engine's
//     pins; ace_wr_len supplies the generated AW's awlen.
//
//------------------------------------------------------------------------------
// Related Modules:
//   - Instantiated by: amber_ace_top (Task 12)
//   - Sits between: amber_fill / amber_drain (via amber_core pins) and
//     axi4ace_master_rd / axi4ace_master_wr
//   - Package: amber_pkg (amber_ace_req_t)
//
//------------------------------------------------------------------------------
// Test:
//   Location: projects/components/cache-ip/amber-mesi-l1/dv/tests/test_amber_ace_top.py
//   Plan: dv/testplans/amber_ace_top_testplan.yaml
//   Run: pytest projects/components/cache-ip/amber-mesi-l1/dv/tests/test_amber_ace_top.py -v
//
//==============================================================================

module amber_ace_issue
    import amber_pkg::*;
#(
    parameter int ADDR_WIDTH     = AMBER_ADDR_WIDTH,
    parameter int BUS_WIDTH      = AMBER_BUS_WIDTH,
    parameter int AXI_ID_WIDTH   = 8,
    parameter int AXI_USER_WIDTH = 1,
    parameter logic [AXI_ID_WIDTH-1:0] AWONLY_ID = 8'h01,
    localparam int STRB_W = BUS_WIDTH / 8,
    localparam int IW     = AXI_ID_WIDTH,
    localparam int UW     = AXI_USER_WIDTH
)(
    input  logic                  aclk,
    input  logic                  aresetn,

    // ------------------------------------------------------------------
    // Cache-event inputs (MAS ch02/08 Table 2.8.1; one pulse per
    // coherence launch, from amber_control via the rig top)
    // ------------------------------------------------------------------
    input  logic                  ace_rd_req,
    input  logic [2:0]            ace_rd_type,
    input  logic [ADDR_WIDTH-1:0] ace_rd_addr,
    input  logic [7:0]            ace_rd_len,
    input  logic                  ace_wr_req,
    input  logic [2:0]            ace_wr_type,
    input  logic [ADDR_WIDTH-1:0] ace_wr_addr,
    input  logic [7:0]            ace_wr_len,

    // ------------------------------------------------------------------
    // Engine side: amber_fill AR
    // ------------------------------------------------------------------
    input  logic [IW-1:0]         eng_arid,
    input  logic [ADDR_WIDTH-1:0] eng_araddr,
    input  logic [7:0]            eng_arlen,
    input  logic [2:0]            eng_arsize,
    input  logic [1:0]            eng_arburst,
    input  logic                  eng_arlock,
    input  logic [3:0]            eng_arcache,
    input  logic [2:0]            eng_arprot,
    input  logic [3:0]            eng_arqos,
    input  logic [3:0]            eng_arregion,
    input  logic [UW-1:0]         eng_aruser,
    input  logic                  eng_arvalid,
    output logic                  eng_arready,

    // ------------------------------------------------------------------
    // Engine side: amber_drain AW + B
    // ------------------------------------------------------------------
    input  logic [IW-1:0]         eng_awid,
    input  logic [ADDR_WIDTH-1:0] eng_awaddr,
    input  logic [7:0]            eng_awlen,
    input  logic [2:0]            eng_awsize,
    input  logic [1:0]            eng_awburst,
    input  logic                  eng_awlock,
    input  logic [3:0]            eng_awcache,
    input  logic [2:0]            eng_awprot,
    input  logic [3:0]            eng_awqos,
    input  logic [3:0]            eng_awregion,
    input  logic [UW-1:0]         eng_awuser,
    input  logic                  eng_awvalid,
    output logic                  eng_awready,

    output logic [IW-1:0]         eng_bid,
    output logic [1:0]            eng_bresp,
    output logic [UW-1:0]         eng_buser,
    output logic                  eng_bvalid,
    input  logic                  eng_bready,

    // ------------------------------------------------------------------
    // Wrapper side: axi4ace_master_rd fub_axi AR
    // ------------------------------------------------------------------
    output logic [IW-1:0]         fub_arid,
    output logic [ADDR_WIDTH-1:0] fub_araddr,
    output logic [7:0]            fub_arlen,
    output logic [2:0]            fub_arsize,
    output logic [1:0]            fub_arburst,
    output logic                  fub_arlock,
    output logic [3:0]            fub_arcache,
    output logic [2:0]            fub_arprot,
    output logic [3:0]            fub_arqos,
    output logic [3:0]            fub_arregion,
    output logic [UW-1:0]         fub_aruser,
    output logic [3:0]            fub_arsnoop,
    output logic                  fub_arvalid,
    input  logic                  fub_arready,

    // ------------------------------------------------------------------
    // Wrapper side: axi4ace_master_wr fub_axi AW + B
    // ------------------------------------------------------------------
    output logic [IW-1:0]         fub_awid,
    output logic [ADDR_WIDTH-1:0] fub_awaddr,
    output logic [7:0]            fub_awlen,
    output logic [2:0]            fub_awsize,
    output logic [1:0]            fub_awburst,
    output logic                  fub_awlock,
    output logic [3:0]            fub_awcache,
    output logic [2:0]            fub_awprot,
    output logic [3:0]            fub_awqos,
    output logic [3:0]            fub_awregion,
    output logic [UW-1:0]         fub_awuser,
    output logic [2:0]            fub_awsnoop,
    output logic                  fub_awvalid,
    input  logic                  fub_awready,

    input  logic [IW-1:0]         fub_bid,
    input  logic [1:0]            fub_bresp,
    input  logic [UW-1:0]         fub_buser,
    input  logic                  fub_bvalid,
    output logic                  fub_bready
);

    // ------------------------------------------------------------------
    // Table 2.8.1 snoop-field encodings (see header for the authority)
    // ------------------------------------------------------------------
    localparam logic [3:0] ARSNOOP_READ_SHARED  = 4'h1;
    localparam logic [3:0] ARSNOOP_READ_UNIQUE  = 4'h7;
    localparam logic [2:0] AWSNOOP_CLEAN_UNIQUE = 3'h6;
    localparam logic [2:0] AWSNOOP_MAKE_UNIQUE  = 3'h4;
    localparam logic [2:0] AWSNOOP_WRITE_BACK   = 3'h3;
    localparam logic [2:0] AWSNOOP_EVICT        = 3'h5;

    // ------------------------------------------------------------------
    // Elaboration-time checks
    // ------------------------------------------------------------------
    initial begin
        if ((BUS_WIDTH % 8) != 0)
            $error("amber_ace_issue: BUS_WIDTH must be a multiple of 8");
        if (AWONLY_ID == '0)
            $error("amber_ace_issue: AWONLY_ID must differ from the engine ID 0");
    end

    /* verilator lint_off UNUSEDSIGNAL */
    logic unused_evt;
    assign unused_evt = &{1'b0, ace_rd_addr, ace_rd_len, 1'b0};
    /* verilator lint_on UNUSEDSIGNAL */

    // ------------------------------------------------------------------
    // AR: engine pass-through + ARSNOOP stamped from the latched class.
    // The fill engine raises AR the cycle after the launch pulse, so the
    // register is stable before the handshake; the map itself is
    // combinational (no pipeline stage, MAS ch02/08 "Timing").
    // ------------------------------------------------------------------
    logic [2:0] rd_class_q;

    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            rd_class_q <= 3'(AMBER_ACE_READ_SHARED);
        end else if (ace_rd_req) begin
            rd_class_q <= ace_rd_type;
        end
    )

    always_comb begin
        unique case (rd_class_q)
            AMBER_ACE_READ_UNIQUE: fub_arsnoop = ARSNOOP_READ_UNIQUE;
            default:               fub_arsnoop = ARSNOOP_READ_SHARED;
        endcase
    end

    assign fub_arid      = eng_arid;
    assign fub_araddr    = eng_araddr;
    assign fub_arlen     = eng_arlen;
    assign fub_arsize    = eng_arsize;
    assign fub_arburst   = eng_arburst;
    assign fub_arlock    = eng_arlock;
    assign fub_arcache   = eng_arcache;
    assign fub_arprot    = eng_arprot;
    assign fub_arqos     = eng_arqos;
    assign fub_arregion  = eng_arregion;
    assign fub_aruser    = eng_aruser;
    assign fub_arvalid   = eng_arvalid;
    assign eng_arready   = fub_arready;

    // ------------------------------------------------------------------
    // AW-only generator: CleanUnique / MakeUnique / Evict carry no engine
    // transaction -- the engines never generate them -- so this block
    // originates the AW and holds it until the transport skid accepts it.
    // Burst fields mirror the engines' constants (whole-line INCR).
    // ------------------------------------------------------------------
    logic                  awonly_valid_q;
    logic [ADDR_WIDTH-1:0] awonly_addr_q;
    logic [7:0]            awonly_len_q;
    logic [2:0]            awonly_type_q;

    logic awonly_req;
    assign awonly_req = ace_wr_req
        && (ace_wr_type == 3'(AMBER_ACE_CLEAN_UNIQUE)
            || ace_wr_type == 3'(AMBER_ACE_MAKE_UNIQUE)
            || ace_wr_type == 3'(AMBER_ACE_EVICT));

    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            awonly_valid_q <= 1'b0;
            awonly_addr_q  <= '0;
            awonly_len_q   <= 8'h0;
            awonly_type_q  <= 3'(AMBER_ACE_CLEAN_UNIQUE);
        end else if (awonly_req) begin
            // a new AW-only request (the blocking control launches one
            // coherence event at a time, so the register is free)
            awonly_valid_q <= 1'b1;
            awonly_addr_q  <= ace_wr_addr;
            awonly_len_q   <= ace_wr_len;
            awonly_type_q  <= ace_wr_type;
        end else if (awonly_valid_q && fub_awready) begin
            awonly_valid_q <= 1'b0;
        end
    )

    // ------------------------------------------------------------------
    // AW mux: the drain engine has priority (the control waits on its
    // WriteBack); the AW-only AW holds until selected. The two never
    // contend by construction (MISS_DRAIN and the upgrade's MISS_FILL are
    // separate transactions), and the priority keeps the choice safe.
    // ------------------------------------------------------------------
    assign fub_awvalid  = eng_awvalid | awonly_valid_q;
    assign eng_awready  = fub_awready & (eng_awvalid | ~awonly_valid_q);

    assign fub_awid     = eng_awvalid ? eng_awid    : AWONLY_ID;
    assign fub_awaddr   = eng_awvalid ? eng_awaddr  : awonly_addr_q;
    assign fub_awlen    = eng_awvalid ? eng_awlen   : awonly_len_q;
    assign fub_awsize   = eng_awvalid ? eng_awsize
                                      : 3'($clog2(STRB_W));
    assign fub_awburst  = eng_awvalid ? eng_awburst : 2'b01;  // INCR
    assign fub_awlock   = eng_awvalid ? eng_awlock  : 1'b0;
    assign fub_awcache  = eng_awvalid ? eng_awcache : 4'b0;
    assign fub_awprot   = eng_awvalid ? eng_awprot  : 3'b0;
    assign fub_awqos    = eng_awvalid ? eng_awqos   : 4'b0;
    assign fub_awregion = eng_awvalid ? eng_awregion : 4'b0;
    assign fub_awuser   = eng_awvalid ? eng_awuser  : '0;

    always_comb begin
        if (eng_awvalid) begin
            // the drain engine only ever carries dirty victims (Table
            // 2.8.1: dirty eviction -> WriteBack)
            fub_awsnoop = AWSNOOP_WRITE_BACK;
        end else begin
            unique case (awonly_type_q)
                AMBER_ACE_MAKE_UNIQUE: fub_awsnoop = AWSNOOP_MAKE_UNIQUE;
                AMBER_ACE_EVICT:       fub_awsnoop = AWSNOOP_EVICT;
                default:               fub_awsnoop = AWSNOOP_CLEAN_UNIQUE;
            endcase
        end
    end

    // ------------------------------------------------------------------
    // B: AW-only responses (BID == AWONLY_ID) are retired here -- the
    // drain engine's bready only exists in D_B and must never see them;
    // engine responses (ID 0) pass through in skid order.
    // ------------------------------------------------------------------
    assign eng_bvalid = fub_bvalid & (fub_bid != AWONLY_ID);
    assign fub_bready = (fub_bid == AWONLY_ID) ? 1'b1 : eng_bready;
    assign eng_bid    = fub_bid;
    assign eng_bresp  = fub_bresp;
    assign eng_buser  = fub_buser;

endmodule : amber_ace_issue
