// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: amber_snoop_resp
// Purpose:
//   ACE-shaped snoop responder for the amber MESI L1. Wraps the house
//   axi4ace_snoop_slave transport, translates the 4-bit IHI0022 ACSNOOP
//   to amber's internal 3-bit snoop encoding, and sequences CR / CD per
//   the MAS SR FSM. Inside amber_core the snoop is bus-agnostic; only
//   this module speaks ACE.
//
// Documentation: projects/components/cache-ip/amber-mesi-l1/docs/amber_mas/ch02_blocks/07_amber_snoop_resp.md
// Subsystem: amber
//
// Author: sean galloway
// Created: 2026-10-06

`timescale 1ns / 1ps

`include "reset_defs.svh"

//==============================================================================
// Module: amber_snoop_resp
//==============================================================================
// Description:
//   One closed snoop response at a time (MAS ch02_blocks/07):
//
//     SR_IDLE   : AC request accepted from the transport; snoop type
//                 translated; request raised to amber_control.
//     SR_LOOKUP : waiting for amber_control (ctrl_snoop_ready); CRRESP is
//                 latched at the handshake.
//     SR_DATA   : CRRESP.DataTransfer set: CD beats pass through from
//                 control until the last beat is accepted.
//     SR_RESP   : CR presented (only after the final CD beat -- IHI0022
//                 and the family onyx-D4 convention); back to IDLE on the
//                 CR handshake.
//
//   ACSNOOP translation (IHI0022 4-bit -> amber 3-bit; encodings per the
//   cocotb-framework 1.2.0 SnoopType table):
//     0x0 ReadOnce      -> 3'b001      0x8 CleanShared  -> 3'b011
//     0x1 ReadShared    -> 3'b000      0x9 CleanInvalid -> 3'b100
//     0x7 ReadUnique    -> 3'b010      0xC MakeInvalid  -> 3'b101
//     anything else     -> 3'b110 (reserved; kmap safe default: no data,
//                          next Invalid)
//
//   The 5-bit CRRESP wire order is IHI0022: {WU[4], IS[3], PD[2], Err[1],
//   DT[0]} -- the same order amber_pkg.amber_snoop_crresp produces and
//   the cocotb-framework CRRESPBit enum defines.
//
//------------------------------------------------------------------------------
// Parameters:
//------------------------------------------------------------------------------
//   ADDR_WIDTH / DATA_WIDTH / LINE_BYTES: geometry; DATA_WIDTH is the CD
//     beat width and LINE_BYTES fixes the beat count the control side
//     supplies (this module forwards control's cdlast; it does not count
//     beats itself -- MAS ch02_blocks/07).
//
//------------------------------------------------------------------------------
// Related Modules:
//------------------------------------------------------------------------------
//   - Wraps: axi4ace_snoop_slave (rtl/amba/ace) -- skid-buffered transport
//   - Sequencing input: amber_control (ctrl_* handshake, stubbed in DV)
//   - Decode authority: amber_pkg Table 3.0 functions (in control)
//
//------------------------------------------------------------------------------
// Test:
//------------------------------------------------------------------------------
//   Location: projects/components/cache-ip/amber-mesi-l1/dv/tests/fub/test_amber_snoop_resp.py
//   Run: pytest projects/components/cache-ip/amber-mesi-l1/dv/tests/fub/test_amber_snoop_resp.py -v
//
//==============================================================================

module amber_snoop_resp
    import amber_pkg::*;
#(
    parameter int ADDR_WIDTH = AMBER_ADDR_WIDTH,
    parameter int DATA_WIDTH = AMBER_BUS_WIDTH,
    parameter int LINE_BYTES = AMBER_LINE_BYTES
)(
    input  logic                    aclk,
    input  logic                    aresetn,

    // ACE snoop slave external side
    input  logic [ADDR_WIDTH-1:0]   m_axi_acaddr,
    input  logic [3:0]              m_axi_acsnoop,
    input  logic [2:0]              m_axi_acprot,
    input  logic                    m_axi_acvalid,
    output logic                    m_axi_acready,
    output logic [4:0]              m_axi_crresp,
    output logic                    m_axi_crvalid,
    input  logic                    m_axi_crready,
    output logic [DATA_WIDTH-1:0]   m_axi_cddata,
    output logic                    m_axi_cdlast,
    output logic                    m_axi_cdvalid,
    input  logic                    m_axi_cdready,

    // Core-facing handshake (amber_control)
    output logic                    ctrl_snoop_req,
    output logic [ADDR_WIDTH-1:0]   ctrl_snoop_addr,
    output logic [2:0]              ctrl_snoop_type,
    input  logic                    ctrl_snoop_ready,
    input  logic [4:0]              ctrl_crresp,
    input  logic [DATA_WIDTH-1:0]   ctrl_cddata,
    input  logic                    ctrl_cdlast,
    input  logic                    ctrl_cdvalid,
    output logic                    ctrl_cdready
);

    // ------------------------------------------------------------------
    // Transport: skid-buffered AC/CR/CD between the ACE pins and the FSM
    // ------------------------------------------------------------------
    logic [ADDR_WIDTH-1:0] fub_acaddr;
    logic [3:0]            fub_acsnoop;
    logic [2:0]            fub_acprot;
    logic                  fub_acvalid;
    logic                  fub_acready;
    logic [4:0]            fub_crresp;
    logic                  fub_crvalid;
    logic                  fub_crready;
    logic [DATA_WIDTH-1:0] fub_cddata;
    logic                  fub_cdlast;
    logic                  fub_cdvalid;
    logic                  fub_cdready;
    logic                  w_busy;

    axi4ace_snoop_slave #(
        .ADDR_WIDTH (ADDR_WIDTH),
        .DATA_WIDTH (DATA_WIDTH)
    ) u_transport (
        .aclk           (aclk),
        .aresetn        (aresetn),
        .m_axi_acaddr   (m_axi_acaddr),
        .m_axi_acsnoop  (m_axi_acsnoop),
        .m_axi_acprot   (m_axi_acprot),
        .m_axi_acvalid  (m_axi_acvalid),
        .m_axi_acready  (m_axi_acready),
        .m_axi_crresp   (m_axi_crresp),
        .m_axi_crvalid  (m_axi_crvalid),
        .m_axi_crready  (m_axi_crready),
        .m_axi_cddata   (m_axi_cddata),
        .m_axi_cdlast   (m_axi_cdlast),
        .m_axi_cdvalid  (m_axi_cdvalid),
        .m_axi_cdready  (m_axi_cdready),
        .fub_acaddr     (fub_acaddr),
        .fub_acsnoop    (fub_acsnoop),
        .fub_acprot     (fub_acprot),
        .fub_acvalid    (fub_acvalid),
        .fub_acready    (fub_acready),
        .fub_crresp     (fub_crresp),
        .fub_crvalid    (fub_crvalid),
        .fub_crready    (fub_crready),
        .fub_cddata     (fub_cddata),
        .fub_cdlast     (fub_cdlast),
        .fub_cdvalid    (fub_cdvalid),
        .fub_cdready    (fub_cdready),
        .busy           (w_busy)
    );

    // ------------------------------------------------------------------
    // ACSNOOP translation: IHI0022 4-bit -> amber internal 3-bit
    // ------------------------------------------------------------------
    logic [2:0] w_snoop_type;
    always_comb begin
        case (fub_acsnoop)
            4'h0:    w_snoop_type = AMBER_SNOOP_READ_ONCE;      // ReadOnce
            4'h1:    w_snoop_type = AMBER_SNOOP_READ_SHARED;    // ReadShared
            4'h7:    w_snoop_type = AMBER_SNOOP_READ_UNIQUE;    // ReadUnique
            4'h8:    w_snoop_type = AMBER_SNOOP_CLEAN_SHARED;   // CleanShared
            4'h9:    w_snoop_type = AMBER_SNOOP_CLEAN_INVALID;  // CleanInvalid
            4'hC:    w_snoop_type = AMBER_SNOOP_MAKE_INVALID;   // MakeInvalid
            default: w_snoop_type = 3'b110;  // reserved: kmap safe default
        endcase
    end

    // ------------------------------------------------------------------
    // SR sequencing FSM (MAS ch02_blocks/07)
    // ------------------------------------------------------------------
    typedef enum logic [1:0] {
        SR_IDLE   = 2'd0,
        SR_LOOKUP = 2'd1,
        SR_DATA   = 2'd2,
        SR_RESP   = 2'd3
    } sr_state_t;

    sr_state_t r_state;
    logic [4:0]              r_crresp;
    logic [ADDR_WIDTH-1:0]   r_snoop_addr;
    logic [2:0]              r_snoop_type;

    assign ctrl_snoop_req  = (r_state == SR_LOOKUP);
    assign ctrl_snoop_addr = r_snoop_addr;
    assign ctrl_snoop_type = r_snoop_type;

    // FUB-side drives (combinational on state; the transport skids absorb
    // the protocol timing)
    assign fub_acready     = (r_state == SR_IDLE);
    assign fub_crresp      = r_crresp;
    assign fub_crvalid     = (r_state == SR_RESP);
    assign fub_cddata      = ctrl_cddata;
    assign fub_cdlast      = ctrl_cdlast;
    assign fub_cdvalid     = (r_state == SR_DATA) && ctrl_cdvalid;
    assign ctrl_cdready    = (r_state == SR_DATA) && fub_cdready;

    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_state      <= SR_IDLE;
            r_crresp     <= '0;
            r_snoop_addr <= '0;
            r_snoop_type <= '0;
        end else begin
            unique case (r_state)
                SR_IDLE: begin
                    if (fub_acvalid && fub_acready) begin
                        r_snoop_addr <= fub_acaddr;
                        r_snoop_type <= w_snoop_type;
                        r_state      <= SR_LOOKUP;
                    end
                end
                SR_LOOKUP: begin
                    if (ctrl_snoop_req && ctrl_snoop_ready) begin
                        r_crresp <= ctrl_crresp;
                        // DT decision uses the CRRESP being latched this
                        // cycle, not the registered one.
                        r_state  <= ctrl_crresp[AMBER_CRRESP_DT] ? SR_DATA
                                                                 : SR_RESP;
                    end
                end
                SR_DATA: begin
                    if (fub_cdvalid && fub_cdready && fub_cdlast) begin
                        r_state <= SR_RESP;
                    end
                end
                SR_RESP: begin
                    if (fub_crvalid && fub_crready) begin
                        r_state <= SR_IDLE;
                    end
                end
                default: r_state <= SR_IDLE;
            endcase
        end
    )

endmodule : amber_snoop_resp
