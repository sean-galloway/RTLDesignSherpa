// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
`timescale 1ns / 1ps
//
// axi4_to_axil5_rd: AXI4 slave -> AXI5-Lite master, read path.
//
// Companion to axi4_to_axil5_wr, and the same shape: a thin wrapper over
// axi4_to_axil4_rd, which does the real work. AXI5-Lite keeps the AXI4-Lite
// transfer protocol, so burst decomposition and RLAST reconstruction are
// inherited untouched; only the ID and the sideband are new here.
//
// Signal set is IHI 0022L B2.1.5 / Table B2.2. AxLOCK, AxMPAM, AxMECID,
// AxNSAID and xLOOP are NOT present on AXI5-Lite and exclusive access is not
// supported, so this module has none of them (they were carried until issue
// #102). AXI4 ARLOCK has nowhere to go and is dropped: an exclusive read
// arriving here completes as a normal read with OKAY, which is the AXI4
// response a Subordinate without exclusive support gives (IHI 0022H A7.2.3).
//
//   ID -- ARID and RID (IHI 0022L A5.1.1):
//     m_axil_arid  <- the AXI4 ARID of the burst the beat belongs to
//     s_axi_rid    <- m_axil_rid, the ID the AXI5-Lite Subordinate returned
//   The core decomposes one AXI4 burst into single AXI5-Lite beats and holds
//   ONE burst in flight per direction (s_axi_arready stays low until that
//   burst's RLAST has been handed back). So every R beat on the AXI5-Lite
//   side belongs to the one burst in flight: the Subordinate cannot reorder
//   across IDs because there is never a second ID outstanding, and same-ID
//   responses come back in order (A5.1.1). An AXI4 master using different
//   ARIDs therefore gets each read's data under its own RID, in issue order,
//   which AXI4 allows (any order is legal across IDs).
//
//   FORWARDED -- AXI4 has an equivalent:
//     aruser  (request)
//     ruser   (response, returned on the AXI4 R channel)
//
//   TIED -- AXI5-Lite optional signal with no AXI4 source, driven to '0:
//     artrace
//
//   TERMINATED -- completer-driven, nothing to return them to:
//     rtrace, rpoison
//
// rpoison deserves a note: AXI4 has no poison bit, so a poisoned read beat
// arriving from an AXI5-Lite slave cannot be signalled to the AXI4 master
// through any protocol field. It is terminated here rather than silently
// folded into RRESP, because turning poison into SLVERR would invent an
// error the slave did not report. A design that must observe poison needs an
// AXI5 master port, not an AXI4 one.
//
// The port convention mirrors rtl/amba/axil5/axil5_slave_rd.sv.

`include "reset_defs.svh"

module axi4_to_axil5_rd #(
    // AXI_ID_WIDTH is also the AXI5-Lite ARID/RID width: the AXI4 ID is
    // carried across unchanged (IHI 0022L Table A5.2 allows 1..32 here).
    parameter int AXI_ID_WIDTH      = 8,
    parameter int AXI_ADDR_WIDTH    = 32,
    parameter int AXI_DATA_WIDTH    = 32,
    parameter int AXI_USER_WIDTH    = 1,

    // Only USER gets an ENABLE_ knob, because only it has an AXI4 source to
    // gate. TRACE / POISON are tied to zero unconditionally -- an ENABLE_ for
    // those would be a parameter that cannot change the design's behaviour,
    // which is worse than no parameter: a reader sets it and believes
    // something happened. The width stays, because it sets the port shape.
    parameter bit ENABLE_USER       = 1'b0,

    parameter int USER_WIDTH        = 1,

    // One poison bit per 64-bit granule, matching rtl/amba/axil5
    localparam int POISON_WIDTH = (AXI_DATA_WIDTH / 64) > 0
                                    ? (AXI_DATA_WIDTH / 64) : 1
) (
    input  logic                        aclk,
    input  logic                        aresetn,

    //==========================================================================
    // Slave AXI4 Read Interface (input, full protocol)
    //==========================================================================
    input  logic [AXI_ID_WIDTH-1:0]     s_axi_arid,
    input  logic [AXI_ADDR_WIDTH-1:0]   s_axi_araddr,
    input  logic [7:0]                  s_axi_arlen,
    input  logic [2:0]                  s_axi_arsize,
    input  logic [1:0]                  s_axi_arburst,
    input  logic                        s_axi_arlock,
    input  logic [3:0]                  s_axi_arcache,
    input  logic [2:0]                  s_axi_arprot,
    input  logic [3:0]                  s_axi_arqos,
    input  logic [3:0]                  s_axi_arregion,
    input  logic [AXI_USER_WIDTH-1:0]   s_axi_aruser,
    input  logic                        s_axi_arvalid,
    output logic                        s_axi_arready,

    output logic [AXI_ID_WIDTH-1:0]     s_axi_rid,
    output logic [AXI_DATA_WIDTH-1:0]   s_axi_rdata,
    output logic [1:0]                  s_axi_rresp,
    output logic                        s_axi_rlast,
    output logic [AXI_USER_WIDTH-1:0]   s_axi_ruser,
    output logic                        s_axi_rvalid,
    input  logic                        s_axi_rready,

    //==========================================================================
    // Master AXI5-Lite Read Interface (output)
    //==========================================================================
    output logic [AXI_ID_WIDTH-1:0]     m_axil_arid,
    output logic [AXI_ADDR_WIDTH-1:0]   m_axil_araddr,
    output logic [2:0]                  m_axil_arprot,
    output logic                        m_axil_arvalid,
    input  logic                        m_axil_arready,

    input  logic [AXI_ID_WIDTH-1:0]     m_axil_rid,
    input  logic [AXI_DATA_WIDTH-1:0]   m_axil_rdata,
    input  logic [1:0]                  m_axil_rresp,
    input  logic                        m_axil_rvalid,
    output logic                        m_axil_rready,

    // ---- AXI5-Lite optional signals -------------------------------------
    output logic [USER_WIDTH-1:0]       m_axil_aruser,
    output logic                        m_axil_artrace,

    input  logic [USER_WIDTH-1:0]       m_axil_ruser,
    input  logic                        m_axil_rtrace,
    input  logic [POISON_WIDTH-1:0]     m_axil_rpoison
);

    //==========================================================================
    // FORWARDED / ID
    //==========================================================================
    // Held, not passed through -- for the reason spelled out in
    // axi4_to_axil5_wr: the core decomposes the burst, so one AXI4 AR
    // handshake becomes N AXI5-Lite AR handshakes, and s_axi_arready drops
    // after the first. The core muxes the address with
    // `r_ar_active ? r_ar_addr : s_axi_araddr`; w_ar_accept below is the
    // same selector expressed from outside the core, so the ID and sideband
    // travel with the address they were issued against.
    wire w_ar_accept = s_axi_arvalid && s_axi_arready;

    logic [AXI_ID_WIDTH-1:0]   r_held_arid;
    logic [AXI_USER_WIDTH-1:0] r_held_aruser;

    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_held_arid   <= '0;
            r_held_aruser <= '0;
        end else if (w_ar_accept) begin
            r_held_arid   <= s_axi_arid;
            r_held_aruser <= s_axi_aruser;
        end
    )

    wire [AXI_USER_WIDTH-1:0] w_aruser_sel = w_ar_accept ? s_axi_aruser : r_held_aruser;

    assign m_axil_arid = w_ar_accept ? s_axi_arid : r_held_arid;

    always_comb begin
        m_axil_aruser = '0;
        if (ENABLE_USER) m_axil_aruser = USER_WIDTH'(w_aruser_sel);
    end

    // RID is the ID the Subordinate returned (A5.1.1). With one burst in
    // flight it always equals that burst's ARID -- see the header.
    assign s_axi_rid = m_axil_rid;

    //==========================================================================
    // TIED: no AXI4 source. Driven, never floating.
    //==========================================================================
    assign m_axil_artrace = 1'b0;

    //==========================================================================
    // TERMINATED. rpoison is deliberately NOT folded into RRESP -- see the
    // header. ruser is the one response-side signal AXI4 can carry. ARLOCK
    // has no AXI5-Lite equivalent (B2.1.5) and is dropped.
    //==========================================================================
    // The core's own RID and RUSER outputs are overridden here, and are given
    // names rather than empty connections (see the note in axi4_to_axil5_wr).
    logic [AXI_ID_WIDTH-1:0]   w_core_rid_unused;
    logic [AXI_USER_WIDTH-1:0] w_core_ruser_unused;

    /* verilator lint_off UNUSED */
    wire _unused_axil5_sideband = &{1'b0, m_axil_rtrace, m_axil_rpoison,
                                    w_core_rid_unused, w_core_ruser_unused};
    /* verilator lint_on UNUSED */

    assign s_axi_ruser = ENABLE_USER ? AXI_USER_WIDTH'(m_axil_ruser) : '0;

    axi4_to_axil4_rd #(
        .AXI_ID_WIDTH   (AXI_ID_WIDTH),
        .AXI_ADDR_WIDTH (AXI_ADDR_WIDTH),
        .AXI_DATA_WIDTH (AXI_DATA_WIDTH),
        .AXI_USER_WIDTH (AXI_USER_WIDTH)
    ) u_core (
        .aclk           (aclk),
        .aresetn        (aresetn),

        .s_axi_arid     (s_axi_arid),
        .s_axi_araddr   (s_axi_araddr),
        .s_axi_arlen    (s_axi_arlen),
        .s_axi_arsize   (s_axi_arsize),
        .s_axi_arburst  (s_axi_arburst),
        .s_axi_arlock   (s_axi_arlock),
        .s_axi_arcache  (s_axi_arcache),
        .s_axi_arprot   (s_axi_arprot),
        .s_axi_arqos    (s_axi_arqos),
        .s_axi_arregion (s_axi_arregion),
        .s_axi_aruser   (s_axi_aruser),
        .s_axi_arvalid  (s_axi_arvalid),
        .s_axi_arready  (s_axi_arready),

        /* rid is driven above from the AXI5-Lite response */
        .s_axi_rid      (w_core_rid_unused),
        .s_axi_rdata    (s_axi_rdata),
        .s_axi_rresp    (s_axi_rresp),
        .s_axi_rlast    (s_axi_rlast),
        /* ruser is driven above from the AXI5-Lite response */
        .s_axi_ruser    (w_core_ruser_unused),
        .s_axi_rvalid   (s_axi_rvalid),
        .s_axi_rready   (s_axi_rready),

        .m_axil_araddr  (m_axil_araddr),
        .m_axil_arprot  (m_axil_arprot),
        .m_axil_arvalid (m_axil_arvalid),
        .m_axil_arready (m_axil_arready),

        .m_axil_rdata   (m_axil_rdata),
        .m_axil_rresp   (m_axil_rresp),
        .m_axil_rvalid  (m_axil_rvalid),
        .m_axil_rready  (m_axil_rready)
    );

endmodule : axi4_to_axil5_rd
