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
// inherited untouched; only the sideband is new here.
//
//   FORWARDED -- AXI4 has an equivalent:
//     arlock, aruser  (request)
//     ruser           (response, returned on the AXI4 R channel)
//
//   TIED -- AXI5 additions with no AXI4 source, driven to '0:
//     arloop, armecid, armpam, arnsaid, artrace
//
//   TERMINATED -- completer-driven, nothing to return them to:
//     rloop, rtrace, rpoison
//
// rpoison deserves a note: AXI4 has no poison bit, so a poisoned read beat
// arriving from an AXI5-Lite slave cannot be signalled to the AXI4 master
// through any protocol field. It is terminated here rather than silently
// folded into RRESP, because turning poison into SLVERR would invent an
// error the slave did not report. A design that must observe poison needs an
// AXI5 master port, not an AXI4 one.
//
// The port convention mirrors rtl/amba/axil5/axil5_slave_rd.sv.

module axi4_to_axil5_rd #(
    parameter int AXI_ID_WIDTH      = 8,
    parameter int AXI_ADDR_WIDTH    = 32,
    parameter int AXI_DATA_WIDTH    = 32,
    parameter int AXI_USER_WIDTH    = 1,

    parameter bit ENABLE_LOCK       = 1'b0,
    parameter bit ENABLE_USER       = 1'b0,
    parameter bit ENABLE_POISON     = 1'b0,
    parameter bit ENABLE_TRACE      = 1'b0,
    parameter bit ENABLE_LOOP       = 1'b0,
    parameter bit ENABLE_MPAM       = 1'b0,
    parameter bit ENABLE_MECID      = 1'b0,
    parameter bit ENABLE_NSAID      = 1'b0,

    parameter int USER_WIDTH        = 1,
    parameter int LOOP_WIDTH        = 1,
    parameter int MPAM_WIDTH        = 11,
    parameter int MECID_WIDTH       = 16,
    parameter int NSAID_WIDTH       = 4,

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
    output logic [AXI_ADDR_WIDTH-1:0]   m_axil_araddr,
    output logic [2:0]                  m_axil_arprot,
    output logic                        m_axil_arvalid,
    input  logic                        m_axil_arready,

    input  logic [AXI_DATA_WIDTH-1:0]   m_axil_rdata,
    input  logic [1:0]                  m_axil_rresp,
    input  logic                        m_axil_rvalid,
    output logic                        m_axil_rready,

    // ---- AXI5-Lite sideband -------------------------------------------
    output logic                        m_axil_arlock,
    output logic [USER_WIDTH-1:0]       m_axil_aruser,
    output logic [LOOP_WIDTH-1:0]       m_axil_arloop,
    output logic [MPAM_WIDTH-1:0]       m_axil_armpam,
    output logic [MECID_WIDTH-1:0]      m_axil_armecid,
    output logic [NSAID_WIDTH-1:0]      m_axil_arnsaid,
    output logic                        m_axil_artrace,

    input  logic [USER_WIDTH-1:0]       m_axil_ruser,
    input  logic [LOOP_WIDTH-1:0]       m_axil_rloop,
    input  logic                        m_axil_rtrace,
    input  logic [POISON_WIDTH-1:0]     m_axil_rpoison
);

    //==========================================================================
    // FORWARDED
    //==========================================================================
    // Held, not passed through -- for the reason spelled out in
    // axi4_to_axil5_wr: the core decomposes the burst, so one AXI4 AR
    // handshake becomes N AXI5-Lite AR handshakes, and s_axi_arready drops
    // after the first. The core muxes the address with
    // `r_ar_active ? r_ar_addr : s_axi_araddr`; w_ar_accept below is the
    // same selector expressed from outside the core, so the sideband
    // travels with the address it was issued against.
    wire w_ar_accept = s_axi_arvalid && s_axi_arready;

    logic                      r_held_arlock;
    logic [AXI_USER_WIDTH-1:0] r_held_aruser;

    // Reset style follows axi4_to_axil4_rd, the module this wraps:
    // manual async reset, not `ALWAYS_FF_RST`. The components-area mandate
    // (GLOBAL_REQUIREMENTS 1.1) says the macro, and these converters predate
    // it. Using the macro HERE while the core stays manual makes one design
    // half sync-reset and half async in the default build -- Verilator says
    // so with SYNCASYNCNET. Converting the whole area is real work with real
    // verification behind it (11 flops change from async to sync reset, and
    // two multi-label `case` arms have to move because the macro takes its
    // body as an argument); it is tracked as CONV-009, not smuggled in here.
    always_ff @(posedge aclk or negedge aresetn) begin
        if (!aresetn) begin
            r_held_arlock <= 1'b0;
            r_held_aruser <= '0;
        end else if (w_ar_accept) begin
            r_held_arlock <= s_axi_arlock;
            r_held_aruser <= s_axi_aruser;
        end
    end

    wire                      w_arlock_sel = w_ar_accept ? s_axi_arlock : r_held_arlock;
    wire [AXI_USER_WIDTH-1:0] w_aruser_sel = w_ar_accept ? s_axi_aruser : r_held_aruser;

    assign m_axil_arlock = ENABLE_LOCK ? w_arlock_sel : 1'b0;

    always_comb begin
        m_axil_aruser = '0;
        if (ENABLE_USER) m_axil_aruser = USER_WIDTH'(w_aruser_sel);
    end

    //==========================================================================
    // TIED: no AXI4 source. Driven, never floating.
    //==========================================================================
    assign m_axil_arloop  = '0;
    assign m_axil_armpam  = '0;
    assign m_axil_armecid = '0;
    assign m_axil_arnsaid = '0;
    assign m_axil_artrace = 1'b0;

    //==========================================================================
    // TERMINATED. rpoison is deliberately NOT folded into RRESP -- see the
    // header. ruser is the one response-side signal AXI4 can carry.
    //==========================================================================
    /* verilator lint_off UNUSED */
    wire _unused_axil5_sideband = &{1'b0, m_axil_rloop, m_axil_rtrace,
                                    m_axil_rpoison};
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

        .s_axi_rid      (s_axi_rid),
        .s_axi_rdata    (s_axi_rdata),
        .s_axi_rresp    (s_axi_rresp),
        .s_axi_rlast    (s_axi_rlast),
        /* ruser is driven above from the AXI5-Lite response */
        .s_axi_ruser    (),
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
