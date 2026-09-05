// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
`timescale 1ns / 1ps
//
// axi4_to_axil5_wr: AXI4 slave -> AXI5-Lite master, write path.
//
// Thin wrapper over axi4_to_axil4_wr, which is the workhorse: AXI5-Lite
// keeps the AXI4-Lite transfer protocol unchanged, so burst decomposition,
// response folding and the skid buffers are all inherited untouched. What
// AXI5-Lite adds on this surface is pure sideband, and this module is only
// about where each of those signals comes from.
//
// Three groups, and the distinction matters because two of them carry real
// data and one cannot:
//
//   FORWARDED -- AXI4 has an equivalent and it is passed straight through:
//     awlock, awuser, wuser  (request side)
//     buser                  (response side, returned to the AXI4 master)
//
//   TIED -- AXI5 introduced these and AXI4 has no source for them. The port
//   exists (an AXI5-Lite boundary whose shape changes with a config knob
//   cannot be wired to a fixed slave) and is driven to '0 rather than left
//   floating. There is deliberately no ENABLE_ for this group: nothing it
//   could switch between.
//     awloop, awmecid, awmpam, awnsaid, awtrace, wpoison
//
//   TERMINATED -- completer-driven, with nothing on the AXI4 side to return
//   them to:
//     bloop, btrace
//
// The tied group is the honest limit of an AXI4 front end: MPAM partition
// IDs, MECID encryption contexts and NSAID security IDs are properties the
// AXI4 master never supplied, so inventing them here would be worse than
// zeroing them. A design that needs them driven should use an AXI5 master
// port and carry them end to end.
//
// The port convention mirrors rtl/amba/axil5/axil5_slave_wr.sv, so this
// master drops onto that slave pin-for-pin.

module axi4_to_axil5_wr #(
    parameter int AXI_ID_WIDTH      = 8,
    parameter int AXI_ADDR_WIDTH    = 32,
    parameter int AXI_DATA_WIDTH    = 32,
    parameter int AXI_USER_WIDTH    = 1,

    // AXI5-Lite feature enables. Each gates one sideband group; all
    // default off so an axil5 port with no features is bit-identical to
    // axil4 plus the forwarded signals.
    // Only LOCK and USER get an ENABLE_ knob, because only they have an AXI4
    // source to gate. TRACE / LOOP / MPAM / MECID / NSAID / POISON are tied
    // to zero unconditionally -- an ENABLE_ for those would be a parameter
    // that cannot change the design's behaviour, which is worse than no
    // parameter: a reader sets it and believes something happened. The
    // widths stay, because they set the port shape.
    parameter bit ENABLE_LOCK       = 1'b0,
    parameter bit ENABLE_USER       = 1'b0,

    parameter int USER_WIDTH        = 1,
    parameter int LOOP_WIDTH        = 1,
    parameter int MPAM_WIDTH        = 11,
    parameter int MECID_WIDTH       = 16,
    parameter int NSAID_WIDTH       = 4,

    localparam int STRB_WIDTH = AXI_DATA_WIDTH / 8,
    // One poison bit per 64-bit granule, matching rtl/amba/axil5
    localparam int POISON_WIDTH = (AXI_DATA_WIDTH / 64) > 0
                                    ? (AXI_DATA_WIDTH / 64) : 1
) (
    input  logic                        aclk,
    input  logic                        aresetn,

    //==========================================================================
    // Slave AXI4 Write Interface (input, full protocol)
    //==========================================================================
    input  logic [AXI_ID_WIDTH-1:0]     s_axi_awid,
    input  logic [AXI_ADDR_WIDTH-1:0]   s_axi_awaddr,
    input  logic [7:0]                  s_axi_awlen,
    input  logic [2:0]                  s_axi_awsize,
    input  logic [1:0]                  s_axi_awburst,
    input  logic                        s_axi_awlock,
    input  logic [3:0]                  s_axi_awcache,
    input  logic [2:0]                  s_axi_awprot,
    input  logic [3:0]                  s_axi_awqos,
    input  logic [3:0]                  s_axi_awregion,
    input  logic [AXI_USER_WIDTH-1:0]   s_axi_awuser,
    input  logic                        s_axi_awvalid,
    output logic                        s_axi_awready,

    input  logic [AXI_DATA_WIDTH-1:0]   s_axi_wdata,
    input  logic [STRB_WIDTH-1:0]       s_axi_wstrb,
    input  logic                        s_axi_wlast,
    input  logic [AXI_USER_WIDTH-1:0]   s_axi_wuser,
    input  logic                        s_axi_wvalid,
    output logic                        s_axi_wready,

    output logic [AXI_ID_WIDTH-1:0]     s_axi_bid,
    output logic [1:0]                  s_axi_bresp,
    output logic [AXI_USER_WIDTH-1:0]   s_axi_buser,
    output logic                        s_axi_bvalid,
    input  logic                        s_axi_bready,

    //==========================================================================
    // Master AXI5-Lite Write Interface (output)
    //==========================================================================
    output logic [AXI_ADDR_WIDTH-1:0]   m_axil_awaddr,
    output logic [2:0]                  m_axil_awprot,
    output logic                        m_axil_awvalid,
    input  logic                        m_axil_awready,

    output logic [AXI_DATA_WIDTH-1:0]   m_axil_wdata,
    output logic [STRB_WIDTH-1:0]       m_axil_wstrb,
    output logic                        m_axil_wvalid,
    input  logic                        m_axil_wready,

    input  logic [1:0]                  m_axil_bresp,
    input  logic                        m_axil_bvalid,
    output logic                        m_axil_bready,

    // ---- AXI5-Lite sideband -------------------------------------------
    output logic                        m_axil_awlock,
    output logic [USER_WIDTH-1:0]       m_axil_awuser,
    output logic [LOOP_WIDTH-1:0]       m_axil_awloop,
    output logic [MPAM_WIDTH-1:0]       m_axil_awmpam,
    output logic [MECID_WIDTH-1:0]      m_axil_awmecid,
    output logic [NSAID_WIDTH-1:0]      m_axil_awnsaid,
    output logic                        m_axil_awtrace,

    output logic [USER_WIDTH-1:0]       m_axil_wuser,
    output logic [POISON_WIDTH-1:0]     m_axil_wpoison,

    input  logic [USER_WIDTH-1:0]       m_axil_buser,
    input  logic [LOOP_WIDTH-1:0]       m_axil_bloop,
    input  logic                        m_axil_btrace
);

    //==========================================================================
    // FORWARDED: AXI4 has these, so they carry real values.
    //==========================================================================
    // The AW sideband has to be HELD, not passed through. The core
    // decomposes a burst: the AXI4 AW handshakes once, the AXI5-Lite AW
    // handshakes once per beat over the following cycles, and the core
    // drops s_axi_awready as soon as it accepts, so the master is free to
    // present the NEXT transaction's AW signals while beats 2..N are still
    // going out. A combinational passthrough would stamp those later beats
    // with the wrong USER and LOCK.
    //
    // The core has the identical problem with the address and solves it
    // with `r_aw_active ? r_aw_addr : s_axi_awaddr`. r_aw_active is
    // registered, so it is still 0 during the accept cycle itself and 1 for
    // every beat after -- which is exactly what w_aw_accept selects here.
    // Mirroring the core's mux keeps the sideband aligned with the address
    // it belongs to, beat for beat.
    wire w_aw_accept = s_axi_awvalid && s_axi_awready;

    logic                      r_held_awlock;
    logic [AXI_USER_WIDTH-1:0] r_held_awuser;

    // Reset style follows axi4_to_axil4_wr, the module this wraps:
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
            r_held_awlock <= 1'b0;
            r_held_awuser <= '0;
        end else if (w_aw_accept) begin
            r_held_awlock <= s_axi_awlock;
            r_held_awuser <= s_axi_awuser;
        end
    end

    wire                      w_awlock_sel = w_aw_accept ? s_axi_awlock : r_held_awlock;
    wire [AXI_USER_WIDTH-1:0] w_awuser_sel = w_aw_accept ? s_axi_awuser : r_held_awuser;

    assign m_axil_awlock = ENABLE_LOCK ? w_awlock_sel : 1'b0;

    // W beats are 1:1 with the AXI4 side (the core assigns m_axil_wdata
    // straight from s_axi_wdata), so WUSER needs no hold -- only AW does.
    //
    // USER widths need not match. Narrow the AXI4 side or zero-extend it,
    // rather than relying on an implicit resize that lint would report and
    // a reader would have to reason about.
    always_comb begin
        m_axil_awuser = '0;
        m_axil_wuser  = '0;
        if (ENABLE_USER) begin
            m_axil_awuser = USER_WIDTH'(w_awuser_sel);
            m_axil_wuser  = USER_WIDTH'(s_axi_wuser);
        end
    end

    //==========================================================================
    // TIED: AXI5 additions with no AXI4 source. Driven, never floating.
    //==========================================================================
    assign m_axil_awloop   = '0;
    assign m_axil_awmpam   = '0;
    assign m_axil_awmecid  = '0;
    assign m_axil_awnsaid  = '0;
    assign m_axil_awtrace  = 1'b0;
    assign m_axil_wpoison  = '0;

    //==========================================================================
    // TERMINATED: completer-driven, nothing on the AXI4 side to receive
    // them. buser is the exception -- AXI4 has BUSER, so it is returned.
    //==========================================================================
    // The core drives its own BUSER, which this module overrides from the
    // AXI5-Lite response. Connected to a named net rather than left open: an
    // empty port connection reads as PINCONNECTEMPTY, and a lint gate that
    // has to be told to ignore a category stops catching the accidents in it.
    logic [AXI_USER_WIDTH-1:0] w_core_buser_unused;

    /* verilator lint_off UNUSED */
    wire _unused_axil5_sideband = &{1'b0, m_axil_bloop, m_axil_btrace,
                                    w_core_buser_unused};
    /* verilator lint_on UNUSED */

    //==========================================================================
    // The AXI4-Lite workhorse. buser is folded back onto the AXI4 B channel
    // by this module rather than by the core, which has no such port.
    //==========================================================================
    logic [AXI_USER_WIDTH-1:0] core_buser;
    assign core_buser  = ENABLE_USER ? AXI_USER_WIDTH'(m_axil_buser) : '0;
    assign s_axi_buser = core_buser;

    axi4_to_axil4_wr #(
        .AXI_ID_WIDTH   (AXI_ID_WIDTH),
        .AXI_ADDR_WIDTH (AXI_ADDR_WIDTH),
        .AXI_DATA_WIDTH (AXI_DATA_WIDTH),
        .AXI_USER_WIDTH (AXI_USER_WIDTH)
    ) u_core (
        .aclk           (aclk),
        .aresetn        (aresetn),

        .s_axi_awid     (s_axi_awid),
        .s_axi_awaddr   (s_axi_awaddr),
        .s_axi_awlen    (s_axi_awlen),
        .s_axi_awsize   (s_axi_awsize),
        .s_axi_awburst  (s_axi_awburst),
        .s_axi_awlock   (s_axi_awlock),
        .s_axi_awcache  (s_axi_awcache),
        .s_axi_awprot   (s_axi_awprot),
        .s_axi_awqos    (s_axi_awqos),
        .s_axi_awregion (s_axi_awregion),
        .s_axi_awuser   (s_axi_awuser),
        .s_axi_awvalid  (s_axi_awvalid),
        .s_axi_awready  (s_axi_awready),

        .s_axi_wdata    (s_axi_wdata),
        .s_axi_wstrb    (s_axi_wstrb),
        .s_axi_wlast    (s_axi_wlast),
        .s_axi_wuser    (s_axi_wuser),
        .s_axi_wvalid   (s_axi_wvalid),
        .s_axi_wready   (s_axi_wready),

        .s_axi_bid      (s_axi_bid),
        .s_axi_bresp    (s_axi_bresp),
        /* buser is driven above from the AXI5-Lite response */
        .s_axi_buser    (w_core_buser_unused),
        .s_axi_bvalid   (s_axi_bvalid),
        .s_axi_bready   (s_axi_bready),

        .m_axil_awaddr  (m_axil_awaddr),
        .m_axil_awprot  (m_axil_awprot),
        .m_axil_awvalid (m_axil_awvalid),
        .m_axil_awready (m_axil_awready),

        .m_axil_wdata   (m_axil_wdata),
        .m_axil_wstrb   (m_axil_wstrb),
        .m_axil_wvalid  (m_axil_wvalid),
        .m_axil_wready  (m_axil_wready),

        .m_axil_bresp   (m_axil_bresp),
        .m_axil_bvalid  (m_axil_bvalid),
        .m_axil_bready  (m_axil_bready)
    );

endmodule : axi4_to_axil5_wr
