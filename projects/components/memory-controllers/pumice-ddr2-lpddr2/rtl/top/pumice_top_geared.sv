// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: pumice_top_geared
// Purpose: pumice_top with a free host AXI data width. The controller core is
//          fixed at its natural width DW = DRAM_BEAT_WIDTH * DFI_RATE (one AXI
//          beat == one DFI word == DFI_RATE DRAM beats). This wrapper places the
//          repo's FORMALLY-VERIFIED AXI data-width converters
//          (axi4_dwidth_converter_wr / _rd, formal/converters/) between a
//          host-width AXI slave and the DW-width controller — so a host SoC can
//          use a convenient fixed AXI width (32/64/128/256/512) regardless of
//          the attached DRAM's (DRAM_BEAT_WIDTH, DFI_RATE) point.
//
//          This is the family-wide gearing path (DDR2/3/4/LPDDR2), NOT specific
//          to any device. It reuses proven+formal IP rather than re-verifying a
//          bespoke gearbox inside the freshly-stabilized controller datapath.
//
//          GEAR-1 (HOST_AXI_DATA_WIDTH == DW): the converters are BYPASSED via a
//          generate — the host AXI connects directly to the core, so existing
//          builds are bit-identical (no converter, no added latency).
//
//          Burst geometry: the core still requires one AXI burst == one DRAM
//          burst at its DW side ((awlen+1)*DFI_RATE == BL). The host issues
//          bursts at HOST width; the converter translates them to DW-width
//          bursts of that geometry (host burst sizing is the host's contract,
//          same spirit as the core's ragged-burst check).
//
// =====================================================================
// *** HARD WIDTH CONSTRAINT (COMPILE-ENFORCED) — READ BEFORE SETTING DWs ***
// =====================================================================
//   HOST_AXI_DATA_WIDTH and the DFI word DW ( = DRAM_BEAT_WIDTH * DFI_RATE )
//   MUST relate by an EXACT POWER-OF-TWO RATIO. i.e. AXI:DFI is G:1 or 1:G,
//   with G a power of two {1,2,4,8,...}. This is asserted below (initial
//   assert -> $fatal) and FAILS ELABORATION/SYNTHESIS if violated — a bad
//   width pairing is a compile error, never a silent broken hybrid.
//
//   WHY (and it is exactly what LiteDRAM does): the DFI word is the atomic
//   memory-side transfer, so one AXI beat must be a WHOLE power-of-two number
//   of DFI words (or vice versa). Any other ratio yields partial words /
//   fractional CHUNK_BEATS / ragged bursts. LiteDRAM enforces the identical
//   rule: its AXI frontend is 1:1 with its native port (frontend/axi.py:
//   `assert axi.data_width == port.data_width`) and ALL width change goes
//   through a dedicated stride converter that requires exact divisibility +
//   log2_int(ratio) (frontend/adapter.py LiteDRAMNativePortUp/DownConverter).
//   We mirror that: the core is fixed 1:1 at DW; THIS wrapper is the only
//   place width changes, via the formal power-of-2 converters.
//
//   Everything else that FRAMES the data (active gear phases, burst length)
//   is a runtime CONFIG register (build-for-max) — only these two DWs are
//   compile-time parameters. See HAS ch03/ch04, MAS AXI-DRAM gearing.
//
// Documentation: docs/AXI_DRAM_GEARING_SCOPE.md ; HAS ch03_architecture,
//   ch04_interfaces ; MAS (AXI<->DFI width gearing).
`timescale 1ns / 1ps

module pumice_top_geared
    import pumice_pkg::*;
#(
    // ---- host AXI data width (free) ----
    parameter int HOST_AXI_DATA_WIDTH = 128,

    // ---- core geometry (mirror pumice_top) ----
    parameter int AXI_ID_WIDTH    = 8,
    parameter int AXI_ADDR_WIDTH  = 32,
    parameter int NUM_RANKS       = 1,
    parameter int NUM_BANKS       = 8,
    parameter int ROW_WIDTH       = 14,
    parameter int COL_WIDTH       = 10,
    parameter int DFI_RATE        = 2,
    parameter int DRAM_BEAT_WIDTH = 64,
    parameter int DRAM_DEVICE_WIDTH = DRAM_BEAT_WIDTH,  // physical device word (x16 => 16)
    parameter int BL              = 8,
    parameter int NUM_ENTRIES     = 8,
    parameter int N_SRAM_SLOTS    = 8,

    // ---- derived ----
    parameter int DW   = DRAM_BEAT_WIDTH * DFI_RATE,  // controller (core) width
    parameter int CSW  = DW / 8,                      // core strobe width
    parameter int HSW  = HOST_AXI_DATA_WIDTH / 8,     // host strobe width
    parameter int IW   = AXI_ID_WIDTH,
    parameter int AW   = AXI_ADDR_WIDTH,
    parameter int DFI_DATA_WIDTH = DW,
    parameter int DFI_STRB_WIDTH = DW / 8,
    parameter int DFI_EN_WIDTH   = DFI_RATE,
    parameter int DFI_VALID_WIDTH = DFI_RATE,
    parameter int DFI_ADDR_BUS_W = ROW_WIDTH * DFI_RATE,
    parameter int DFI_BANK_BUS_W = $clog2(NUM_BANKS) * DFI_RATE,
    parameter int DFI_CTRL_BUS_W = 1 * DFI_RATE,
    parameter int DFI_CS_BUS_W   = NUM_RANKS * DFI_RATE,
    parameter int CSR_ADDR_W     = 12
) (
    input  logic aclk, aresetn, dfi_clk, dfi_rstn,

    // ---- register cpuif (PeakRDL passthrough — straight through) ----
    input  logic                    s_cpuif_req,
    input  logic                    s_cpuif_req_is_wr,
    input  logic [CSR_ADDR_W-1:0]   s_cpuif_addr,
    input  logic [31:0]             s_cpuif_wr_data,
    input  logic [31:0]             s_cpuif_wr_biten,
    output logic                    s_cpuif_req_stall_wr,
    output logic                    s_cpuif_req_stall_rd,
    output logic                    s_cpuif_rd_ack,
    output logic                    s_cpuif_rd_err,
    output logic [31:0]             s_cpuif_rd_data,
    output logic                    s_cpuif_wr_ack,
    output logic                    s_cpuif_wr_err,

    output logic                    init_done_o,

    // ---- host AXI4 (HOST_AXI_DATA_WIDTH) ----
    input  logic [IW-1:0]  s_axi_awid,   input logic [AW-1:0] s_axi_awaddr,
    input  logic [7:0]     s_axi_awlen,  input logic [2:0]    s_axi_awsize,
    input  logic [1:0]     s_axi_awburst,input logic          s_axi_awlock,
    input  logic [3:0]     s_axi_awcache,input logic [2:0]    s_axi_awprot,
    input  logic [3:0]     s_axi_awqos,  input logic [3:0]    s_axi_awregion,
    input  logic           s_axi_awuser, input logic          s_axi_awvalid,
    output logic           s_axi_awready,
    input  logic [HOST_AXI_DATA_WIDTH-1:0] s_axi_wdata,
    input  logic [HSW-1:0] s_axi_wstrb,
    input  logic           s_axi_wlast,  input logic          s_axi_wuser,
    input  logic           s_axi_wvalid, output logic         s_axi_wready,
    output logic [IW-1:0]  s_axi_bid,    output logic [1:0]   s_axi_bresp,
    output logic           s_axi_buser,  output logic         s_axi_bvalid,
    input  logic           s_axi_bready,
    input  logic [IW-1:0]  s_axi_arid,   input logic [AW-1:0] s_axi_araddr,
    input  logic [7:0]     s_axi_arlen,  input logic [2:0]    s_axi_arsize,
    input  logic [1:0]     s_axi_arburst,input logic          s_axi_arlock,
    input  logic [3:0]     s_axi_arcache,input logic [2:0]    s_axi_arprot,
    input  logic [3:0]     s_axi_arqos,  input logic [3:0]    s_axi_arregion,
    input  logic           s_axi_aruser, input logic          s_axi_arvalid,
    output logic           s_axi_arready,
    output logic [IW-1:0]  s_axi_rid,    output logic [HOST_AXI_DATA_WIDTH-1:0] s_axi_rdata,
    output logic [1:0]     s_axi_rresp,  output logic          s_axi_rlast,
    output logic           s_axi_ruser,  output logic          s_axi_rvalid,
    input  logic           s_axi_rready,

    // ---- DFI 2.1 pin bus (straight through) ----
    output logic [DFI_ADDR_BUS_W-1:0]  dfi_address_o,
    output logic [DFI_BANK_BUS_W-1:0]  dfi_bank_o,
    output logic [DFI_CTRL_BUS_W-1:0]  dfi_cas_n_o, dfi_ras_n_o, dfi_we_n_o,
    output logic [DFI_CS_BUS_W-1:0]    dfi_cs_n_o, dfi_odt_o,
    output logic [DFI_DATA_WIDTH-1:0]  dfi_wrdata_o,
    output logic [DFI_EN_WIDTH-1:0]    dfi_wrdata_en_o,
    output logic [DFI_STRB_WIDTH-1:0]  dfi_wrdata_mask_o,
    output logic [DFI_EN_WIDTH-1:0]    dfi_rddata_en_o,
    input  logic [DFI_DATA_WIDTH-1:0]  dfi_rddata_i,
    input  logic [DFI_VALID_WIDTH-1:0] dfi_rddata_valid_i,
    output logic                       dfi_init_start_o,
    input  logic                       dfi_init_complete_i
);

    // ===================================================================
    // HARD WIDTH CONSTRAINT (compile-enforced) — see the header block.
    // HOST_AXI_DATA_WIDTH : DFI word DW must be an EXACT POWER-OF-TWO ratio
    // (AXI:DFI = G:1 or 1:G). Anything else -> partial words / ragged bursts.
    // This $fatal fires at ELABORATION/SYNTH (proven: same idiom as
    // pumice_axi_burst_chopper's CHUNK_BEATS check errored in Vivado synth),
    // so a bad width pairing is a compile error, not a silent broken build.
    // Mirrors LiteDRAM (axi frontend 1:1 + power-of-2 stride converter).
    // ===================================================================
    localparam int W_HI  = (HOST_AXI_DATA_WIDTH >= DW) ? HOST_AXI_DATA_WIDTH : DW;
    localparam int W_LO  = (HOST_AXI_DATA_WIDTH >= DW) ? DW : HOST_AXI_DATA_WIDTH;
    localparam int W_RAT = W_HI / W_LO;
    initial begin
        assert ((W_LO >= 1) && (W_HI % W_LO == 0) && (W_RAT == (1 << $clog2(W_RAT))))
            else $fatal(1, "pumice_top_geared: HOST_AXI_DATA_WIDTH=%0d and DFI word DW=%0d must relate by a power-of-two ratio (AXI:DFI = G:1 or 1:G); got %0d:%0d. Fix the DW pairing where these params are set.",
                HOST_AXI_DATA_WIDTH, DW, W_HI, W_LO);
    end

    // ---- core-side (DW-width) AXI nets between converters and pumice_top ----
    logic [IW-1:0]  c_awid;   logic [AW-1:0] c_awaddr;
    logic [7:0]     c_awlen;  logic [2:0]    c_awsize;
    logic [1:0]     c_awburst;logic          c_awlock;
    logic [3:0]     c_awcache;logic [2:0]    c_awprot;
    logic [3:0]     c_awqos;  logic [3:0]    c_awregion;
    logic           c_awuser; logic          c_awvalid, c_awready;
    logic [DW-1:0]  c_wdata;  logic [CSW-1:0] c_wstrb;
    logic           c_wlast;  logic          c_wuser, c_wvalid, c_wready;
    logic [IW-1:0]  c_bid;    logic [1:0]    c_bresp;
    logic           c_buser;  logic          c_bvalid, c_bready;
    logic [IW-1:0]  c_arid;   logic [AW-1:0] c_araddr;
    logic [7:0]     c_arlen;  logic [2:0]    c_arsize;
    logic [1:0]     c_arburst;logic          c_arlock;
    logic [3:0]     c_arcache;logic [2:0]    c_arprot;
    logic [3:0]     c_arqos;  logic [3:0]    c_arregion;
    logic           c_aruser; logic          c_arvalid, c_arready;
    logic [IW-1:0]  c_rid;    logic [DW-1:0] c_rdata;
    logic [1:0]     c_rresp;  logic          c_rlast;
    logic           c_ruser;  logic          c_rvalid, c_rready;

    generate
    if (HOST_AXI_DATA_WIDTH == DW) begin : g_direct
        // GEAR-1: no width change — connect host straight to the core.
        assign c_awid=s_axi_awid; assign c_awaddr=s_axi_awaddr; assign c_awlen=s_axi_awlen;
        assign c_awsize=s_axi_awsize; assign c_awburst=s_axi_awburst; assign c_awlock=s_axi_awlock;
        assign c_awcache=s_axi_awcache; assign c_awprot=s_axi_awprot; assign c_awqos=s_axi_awqos;
        assign c_awregion=s_axi_awregion; assign c_awuser=s_axi_awuser; assign c_awvalid=s_axi_awvalid;
        assign s_axi_awready=c_awready;
        assign c_wdata=s_axi_wdata; assign c_wstrb=s_axi_wstrb; assign c_wlast=s_axi_wlast;
        assign c_wuser=s_axi_wuser; assign c_wvalid=s_axi_wvalid; assign s_axi_wready=c_wready;
        assign s_axi_bid=c_bid; assign s_axi_bresp=c_bresp; assign s_axi_buser=c_buser;
        assign s_axi_bvalid=c_bvalid; assign c_bready=s_axi_bready;
        assign c_arid=s_axi_arid; assign c_araddr=s_axi_araddr; assign c_arlen=s_axi_arlen;
        assign c_arsize=s_axi_arsize; assign c_arburst=s_axi_arburst; assign c_arlock=s_axi_arlock;
        assign c_arcache=s_axi_arcache; assign c_arprot=s_axi_arprot; assign c_arqos=s_axi_arqos;
        assign c_arregion=s_axi_arregion; assign c_aruser=s_axi_aruser; assign c_arvalid=s_axi_arvalid;
        assign s_axi_arready=c_arready;
        assign s_axi_rid=c_rid; assign s_axi_rdata=c_rdata; assign s_axi_rresp=c_rresp;
        assign s_axi_rlast=c_rlast; assign s_axi_ruser=c_ruser; assign s_axi_rvalid=c_rvalid;
        assign c_rready=s_axi_rready;
    end else begin : g_conv
        // Geared: formally-verified data-width converters host <-> DW.
        axi4_dwidth_converter_wr #(
            .S_AXI_DATA_WIDTH(HOST_AXI_DATA_WIDTH), .M_AXI_DATA_WIDTH(DW),
            .AXI_ID_WIDTH(IW), .AXI_ADDR_WIDTH(AW), .AXI_USER_WIDTH(1)
        ) u_wr_conv (
            .aclk(aclk), .aresetn(aresetn),
            // host slave
            .s_axi_awid(s_axi_awid), .s_axi_awaddr(s_axi_awaddr), .s_axi_awlen(s_axi_awlen),
            .s_axi_awsize(s_axi_awsize), .s_axi_awburst(s_axi_awburst), .s_axi_awlock(s_axi_awlock),
            .s_axi_awcache(s_axi_awcache), .s_axi_awprot(s_axi_awprot), .s_axi_awqos(s_axi_awqos),
            .s_axi_awregion(s_axi_awregion), .s_axi_awuser(s_axi_awuser), .s_axi_awvalid(s_axi_awvalid),
            .s_axi_awready(s_axi_awready),
            .s_axi_wdata(s_axi_wdata), .s_axi_wstrb(s_axi_wstrb), .s_axi_wlast(s_axi_wlast),
            .s_axi_wuser(s_axi_wuser), .s_axi_wvalid(s_axi_wvalid), .s_axi_wready(s_axi_wready),
            .s_axi_bid(s_axi_bid), .s_axi_bresp(s_axi_bresp), .s_axi_buser(s_axi_buser),
            .s_axi_bvalid(s_axi_bvalid), .s_axi_bready(s_axi_bready),
            // core master
            .m_axi_awid(c_awid), .m_axi_awaddr(c_awaddr), .m_axi_awlen(c_awlen),
            .m_axi_awsize(c_awsize), .m_axi_awburst(c_awburst), .m_axi_awlock(c_awlock),
            .m_axi_awcache(c_awcache), .m_axi_awprot(c_awprot), .m_axi_awqos(c_awqos),
            .m_axi_awregion(c_awregion), .m_axi_awuser(c_awuser), .m_axi_awvalid(c_awvalid),
            .m_axi_awready(c_awready),
            .m_axi_wdata(c_wdata), .m_axi_wstrb(c_wstrb), .m_axi_wlast(c_wlast),
            .m_axi_wuser(c_wuser), .m_axi_wvalid(c_wvalid), .m_axi_wready(c_wready),
            .m_axi_bid(c_bid), .m_axi_bresp(c_bresp), .m_axi_buser(c_buser),
            .m_axi_bvalid(c_bvalid), .m_axi_bready(c_bready)
        );

        axi4_dwidth_converter_rd #(
            .S_AXI_DATA_WIDTH(HOST_AXI_DATA_WIDTH), .M_AXI_DATA_WIDTH(DW),
            .AXI_ID_WIDTH(IW), .AXI_ADDR_WIDTH(AW), .AXI_USER_WIDTH(1)
        ) u_rd_conv (
            .aclk(aclk), .aresetn(aresetn),
            // host slave
            .s_axi_arid(s_axi_arid), .s_axi_araddr(s_axi_araddr), .s_axi_arlen(s_axi_arlen),
            .s_axi_arsize(s_axi_arsize), .s_axi_arburst(s_axi_arburst), .s_axi_arlock(s_axi_arlock),
            .s_axi_arcache(s_axi_arcache), .s_axi_arprot(s_axi_arprot), .s_axi_arqos(s_axi_arqos),
            .s_axi_arregion(s_axi_arregion), .s_axi_aruser(s_axi_aruser), .s_axi_arvalid(s_axi_arvalid),
            .s_axi_arready(s_axi_arready),
            .s_axi_rid(s_axi_rid), .s_axi_rdata(s_axi_rdata), .s_axi_rresp(s_axi_rresp),
            .s_axi_rlast(s_axi_rlast), .s_axi_ruser(s_axi_ruser), .s_axi_rvalid(s_axi_rvalid),
            .s_axi_rready(s_axi_rready),
            // core master
            .m_axi_arid(c_arid), .m_axi_araddr(c_araddr), .m_axi_arlen(c_arlen),
            .m_axi_arsize(c_arsize), .m_axi_arburst(c_arburst), .m_axi_arlock(c_arlock),
            .m_axi_arcache(c_arcache), .m_axi_arprot(c_arprot), .m_axi_arqos(c_arqos),
            .m_axi_arregion(c_arregion), .m_axi_aruser(c_aruser), .m_axi_arvalid(c_arvalid),
            .m_axi_arready(c_arready),
            .m_axi_rid(c_rid), .m_axi_rdata(c_rdata), .m_axi_rresp(c_rresp),
            .m_axi_rlast(c_rlast), .m_axi_ruser(c_ruser), .m_axi_rvalid(c_rvalid),
            .m_axi_rready(c_rready)
        );
    end
    endgenerate

    // ---- controller core (fixed DW width) ----
    pumice_top #(
        .AXI_ID_WIDTH(IW), .AXI_ADDR_WIDTH(AW), .NUM_RANKS(NUM_RANKS),
        .NUM_BANKS(NUM_BANKS), .ROW_WIDTH(ROW_WIDTH), .COL_WIDTH(COL_WIDTH),
        .DFI_RATE(DFI_RATE), .DRAM_BEAT_WIDTH(DRAM_BEAT_WIDTH),
        .DRAM_DEVICE_WIDTH(DRAM_DEVICE_WIDTH), .BL(BL),
        .NUM_ENTRIES(NUM_ENTRIES), .N_SRAM_SLOTS(N_SRAM_SLOTS)
    ) u_core (
        .aclk(aclk), .aresetn(aresetn), .dfi_clk(dfi_clk), .dfi_rstn(dfi_rstn),
        .s_cpuif_req(s_cpuif_req), .s_cpuif_req_is_wr(s_cpuif_req_is_wr),
        .s_cpuif_addr(s_cpuif_addr), .s_cpuif_wr_data(s_cpuif_wr_data),
        .s_cpuif_wr_biten(s_cpuif_wr_biten),
        .s_cpuif_req_stall_wr(s_cpuif_req_stall_wr), .s_cpuif_req_stall_rd(s_cpuif_req_stall_rd),
        .s_cpuif_rd_ack(s_cpuif_rd_ack), .s_cpuif_rd_err(s_cpuif_rd_err),
        .s_cpuif_rd_data(s_cpuif_rd_data), .s_cpuif_wr_ack(s_cpuif_wr_ack),
        .s_cpuif_wr_err(s_cpuif_wr_err), .init_done_o(init_done_o),
        // AXI (DW) from the converter/direct path
        .s_axi_awid(c_awid), .s_axi_awaddr(c_awaddr), .s_axi_awlen(c_awlen),
        .s_axi_awsize(c_awsize), .s_axi_awburst(c_awburst), .s_axi_awlock(c_awlock),
        .s_axi_awcache(c_awcache), .s_axi_awprot(c_awprot), .s_axi_awqos(c_awqos),
        .s_axi_awregion(c_awregion), .s_axi_awuser(c_awuser), .s_axi_awvalid(c_awvalid),
        .s_axi_awready(c_awready),
        .s_axi_wdata(c_wdata), .s_axi_wstrb(c_wstrb), .s_axi_wlast(c_wlast),
        .s_axi_wuser(c_wuser), .s_axi_wvalid(c_wvalid), .s_axi_wready(c_wready),
        .s_axi_bid(c_bid), .s_axi_bresp(c_bresp), .s_axi_buser(c_buser),
        .s_axi_bvalid(c_bvalid), .s_axi_bready(c_bready),
        .s_axi_arid(c_arid), .s_axi_araddr(c_araddr), .s_axi_arlen(c_arlen),
        .s_axi_arsize(c_arsize), .s_axi_arburst(c_arburst), .s_axi_arlock(c_arlock),
        .s_axi_arcache(c_arcache), .s_axi_arprot(c_arprot), .s_axi_arqos(c_arqos),
        .s_axi_arregion(c_arregion), .s_axi_aruser(c_aruser), .s_axi_arvalid(c_arvalid),
        .s_axi_arready(c_arready),
        .s_axi_rid(c_rid), .s_axi_rdata(c_rdata), .s_axi_rresp(c_rresp),
        .s_axi_rlast(c_rlast), .s_axi_ruser(c_ruser), .s_axi_rvalid(c_rvalid),
        .s_axi_rready(c_rready),
        // DFI
        .dfi_address_o(dfi_address_o), .dfi_bank_o(dfi_bank_o),
        .dfi_cas_n_o(dfi_cas_n_o), .dfi_ras_n_o(dfi_ras_n_o), .dfi_we_n_o(dfi_we_n_o),
        .dfi_cs_n_o(dfi_cs_n_o), .dfi_odt_o(dfi_odt_o),
        .dfi_wrdata_o(dfi_wrdata_o), .dfi_wrdata_en_o(dfi_wrdata_en_o),
        .dfi_wrdata_mask_o(dfi_wrdata_mask_o), .dfi_rddata_en_o(dfi_rddata_en_o),
        .dfi_rddata_i(dfi_rddata_i), .dfi_rddata_valid_i(dfi_rddata_valid_i),
        .dfi_init_start_o(dfi_init_start_o), .dfi_init_complete_i(dfi_init_complete_i)
    );

endmodule : pumice_top_geared
