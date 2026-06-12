// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// Module: bridge_1x2_rd_regblock_mon_smoke
// Purpose: Smoke-test wrapper for bridge_1x2_rd_regblock_mon -- the
//          regblock-cfg variant of bridge_1x2_rd_mon.
//
// This wrapper is the closest thing to the stream_char_axil harness's
// posture that still fits inside components/bridge: a single AXI4 read
// master, two AXI4 slaves, monbus-axil-group internal, every cfg field
// driven from the PeakRDL regblock instead of tied-off pins.
//
// Tie-offs:
//   - s_cfg_axil_*          held idle (no host writes) -- regblock
//                           holds reset defaults; per the .rdl reset
//                           values that means monitor_enable=1 and
//                           error_enable=1 on every adapter, with all
//                           masks=0 and timeout/perf/compl/threshold/
//                           debug enables=0
//   - s_mon_axil_*          held idle (no err-fifo drain)
//   - m_mon_axil_*          always-ready slave with one-cycle bvalid
//                           after each W beat; wires probeable from
//                           cocotb so a capture test can decode packets
//   - mon_irq_out           exposed as internal logic for cocotb probe

`timescale 1ns / 1ps

module bridge_1x2_rd_regblock_mon_smoke (
    input  logic aclk,
    input  logic aresetn,

    // Master: cpu_rd (rd channel)
    input  logic [3:0]  cpu_rd_axi_arid,
    input  logic [31:0] cpu_rd_axi_araddr,
    input  logic [7:0]  cpu_rd_axi_arlen,
    input  logic [2:0]  cpu_rd_axi_arsize,
    input  logic [1:0]  cpu_rd_axi_arburst,
    input  logic        cpu_rd_axi_arlock,
    input  logic [3:0]  cpu_rd_axi_arcache,
    input  logic [2:0]  cpu_rd_axi_arprot,
    input  logic [3:0]  cpu_rd_axi_arqos,
    input  logic [3:0]  cpu_rd_axi_arregion,
    input  logic        cpu_rd_axi_aruser,
    input  logic        cpu_rd_axi_arvalid,
    output logic        cpu_rd_axi_arready,

    output logic [3:0]  cpu_rd_axi_rid,
    output logic [31:0] cpu_rd_axi_rdata,
    output logic [1:0]  cpu_rd_axi_rresp,
    output logic        cpu_rd_axi_rlast,
    output logic        cpu_rd_axi_ruser,
    output logic        cpu_rd_axi_rvalid,
    input  logic        cpu_rd_axi_rready,

    // Slave: ddr_rd
    output logic [3:0]  ddr_rd_axi_arid,
    output logic [31:0] ddr_rd_axi_araddr,
    output logic [7:0]  ddr_rd_axi_arlen,
    output logic [2:0]  ddr_rd_axi_arsize,
    output logic [1:0]  ddr_rd_axi_arburst,
    output logic        ddr_rd_axi_arlock,
    output logic [3:0]  ddr_rd_axi_arcache,
    output logic [2:0]  ddr_rd_axi_arprot,
    output logic [3:0]  ddr_rd_axi_arqos,
    output logic [3:0]  ddr_rd_axi_arregion,
    output logic        ddr_rd_axi_aruser,
    output logic        ddr_rd_axi_arvalid,
    input  logic        ddr_rd_axi_arready,

    input  logic [3:0]  ddr_rd_axi_rid,
    input  logic [31:0] ddr_rd_axi_rdata,
    input  logic [1:0]  ddr_rd_axi_rresp,
    input  logic        ddr_rd_axi_rlast,
    input  logic        ddr_rd_axi_ruser,
    input  logic        ddr_rd_axi_rvalid,
    output logic        ddr_rd_axi_rready,

    // Slave: sram_rd
    output logic [3:0]  sram_rd_axi_arid,
    output logic [31:0] sram_rd_axi_araddr,
    output logic [7:0]  sram_rd_axi_arlen,
    output logic [2:0]  sram_rd_axi_arsize,
    output logic [1:0]  sram_rd_axi_arburst,
    output logic        sram_rd_axi_arlock,
    output logic [3:0]  sram_rd_axi_arcache,
    output logic [2:0]  sram_rd_axi_arprot,
    output logic [3:0]  sram_rd_axi_arqos,
    output logic [3:0]  sram_rd_axi_arregion,
    output logic        sram_rd_axi_aruser,
    output logic        sram_rd_axi_arvalid,
    input  logic        sram_rd_axi_arready,

    input  logic [3:0]  sram_rd_axi_rid,
    input  logic [31:0] sram_rd_axi_rdata,
    input  logic [1:0]  sram_rd_axi_rresp,
    input  logic        sram_rd_axi_rlast,
    input  logic        sram_rd_axi_ruser,
    input  logic        sram_rd_axi_rvalid,
    output logic        sram_rd_axi_rready
);

    // ----------------------------------------------------------------
    // Cfg AXIL slave -- held idle (no writes/reads).  When the host
    // never touches it, the PeakRDL regblock holds its reset defaults
    // and the bridge top fans those reset defaults out to every
    // monitor.
    // ----------------------------------------------------------------
    logic        s_cfg_axil_awvalid;
    logic [31:0] s_cfg_axil_awaddr;
    logic [2:0]  s_cfg_axil_awprot;
    logic        s_cfg_axil_wvalid;
    logic [31:0] s_cfg_axil_wdata;
    logic [3:0]  s_cfg_axil_wstrb;
    logic        s_cfg_axil_bready;
    logic        s_cfg_axil_arvalid;
    logic [31:0] s_cfg_axil_araddr;
    logic [2:0]  s_cfg_axil_arprot;
    logic        s_cfg_axil_rready;
    logic        s_cfg_axil_awready;
    logic        s_cfg_axil_wready;
    logic        s_cfg_axil_bvalid;
    logic [1:0]  s_cfg_axil_bresp;
    logic        s_cfg_axil_arready;
    logic        s_cfg_axil_rvalid;
    logic [31:0] s_cfg_axil_rdata;
    logic [1:0]  s_cfg_axil_rresp;

    initial begin
        s_cfg_axil_awvalid = 1'b0;
        s_cfg_axil_awaddr  = '0;
        s_cfg_axil_awprot  = '0;
        s_cfg_axil_wvalid  = 1'b0;
        s_cfg_axil_wdata   = '0;
        s_cfg_axil_wstrb   = '0;
        s_cfg_axil_bready  = 1'b0;
        s_cfg_axil_arvalid = 1'b0;
        s_cfg_axil_araddr  = '0;
        s_cfg_axil_arprot  = '0;
        s_cfg_axil_rready  = 1'b0;
    end

    // ----------------------------------------------------------------
    // s_mon_axil_* (slave AXIL read into the err FIFO drain path).
    // Held idle for the smoke test -- the regblock_capture test can
    // override these to issue drain reads later.
    // ----------------------------------------------------------------
    logic        s_mon_axil_arvalid;
    logic [31:0] s_mon_axil_araddr;
    logic [2:0]  s_mon_axil_arprot;
    logic        s_mon_axil_rready;
    logic        s_mon_axil_arready;
    logic        s_mon_axil_rvalid;
    logic [63:0] s_mon_axil_rdata;
    logic [1:0]  s_mon_axil_rresp;

    initial begin
        s_mon_axil_arvalid = 1'b0;
        s_mon_axil_araddr  = '0;
        s_mon_axil_arprot  = '0;
        s_mon_axil_rready  = 1'b0;
    end

    // ----------------------------------------------------------------
    // m_mon_axil_* -- always-ready slave with one-cycle bvalid after
    // each W beat.  Probeable from cocotb so a capture test can snoop
    // the packet stream draining out of monbus_axil_group.
    // ----------------------------------------------------------------
    logic        m_mon_axil_awvalid;
    logic [31:0] m_mon_axil_awaddr;
    logic [2:0]  m_mon_axil_awprot;
    logic        m_mon_axil_wvalid;
    logic [63:0] m_mon_axil_wdata;
    logic [7:0]  m_mon_axil_wstrb;
    logic        m_mon_axil_bready;
    logic        m_mon_axil_bvalid_q;

    always_ff @(posedge aclk or negedge aresetn) begin
        if (!aresetn) begin
            m_mon_axil_bvalid_q <= 1'b0;
        end else begin
            if (m_mon_axil_wvalid)      m_mon_axil_bvalid_q <= 1'b1;
            else if (m_mon_axil_bready) m_mon_axil_bvalid_q <= 1'b0;
        end
    end

    logic mon_irq_out;

    bridge_1x2_rd_regblock_mon u_dut (
        .aclk    (aclk),
        .aresetn (aresetn),

        // Master: cpu_rd
        .cpu_rd_axi_arid     (cpu_rd_axi_arid),
        .cpu_rd_axi_araddr   (cpu_rd_axi_araddr),
        .cpu_rd_axi_arlen    (cpu_rd_axi_arlen),
        .cpu_rd_axi_arsize   (cpu_rd_axi_arsize),
        .cpu_rd_axi_arburst  (cpu_rd_axi_arburst),
        .cpu_rd_axi_arlock   (cpu_rd_axi_arlock),
        .cpu_rd_axi_arcache  (cpu_rd_axi_arcache),
        .cpu_rd_axi_arprot   (cpu_rd_axi_arprot),
        .cpu_rd_axi_arqos    (cpu_rd_axi_arqos),
        .cpu_rd_axi_arregion (cpu_rd_axi_arregion),
        .cpu_rd_axi_aruser   (cpu_rd_axi_aruser),
        .cpu_rd_axi_arvalid  (cpu_rd_axi_arvalid),
        .cpu_rd_axi_arready  (cpu_rd_axi_arready),

        .cpu_rd_axi_rid    (cpu_rd_axi_rid),
        .cpu_rd_axi_rdata  (cpu_rd_axi_rdata),
        .cpu_rd_axi_rresp  (cpu_rd_axi_rresp),
        .cpu_rd_axi_rlast  (cpu_rd_axi_rlast),
        .cpu_rd_axi_ruser  (cpu_rd_axi_ruser),
        .cpu_rd_axi_rvalid (cpu_rd_axi_rvalid),
        .cpu_rd_axi_rready (cpu_rd_axi_rready),

        // Slave: ddr_rd
        .ddr_rd_axi_arid     (ddr_rd_axi_arid),
        .ddr_rd_axi_araddr   (ddr_rd_axi_araddr),
        .ddr_rd_axi_arlen    (ddr_rd_axi_arlen),
        .ddr_rd_axi_arsize   (ddr_rd_axi_arsize),
        .ddr_rd_axi_arburst  (ddr_rd_axi_arburst),
        .ddr_rd_axi_arlock   (ddr_rd_axi_arlock),
        .ddr_rd_axi_arcache  (ddr_rd_axi_arcache),
        .ddr_rd_axi_arprot   (ddr_rd_axi_arprot),
        .ddr_rd_axi_arqos    (ddr_rd_axi_arqos),
        .ddr_rd_axi_arregion (ddr_rd_axi_arregion),
        .ddr_rd_axi_aruser   (ddr_rd_axi_aruser),
        .ddr_rd_axi_arvalid  (ddr_rd_axi_arvalid),
        .ddr_rd_axi_arready  (ddr_rd_axi_arready),

        .ddr_rd_axi_rid    (ddr_rd_axi_rid),
        .ddr_rd_axi_rdata  (ddr_rd_axi_rdata),
        .ddr_rd_axi_rresp  (ddr_rd_axi_rresp),
        .ddr_rd_axi_rlast  (ddr_rd_axi_rlast),
        .ddr_rd_axi_ruser  (ddr_rd_axi_ruser),
        .ddr_rd_axi_rvalid (ddr_rd_axi_rvalid),
        .ddr_rd_axi_rready (ddr_rd_axi_rready),

        // Slave: sram_rd
        .sram_rd_axi_arid     (sram_rd_axi_arid),
        .sram_rd_axi_araddr   (sram_rd_axi_araddr),
        .sram_rd_axi_arlen    (sram_rd_axi_arlen),
        .sram_rd_axi_arsize   (sram_rd_axi_arsize),
        .sram_rd_axi_arburst  (sram_rd_axi_arburst),
        .sram_rd_axi_arlock   (sram_rd_axi_arlock),
        .sram_rd_axi_arcache  (sram_rd_axi_arcache),
        .sram_rd_axi_arprot   (sram_rd_axi_arprot),
        .sram_rd_axi_arqos    (sram_rd_axi_arqos),
        .sram_rd_axi_arregion (sram_rd_axi_arregion),
        .sram_rd_axi_aruser   (sram_rd_axi_aruser),
        .sram_rd_axi_arvalid  (sram_rd_axi_arvalid),
        .sram_rd_axi_arready  (sram_rd_axi_arready),

        .sram_rd_axi_rid    (sram_rd_axi_rid),
        .sram_rd_axi_rdata  (sram_rd_axi_rdata),
        .sram_rd_axi_rresp  (sram_rd_axi_rresp),
        .sram_rd_axi_rlast  (sram_rd_axi_rlast),
        .sram_rd_axi_ruser  (sram_rd_axi_ruser),
        .sram_rd_axi_rvalid (sram_rd_axi_rvalid),
        .sram_rd_axi_rready (sram_rd_axi_rready),

        // Cfg regblock AXIL slave (idle)
        .s_cfg_axil_awvalid (s_cfg_axil_awvalid),
        .s_cfg_axil_awready (s_cfg_axil_awready),
        .s_cfg_axil_awaddr  (s_cfg_axil_awaddr),
        .s_cfg_axil_awprot  (s_cfg_axil_awprot),
        .s_cfg_axil_wvalid  (s_cfg_axil_wvalid),
        .s_cfg_axil_wready  (s_cfg_axil_wready),
        .s_cfg_axil_wdata   (s_cfg_axil_wdata),
        .s_cfg_axil_wstrb   (s_cfg_axil_wstrb),
        .s_cfg_axil_bvalid  (s_cfg_axil_bvalid),
        .s_cfg_axil_bready  (s_cfg_axil_bready),
        .s_cfg_axil_bresp   (s_cfg_axil_bresp),
        .s_cfg_axil_arvalid (s_cfg_axil_arvalid),
        .s_cfg_axil_arready (s_cfg_axil_arready),
        .s_cfg_axil_araddr  (s_cfg_axil_araddr),
        .s_cfg_axil_arprot  (s_cfg_axil_arprot),
        .s_cfg_axil_rvalid  (s_cfg_axil_rvalid),
        .s_cfg_axil_rready  (s_cfg_axil_rready),
        .s_cfg_axil_rdata   (s_cfg_axil_rdata),
        .s_cfg_axil_rresp   (s_cfg_axil_rresp),

        // monbus_axil_group AXIL slave (idle)
        .s_mon_axil_arvalid (s_mon_axil_arvalid),
        .s_mon_axil_arready (s_mon_axil_arready),
        .s_mon_axil_araddr  (s_mon_axil_araddr),
        .s_mon_axil_arprot  (s_mon_axil_arprot),
        .s_mon_axil_rvalid  (s_mon_axil_rvalid),
        .s_mon_axil_rready  (s_mon_axil_rready),
        .s_mon_axil_rdata   (s_mon_axil_rdata),
        .s_mon_axil_rresp   (s_mon_axil_rresp),

        // monbus_axil_group AXIL master (always-ready slave)
        .m_mon_axil_awvalid (m_mon_axil_awvalid),
        .m_mon_axil_awready (1'b1),
        .m_mon_axil_awaddr  (m_mon_axil_awaddr),
        .m_mon_axil_awprot  (m_mon_axil_awprot),
        .m_mon_axil_wvalid  (m_mon_axil_wvalid),
        .m_mon_axil_wready  (1'b1),
        .m_mon_axil_wdata   (m_mon_axil_wdata),
        .m_mon_axil_wstrb   (m_mon_axil_wstrb),
        .m_mon_axil_bvalid  (m_mon_axil_bvalid_q),
        .m_mon_axil_bready  (m_mon_axil_bready),
        .m_mon_axil_bresp   (2'b00),

        .mon_irq_out (mon_irq_out)
    );

endmodule : bridge_1x2_rd_regblock_mon_smoke
