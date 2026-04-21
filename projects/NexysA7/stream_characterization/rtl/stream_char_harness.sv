// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2025 sean galloway
//
// Module: stream_char_harness
// Purpose: Internal integration for the STREAM characterization harness.
//
// Instantiates:
//   - uart_axil_bridge                (host interface)
//   - axil_decode_5s                  (1->5 AXIL decoder)
//   - axil2apb                        (drives STREAM APB config)
//   - harness_csr                     (control/status)
//   - desc_ram                        (descriptor storage)
//   - debug_sram                      (MonBus trace capture)
//   - axi4_slave_rd_pattern_gen       (DMA source)
//   - axi4_slave_wr_crc_check         (DMA sink)
//   - stream_top_ch8                  (DUT: STREAM DMA)
//
// The top level (stream_char_top.sv) wraps this with FPGA pin-level I/O.

`timescale 1ns / 1ps

`include "reset_defs.svh"

module stream_char_harness #(
    parameter int FPGA_CLK_HZ  = 100_000_000,
    parameter int UART_BAUD    = 115_200,
    parameter int DATA_WIDTH   = 128,
    parameter int ADDR_WIDTH   = 32,
    parameter int SRAM_DEPTH   = 256
) (
    input  logic            aclk,
    input  logic            aresetn,

    // UART
    input  logic            i_uart_rx,
    output logic            o_uart_tx,

    // Top-level status (to LEDs)
    output logic            o_stream_irq,
    output logic            o_any_error,
    output logic            o_trace_overflow,
    output logic [3:0]      o_heartbeat
);

    localparam int AXI_ID_WIDTH   = 8;
    localparam int AXI_USER_WIDTH = 3;     // $clog2(NUM_CHANNELS=8)
    localparam int APB_ADDR_WIDTH = 12;
    localparam int APB_DATA_WIDTH = 32;

    localparam int CLKS_PER_BIT = FPGA_CLK_HZ / UART_BAUD;

    // =========================================================================
    // UART-AXIL bridge
    // =========================================================================
    logic [31:0] uart_awaddr;
    logic [2:0]  uart_awprot;
    logic        uart_awvalid, uart_awready;
    logic [31:0] uart_wdata;
    logic [3:0]  uart_wstrb;
    logic        uart_wvalid, uart_wready;
    logic [1:0]  uart_bresp;
    logic        uart_bvalid, uart_bready;
    logic [31:0] uart_araddr;
    logic [2:0]  uart_arprot;
    logic        uart_arvalid, uart_arready;
    logic [31:0] uart_rdata;
    logic [1:0]  uart_rresp;
    logic        uart_rvalid, uart_rready;

    uart_axil_bridge #(
        .AXIL_ADDR_WIDTH (32),
        .AXIL_DATA_WIDTH (32),
        .CLKS_PER_BIT    (CLKS_PER_BIT)
    ) u_uart (
        .aclk     (aclk),
        .aresetn  (aresetn),
        .i_uart_rx(i_uart_rx),
        .o_uart_tx(o_uart_tx),

        .m_axil_awaddr (uart_awaddr),
        .m_axil_awprot (uart_awprot),
        .m_axil_awvalid(uart_awvalid),
        .m_axil_awready(uart_awready),
        .m_axil_wdata  (uart_wdata),
        .m_axil_wstrb  (uart_wstrb),
        .m_axil_wvalid (uart_wvalid),
        .m_axil_wready (uart_wready),
        .m_axil_bresp  (uart_bresp),
        .m_axil_bvalid (uart_bvalid),
        .m_axil_bready (uart_bready),
        .m_axil_araddr (uart_araddr),
        .m_axil_arprot (uart_arprot),
        .m_axil_arvalid(uart_arvalid),
        .m_axil_arready(uart_arready),
        .m_axil_rdata  (uart_rdata),
        .m_axil_rresp  (uart_rresp),
        .m_axil_rvalid (uart_rvalid),
        .m_axil_rready (uart_rready)
    );

    // =========================================================================
    // 1 -> 5 AXIL decoder
    //
    // S0 = STREAM APB  (via axil2apb)  0x0000_0000
    // S1 = harness_csr                 0x0001_0000
    // S2 = desc_ram                    0x0002_0000
    // S3 = STREAM err FIFO             0x0003_0000
    // S4 = debug_sram (read)           0x0004_0000
    // =========================================================================
    // S0 master wires (→ axil2apb)
    logic [31:0] s0_awaddr, s0_wdata, s0_araddr, s0_rdata;
    logic [3:0]  s0_wstrb;
    logic [2:0]  s0_awprot, s0_arprot;
    logic [1:0]  s0_bresp, s0_rresp;
    logic s0_awvalid, s0_awready, s0_wvalid, s0_wready, s0_bvalid, s0_bready;
    logic s0_arvalid, s0_arready, s0_rvalid, s0_rready;

    // S1 master wires (→ harness_csr)
    logic [31:0] s1_awaddr, s1_wdata, s1_araddr, s1_rdata;
    logic [3:0]  s1_wstrb;
    logic [2:0]  s1_awprot, s1_arprot;
    logic [1:0]  s1_bresp, s1_rresp;
    logic s1_awvalid, s1_awready, s1_wvalid, s1_wready, s1_bvalid, s1_bready;
    logic s1_arvalid, s1_arready, s1_rvalid, s1_rready;

    // S2 master wires (→ desc_ram)
    logic [31:0] s2_awaddr, s2_wdata, s2_araddr, s2_rdata;
    logic [3:0]  s2_wstrb;
    logic [2:0]  s2_awprot, s2_arprot;
    logic [1:0]  s2_bresp, s2_rresp;
    logic s2_awvalid, s2_awready, s2_wvalid, s2_wready, s2_bvalid, s2_bready;
    logic s2_arvalid, s2_arready, s2_rvalid, s2_rready;

    // S3 master wires (→ STREAM err FIFO AXIL slave, read-only)
    logic [31:0] s3_awaddr, s3_wdata, s3_araddr, s3_rdata;
    logic [3:0]  s3_wstrb;
    logic [2:0]  s3_awprot, s3_arprot;
    logic [1:0]  s3_bresp, s3_rresp;
    logic s3_awvalid, s3_awready, s3_wvalid, s3_wready, s3_bvalid, s3_bready;
    logic s3_arvalid, s3_arready, s3_rvalid, s3_rready;

    // S4 master wires (→ debug_sram host-read port)
    logic [31:0] s4_awaddr, s4_wdata, s4_araddr, s4_rdata;
    logic [3:0]  s4_wstrb;
    logic [2:0]  s4_awprot, s4_arprot;
    logic [1:0]  s4_bresp, s4_rresp;
    logic s4_awvalid, s4_awready, s4_wvalid, s4_wready, s4_bvalid, s4_bready;
    logic s4_arvalid, s4_arready, s4_rvalid, s4_rready;

    axil_decode_5s #(
        .AW      (32),
        .DW      (32),
        .S0_BASE (32'h0000_0000), .S0_SIZE (32'h0000_1000),
        .S1_BASE (32'h0001_0000), .S1_SIZE (32'h0000_0100),
        .S2_BASE (32'h0002_0000), .S2_SIZE (32'h0001_0000),
        .S3_BASE (32'h0003_0000), .S3_SIZE (32'h0000_0040),
        .S4_BASE (32'h0004_0000), .S4_SIZE (32'h0004_0000)
    ) u_decode (
        .aclk(aclk), .aresetn(aresetn),
        .s_awaddr(uart_awaddr), .s_awprot(uart_awprot),
        .s_awvalid(uart_awvalid), .s_awready(uart_awready),
        .s_wdata(uart_wdata), .s_wstrb(uart_wstrb),
        .s_wvalid(uart_wvalid), .s_wready(uart_wready),
        .s_bresp(uart_bresp), .s_bvalid(uart_bvalid), .s_bready(uart_bready),
        .s_araddr(uart_araddr), .s_arprot(uart_arprot),
        .s_arvalid(uart_arvalid), .s_arready(uart_arready),
        .s_rdata(uart_rdata), .s_rresp(uart_rresp),
        .s_rvalid(uart_rvalid), .s_rready(uart_rready),

        .m0_awaddr(s0_awaddr), .m0_awprot(s0_awprot),
        .m0_awvalid(s0_awvalid), .m0_awready(s0_awready),
        .m0_wdata(s0_wdata), .m0_wstrb(s0_wstrb),
        .m0_wvalid(s0_wvalid), .m0_wready(s0_wready),
        .m0_bresp(s0_bresp), .m0_bvalid(s0_bvalid), .m0_bready(s0_bready),
        .m0_araddr(s0_araddr), .m0_arprot(s0_arprot),
        .m0_arvalid(s0_arvalid), .m0_arready(s0_arready),
        .m0_rdata(s0_rdata), .m0_rresp(s0_rresp),
        .m0_rvalid(s0_rvalid), .m0_rready(s0_rready),

        .m1_awaddr(s1_awaddr), .m1_awprot(s1_awprot),
        .m1_awvalid(s1_awvalid), .m1_awready(s1_awready),
        .m1_wdata(s1_wdata), .m1_wstrb(s1_wstrb),
        .m1_wvalid(s1_wvalid), .m1_wready(s1_wready),
        .m1_bresp(s1_bresp), .m1_bvalid(s1_bvalid), .m1_bready(s1_bready),
        .m1_araddr(s1_araddr), .m1_arprot(s1_arprot),
        .m1_arvalid(s1_arvalid), .m1_arready(s1_arready),
        .m1_rdata(s1_rdata), .m1_rresp(s1_rresp),
        .m1_rvalid(s1_rvalid), .m1_rready(s1_rready),

        .m2_awaddr(s2_awaddr), .m2_awprot(s2_awprot),
        .m2_awvalid(s2_awvalid), .m2_awready(s2_awready),
        .m2_wdata(s2_wdata), .m2_wstrb(s2_wstrb),
        .m2_wvalid(s2_wvalid), .m2_wready(s2_wready),
        .m2_bresp(s2_bresp), .m2_bvalid(s2_bvalid), .m2_bready(s2_bready),
        .m2_araddr(s2_araddr), .m2_arprot(s2_arprot),
        .m2_arvalid(s2_arvalid), .m2_arready(s2_arready),
        .m2_rdata(s2_rdata), .m2_rresp(s2_rresp),
        .m2_rvalid(s2_rvalid), .m2_rready(s2_rready),

        .m3_awaddr(s3_awaddr), .m3_awprot(s3_awprot),
        .m3_awvalid(s3_awvalid), .m3_awready(s3_awready),
        .m3_wdata(s3_wdata), .m3_wstrb(s3_wstrb),
        .m3_wvalid(s3_wvalid), .m3_wready(s3_wready),
        .m3_bresp(s3_bresp), .m3_bvalid(s3_bvalid), .m3_bready(s3_bready),
        .m3_araddr(s3_araddr), .m3_arprot(s3_arprot),
        .m3_arvalid(s3_arvalid), .m3_arready(s3_arready),
        .m3_rdata(s3_rdata), .m3_rresp(s3_rresp),
        .m3_rvalid(s3_rvalid), .m3_rready(s3_rready),

        .m4_awaddr(s4_awaddr), .m4_awprot(s4_awprot),
        .m4_awvalid(s4_awvalid), .m4_awready(s4_awready),
        .m4_wdata(s4_wdata), .m4_wstrb(s4_wstrb),
        .m4_wvalid(s4_wvalid), .m4_wready(s4_wready),
        .m4_bresp(s4_bresp), .m4_bvalid(s4_bvalid), .m4_bready(s4_bready),
        .m4_araddr(s4_araddr), .m4_arprot(s4_arprot),
        .m4_arvalid(s4_arvalid), .m4_arready(s4_arready),
        .m4_rdata(s4_rdata), .m4_rresp(s4_rresp),
        .m4_rvalid(s4_rvalid), .m4_rready(s4_rready)
    );

    // =========================================================================
    // S0: AXIL → APB → STREAM APB slave
    // =========================================================================
    logic [APB_ADDR_WIDTH-1:0]   apb_paddr;
    logic                        apb_psel, apb_penable, apb_pwrite;
    logic [APB_DATA_WIDTH-1:0]   apb_pwdata, apb_prdata;
    logic [(APB_DATA_WIDTH/8)-1:0] apb_pstrb;
    logic                        apb_pready, apb_pslverr;

    axil2apb #(
        .AXIL_AW(32), .AXIL_DW(32),
        .APB_AW (APB_ADDR_WIDTH), .APB_DW(APB_DATA_WIDTH)
    ) u_axil2apb (
        .aclk(aclk), .aresetn(aresetn),
        .s_axil_awaddr(s0_awaddr), .s_axil_awprot(s0_awprot),
        .s_axil_awvalid(s0_awvalid), .s_axil_awready(s0_awready),
        .s_axil_wdata(s0_wdata), .s_axil_wstrb(s0_wstrb),
        .s_axil_wvalid(s0_wvalid), .s_axil_wready(s0_wready),
        .s_axil_bresp(s0_bresp), .s_axil_bvalid(s0_bvalid), .s_axil_bready(s0_bready),
        .s_axil_araddr(s0_araddr), .s_axil_arprot(s0_arprot),
        .s_axil_arvalid(s0_arvalid), .s_axil_arready(s0_arready),
        .s_axil_rdata(s0_rdata), .s_axil_rresp(s0_rresp),
        .s_axil_rvalid(s0_rvalid), .s_axil_rready(s0_rready),
        .m_apb_paddr(apb_paddr), .m_apb_psel(apb_psel),
        .m_apb_penable(apb_penable), .m_apb_pwrite(apb_pwrite),
        .m_apb_pwdata(apb_pwdata), .m_apb_pstrb(apb_pstrb),
        .m_apb_prdata(apb_prdata), .m_apb_pready(apb_pready),
        .m_apb_pslverr(apb_pslverr)
    );

    // =========================================================================
    // S1: harness_csr
    // =========================================================================
    logic        csr_start_pulse, csr_clear_pulse, csr_freeze, csr_soft_reset;
    logic [31:0] dbg_wr_ptr;
    logic        dbg_overflow;
    logic [31:0] read_crc_value, write_crc_value;
    logic        read_crc_valid, write_crc_valid;
    logic [31:0] read_beat_count, write_beat_count;
    logic        stream_irq;

    // Simple CRC match comparison
    wire crc_match = read_crc_valid && write_crc_valid && (read_crc_value == write_crc_value);
    wire crc_both_valid = read_crc_valid && write_crc_valid;
    // any_error: sticky "something went wrong" signal routed to CSR_STATUS[1].
    // TODO: drive from a real error source. stream_top_ch8 does not yet expose
    // a scheduler/engine error wire at its boundary, so for now this stays tied
    // to 0 and callers must poll the in-band SCHED_ERROR register (stream_regs
    // @ 0x170) for error visibility. The primary completion signal for tests is
    // stream_irq from monbus_axil_group.irq_out.
    wire any_error = 1'b0;

    harness_csr #(.AW(32), .DW(32)) u_csr (
        .aclk(aclk), .aresetn(aresetn),
        .s_awaddr(s1_awaddr), .s_awprot(s1_awprot),
        .s_awvalid(s1_awvalid), .s_awready(s1_awready),
        .s_wdata(s1_wdata), .s_wstrb(s1_wstrb),
        .s_wvalid(s1_wvalid), .s_wready(s1_wready),
        .s_bresp(s1_bresp), .s_bvalid(s1_bvalid), .s_bready(s1_bready),
        .s_araddr(s1_araddr), .s_arprot(s1_arprot),
        .s_arvalid(s1_arvalid), .s_arready(s1_arready),
        .s_rdata(s1_rdata), .s_rresp(s1_rresp),
        .s_rvalid(s1_rvalid), .s_rready(s1_rready),
        .o_start_pulse      (csr_start_pulse),
        .o_clear_stats_pulse(csr_clear_pulse),
        .o_freeze_trace     (csr_freeze),
        .o_soft_reset_pulse (csr_soft_reset),
        .i_stream_irq       (stream_irq),
        .i_any_error        (any_error),
        .i_dbg_wr_ptr       (dbg_wr_ptr),
        .i_dbg_overflow     (dbg_overflow),
        .i_crc_rd_expected  (read_crc_value),
        .i_crc_wr_expected  (read_crc_value),  // expected = source CRC
        .i_crc_wr_computed  (write_crc_value),
        .i_crc_valid        (crc_both_valid),
        .i_crc_match        (crc_match)
    );

    // =========================================================================
    // S2: desc_ram  (AXIL write + AXI4 read)
    // =========================================================================
    // AXI4 read side wired to STREAM m_axi_desc
    logic [AXI_ID_WIDTH-1:0]    desc_arid;
    logic [ADDR_WIDTH-1:0]      desc_araddr;
    logic [7:0]                 desc_arlen;
    logic [2:0]                 desc_arsize;
    logic [1:0]                 desc_arburst;
    logic                       desc_arlock;
    logic [3:0]                 desc_arcache;
    logic [2:0]                 desc_arprot;
    logic [3:0]                 desc_arqos;
    logic [3:0]                 desc_arregion;
    logic [AXI_USER_WIDTH-1:0]  desc_aruser;
    logic                       desc_arvalid, desc_arready;
    logic [AXI_ID_WIDTH-1:0]    desc_rid;
    logic [255:0]               desc_rdata;
    logic [1:0]                 desc_rresp;
    logic                       desc_rlast;
    logic [AXI_USER_WIDTH-1:0]  desc_ruser;
    logic                       desc_rvalid, desc_rready;

    desc_ram #(
        .AXI_ID_WIDTH  (AXI_ID_WIDTH),
        .AXI_USER_WIDTH(AXI_USER_WIDTH),
        .AXI_ADDR_WIDTH(ADDR_WIDTH),
        .DEPTH_256     (2048)
    ) u_desc_ram (
        .aclk(aclk), .aresetn(aresetn),
        // AXIL write (from host decode S2)
        .s_axil_awaddr (s2_awaddr), .s_axil_awprot(s2_awprot),
        .s_axil_awvalid(s2_awvalid), .s_axil_awready(s2_awready),
        .s_axil_wdata  (s2_wdata), .s_axil_wstrb(s2_wstrb),
        .s_axil_wvalid (s2_wvalid), .s_axil_wready(s2_wready),
        .s_axil_bresp  (s2_bresp), .s_axil_bvalid(s2_bvalid), .s_axil_bready(s2_bready),
        .s_axil_araddr (s2_araddr), .s_axil_arprot(s2_arprot),
        .s_axil_arvalid(s2_arvalid), .s_axil_arready(s2_arready),
        .s_axil_rdata  (s2_rdata), .s_axil_rresp(s2_rresp),
        .s_axil_rvalid (s2_rvalid), .s_axil_rready(s2_rready),
        // AXI4 read (from STREAM m_axi_desc)
        .s_axi_arid   (desc_arid),   .s_axi_araddr(desc_araddr),
        .s_axi_arlen  (desc_arlen),  .s_axi_arsize(desc_arsize),
        .s_axi_arburst(desc_arburst),.s_axi_arlock(desc_arlock),
        .s_axi_arcache(desc_arcache),.s_axi_arprot(desc_arprot),
        .s_axi_arqos  (desc_arqos),  .s_axi_arregion(desc_arregion),
        .s_axi_aruser (desc_aruser), .s_axi_arvalid(desc_arvalid),
        .s_axi_arready(desc_arready),
        .s_axi_rid    (desc_rid),    .s_axi_rdata(desc_rdata),
        .s_axi_rresp  (desc_rresp),  .s_axi_rlast(desc_rlast),
        .s_axi_ruser  (desc_ruser),  .s_axi_rvalid(desc_rvalid),
        .s_axi_rready (desc_rready)
    );

    // =========================================================================
    // S3: STREAM err FIFO AXIL slave (wired to stream.s_axil_err_*)
    //
    // S3 from decoder drives the AXIL read channel of STREAM err FIFO.
    // Write channel on this slot is unused; tie off with OKAY.
    // =========================================================================
    logic        s3_err_arvalid, s3_err_arready;
    logic [31:0] s3_err_araddr;
    logic [2:0]  s3_err_arprot;
    logic        s3_err_rvalid,  s3_err_rready;
    logic [31:0] s3_err_rdata;
    logic [1:0]  s3_err_rresp;

    assign s3_err_arvalid = s3_arvalid;
    assign s3_err_araddr  = s3_araddr;
    assign s3_err_arprot  = s3_arprot;
    assign s3_arready     = s3_err_arready;

    assign s3_rvalid      = s3_err_rvalid;
    assign s3_rdata       = s3_err_rdata;
    assign s3_rresp       = s3_err_rresp;
    assign s3_err_rready  = s3_rready;

    // Write side on S3: sink with OKAY (host shouldn't write here)
    logic r_s3_bvalid;
    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_s3_bvalid <= 1'b0;
        end else begin
            if (s3_awvalid && s3_wvalid && !r_s3_bvalid) r_s3_bvalid <= 1'b1;
            else if (s3_bready && r_s3_bvalid)            r_s3_bvalid <= 1'b0;
        end
    )
    assign s3_awready = !r_s3_bvalid;
    assign s3_wready  = !r_s3_bvalid;
    assign s3_bvalid  = r_s3_bvalid;
    assign s3_bresp   = 2'b10;  // SLVERR

    // =========================================================================
    // S4: debug_sram (host read port) + STREAM m_axil_mon writes
    // =========================================================================
    // STREAM m_axil_mon AXIL master signals
    logic        mon_awvalid, mon_awready;
    logic [31:0] mon_awaddr;
    logic [2:0]  mon_awprot;
    logic        mon_wvalid,  mon_wready;
    logic [31:0] mon_wdata;
    logic [3:0]  mon_wstrb;
    logic        mon_bvalid,  mon_bready;
    logic [1:0]  mon_bresp;

    debug_sram #(
        .DEPTH_WORDS(65536)  // 64K x 32b = 256 KB
    ) u_debug_sram (
        .aclk(aclk), .aresetn(aresetn),
        .i_freeze     (csr_freeze),
        .i_clear_pulse(csr_clear_pulse),
        .o_wr_ptr     (dbg_wr_ptr),
        .o_overflow   (dbg_overflow),
        // Write-only port from STREAM monbus AXIL master
        .wr_awaddr (mon_awaddr), .wr_awprot(mon_awprot),
        .wr_awvalid(mon_awvalid), .wr_awready(mon_awready),
        .wr_wdata  (mon_wdata), .wr_wstrb(mon_wstrb),
        .wr_wvalid (mon_wvalid), .wr_wready(mon_wready),
        .wr_bresp  (mon_bresp), .wr_bvalid(mon_bvalid), .wr_bready(mon_bready),
        .wr_araddr (32'h0), .wr_arprot(3'h0),
        .wr_arvalid(1'b0), .wr_arready(),
        .wr_rdata  (), .wr_rresp(),
        .wr_rvalid (), .wr_rready(1'b1),
        // Read-only port from host decoder S4
        .rd_awaddr (s4_awaddr), .rd_awprot(s4_awprot),
        .rd_awvalid(s4_awvalid), .rd_awready(s4_awready),
        .rd_wdata  (s4_wdata), .rd_wstrb(s4_wstrb),
        .rd_wvalid (s4_wvalid), .rd_wready(s4_wready),
        .rd_bresp  (s4_bresp), .rd_bvalid(s4_bvalid), .rd_bready(s4_bready),
        .rd_araddr (s4_araddr), .rd_arprot(s4_arprot),
        .rd_arvalid(s4_arvalid), .rd_arready(s4_arready),
        .rd_rdata  (s4_rdata), .rd_rresp(s4_rresp),
        .rd_rvalid (s4_rvalid), .rd_rready(s4_rready)
    );

    // =========================================================================
    // DMA source: axi4_slave_rd_pattern_gen (wired to STREAM m_axi_rd)
    // =========================================================================
    logic [AXI_ID_WIDTH-1:0]    rd_arid;
    logic [ADDR_WIDTH-1:0]      rd_araddr;
    logic [7:0]                 rd_arlen;
    logic [2:0]                 rd_arsize;
    logic [1:0]                 rd_arburst;
    logic                       rd_arlock;
    logic [3:0]                 rd_arcache;
    logic [2:0]                 rd_arprot;
    logic [3:0]                 rd_arqos;
    logic [3:0]                 rd_arregion;
    logic [AXI_USER_WIDTH-1:0]  rd_aruser;
    logic                       rd_arvalid, rd_arready;
    logic [AXI_ID_WIDTH-1:0]    rd_rid;
    logic [DATA_WIDTH-1:0]      rd_rdata;
    logic [1:0]                 rd_rresp;
    logic                       rd_rlast;
    logic [AXI_USER_WIDTH-1:0]  rd_ruser;
    logic                       rd_rvalid, rd_rready;

    axi4_slave_rd_pattern_gen #(
        .AXI_ID_WIDTH  (AXI_ID_WIDTH),
        .AXI_ADDR_WIDTH(ADDR_WIDTH),
        .AXI_DATA_WIDTH(DATA_WIDTH),
        .AXI_USER_WIDTH(AXI_USER_WIDTH)
    ) u_rd_pattern (
        .aclk(aclk), .aresetn(aresetn),
        .crc_lfsr_reset (csr_clear_pulse),
        .read_crc_value (read_crc_value),
        .read_crc_valid (read_crc_valid),
        .read_beat_count(read_beat_count),
        .s_axi_arid    (rd_arid),    .s_axi_araddr(rd_araddr),
        .s_axi_arlen   (rd_arlen),   .s_axi_arsize(rd_arsize),
        .s_axi_arburst (rd_arburst), .s_axi_arlock(rd_arlock),
        .s_axi_arcache (rd_arcache), .s_axi_arprot(rd_arprot),
        .s_axi_arqos   (rd_arqos),   .s_axi_arregion(rd_arregion),
        .s_axi_aruser  (rd_aruser),  .s_axi_arvalid(rd_arvalid),
        .s_axi_arready (rd_arready),
        .s_axi_rid     (rd_rid),     .s_axi_rdata(rd_rdata),
        .s_axi_rresp   (rd_rresp),   .s_axi_rlast(rd_rlast),
        .s_axi_ruser   (rd_ruser),   .s_axi_rvalid(rd_rvalid),
        .s_axi_rready  (rd_rready),
        .busy          ()
    );

    // =========================================================================
    // DMA sink: axi4_slave_wr_crc_check (wired to STREAM m_axi_wr)
    // =========================================================================
    logic [AXI_ID_WIDTH-1:0]    wr_awid;
    logic [ADDR_WIDTH-1:0]      wr_awaddr;
    logic [7:0]                 wr_awlen;
    logic [2:0]                 wr_awsize;
    logic [1:0]                 wr_awburst;
    logic                       wr_awlock;
    logic [3:0]                 wr_awcache;
    logic [2:0]                 wr_awprot;
    logic [3:0]                 wr_awqos;
    logic [3:0]                 wr_awregion;
    logic [AXI_USER_WIDTH-1:0]  wr_awuser;
    logic                       wr_awvalid, wr_awready;
    logic [DATA_WIDTH-1:0]      wr_wdata;
    logic [DATA_WIDTH/8-1:0]    wr_wstrb;
    logic                       wr_wlast;
    logic [AXI_USER_WIDTH-1:0]  wr_wuser;
    logic                       wr_wvalid, wr_wready;
    logic [AXI_ID_WIDTH-1:0]    wr_bid;
    logic [1:0]                 wr_bresp;
    logic [AXI_USER_WIDTH-1:0]  wr_buser;
    logic                       wr_bvalid, wr_bready;

    axi4_slave_wr_crc_check #(
        .AXI_ID_WIDTH  (AXI_ID_WIDTH),
        .AXI_ADDR_WIDTH(ADDR_WIDTH),
        .AXI_DATA_WIDTH(DATA_WIDTH),
        .AXI_USER_WIDTH(AXI_USER_WIDTH)
    ) u_wr_crc_check (
        .aclk(aclk), .aresetn(aresetn),
        .crc_reset      (csr_clear_pulse),
        .write_crc_value(write_crc_value),
        .write_crc_valid(write_crc_valid),
        .write_beat_count(write_beat_count),
        .s_axi_awid   (wr_awid),   .s_axi_awaddr(wr_awaddr),
        .s_axi_awlen  (wr_awlen),  .s_axi_awsize(wr_awsize),
        .s_axi_awburst(wr_awburst),.s_axi_awlock(wr_awlock),
        .s_axi_awcache(wr_awcache),.s_axi_awprot(wr_awprot),
        .s_axi_awqos  (wr_awqos),  .s_axi_awregion(wr_awregion),
        .s_axi_awuser (wr_awuser), .s_axi_awvalid(wr_awvalid),
        .s_axi_awready(wr_awready),
        .s_axi_wdata  (wr_wdata),  .s_axi_wstrb(wr_wstrb),
        .s_axi_wlast  (wr_wlast),  .s_axi_wuser(wr_wuser),
        .s_axi_wvalid (wr_wvalid), .s_axi_wready(wr_wready),
        .s_axi_bid    (wr_bid),    .s_axi_bresp(wr_bresp),
        .s_axi_buser  (wr_buser),  .s_axi_bvalid(wr_bvalid),
        .s_axi_bready (wr_bready),
        .busy         ()
    );

    // =========================================================================
    // STREAM DUT
    // =========================================================================
    stream_top_ch8 #(
        .NUM_CHANNELS    (8),
        .DATA_WIDTH      (DATA_WIDTH),
        .ADDR_WIDTH      (ADDR_WIDTH),
        .SRAM_DEPTH      (SRAM_DEPTH),
        .APB_ADDR_WIDTH  (APB_ADDR_WIDTH),
        .APB_DATA_WIDTH  (APB_DATA_WIDTH),
        .AXI_ID_WIDTH    (AXI_ID_WIDTH),
        .AXI_USER_WIDTH  (AXI_USER_WIDTH),
        .USE_AXI_MONITORS(1),
        .CDC_ENABLE      (0)
    ) u_stream (
        .aclk    (aclk),   .aresetn(aresetn),
        .pclk    (aclk),   .presetn(aresetn),

        // APB config
        .s_apb_paddr  (apb_paddr),
        .s_apb_psel   (apb_psel),
        .s_apb_penable(apb_penable),
        .s_apb_pwrite (apb_pwrite),
        .s_apb_pwdata (apb_pwdata),
        .s_apb_pstrb  (apb_pstrb),
        .s_apb_prdata (apb_prdata),
        .s_apb_pready (apb_pready),
        .s_apb_pslverr(apb_pslverr),

        // Descriptor fetch master
        .m_axi_desc_arid   (desc_arid),   .m_axi_desc_araddr(desc_araddr),
        .m_axi_desc_arlen  (desc_arlen),  .m_axi_desc_arsize(desc_arsize),
        .m_axi_desc_arburst(desc_arburst),.m_axi_desc_arlock(desc_arlock),
        .m_axi_desc_arcache(desc_arcache),.m_axi_desc_arprot(desc_arprot),
        .m_axi_desc_arqos  (desc_arqos),  .m_axi_desc_arregion(desc_arregion),
        .m_axi_desc_aruser (desc_aruser), .m_axi_desc_arvalid(desc_arvalid),
        .m_axi_desc_arready(desc_arready),
        .m_axi_desc_rid    (desc_rid),    .m_axi_desc_rdata(desc_rdata),
        .m_axi_desc_rresp  (desc_rresp),  .m_axi_desc_rlast(desc_rlast),
        .m_axi_desc_ruser  (desc_ruser),  .m_axi_desc_rvalid(desc_rvalid),
        .m_axi_desc_rready (desc_rready),

        // Data read master
        .m_axi_rd_arid   (rd_arid),   .m_axi_rd_araddr(rd_araddr),
        .m_axi_rd_arlen  (rd_arlen),  .m_axi_rd_arsize(rd_arsize),
        .m_axi_rd_arburst(rd_arburst),.m_axi_rd_arlock(rd_arlock),
        .m_axi_rd_arcache(rd_arcache),.m_axi_rd_arprot(rd_arprot),
        .m_axi_rd_arqos  (rd_arqos),  .m_axi_rd_arregion(rd_arregion),
        .m_axi_rd_aruser (rd_aruser), .m_axi_rd_arvalid(rd_arvalid),
        .m_axi_rd_arready(rd_arready),
        .m_axi_rd_rid    (rd_rid),    .m_axi_rd_rdata(rd_rdata),
        .m_axi_rd_rresp  (rd_rresp),  .m_axi_rd_rlast(rd_rlast),
        .m_axi_rd_ruser  (rd_ruser),  .m_axi_rd_rvalid(rd_rvalid),
        .m_axi_rd_rready (rd_rready),

        // Data write master
        .m_axi_wr_awid   (wr_awid),   .m_axi_wr_awaddr(wr_awaddr),
        .m_axi_wr_awlen  (wr_awlen),  .m_axi_wr_awsize(wr_awsize),
        .m_axi_wr_awburst(wr_awburst),.m_axi_wr_awlock(wr_awlock),
        .m_axi_wr_awcache(wr_awcache),.m_axi_wr_awprot(wr_awprot),
        .m_axi_wr_awqos  (wr_awqos),  .m_axi_wr_awregion(wr_awregion),
        .m_axi_wr_awuser (wr_awuser), .m_axi_wr_awvalid(wr_awvalid),
        .m_axi_wr_awready(wr_awready),
        .m_axi_wr_wdata  (wr_wdata),  .m_axi_wr_wstrb(wr_wstrb),
        .m_axi_wr_wlast  (wr_wlast),  .m_axi_wr_wuser(wr_wuser),
        .m_axi_wr_wvalid (wr_wvalid), .m_axi_wr_wready(wr_wready),
        .m_axi_wr_bid    (wr_bid),    .m_axi_wr_bresp(wr_bresp),
        .m_axi_wr_buser  (wr_buser),  .m_axi_wr_bvalid(wr_bvalid),
        .m_axi_wr_bready (wr_bready),

        // Err FIFO AXIL slave (host reads via S3)
        .s_axil_err_arvalid(s3_err_arvalid),
        .s_axil_err_arready(s3_err_arready),
        .s_axil_err_araddr (s3_err_araddr),
        .s_axil_err_arprot (s3_err_arprot),
        .s_axil_err_rvalid (s3_err_rvalid),
        .s_axil_err_rready (s3_err_rready),
        .s_axil_err_rdata  (s3_err_rdata),
        .s_axil_err_rresp  (s3_err_rresp),

        // Monitor data AXIL master (writes to debug_sram)
        .m_axil_mon_awvalid(mon_awvalid),
        .m_axil_mon_awready(mon_awready),
        .m_axil_mon_awaddr (mon_awaddr),
        .m_axil_mon_awprot (mon_awprot),
        .m_axil_mon_wvalid (mon_wvalid),
        .m_axil_mon_wready (mon_wready),
        .m_axil_mon_wdata  (mon_wdata),
        .m_axil_mon_wstrb  (mon_wstrb),
        .m_axil_mon_bvalid (mon_bvalid),
        .m_axil_mon_bready (mon_bready),
        .m_axil_mon_bresp  (mon_bresp),

        // Interrupt out
        .stream_irq        (stream_irq),

        // Debug outputs (unconnected at top level)
        .debug_hwif_scheduler_idle  (),
        .debug_hwif_desc_engine_idle(),
        .debug_hwif_channel_idle    (),
        .debug_regblk_req           (),
        .debug_regblk_req_is_wr     (),
        .debug_regblk_addr          (),
        .debug_regblk_rd_data       (),
        .debug_regblk_rd_ack        (),
        .debug_peakrdl_cmd_valid    (),
        .debug_peakrdl_cmd_paddr    (),
        .debug_peakrdl_rsp_valid    (),
        .debug_peakrdl_rsp_prdata   (),
        .debug_last_cpuif_addr      (),
        .debug_last_cpuif_rd_data   (),
        .debug_last_cpuif_rd_ack    (),
        .debug_apb_cmd_valid          (),
        .debug_apb_cmd_ready          (),
        .debug_apb_cmd_pwrite         (),
        .debug_apb_cmd_paddr          (),
        .debug_apb_rsp_valid          (),
        .debug_apb_rsp_ready          (),
        .debug_apb_rsp_prdata         (),
        .debug_apb_rd_cmd_seen        (),
        .debug_apb_rd_cmd_addr        (),
        .debug_apb_rsp_prdata_captured(),
        .debug_apb_rd_count           (),
        .debug_peakrdl_rd_count       (),
        .debug_regblk_rd_count        ()
    );

    // =========================================================================
    // Status outputs to top (→ LEDs)
    // =========================================================================
    assign o_stream_irq     = stream_irq;
    assign o_any_error      = any_error;
    assign o_trace_overflow = dbg_overflow;

    // Heartbeat (bit-26 of a free-running counter = ~1 Hz blink at 100 MHz)
    logic [26:0] r_hb;
    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_hb <= '0;
        end else begin
            r_hb <= r_hb + 27'd1;
        end
    )
    assign o_heartbeat = r_hb[26:23];

    // Prevent unused signal warnings
    /* verilator lint_off UNUSED */
    wire _unused_ok = &{1'b0,
        read_beat_count, write_beat_count,
        csr_start_pulse, csr_soft_reset,
        1'b0};
    /* verilator lint_on UNUSED */

endmodule : stream_char_harness
