`timescale 1ns / 1ps

module bridge_ooo_with_arbiter #(parameter int  NUM_MASTERS = 5,
parameter int  NUM_SLAVES = 3,
parameter int  XBAR_DATA_WIDTH = 512,
parameter int  XBAR_ADDR_WIDTH = 64,
parameter int  XBAR_ID_WIDTH = 8,
parameter int  XBAR_STRB_WIDTH = 64 )(
    input  logic         aclk,
    input  logic         aresetn,
    input  logic [63:0]  rapids_descr_m_axi_awaddr,
    input  logic [7:0]   rapids_descr_m_axi_awid,
    input  logic [7:0]   rapids_descr_m_axi_awlen,
    input  logic [2:0]   rapids_descr_m_axi_awsize,
    input  logic [1:0]   rapids_descr_m_axi_awburst,
    input  logic         rapids_descr_m_axi_awlock,
    input  logic [3:0]   rapids_descr_m_axi_awcache,
    input  logic [2:0]   rapids_descr_m_axi_awprot,
    input  logic         rapids_descr_m_axi_awvalid,
    output logic         rapids_descr_m_axi_awready,
    input  logic [511:0] rapids_descr_m_axi_wdata,
    input  logic [63:0]  rapids_descr_m_axi_wstrb,
    input  logic         rapids_descr_m_axi_wlast,
    input  logic         rapids_descr_m_axi_wvalid,
    output logic         rapids_descr_m_axi_wready,
    output logic [7:0]   rapids_descr_m_axi_bid,
    output logic [1:0]   rapids_descr_m_axi_bresp,
    output logic         rapids_descr_m_axi_bvalid,
    input  logic         rapids_descr_m_axi_bready,
    input  logic [63:0]  rapids_sink_m_axi_awaddr,
    input  logic [7:0]   rapids_sink_m_axi_awid,
    input  logic [7:0]   rapids_sink_m_axi_awlen,
    input  logic [2:0]   rapids_sink_m_axi_awsize,
    input  logic [1:0]   rapids_sink_m_axi_awburst,
    input  logic         rapids_sink_m_axi_awlock,
    input  logic [3:0]   rapids_sink_m_axi_awcache,
    input  logic [2:0]   rapids_sink_m_axi_awprot,
    input  logic         rapids_sink_m_axi_awvalid,
    output logic         rapids_sink_m_axi_awready,
    input  logic [511:0] rapids_sink_m_axi_wdata,
    input  logic [63:0]  rapids_sink_m_axi_wstrb,
    input  logic         rapids_sink_m_axi_wlast,
    input  logic         rapids_sink_m_axi_wvalid,
    output logic         rapids_sink_m_axi_wready,
    output logic [7:0]   rapids_sink_m_axi_bid,
    output logic [1:0]   rapids_sink_m_axi_bresp,
    output logic         rapids_sink_m_axi_bvalid,
    input  logic         rapids_sink_m_axi_bready,
    input  logic [63:0]  rapids_src_m_axi_araddr,
    input  logic [7:0]   rapids_src_m_axi_arid,
    input  logic [7:0]   rapids_src_m_axi_arlen,
    input  logic [2:0]   rapids_src_m_axi_arsize,
    input  logic [1:0]   rapids_src_m_axi_arburst,
    input  logic         rapids_src_m_axi_arlock,
    input  logic [3:0]   rapids_src_m_axi_arcache,
    input  logic [2:0]   rapids_src_m_axi_arprot,
    input  logic         rapids_src_m_axi_arvalid,
    output logic         rapids_src_m_axi_arready,
    output logic [511:0] rapids_src_m_axi_rdata,
    output logic [7:0]   rapids_src_m_axi_rid,
    output logic [1:0]   rapids_src_m_axi_rresp,
    output logic         rapids_src_m_axi_rlast,
    output logic         rapids_src_m_axi_rvalid,
    input  logic         rapids_src_m_axi_rready,
    input  logic [63:0]  stream_m_axi_awaddr,
    input  logic [7:0]   stream_m_axi_awid,
    input  logic [7:0]   stream_m_axi_awlen,
    input  logic [2:0]   stream_m_axi_awsize,
    input  logic [1:0]   stream_m_axi_awburst,
    input  logic         stream_m_axi_awlock,
    input  logic [3:0]   stream_m_axi_awcache,
    input  logic [2:0]   stream_m_axi_awprot,
    input  logic         stream_m_axi_awvalid,
    output logic         stream_m_axi_awready,
    input  logic [511:0] stream_m_axi_wdata,
    input  logic [63:0]  stream_m_axi_wstrb,
    input  logic         stream_m_axi_wlast,
    input  logic         stream_m_axi_wvalid,
    output logic         stream_m_axi_wready,
    output logic [7:0]   stream_m_axi_bid,
    output logic [1:0]   stream_m_axi_bresp,
    output logic         stream_m_axi_bvalid,
    input  logic         stream_m_axi_bready,
    input  logic [63:0]  stream_m_axi_araddr,
    input  logic [7:0]   stream_m_axi_arid,
    input  logic [7:0]   stream_m_axi_arlen,
    input  logic [2:0]   stream_m_axi_arsize,
    input  logic [1:0]   stream_m_axi_arburst,
    input  logic         stream_m_axi_arlock,
    input  logic [3:0]   stream_m_axi_arcache,
    input  logic [2:0]   stream_m_axi_arprot,
    input  logic         stream_m_axi_arvalid,
    output logic         stream_m_axi_arready,
    output logic [511:0] stream_m_axi_rdata,
    output logic [7:0]   stream_m_axi_rid,
    output logic [1:0]   stream_m_axi_rresp,
    output logic         stream_m_axi_rlast,
    output logic         stream_m_axi_rvalid,
    input  logic         stream_m_axi_rready,
    input  logic [31:0]  cpu_m_axi_awaddr,
    input  logic [3:0]   cpu_m_axi_awid,
    input  logic [7:0]   cpu_m_axi_awlen,
    input  logic [2:0]   cpu_m_axi_awsize,
    input  logic [1:0]   cpu_m_axi_awburst,
    input  logic         cpu_m_axi_awlock,
    input  logic [3:0]   cpu_m_axi_awcache,
    input  logic [2:0]   cpu_m_axi_awprot,
    input  logic         cpu_m_axi_awvalid,
    output logic         cpu_m_axi_awready,
    input  logic [63:0]  cpu_m_axi_wdata,
    input  logic [7:0]   cpu_m_axi_wstrb,
    input  logic         cpu_m_axi_wlast,
    input  logic         cpu_m_axi_wvalid,
    output logic         cpu_m_axi_wready,
    output logic [3:0]   cpu_m_axi_bid,
    output logic [1:0]   cpu_m_axi_bresp,
    output logic         cpu_m_axi_bvalid,
    input  logic         cpu_m_axi_bready,
    input  logic [31:0]  cpu_m_axi_araddr,
    input  logic [3:0]   cpu_m_axi_arid,
    input  logic [7:0]   cpu_m_axi_arlen,
    input  logic [2:0]   cpu_m_axi_arsize,
    input  logic [1:0]   cpu_m_axi_arburst,
    input  logic         cpu_m_axi_arlock,
    input  logic [3:0]   cpu_m_axi_arcache,
    input  logic [2:0]   cpu_m_axi_arprot,
    input  logic         cpu_m_axi_arvalid,
    output logic         cpu_m_axi_arready,
    output logic [63:0]  cpu_m_axi_rdata,
    output logic [3:0]   cpu_m_axi_rid,
    output logic [1:0]   cpu_m_axi_rresp,
    output logic         cpu_m_axi_rlast,
    output logic         cpu_m_axi_rvalid,
    input  logic         cpu_m_axi_rready,
    output logic [63:0]  ddr_s_axi_awaddr,
    output logic [7:0]   ddr_s_axi_awid,
    output logic [7:0]   ddr_s_axi_awlen,
    output logic [2:0]   ddr_s_axi_awsize,
    output logic [1:0]   ddr_s_axi_awburst,
    output logic         ddr_s_axi_awlock,
    output logic [3:0]   ddr_s_axi_awcache,
    output logic [2:0]   ddr_s_axi_awprot,
    output logic         ddr_s_axi_awvalid,
    input  logic         ddr_s_axi_awready,
    output logic [511:0] ddr_s_axi_wdata,
    output logic [63:0]  ddr_s_axi_wstrb,
    output logic         ddr_s_axi_wlast,
    output logic         ddr_s_axi_wvalid,
    input  logic         ddr_s_axi_wready,
    input  logic [7:0]   ddr_s_axi_bid,
    input  logic [1:0]   ddr_s_axi_bresp,
    input  logic         ddr_s_axi_bvalid,
    output logic         ddr_s_axi_bready,
    output logic [63:0]  ddr_s_axi_araddr,
    output logic [7:0]   ddr_s_axi_arid,
    output logic [7:0]   ddr_s_axi_arlen,
    output logic [2:0]   ddr_s_axi_arsize,
    output logic [1:0]   ddr_s_axi_arburst,
    output logic         ddr_s_axi_arlock,
    output logic [3:0]   ddr_s_axi_arcache,
    output logic [2:0]   ddr_s_axi_arprot,
    output logic         ddr_s_axi_arvalid,
    input  logic         ddr_s_axi_arready,
    input  logic [511:0] ddr_s_axi_rdata,
    input  logic [7:0]   ddr_s_axi_rid,
    input  logic [1:0]   ddr_s_axi_rresp,
    input  logic         ddr_s_axi_rlast,
    input  logic         ddr_s_axi_rvalid,
    output logic         ddr_s_axi_rready,
    output logic [47:0]  sram_s_axi_awaddr,
    output logic [7:0]   sram_s_axi_awid,
    output logic [7:0]   sram_s_axi_awlen,
    output logic [2:0]   sram_s_axi_awsize,
    output logic [1:0]   sram_s_axi_awburst,
    output logic         sram_s_axi_awlock,
    output logic [3:0]   sram_s_axi_awcache,
    output logic [2:0]   sram_s_axi_awprot,
    output logic         sram_s_axi_awvalid,
    input  logic         sram_s_axi_awready,
    output logic [511:0] sram_s_axi_wdata,
    output logic [63:0]  sram_s_axi_wstrb,
    output logic         sram_s_axi_wlast,
    output logic         sram_s_axi_wvalid,
    input  logic         sram_s_axi_wready,
    input  logic [7:0]   sram_s_axi_bid,
    input  logic [1:0]   sram_s_axi_bresp,
    input  logic         sram_s_axi_bvalid,
    output logic         sram_s_axi_bready,
    output logic [47:0]  sram_s_axi_araddr,
    output logic [7:0]   sram_s_axi_arid,
    output logic [7:0]   sram_s_axi_arlen,
    output logic [2:0]   sram_s_axi_arsize,
    output logic [1:0]   sram_s_axi_arburst,
    output logic         sram_s_axi_arlock,
    output logic [3:0]   sram_s_axi_arcache,
    output logic [2:0]   sram_s_axi_arprot,
    output logic         sram_s_axi_arvalid,
    input  logic         sram_s_axi_arready,
    input  logic [511:0] sram_s_axi_rdata,
    input  logic [7:0]   sram_s_axi_rid,
    input  logic [1:0]   sram_s_axi_rresp,
    input  logic         sram_s_axi_rlast,
    input  logic         sram_s_axi_rvalid,
    output logic         sram_s_axi_rready,
    output logic         apb0_psel,
    output logic         apb0_penable,
    output logic [31:0]  apb0_paddr,
    output logic         apb0_pwrite,
    output logic [31:0]  apb0_pwdata,
    output logic [3:0]   apb0_pstrb,
    output logic [2:0]   apb0_pprot,
    input  logic         apb0_pready,
    input  logic [31:0]  apb0_prdata,
    input  logic         apb0_pslverr
);

// ==============================================================================
// Module: bridge_ooo_with_arbiter
// CSV-Based Bridge Generator - Phase 2
// ==============================================================================
// 
// Configuration:
//   Masters: 5
//     - rapids_descr_wr (AXI4, 512b, prefix: rapids_descr_m_axi_)
//     - rapids_sink_wr (AXI4, 512b, prefix: rapids_sink_m_axi_)
//     - rapids_src_rd (AXI4, 512b, prefix: rapids_src_m_axi_)
//     - stream_master (AXI4, 512b, prefix: stream_m_axi_)
//     - cpu_master (AXI4, 64b, prefix: cpu_m_axi_)
//   Slaves: 3
//     - ddr_controller (AXI4, 512b, prefix: ddr_s_axi_)
//     - sram_buffer (AXI4, 512b, prefix: sram_s_axi_)
//     - apb_periph0 (APB, 32b, prefix: apb0_) +AXI2APB +WIDTH(32b)
// 
// Internal Crossbar: 512b data, 64b addr, 8b ID
// 
// Generated from CSV configuration:
//   - Custom port prefixes from ports.csv
//   - Partial connectivity from connectivity.csv
//   - Automatic converter insertion (AXI2APB, width converters)
// 
// Architecture:
//   External Masters -> [Width Conv] -> Internal Crossbar
//                                      -> [Width Conv] -> [AXI2APB] -> External Slaves
// ==============================================================================

// ==============================================================================
// Internal Signals - Crossbar Connections
// ==============================================================================
// Internal crossbar: 5 masters × 3 slaves at 512b data width

// Crossbar master-side interfaces (after width conversion if needed)

            logic [63:0] xbar_m_awaddr  [NUM_MASTERS];
            logic [7:0] xbar_m_awid    [NUM_MASTERS];
            logic [7:0]           xbar_m_awlen   [NUM_MASTERS];
            logic [2:0]           xbar_m_awsize  [NUM_MASTERS];
            logic [1:0]           xbar_m_awburst [NUM_MASTERS];
            logic                 xbar_m_awlock  [NUM_MASTERS];
            logic [3:0]           xbar_m_awcache [NUM_MASTERS];
            logic [2:0]           xbar_m_awprot  [NUM_MASTERS];
            logic                 xbar_m_awvalid [NUM_MASTERS];
            logic                 xbar_m_awready [NUM_MASTERS];

            logic [511:0] xbar_m_wdata  [NUM_MASTERS];
            logic [63:0] xbar_m_wstrb  [NUM_MASTERS];
            logic                 xbar_m_wlast  [NUM_MASTERS];
            logic                 xbar_m_wvalid [NUM_MASTERS];
            logic                 xbar_m_wready [NUM_MASTERS];

            logic [7:0] xbar_m_bid    [NUM_MASTERS];
            logic [1:0]           xbar_m_bresp  [NUM_MASTERS];
            logic                 xbar_m_bvalid [NUM_MASTERS];
            logic                 xbar_m_bready [NUM_MASTERS];

            logic [63:0] xbar_m_araddr  [NUM_MASTERS];
            logic [7:0] xbar_m_arid    [NUM_MASTERS];
            logic [7:0]           xbar_m_arlen   [NUM_MASTERS];
            logic [2:0]           xbar_m_arsize  [NUM_MASTERS];
            logic [1:0]           xbar_m_arburst [NUM_MASTERS];
            logic                 xbar_m_arlock  [NUM_MASTERS];
            logic [3:0]           xbar_m_arcache [NUM_MASTERS];
            logic [2:0]           xbar_m_arprot  [NUM_MASTERS];
            logic                 xbar_m_arvalid [NUM_MASTERS];
            logic                 xbar_m_arready [NUM_MASTERS];

            logic [511:0] xbar_m_rdata  [NUM_MASTERS];
            logic [7:0] xbar_m_rid    [NUM_MASTERS];
            logic [1:0]           xbar_m_rresp  [NUM_MASTERS];
            logic                 xbar_m_rlast  [NUM_MASTERS];
            logic                 xbar_m_rvalid [NUM_MASTERS];
            logic                 xbar_m_rready [NUM_MASTERS];
        

// Crossbar slave-side interfaces (before width/protocol conversion if needed)

            logic [63:0] xbar_s_awaddr  [NUM_SLAVES];
            logic [7:0] xbar_s_awid    [NUM_SLAVES];
            logic [7:0]           xbar_s_awlen   [NUM_SLAVES];
            logic [2:0]           xbar_s_awsize  [NUM_SLAVES];
            logic [1:0]           xbar_s_awburst [NUM_SLAVES];
            logic                 xbar_s_awlock  [NUM_SLAVES];
            logic [3:0]           xbar_s_awcache [NUM_SLAVES];
            logic [2:0]           xbar_s_awprot  [NUM_SLAVES];
            logic                 xbar_s_awvalid [NUM_SLAVES];
            logic                 xbar_s_awready [NUM_SLAVES];

            logic [511:0] xbar_s_wdata  [NUM_SLAVES];
            logic [63:0] xbar_s_wstrb  [NUM_SLAVES];
            logic                 xbar_s_wlast  [NUM_SLAVES];
            logic                 xbar_s_wvalid [NUM_SLAVES];
            logic                 xbar_s_wready [NUM_SLAVES];

            logic [7:0] xbar_s_bid    [NUM_SLAVES];
            logic [1:0]           xbar_s_bresp  [NUM_SLAVES];
            logic                 xbar_s_bvalid [NUM_SLAVES];
            logic                 xbar_s_bready [NUM_SLAVES];

            logic [63:0] xbar_s_araddr  [NUM_SLAVES];
            logic [7:0] xbar_s_arid    [NUM_SLAVES];
            logic [7:0]           xbar_s_arlen   [NUM_SLAVES];
            logic [2:0]           xbar_s_arsize  [NUM_SLAVES];
            logic [1:0]           xbar_s_arburst [NUM_SLAVES];
            logic                 xbar_s_arlock  [NUM_SLAVES];
            logic [3:0]           xbar_s_arcache [NUM_SLAVES];
            logic [2:0]           xbar_s_arprot  [NUM_SLAVES];
            logic                 xbar_s_arvalid [NUM_SLAVES];
            logic                 xbar_s_arready [NUM_SLAVES];

            logic [511:0] xbar_s_rdata  [NUM_SLAVES];
            logic [7:0] xbar_s_rid    [NUM_SLAVES];
            logic [1:0]           xbar_s_rresp  [NUM_SLAVES];
            logic                 xbar_s_rlast  [NUM_SLAVES];
            logic                 xbar_s_rvalid [NUM_SLAVES];
            logic                 xbar_s_rready [NUM_SLAVES];
        

// Transaction Tracking Signals (CAM for OOO slaves, FIFO for in-order slaves)
// CAM signals for OOO slave 0: ddr_controller

            // CAM allocation signals (AW/AR grant to ddr_controller)
            logic                         cam_ddr_controller_allocate;
            logic [7:0]         cam_ddr_controller_allocate_tag;
            logic [2:0] cam_ddr_controller_allocate_data;

            // CAM deallocation signals (B/R response from ddr_controller)
            logic                         cam_ddr_controller_deallocate;
            logic [7:0]         cam_ddr_controller_deallocate_tag;
            logic                         cam_ddr_controller_deallocate_valid;
            logic [2:0] cam_ddr_controller_deallocate_data;
            logic [3:0]                   cam_ddr_controller_deallocate_count;

            // CAM status signals
            logic                         cam_ddr_controller_hit;
            logic                         cam_ddr_controller_empty;
            logic                         cam_ddr_controller_full;
            logic [4:0]                   cam_ddr_controller_count;
                
// FIFO tracker signals for in-order slave 1: sram_buffer

            // FIFO write signals (AW/AR grant to sram_buffer)
            logic                         fifo_sram_buffer_wr_valid;
            logic [2:0] fifo_sram_buffer_wr_data;
            logic                         fifo_sram_buffer_wr_ready;

            // FIFO read signals (B/R response from sram_buffer)
            logic                         fifo_sram_buffer_rd_valid;
            logic [2:0] fifo_sram_buffer_rd_data;
            logic                         fifo_sram_buffer_rd_ready;

            // FIFO status signals
            logic                         fifo_sram_buffer_full;
            logic                         fifo_sram_buffer_empty;
            logic [4:0]                   fifo_sram_buffer_count;
                

// ==============================================================================
// Internal AXI4 Crossbar Instance
// ==============================================================================
// Configuration: 5x3 crossbar
// Data width: 512b
// Address width: 64b
// ID width: 8b

// Address map for crossbar routing:
//   Slave 0 (ddr_controller): 0x80000000 - 0xFFFFFFFF
//   Slave 1 (sram_buffer): 0x40000000 - 0x4FFFFFFF
//   Slave 2 (apb_periph0): 0x00000000 - 0x0000FFFF


        bridge_axi4_flat_5x3 #(
            .NUM_MASTERS  (NUM_MASTERS),
            .NUM_SLAVES   (NUM_SLAVES),
            .DATA_WIDTH   (XBAR_DATA_WIDTH),
            .ADDR_WIDTH   (XBAR_ADDR_WIDTH),
            .ID_WIDTH     (XBAR_ID_WIDTH)
        ) u_crossbar (
            .aclk    (aclk),
            .aresetn (aresetn),

            // Master-side connections (from external masters)
            .s_axi_awaddr  (xbar_m_awaddr),
            .s_axi_awid    (xbar_m_awid),
            .s_axi_awlen   (xbar_m_awlen),
            .s_axi_awsize  (xbar_m_awsize),
            .s_axi_awburst (xbar_m_awburst),
            .s_axi_awlock  (xbar_m_awlock),
            .s_axi_awcache (xbar_m_awcache),
            .s_axi_awprot  (xbar_m_awprot),
            .s_axi_awvalid (xbar_m_awvalid),
            .s_axi_awready (xbar_m_awready),

            .s_axi_wdata  (xbar_m_wdata),
            .s_axi_wstrb  (xbar_m_wstrb),
            .s_axi_wlast  (xbar_m_wlast),
            .s_axi_wvalid (xbar_m_wvalid),
            .s_axi_wready (xbar_m_wready),

            .s_axi_bid    (xbar_m_bid),
            .s_axi_bresp  (xbar_m_bresp),
            .s_axi_bvalid (xbar_m_bvalid),
            .s_axi_bready (xbar_m_bready),

            .s_axi_araddr  (xbar_m_araddr),
            .s_axi_arid    (xbar_m_arid),
            .s_axi_arlen   (xbar_m_arlen),
            .s_axi_arsize  (xbar_m_arsize),
            .s_axi_arburst (xbar_m_arburst),
            .s_axi_arlock  (xbar_m_arlock),
            .s_axi_arcache (xbar_m_arcache),
            .s_axi_arprot  (xbar_m_arprot),
            .s_axi_arvalid (xbar_m_arvalid),
            .s_axi_arready (xbar_m_arready),

            .s_axi_rdata  (xbar_m_rdata),
            .s_axi_rid    (xbar_m_rid),
            .s_axi_rresp  (xbar_m_rresp),
            .s_axi_rlast  (xbar_m_rlast),
            .s_axi_rvalid (xbar_m_rvalid),
            .s_axi_rready (xbar_m_rready),

            // Slave-side connections (to external slaves)
            .m_axi_awaddr  (xbar_s_awaddr),
            .m_axi_awid    (xbar_s_awid),
            .m_axi_awlen   (xbar_s_awlen),
            .m_axi_awsize  (xbar_s_awsize),
            .m_axi_awburst (xbar_s_awburst),
            .m_axi_awlock  (xbar_s_awlock),
            .m_axi_awcache (xbar_s_awcache),
            .m_axi_awprot  (xbar_s_awprot),
            .m_axi_awvalid (xbar_s_awvalid),
            .m_axi_awready (xbar_s_awready),

            .m_axi_wdata  (xbar_s_wdata),
            .m_axi_wstrb  (xbar_s_wstrb),
            .m_axi_wlast  (xbar_s_wlast),
            .m_axi_wvalid (xbar_s_wvalid),
            .m_axi_wready (xbar_s_wready),

            .m_axi_bid    (xbar_s_bid),
            .m_axi_bresp  (xbar_s_bresp),
            .m_axi_bvalid (xbar_s_bvalid),
            .m_axi_bready (xbar_s_bready),

            .m_axi_araddr  (xbar_s_araddr),
            .m_axi_arid    (xbar_s_arid),
            .m_axi_arlen   (xbar_s_arlen),
            .m_axi_arsize  (xbar_s_arsize),
            .m_axi_arburst (xbar_s_arburst),
            .m_axi_arlock  (xbar_s_arlock),
            .m_axi_arcache (xbar_s_arcache),
            .m_axi_arprot  (xbar_s_arprot),
            .m_axi_arvalid (xbar_s_arvalid),
            .m_axi_arready (xbar_s_arready),

            .m_axi_rdata  (xbar_s_rdata),
            .m_axi_rid    (xbar_s_rid),
            .m_axi_rresp  (xbar_s_rresp),
            .m_axi_rlast  (xbar_s_rlast),
            .m_axi_rvalid (xbar_s_rvalid),
            .m_axi_rready (xbar_s_rready)
        );
        

// ==============================================================================
// Transaction Tracking Mechanisms
// ==============================================================================
// CAM instances for out-of-order slaves (ooo=1)
// FIFO instances for in-order slaves (ooo=0)


// =============================================================================
// Bridge CAM for Out-of-Order Slave: ddr_controller
// =============================================================================
//
// Purpose:
//   Tracks transaction IDs for ddr_controller (out-of-order responses)
//   Routes response transactions (B/R channels) back to the correct master
//
// Configuration:
//   TAG_WIDTH  = 8  (matches crossbar ID width)
//   DATA_WIDTH = 3  ($clog2(5 masters))
//   DEPTH      = 16 (configurable via parameter)
//   MODE       = 2 (FIFO ordering for duplicate IDs)
//
// Operation:
//   Allocation   : When master issues AW/AR to this slave
//   Deallocation : When slave returns B/R response
//   Routing      : deallocate_data indicates which master to route to
//

bridge_cam #(.TAG_WIDTH(8),.DATA_WIDTH(3),.DEPTH(16),.ALLOW_DUPLICATES(1),.PIPELINE_EVICT(0)) u_ddr_controller_cam(.clk(aclk),.rst_n(aresetn),.allocate(cam_ddr_controller_allocate),.allocate_tag(cam_ddr_controller_allocate_tag),.allocate_data(cam_ddr_controller_allocate_data),.deallocate(cam_ddr_controller_deallocate),.deallocate_tag(cam_ddr_controller_deallocate_tag),.deallocate_valid(cam_ddr_controller_deallocate_valid),.deallocate_data(cam_ddr_controller_deallocate_data),.deallocate_count(cam_ddr_controller_deallocate_count),.cam_hit(cam_ddr_controller_hit),.tags_empty(cam_ddr_controller_empty),.tags_full(cam_ddr_controller_full),.tags_count(cam_ddr_controller_count));

// CAM Signal Connections for ddr_controller
// Implementation: Track transactions to OOO slave using master-side monitoring

// Internal tracking signals
logic cam_aw_alloc, cam_ar_alloc;
logic [7:0] cam_aw_tag, cam_ar_tag;
logic [2:0] cam_aw_midx, cam_ar_midx;
logic cam_b_dealloc, cam_r_dealloc;
logic [7:0] cam_b_tag, cam_r_tag;

// CAM Allocation Logic - Track AW/AR transactions to slave 0 (ddr_controller)
// Monitor master-side handshakes and decode addresses to detect slave 0 targets
always_comb begin
    cam_aw_alloc = 1'b0;
    cam_aw_tag = 8'b0;
    cam_aw_midx = 3'b0;

    // Check each master for AW handshake targeting slave 0 (address 0x8...)
    for (int m = 0; m < NUM_MASTERS; m++) begin
        if (xbar_m_awvalid[m] && xbar_m_awready[m]) begin
            // Decode address - slave 0 = 0x8... (DDR at 0x80000000-0xFFFFFFFF)
            if (xbar_m_awaddr[m][63:60] == 4'h8) begin
                cam_aw_alloc = 1'b1;
                cam_aw_tag = xbar_m_awid[m];
                cam_aw_midx = m[2:0];
            end
        end
    end
end

always_comb begin
    cam_ar_alloc = 1'b0;
    cam_ar_tag = 8'b0;
    cam_ar_midx = 3'b0;

    // Check each master for AR handshake targeting slave 0
    for (int m = 0; m < NUM_MASTERS; m++) begin
        if (xbar_m_arvalid[m] && xbar_m_arready[m]) begin
            if (xbar_m_araddr[m][63:60] == 4'h8) begin
                cam_ar_alloc = 1'b1;
                cam_ar_tag = xbar_m_arid[m];
                cam_ar_midx = m[2:0];
            end
        end
    end
end

// Merge AW/AR allocations (priority to AW if both happen same cycle)
assign cam_ddr_controller_allocate = cam_aw_alloc | cam_ar_alloc;
assign cam_ddr_controller_allocate_tag = cam_aw_alloc ? cam_aw_tag : cam_ar_tag;
assign cam_ddr_controller_allocate_data = cam_aw_alloc ? cam_aw_midx : cam_ar_midx;

// CAM Deallocation Logic - Track B/R responses from slave 0
always_comb begin
    cam_b_dealloc = xbar_s_bvalid[0] && xbar_s_bready[0];
    cam_b_tag = xbar_s_bid[0];

    cam_r_dealloc = xbar_s_rvalid[0] && xbar_s_rready[0] && xbar_s_rlast[0];
    cam_r_tag = xbar_s_rid[0];
end

// Merge B/R deallocations (priority to B if both happen same cycle)
assign cam_ddr_controller_deallocate = cam_b_dealloc | cam_r_dealloc;
assign cam_ddr_controller_deallocate_tag = cam_b_dealloc ? cam_b_tag : cam_r_tag;


// =============================================================================
// FIFO Tracker for In-Order Slave: sram_buffer
// =============================================================================
//
// Purpose:
//   Simple FIFO-based tracking for sram_buffer (in-order responses)
//   Stores master indices in request order
//   Routes response transactions back in FIFO order
//
// Configuration:
//   DATA_WIDTH = 3  ($clog2(5 masters))
//   DEPTH      = 16 (matches expected outstanding transactions)
//
// Operation:
//   Push : When master's AW/AR is granted to this slave
//   Pop  : When slave returns B/R response (FIFO order)
//

gaxi_fifo_sync #(.DATA_WIDTH(3),.DEPTH(16)) u_sram_buffer_tracker(.axi_aclk(aclk),.axi_aresetn(aresetn),.wr_valid(fifo_sram_buffer_wr_valid),.wr_data(fifo_sram_buffer_wr_data),.rd_ready(fifo_sram_buffer_rd_ready),.wr_ready(fifo_sram_buffer_wr_ready),.rd_data(fifo_sram_buffer_rd_data),.rd_valid(fifo_sram_buffer_rd_valid),.count(fifo_sram_buffer_count));

// FIFO Tracker Signal Connections for sram_buffer
// Implementation: Track transactions to in-order slave using master-side monitoring

// Internal tracking signals
logic fifo_aw_push, fifo_ar_push;
logic [2:0] fifo_aw_midx, fifo_ar_midx;
logic fifo_b_pop, fifo_r_pop;

// FIFO Write Logic - Track AW/AR transactions to slave 1 (sram_buffer)
// Monitor master-side handshakes and decode addresses to detect slave 1 targets
always_comb begin
    fifo_aw_push = 1'b0;
    fifo_aw_midx = 3'b0;

    // Check each master for AW handshake targeting slave 1 (address 0x4...)
    for (int m = 0; m < NUM_MASTERS; m++) begin
        if (xbar_m_awvalid[m] && xbar_m_awready[m]) begin
            // Decode address - slave 1 = 0x4... (SRAM at 0x40000000-0x4FFFFFFF)
            if (xbar_m_awaddr[m][63:60] == 4'h4) begin
                fifo_aw_push = 1'b1;
                fifo_aw_midx = m[2:0];
            end
        end
    end
end

always_comb begin
    fifo_ar_push = 1'b0;
    fifo_ar_midx = 3'b0;

    // Check each master for AR handshake targeting slave 1
    for (int m = 0; m < NUM_MASTERS; m++) begin
        if (xbar_m_arvalid[m] && xbar_m_arready[m]) begin
            if (xbar_m_araddr[m][63:60] == 4'h4) begin
                fifo_ar_push = 1'b1;
                fifo_ar_midx = m[2:0];
            end
        end
    end
end

// Merge AW/AR pushes (priority to AW if both happen same cycle)
assign fifo_sram_buffer_wr_valid = fifo_aw_push | fifo_ar_push;
assign fifo_sram_buffer_wr_data = fifo_aw_push ? fifo_aw_midx : fifo_ar_midx;

// FIFO Read Logic - Pop when B/R responses arrive from slave 1
always_comb begin
    fifo_b_pop = xbar_s_bvalid[1] && xbar_s_bready[1];
    fifo_r_pop = xbar_s_rvalid[1] && xbar_s_rready[1] && xbar_s_rlast[1];
end

// Merge B/R pops - signal ready to FIFO when either channel needs data
assign fifo_sram_buffer_rd_ready = fifo_b_pop | fifo_r_pop;

// ==============================================================================
// Master Port Connections to Crossbar
// ==============================================================================

// Master 0: rapids_descr_wr [WR] - Direct connection (no width conversion)
// Master 0: rapids_descr_wr [WR] (direct connection)

                assign xbar_m_awaddr[0]  = rapids_descr_m_axi_awaddr;
                assign xbar_m_awid[0]    = rapids_descr_m_axi_awid;
                assign xbar_m_awlen[0]   = rapids_descr_m_axi_awlen;
                assign xbar_m_awsize[0]  = rapids_descr_m_axi_awsize;
                assign xbar_m_awburst[0] = rapids_descr_m_axi_awburst;
                assign xbar_m_awlock[0]  = rapids_descr_m_axi_awlock;
                assign xbar_m_awcache[0] = rapids_descr_m_axi_awcache;
                assign xbar_m_awprot[0]  = rapids_descr_m_axi_awprot;
                assign xbar_m_awvalid[0] = rapids_descr_m_axi_awvalid;
                assign rapids_descr_m_axi_awready = xbar_m_awready[0];

                assign xbar_m_wdata[0]  = rapids_descr_m_axi_wdata;
                assign xbar_m_wstrb[0]  = rapids_descr_m_axi_wstrb;
                assign xbar_m_wlast[0]  = rapids_descr_m_axi_wlast;
                assign xbar_m_wvalid[0] = rapids_descr_m_axi_wvalid;
                assign rapids_descr_m_axi_wready = xbar_m_wready[0];

                assign rapids_descr_m_axi_bid    = xbar_m_bid[0];
                assign rapids_descr_m_axi_bresp  = xbar_m_bresp[0];
                assign rapids_descr_m_axi_bvalid = xbar_m_bvalid[0];
                assign xbar_m_bready[0] = rapids_descr_m_axi_bready;


// Master 1: rapids_sink_wr [WR] - Direct connection (no width conversion)
// Master 1: rapids_sink_wr [WR] (direct connection)

                assign xbar_m_awaddr[1]  = rapids_sink_m_axi_awaddr;
                assign xbar_m_awid[1]    = rapids_sink_m_axi_awid;
                assign xbar_m_awlen[1]   = rapids_sink_m_axi_awlen;
                assign xbar_m_awsize[1]  = rapids_sink_m_axi_awsize;
                assign xbar_m_awburst[1] = rapids_sink_m_axi_awburst;
                assign xbar_m_awlock[1]  = rapids_sink_m_axi_awlock;
                assign xbar_m_awcache[1] = rapids_sink_m_axi_awcache;
                assign xbar_m_awprot[1]  = rapids_sink_m_axi_awprot;
                assign xbar_m_awvalid[1] = rapids_sink_m_axi_awvalid;
                assign rapids_sink_m_axi_awready = xbar_m_awready[1];

                assign xbar_m_wdata[1]  = rapids_sink_m_axi_wdata;
                assign xbar_m_wstrb[1]  = rapids_sink_m_axi_wstrb;
                assign xbar_m_wlast[1]  = rapids_sink_m_axi_wlast;
                assign xbar_m_wvalid[1] = rapids_sink_m_axi_wvalid;
                assign rapids_sink_m_axi_wready = xbar_m_wready[1];

                assign rapids_sink_m_axi_bid    = xbar_m_bid[1];
                assign rapids_sink_m_axi_bresp  = xbar_m_bresp[1];
                assign rapids_sink_m_axi_bvalid = xbar_m_bvalid[1];
                assign xbar_m_bready[1] = rapids_sink_m_axi_bready;


// Master 2: rapids_src_rd [RD] - Direct connection (no width conversion)
// Master 2: rapids_src_rd [RD] (direct connection)

                assign xbar_m_araddr[2]  = rapids_src_m_axi_araddr;
                assign xbar_m_arid[2]    = rapids_src_m_axi_arid;
                assign xbar_m_arlen[2]   = rapids_src_m_axi_arlen;
                assign xbar_m_arsize[2]  = rapids_src_m_axi_arsize;
                assign xbar_m_arburst[2] = rapids_src_m_axi_arburst;
                assign xbar_m_arlock[2]  = rapids_src_m_axi_arlock;
                assign xbar_m_arcache[2] = rapids_src_m_axi_arcache;
                assign xbar_m_arprot[2]  = rapids_src_m_axi_arprot;
                assign xbar_m_arvalid[2] = rapids_src_m_axi_arvalid;
                assign rapids_src_m_axi_arready = xbar_m_arready[2];

                assign rapids_src_m_axi_rdata  = xbar_m_rdata[2];
                assign rapids_src_m_axi_rid    = xbar_m_rid[2];
                assign rapids_src_m_axi_rresp  = xbar_m_rresp[2];
                assign rapids_src_m_axi_rlast  = xbar_m_rlast[2];
                assign rapids_src_m_axi_rvalid = xbar_m_rvalid[2];
                assign xbar_m_rready[2] = rapids_src_m_axi_rready;


// Master 3: stream_master  - Direct connection (no width conversion)
// Master 3: stream_master  (direct connection)

                assign xbar_m_awaddr[3]  = stream_m_axi_awaddr;
                assign xbar_m_awid[3]    = stream_m_axi_awid;
                assign xbar_m_awlen[3]   = stream_m_axi_awlen;
                assign xbar_m_awsize[3]  = stream_m_axi_awsize;
                assign xbar_m_awburst[3] = stream_m_axi_awburst;
                assign xbar_m_awlock[3]  = stream_m_axi_awlock;
                assign xbar_m_awcache[3] = stream_m_axi_awcache;
                assign xbar_m_awprot[3]  = stream_m_axi_awprot;
                assign xbar_m_awvalid[3] = stream_m_axi_awvalid;
                assign stream_m_axi_awready = xbar_m_awready[3];

                assign xbar_m_wdata[3]  = stream_m_axi_wdata;
                assign xbar_m_wstrb[3]  = stream_m_axi_wstrb;
                assign xbar_m_wlast[3]  = stream_m_axi_wlast;
                assign xbar_m_wvalid[3] = stream_m_axi_wvalid;
                assign stream_m_axi_wready = xbar_m_wready[3];

                assign stream_m_axi_bid    = xbar_m_bid[3];
                assign stream_m_axi_bresp  = xbar_m_bresp[3];
                assign stream_m_axi_bvalid = xbar_m_bvalid[3];
                assign xbar_m_bready[3] = stream_m_axi_bready;

                assign xbar_m_araddr[3]  = stream_m_axi_araddr;
                assign xbar_m_arid[3]    = stream_m_axi_arid;
                assign xbar_m_arlen[3]   = stream_m_axi_arlen;
                assign xbar_m_arsize[3]  = stream_m_axi_arsize;
                assign xbar_m_arburst[3] = stream_m_axi_arburst;
                assign xbar_m_arlock[3]  = stream_m_axi_arlock;
                assign xbar_m_arcache[3] = stream_m_axi_arcache;
                assign xbar_m_arprot[3]  = stream_m_axi_arprot;
                assign xbar_m_arvalid[3] = stream_m_axi_arvalid;
                assign stream_m_axi_arready = xbar_m_arready[3];

                assign stream_m_axi_rdata  = xbar_m_rdata[3];
                assign stream_m_axi_rid    = xbar_m_rid[3];
                assign stream_m_axi_rresp  = xbar_m_rresp[3];
                assign stream_m_axi_rlast  = xbar_m_rlast[3];
                assign stream_m_axi_rvalid = xbar_m_rvalid[3];
                assign xbar_m_rready[3] = stream_m_axi_rready;


// Width Converter for Master 4: cpu_master [RW]
//   Upsize: 64b → 512b

        // Width Converter (WRITE) - Master 4: cpu_master
        axi4_dwidth_converter_wr #(
            .S_AXI_DATA_WIDTH(64),
            .M_AXI_DATA_WIDTH(512),
            .AXI_ID_WIDTH(4),
            .AXI_ADDR_WIDTH(32),
            .AXI_USER_WIDTH(1)
        ) u_wconv_m4_wr (
            .aclk         (aclk),
            .aresetn      (aresetn),
            // Slave interface (external master port)
            .s_axi_awid   (cpu_m_axi_awid),
            .s_axi_awaddr (cpu_m_axi_awaddr),
            .s_axi_awlen  (cpu_m_axi_awlen),
            .s_axi_awsize (cpu_m_axi_awsize),
            .s_axi_awburst(cpu_m_axi_awburst),
            .s_axi_awlock (cpu_m_axi_awlock),
            .s_axi_awcache(cpu_m_axi_awcache),
            .s_axi_awprot (cpu_m_axi_awprot),
            .s_axi_awqos  (4'b0),
            .s_axi_awregion(4'b0),
            .s_axi_awuser (1'b0),
            .s_axi_awvalid(cpu_m_axi_awvalid),
            .s_axi_awready(cpu_m_axi_awready),
            .s_axi_wdata  (cpu_m_axi_wdata),
            .s_axi_wstrb  (cpu_m_axi_wstrb),
            .s_axi_wlast  (cpu_m_axi_wlast),
            .s_axi_wuser  (1'b0),
            .s_axi_wvalid (cpu_m_axi_wvalid),
            .s_axi_wready (cpu_m_axi_wready),
            .s_axi_bid    (cpu_m_axi_bid),
            .s_axi_bresp  (cpu_m_axi_bresp),
            .s_axi_buser  (/* unused */),
            .s_axi_bvalid (cpu_m_axi_bvalid),
            .s_axi_bready (cpu_m_axi_bready),
            // Master interface (to crossbar)
            .m_axi_awid   (xbar_m_awid[4]),
            .m_axi_awaddr (xbar_m_awaddr[4]),
            .m_axi_awlen  (xbar_m_awlen[4]),
            .m_axi_awsize (xbar_m_awsize[4]),
            .m_axi_awburst(xbar_m_awburst[4]),
            .m_axi_awlock (xbar_m_awlock[4]),
            .m_axi_awcache(xbar_m_awcache[4]),
            .m_axi_awprot (xbar_m_awprot[4]),
            .m_axi_awqos  (/* unused */),
            .m_axi_awregion(/* unused */),
            .m_axi_awuser (/* unused */),
            .m_axi_awvalid(xbar_m_awvalid[4]),
            .m_axi_awready(xbar_m_awready[4]),
            .m_axi_wdata  (xbar_m_wdata[4]),
            .m_axi_wstrb  (xbar_m_wstrb[4]),
            .m_axi_wlast  (xbar_m_wlast[4]),
            .m_axi_wuser  (/* unused */),
            .m_axi_wvalid (xbar_m_wvalid[4]),
            .m_axi_wready (xbar_m_wready[4]),
            .m_axi_bid    (xbar_m_bid[4]),
            .m_axi_bresp  (xbar_m_bresp[4]),
            .m_axi_buser  (1'b0),
            .m_axi_bvalid (xbar_m_bvalid[4]),
            .m_axi_bready (xbar_m_bready[4])
        );

        // Width Converter (READ) - Master 4: cpu_master
        axi4_dwidth_converter_rd #(
            .S_AXI_DATA_WIDTH(64),
            .M_AXI_DATA_WIDTH(512),
            .AXI_ID_WIDTH(4),
            .AXI_ADDR_WIDTH(32),
            .AXI_USER_WIDTH(1)
        ) u_wconv_m4_rd (
            .aclk         (aclk),
            .aresetn      (aresetn),
            // Slave interface (external master port)
            .s_axi_arid   (cpu_m_axi_arid),
            .s_axi_araddr (cpu_m_axi_araddr),
            .s_axi_arlen  (cpu_m_axi_arlen),
            .s_axi_arsize (cpu_m_axi_arsize),
            .s_axi_arburst(cpu_m_axi_arburst),
            .s_axi_arlock (cpu_m_axi_arlock),
            .s_axi_arcache(cpu_m_axi_arcache),
            .s_axi_arprot (cpu_m_axi_arprot),
            .s_axi_arqos  (4'b0),
            .s_axi_arregion(4'b0),
            .s_axi_aruser (1'b0),
            .s_axi_arvalid(cpu_m_axi_arvalid),
            .s_axi_arready(cpu_m_axi_arready),
            .s_axi_rid    (cpu_m_axi_rid),
            .s_axi_rdata  (cpu_m_axi_rdata),
            .s_axi_rresp  (cpu_m_axi_rresp),
            .s_axi_rlast  (cpu_m_axi_rlast),
            .s_axi_ruser  (/* unused */),
            .s_axi_rvalid (cpu_m_axi_rvalid),
            .s_axi_rready (cpu_m_axi_rready),
            // Master interface (to crossbar)
            .m_axi_arid   (xbar_m_arid[4]),
            .m_axi_araddr (xbar_m_araddr[4]),
            .m_axi_arlen  (xbar_m_arlen[4]),
            .m_axi_arsize (xbar_m_arsize[4]),
            .m_axi_arburst(xbar_m_arburst[4]),
            .m_axi_arlock (xbar_m_arlock[4]),
            .m_axi_arcache(xbar_m_arcache[4]),
            .m_axi_arprot (xbar_m_arprot[4]),
            .m_axi_arqos  (/* unused */),
            .m_axi_arregion(/* unused */),
            .m_axi_aruser (/* unused */),
            .m_axi_arvalid(xbar_m_arvalid[4]),
            .m_axi_arready(xbar_m_arready[4]),
            .m_axi_rid    (xbar_m_rid[4]),
            .m_axi_rdata  (xbar_m_rdata[4]),
            .m_axi_rresp  (xbar_m_rresp[4]),
            .m_axi_rlast  (xbar_m_rlast[4]),
            .m_axi_ruser  (1'b0),
            .m_axi_rvalid (xbar_m_rvalid[4]),
            .m_axi_rready (xbar_m_rready[4])
        );
        

// ==============================================================================
// Slave Port Connections from Crossbar
// ==============================================================================

// Slave 0: ddr_controller - Direct connection (no conversion)
// Slave 0: ddr_controller (direct connection)

                assign ddr_s_axi_awaddr  = xbar_s_awaddr[0];
                assign ddr_s_axi_awid    = xbar_s_awid[0];
                assign ddr_s_axi_awlen   = xbar_s_awlen[0];
                assign ddr_s_axi_awsize  = xbar_s_awsize[0];
                assign ddr_s_axi_awburst = xbar_s_awburst[0];
                assign ddr_s_axi_awlock  = xbar_s_awlock[0];
                assign ddr_s_axi_awcache = xbar_s_awcache[0];
                assign ddr_s_axi_awprot  = xbar_s_awprot[0];
                assign ddr_s_axi_awvalid = xbar_s_awvalid[0];
                assign xbar_s_awready[0] = ddr_s_axi_awready;

                assign ddr_s_axi_wdata  = xbar_s_wdata[0];
                assign ddr_s_axi_wstrb  = xbar_s_wstrb[0];
                assign ddr_s_axi_wlast  = xbar_s_wlast[0];
                assign ddr_s_axi_wvalid = xbar_s_wvalid[0];
                assign xbar_s_wready[0] = ddr_s_axi_wready;

                assign xbar_s_bid[0]    = ddr_s_axi_bid;
                assign xbar_s_bresp[0]  = ddr_s_axi_bresp;
                assign xbar_s_bvalid[0] = ddr_s_axi_bvalid;
                assign ddr_s_axi_bready = xbar_s_bready[0];

                assign ddr_s_axi_araddr  = xbar_s_araddr[0];
                assign ddr_s_axi_arid    = xbar_s_arid[0];
                assign ddr_s_axi_arlen   = xbar_s_arlen[0];
                assign ddr_s_axi_arsize  = xbar_s_arsize[0];
                assign ddr_s_axi_arburst = xbar_s_arburst[0];
                assign ddr_s_axi_arlock  = xbar_s_arlock[0];
                assign ddr_s_axi_arcache = xbar_s_arcache[0];
                assign ddr_s_axi_arprot  = xbar_s_arprot[0];
                assign ddr_s_axi_arvalid = xbar_s_arvalid[0];
                assign xbar_s_arready[0] = ddr_s_axi_arready;

                assign xbar_s_rdata[0]  = ddr_s_axi_rdata;
                assign xbar_s_rid[0]    = ddr_s_axi_rid;
                assign xbar_s_rresp[0]  = ddr_s_axi_rresp;
                assign xbar_s_rlast[0]  = ddr_s_axi_rlast;
                assign xbar_s_rvalid[0] = ddr_s_axi_rvalid;
                assign ddr_s_axi_rready = xbar_s_rready[0];
                

// Slave 1: sram_buffer - Direct connection (no conversion)
// Slave 1: sram_buffer (direct connection)

                assign sram_s_axi_awaddr  = xbar_s_awaddr[1];
                assign sram_s_axi_awid    = xbar_s_awid[1];
                assign sram_s_axi_awlen   = xbar_s_awlen[1];
                assign sram_s_axi_awsize  = xbar_s_awsize[1];
                assign sram_s_axi_awburst = xbar_s_awburst[1];
                assign sram_s_axi_awlock  = xbar_s_awlock[1];
                assign sram_s_axi_awcache = xbar_s_awcache[1];
                assign sram_s_axi_awprot  = xbar_s_awprot[1];
                assign sram_s_axi_awvalid = xbar_s_awvalid[1];
                assign xbar_s_awready[1] = sram_s_axi_awready;

                assign sram_s_axi_wdata  = xbar_s_wdata[1];
                assign sram_s_axi_wstrb  = xbar_s_wstrb[1];
                assign sram_s_axi_wlast  = xbar_s_wlast[1];
                assign sram_s_axi_wvalid = xbar_s_wvalid[1];
                assign xbar_s_wready[1] = sram_s_axi_wready;

                assign xbar_s_bid[1]    = sram_s_axi_bid;
                assign xbar_s_bresp[1]  = sram_s_axi_bresp;
                assign xbar_s_bvalid[1] = sram_s_axi_bvalid;
                assign sram_s_axi_bready = xbar_s_bready[1];

                assign sram_s_axi_araddr  = xbar_s_araddr[1];
                assign sram_s_axi_arid    = xbar_s_arid[1];
                assign sram_s_axi_arlen   = xbar_s_arlen[1];
                assign sram_s_axi_arsize  = xbar_s_arsize[1];
                assign sram_s_axi_arburst = xbar_s_arburst[1];
                assign sram_s_axi_arlock  = xbar_s_arlock[1];
                assign sram_s_axi_arcache = xbar_s_arcache[1];
                assign sram_s_axi_arprot  = xbar_s_arprot[1];
                assign sram_s_axi_arvalid = xbar_s_arvalid[1];
                assign xbar_s_arready[1] = sram_s_axi_arready;

                assign xbar_s_rdata[1]  = sram_s_axi_rdata;
                assign xbar_s_rid[1]    = sram_s_axi_rid;
                assign xbar_s_rresp[1]  = sram_s_axi_rresp;
                assign xbar_s_rlast[1]  = sram_s_axi_rlast;
                assign xbar_s_rvalid[1] = sram_s_axi_rvalid;
                assign sram_s_axi_rready = xbar_s_rready[1];
                

// AXI2APB Converter for Slave 2: apb_periph0
//   Crossbar: 512b AXI4 → APB: 32b
// 
// NOTE: The axi4_to_apb_convert module uses packed signals.
//       A wrapper module or signal packing logic is required.
//       For CSV-generated bridges, consider using axi4_to_apb_shim
//       or creating a wrapper that converts unpacked → packed.
// 

        // TODO: AXI2APB Converter - Slave 2: apb_periph0
        //
        // Recommended approach:
        // 1. Create intermediate 32b AXI4 signals between crossbar and APB converter
        // 2. Instantiate width downsize converter (512b → 32b) if needed
        // 3. Instantiate axi4_to_apb_convert or create unpacked-signal wrapper
        // 4. Connect APB output signals to external port
        //
        // Example structure:
        //
        // logic [64-1:0] s2_axi_awaddr;
        // logic [7:0] s2_axi_awid;
        // ... (all AXI4 signals)
        //
        // axi4_to_apb_convert #(
        //     .AXI_ADDR_WIDTH(64),
        //     .AXI_DATA_WIDTH(32),
        //     .AXI_ID_WIDTH(8),
        //     .APB_ADDR_WIDTH(32),
        //     .APB_DATA_WIDTH(32)
        // ) u_axi2apb_s2 (
        //     .aclk    (aclk),
        //     .aresetn (aresetn),
        //     // AXI4 slave interface (from crossbar, packed signals)
        //     // ... packed signal connections
        //     // APB master interface
        //     .psel    (apb0_psel),
        //     .penable (apb0_penable),
        //     .paddr   (apb0_paddr),
        //     .pwrite  (apb0_pwrite),
        //     .pwdata  (apb0_pwdata),
        //     .pstrb   (apb0_pstrb),
        //     .pprot   (apb0_pprot),
        //     .pready  (apb0_pready),
        //     .prdata  (apb0_prdata),
        //     .pslverr (apb0_pslverr)
        // );
        

endmodule
