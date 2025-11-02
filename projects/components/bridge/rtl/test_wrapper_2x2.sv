// ==============================================================================
// Module: bridge_wrapper_2x2
// Purpose: Verilator-compatible wrapper for AXI4 bridge crossbar
// ==============================================================================
//
// This wrapper expands array ports into individual signals for
// Verilator VPI compatibility. The core bridge uses arrays internally.
//
// Configuration: 2x2, DW=32, AW=32, ID=4
//
// Internal array signals for core bridge
logic [ADDR_WIDTH-1:0]   core_s_axi_awaddr  [NUM_MASTERS];
logic [ID_WIDTH-1:0]     core_s_axi_awid    [NUM_MASTERS];
logic [7:0]              core_s_axi_awlen   [NUM_MASTERS];
logic [2:0]              core_s_axi_awsize  [NUM_MASTERS];
logic [1:0]              core_s_axi_awburst [NUM_MASTERS];
logic                    core_s_axi_awlock  [NUM_MASTERS];
logic [3:0]              core_s_axi_awcache [NUM_MASTERS];
logic [2:0]              core_s_axi_awprot  [NUM_MASTERS];
logic                    core_s_axi_awvalid [NUM_MASTERS];
logic                    core_s_axi_awready [NUM_MASTERS];
//
logic [DATA_WIDTH-1:0]   core_s_axi_wdata  [NUM_MASTERS];
logic [STRB_WIDTH-1:0]   core_s_axi_wstrb  [NUM_MASTERS];
logic                    core_s_axi_wlast  [NUM_MASTERS];
logic                    core_s_axi_wvalid [NUM_MASTERS];
logic                    core_s_axi_wready [NUM_MASTERS];
//
logic [ID_WIDTH-1:0]     core_s_axi_bid    [NUM_MASTERS];
logic [1:0]              core_s_axi_bresp  [NUM_MASTERS];
logic                    core_s_axi_bvalid [NUM_MASTERS];
logic                    core_s_axi_bready [NUM_MASTERS];
//
logic [ADDR_WIDTH-1:0]   core_s_axi_araddr  [NUM_MASTERS];
logic [ID_WIDTH-1:0]     core_s_axi_arid    [NUM_MASTERS];
logic [7:0]              core_s_axi_arlen   [NUM_MASTERS];
logic [2:0]              core_s_axi_arsize  [NUM_MASTERS];
logic [1:0]              core_s_axi_arburst [NUM_MASTERS];
logic                    core_s_axi_arlock  [NUM_MASTERS];
logic [3:0]              core_s_axi_arcache [NUM_MASTERS];
logic [2:0]              core_s_axi_arprot  [NUM_MASTERS];
logic                    core_s_axi_arvalid [NUM_MASTERS];
logic                    core_s_axi_arready [NUM_MASTERS];
//
logic [DATA_WIDTH-1:0]   core_s_axi_rdata  [NUM_MASTERS];
logic [ID_WIDTH-1:0]     core_s_axi_rid    [NUM_MASTERS];
logic [1:0]              core_s_axi_rresp  [NUM_MASTERS];
logic                    core_s_axi_rlast  [NUM_MASTERS];
logic                    core_s_axi_rvalid [NUM_MASTERS];
logic                    core_s_axi_rready [NUM_MASTERS];
//
logic [ADDR_WIDTH-1:0]   core_m_axi_awaddr  [NUM_SLAVES];
logic [ID_WIDTH-1:0]     core_m_axi_awid    [NUM_SLAVES];
logic [7:0]              core_m_axi_awlen   [NUM_SLAVES];
logic [2:0]              core_m_axi_awsize  [NUM_SLAVES];
logic [1:0]              core_m_axi_awburst [NUM_SLAVES];
logic                    core_m_axi_awlock  [NUM_SLAVES];
logic [3:0]              core_m_axi_awcache [NUM_SLAVES];
logic [2:0]              core_m_axi_awprot  [NUM_SLAVES];
logic                    core_m_axi_awvalid [NUM_SLAVES];
logic                    core_m_axi_awready [NUM_SLAVES];
//
logic [DATA_WIDTH-1:0]   core_m_axi_wdata  [NUM_SLAVES];
logic [STRB_WIDTH-1:0]   core_m_axi_wstrb  [NUM_SLAVES];
logic                    core_m_axi_wlast  [NUM_SLAVES];
logic                    core_m_axi_wvalid [NUM_SLAVES];
logic                    core_m_axi_wready [NUM_SLAVES];
//
logic [ID_WIDTH-1:0]     core_m_axi_bid    [NUM_SLAVES];
logic [1:0]              core_m_axi_bresp  [NUM_SLAVES];
logic                    core_m_axi_bvalid [NUM_SLAVES];
logic                    core_m_axi_bready [NUM_SLAVES];
//
logic [ADDR_WIDTH-1:0]   core_m_axi_araddr  [NUM_SLAVES];
logic [ID_WIDTH-1:0]     core_m_axi_arid    [NUM_SLAVES];
logic [7:0]              core_m_axi_arlen   [NUM_SLAVES];
logic [2:0]              core_m_axi_arsize  [NUM_SLAVES];
logic [1:0]              core_m_axi_arburst [NUM_SLAVES];
logic                    core_m_axi_arlock  [NUM_SLAVES];
logic [3:0]              core_m_axi_arcache [NUM_SLAVES];
logic [2:0]              core_m_axi_arprot  [NUM_SLAVES];
logic                    core_m_axi_arvalid [NUM_SLAVES];
logic                    core_m_axi_arready [NUM_SLAVES];
//
logic [DATA_WIDTH-1:0]   core_m_axi_rdata  [NUM_SLAVES];
logic [ID_WIDTH-1:0]     core_m_axi_rid    [NUM_SLAVES];
logic [1:0]              core_m_axi_rresp  [NUM_SLAVES];
logic                    core_m_axi_rlast  [NUM_SLAVES];
logic                    core_m_axi_rvalid [NUM_SLAVES];
logic                    core_m_axi_rready [NUM_SLAVES];
//
// Connect individual master signals to internal arrays
// Master 0 connections
assign core_s_axi_awaddr[0]  = s0_axi_awaddr;
assign core_s_axi_awid[0]    = s0_axi_awid;
assign core_s_axi_awlen[0]   = s0_axi_awlen;
assign core_s_axi_awsize[0]  = s0_axi_awsize;
assign core_s_axi_awburst[0] = s0_axi_awburst;
assign core_s_axi_awlock[0]  = s0_axi_awlock;
assign core_s_axi_awcache[0] = s0_axi_awcache;
assign core_s_axi_awprot[0]  = s0_axi_awprot;
assign core_s_axi_awvalid[0] = s0_axi_awvalid;
assign s0_axi_awready = core_s_axi_awready[0];
//
assign core_s_axi_wdata[0]  = s0_axi_wdata;
assign core_s_axi_wstrb[0]  = s0_axi_wstrb;
assign core_s_axi_wlast[0]  = s0_axi_wlast;
assign core_s_axi_wvalid[0] = s0_axi_wvalid;
assign s0_axi_wready = core_s_axi_wready[0];
//
assign s0_axi_bid   = core_s_axi_bid[0];
assign s0_axi_bresp = core_s_axi_bresp[0];
assign s0_axi_bvalid = core_s_axi_bvalid[0];
assign core_s_axi_bready[0] = s0_axi_bready;
//
assign core_s_axi_araddr[0]  = s0_axi_araddr;
assign core_s_axi_arid[0]    = s0_axi_arid;
assign core_s_axi_arlen[0]   = s0_axi_arlen;
assign core_s_axi_arsize[0]  = s0_axi_arsize;
assign core_s_axi_arburst[0] = s0_axi_arburst;
assign core_s_axi_arlock[0]  = s0_axi_arlock;
assign core_s_axi_arcache[0] = s0_axi_arcache;
assign core_s_axi_arprot[0]  = s0_axi_arprot;
assign core_s_axi_arvalid[0] = s0_axi_arvalid;
assign s0_axi_arready = core_s_axi_arready[0];
//
assign s0_axi_rdata  = core_s_axi_rdata[0];
assign s0_axi_rid    = core_s_axi_rid[0];
assign s0_axi_rresp  = core_s_axi_rresp[0];
assign s0_axi_rlast  = core_s_axi_rlast[0];
assign s0_axi_rvalid = core_s_axi_rvalid[0];
assign core_s_axi_rready[0] = s0_axi_rready;
//
// Master 1 connections
assign core_s_axi_awaddr[1]  = s1_axi_awaddr;
assign core_s_axi_awid[1]    = s1_axi_awid;
assign core_s_axi_awlen[1]   = s1_axi_awlen;
assign core_s_axi_awsize[1]  = s1_axi_awsize;
assign core_s_axi_awburst[1] = s1_axi_awburst;
assign core_s_axi_awlock[1]  = s1_axi_awlock;
assign core_s_axi_awcache[1] = s1_axi_awcache;
assign core_s_axi_awprot[1]  = s1_axi_awprot;
assign core_s_axi_awvalid[1] = s1_axi_awvalid;
assign s1_axi_awready = core_s_axi_awready[1];
//
assign core_s_axi_wdata[1]  = s1_axi_wdata;
assign core_s_axi_wstrb[1]  = s1_axi_wstrb;
assign core_s_axi_wlast[1]  = s1_axi_wlast;
assign core_s_axi_wvalid[1] = s1_axi_wvalid;
assign s1_axi_wready = core_s_axi_wready[1];
//
assign s1_axi_bid   = core_s_axi_bid[1];
assign s1_axi_bresp = core_s_axi_bresp[1];
assign s1_axi_bvalid = core_s_axi_bvalid[1];
assign core_s_axi_bready[1] = s1_axi_bready;
//
assign core_s_axi_araddr[1]  = s1_axi_araddr;
assign core_s_axi_arid[1]    = s1_axi_arid;
assign core_s_axi_arlen[1]   = s1_axi_arlen;
assign core_s_axi_arsize[1]  = s1_axi_arsize;
assign core_s_axi_arburst[1] = s1_axi_arburst;
assign core_s_axi_arlock[1]  = s1_axi_arlock;
assign core_s_axi_arcache[1] = s1_axi_arcache;
assign core_s_axi_arprot[1]  = s1_axi_arprot;
assign core_s_axi_arvalid[1] = s1_axi_arvalid;
assign s1_axi_arready = core_s_axi_arready[1];
//
assign s1_axi_rdata  = core_s_axi_rdata[1];
assign s1_axi_rid    = core_s_axi_rid[1];
assign s1_axi_rresp  = core_s_axi_rresp[1];
assign s1_axi_rlast  = core_s_axi_rlast[1];
assign s1_axi_rvalid = core_s_axi_rvalid[1];
assign core_s_axi_rready[1] = s1_axi_rready;
//
// Connect individual slave signals to internal arrays
// Slave 0 connections
assign m0_axi_awaddr  = core_m_axi_awaddr[0];
assign m0_axi_awid    = core_m_axi_awid[0];
assign m0_axi_awlen   = core_m_axi_awlen[0];
assign m0_axi_awsize  = core_m_axi_awsize[0];
assign m0_axi_awburst = core_m_axi_awburst[0];
assign m0_axi_awlock  = core_m_axi_awlock[0];
assign m0_axi_awcache = core_m_axi_awcache[0];
assign m0_axi_awprot  = core_m_axi_awprot[0];
assign m0_axi_awvalid = core_m_axi_awvalid[0];
assign core_m_axi_awready[0] = m0_axi_awready;
//
assign m0_axi_wdata  = core_m_axi_wdata[0];
assign m0_axi_wstrb  = core_m_axi_wstrb[0];
assign m0_axi_wlast  = core_m_axi_wlast[0];
assign m0_axi_wvalid = core_m_axi_wvalid[0];
assign core_m_axi_wready[0] = m0_axi_wready;
//
assign core_m_axi_bid[0]   = m0_axi_bid;
assign core_m_axi_bresp[0] = m0_axi_bresp;
assign core_m_axi_bvalid[0] = m0_axi_bvalid;
assign m0_axi_bready = core_m_axi_bready[0];
//
assign m0_axi_araddr  = core_m_axi_araddr[0];
assign m0_axi_arid    = core_m_axi_arid[0];
assign m0_axi_arlen   = core_m_axi_arlen[0];
assign m0_axi_arsize  = core_m_axi_arsize[0];
assign m0_axi_arburst = core_m_axi_arburst[0];
assign m0_axi_arlock  = core_m_axi_arlock[0];
assign m0_axi_arcache = core_m_axi_arcache[0];
assign m0_axi_arprot  = core_m_axi_arprot[0];
assign m0_axi_arvalid = core_m_axi_arvalid[0];
assign core_m_axi_arready[0] = m0_axi_arready;
//
assign core_m_axi_rdata[0]  = m0_axi_rdata;
assign core_m_axi_rid[0]    = m0_axi_rid;
assign core_m_axi_rresp[0]  = m0_axi_rresp;
assign core_m_axi_rlast[0]  = m0_axi_rlast;
assign core_m_axi_rvalid[0] = m0_axi_rvalid;
assign m0_axi_rready = core_m_axi_rready[0];
//
// Slave 1 connections
assign m1_axi_awaddr  = core_m_axi_awaddr[1];
assign m1_axi_awid    = core_m_axi_awid[1];
assign m1_axi_awlen   = core_m_axi_awlen[1];
assign m1_axi_awsize  = core_m_axi_awsize[1];
assign m1_axi_awburst = core_m_axi_awburst[1];
assign m1_axi_awlock  = core_m_axi_awlock[1];
assign m1_axi_awcache = core_m_axi_awcache[1];
assign m1_axi_awprot  = core_m_axi_awprot[1];
assign m1_axi_awvalid = core_m_axi_awvalid[1];
assign core_m_axi_awready[1] = m1_axi_awready;
//
assign m1_axi_wdata  = core_m_axi_wdata[1];
assign m1_axi_wstrb  = core_m_axi_wstrb[1];
assign m1_axi_wlast  = core_m_axi_wlast[1];
assign m1_axi_wvalid = core_m_axi_wvalid[1];
assign core_m_axi_wready[1] = m1_axi_wready;
//
assign core_m_axi_bid[1]   = m1_axi_bid;
assign core_m_axi_bresp[1] = m1_axi_bresp;
assign core_m_axi_bvalid[1] = m1_axi_bvalid;
assign m1_axi_bready = core_m_axi_bready[1];
//
assign m1_axi_araddr  = core_m_axi_araddr[1];
assign m1_axi_arid    = core_m_axi_arid[1];
assign m1_axi_arlen   = core_m_axi_arlen[1];
assign m1_axi_arsize  = core_m_axi_arsize[1];
assign m1_axi_arburst = core_m_axi_arburst[1];
assign m1_axi_arlock  = core_m_axi_arlock[1];
assign m1_axi_arcache = core_m_axi_arcache[1];
assign m1_axi_arprot  = core_m_axi_arprot[1];
assign m1_axi_arvalid = core_m_axi_arvalid[1];
assign core_m_axi_arready[1] = m1_axi_arready;
//
assign core_m_axi_rdata[1]  = m1_axi_rdata;
assign core_m_axi_rid[1]    = m1_axi_rid;
assign core_m_axi_rresp[1]  = m1_axi_rresp;
assign core_m_axi_rlast[1]  = m1_axi_rlast;
assign core_m_axi_rvalid[1] = m1_axi_rvalid;
assign m1_axi_rready = core_m_axi_rready[1];
//
// ==============================================================================
// Core Bridge Instantiation
// ==============================================================================
//
bridge_axi4_flat_2x2 #(
    .NUM_MASTERS (NUM_MASTERS),
    .NUM_SLAVES  (NUM_SLAVES),
    .DATA_WIDTH  (DATA_WIDTH),
    .ADDR_WIDTH  (ADDR_WIDTH),
    .ID_WIDTH    (ID_WIDTH)
) u_core (
    .aclk    (aclk),
    .aresetn (aresetn),
//
    // Master interfaces (arrays)
    .s_axi_awaddr  (core_s_axi_awaddr),
    .s_axi_awid    (core_s_axi_awid),
    .s_axi_awlen   (core_s_axi_awlen),
    .s_axi_awsize  (core_s_axi_awsize),
    .s_axi_awburst (core_s_axi_awburst),
    .s_axi_awlock  (core_s_axi_awlock),
    .s_axi_awcache (core_s_axi_awcache),
    .s_axi_awprot  (core_s_axi_awprot),
    .s_axi_awvalid (core_s_axi_awvalid),
    .s_axi_awready (core_s_axi_awready),
//
    .s_axi_wdata  (core_s_axi_wdata),
    .s_axi_wstrb  (core_s_axi_wstrb),
    .s_axi_wlast  (core_s_axi_wlast),
    .s_axi_wvalid (core_s_axi_wvalid),
    .s_axi_wready (core_s_axi_wready),
//
    .s_axi_bid    (core_s_axi_bid),
    .s_axi_bresp  (core_s_axi_bresp),
    .s_axi_bvalid (core_s_axi_bvalid),
    .s_axi_bready (core_s_axi_bready),
//
    .s_axi_araddr  (core_s_axi_araddr),
    .s_axi_arid    (core_s_axi_arid),
    .s_axi_arlen   (core_s_axi_arlen),
    .s_axi_arsize  (core_s_axi_arsize),
    .s_axi_arburst (core_s_axi_arburst),
    .s_axi_arlock  (core_s_axi_arlock),
    .s_axi_arcache (core_s_axi_arcache),
    .s_axi_arprot  (core_s_axi_arprot),
    .s_axi_arvalid (core_s_axi_arvalid),
    .s_axi_arready (core_s_axi_arready),
//
    .s_axi_rdata  (core_s_axi_rdata),
    .s_axi_rid    (core_s_axi_rid),
    .s_axi_rresp  (core_s_axi_rresp),
    .s_axi_rlast  (core_s_axi_rlast),
    .s_axi_rvalid (core_s_axi_rvalid),
    .s_axi_rready (core_s_axi_rready),
//
    // Slave interfaces (arrays)
    .m_axi_awaddr  (core_m_axi_awaddr),
    .m_axi_awid    (core_m_axi_awid),
    .m_axi_awlen   (core_m_axi_awlen),
    .m_axi_awsize  (core_m_axi_awsize),
    .m_axi_awburst (core_m_axi_awburst),
    .m_axi_awlock  (core_m_axi_awlock),
    .m_axi_awcache (core_m_axi_awcache),
    .m_axi_awprot  (core_m_axi_awprot),
    .m_axi_awvalid (core_m_axi_awvalid),
    .m_axi_awready (core_m_axi_awready),
//
    .m_axi_wdata  (core_m_axi_wdata),
    .m_axi_wstrb  (core_m_axi_wstrb),
    .m_axi_wlast  (core_m_axi_wlast),
    .m_axi_wvalid (core_m_axi_wvalid),
    .m_axi_wready (core_m_axi_wready),
//
    .m_axi_bid    (core_m_axi_bid),
    .m_axi_bresp  (core_m_axi_bresp),
    .m_axi_bvalid (core_m_axi_bvalid),
    .m_axi_bready (core_m_axi_bready),
//
    .m_axi_araddr  (core_m_axi_araddr),
    .m_axi_arid    (core_m_axi_arid),
    .m_axi_arlen   (core_m_axi_arlen),
    .m_axi_arsize  (core_m_axi_arsize),
    .m_axi_arburst (core_m_axi_arburst),
    .m_axi_arlock  (core_m_axi_arlock),
    .m_axi_arcache (core_m_axi_arcache),
    .m_axi_arprot  (core_m_axi_arprot),
    .m_axi_arvalid (core_m_axi_arvalid),
    .m_axi_arready (core_m_axi_arready),
//
    .m_axi_rdata  (core_m_axi_rdata),
    .m_axi_rid    (core_m_axi_rid),
    .m_axi_rresp  (core_m_axi_rresp),
    .m_axi_rlast  (core_m_axi_rlast),
    .m_axi_rvalid (core_m_axi_rvalid),
    .m_axi_rready (core_m_axi_rready)
);
//
