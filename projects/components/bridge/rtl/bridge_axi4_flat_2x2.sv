`timescale 1ns / 1ps

module bridge_axi4_flat_2x2 #(parameter int  NUM_MASTERS = 2,
parameter int  NUM_SLAVES = 2,
parameter int  DATA_WIDTH = 32,
parameter int  ADDR_WIDTH = 32,
parameter int  ID_WIDTH = 4,
parameter int  STRB_WIDTH = 4 )(
    input  logic                  aclk,
    input  logic                  aresetn,
    input  logic [ADDR_WIDTH-1:0] s_axi_awaddr  [NUM_MASTERS],
    input  logic [ID_WIDTH-1:0]   s_axi_awid    [NUM_MASTERS],
    input  logic [7:0]            s_axi_awlen   [NUM_MASTERS],
    input  logic [2:0]            s_axi_awsize  [NUM_MASTERS],
    input  logic [1:0]            s_axi_awburst [NUM_MASTERS],
    input  logic                  s_axi_awlock  [NUM_MASTERS],
    input  logic [3:0]            s_axi_awcache [NUM_MASTERS],
    input  logic [2:0]            s_axi_awprot  [NUM_MASTERS],
    input  logic                  s_axi_awvalid [NUM_MASTERS],
    output logic                  s_axi_awready [NUM_MASTERS],
    input  logic [DATA_WIDTH-1:0] s_axi_wdata   [NUM_MASTERS],
    input  logic [STRB_WIDTH-1:0] s_axi_wstrb   [NUM_MASTERS],
    input  logic                  s_axi_wlast   [NUM_MASTERS],
    input  logic                  s_axi_wvalid  [NUM_MASTERS],
    output logic                  s_axi_wready  [NUM_MASTERS],
    output logic [ID_WIDTH-1:0]   s_axi_bid     [NUM_MASTERS],
    output logic [1:0]            s_axi_bresp   [NUM_MASTERS],
    output logic                  s_axi_bvalid  [NUM_MASTERS],
    input  logic                  s_axi_bready  [NUM_MASTERS],
    input  logic [ADDR_WIDTH-1:0] s_axi_araddr  [NUM_MASTERS],
    input  logic [ID_WIDTH-1:0]   s_axi_arid    [NUM_MASTERS],
    input  logic [7:0]            s_axi_arlen   [NUM_MASTERS],
    input  logic [2:0]            s_axi_arsize  [NUM_MASTERS],
    input  logic [1:0]            s_axi_arburst [NUM_MASTERS],
    input  logic                  s_axi_arlock  [NUM_MASTERS],
    input  logic [3:0]            s_axi_arcache [NUM_MASTERS],
    input  logic [2:0]            s_axi_arprot  [NUM_MASTERS],
    input  logic                  s_axi_arvalid [NUM_MASTERS],
    output logic                  s_axi_arready [NUM_MASTERS],
    output logic [DATA_WIDTH-1:0] s_axi_rdata   [NUM_MASTERS],
    output logic [ID_WIDTH-1:0]   s_axi_rid     [NUM_MASTERS],
    output logic [1:0]            s_axi_rresp   [NUM_MASTERS],
    output logic                  s_axi_rlast   [NUM_MASTERS],
    output logic                  s_axi_rvalid  [NUM_MASTERS],
    input  logic                  s_axi_rready  [NUM_MASTERS],
    output logic [ADDR_WIDTH-1:0] m_axi_awaddr  [NUM_SLAVES],
    output logic [ID_WIDTH-1:0]   m_axi_awid    [NUM_SLAVES],
    output logic [7:0]            m_axi_awlen   [NUM_SLAVES],
    output logic [2:0]            m_axi_awsize  [NUM_SLAVES],
    output logic [1:0]            m_axi_awburst [NUM_SLAVES],
    output logic                  m_axi_awlock  [NUM_SLAVES],
    output logic [3:0]            m_axi_awcache [NUM_SLAVES],
    output logic [2:0]            m_axi_awprot  [NUM_SLAVES],
    output logic                  m_axi_awvalid [NUM_SLAVES],
    input  logic                  m_axi_awready [NUM_SLAVES],
    output logic [DATA_WIDTH-1:0] m_axi_wdata   [NUM_SLAVES],
    output logic [STRB_WIDTH-1:0] m_axi_wstrb   [NUM_SLAVES],
    output logic                  m_axi_wlast   [NUM_SLAVES],
    output logic                  m_axi_wvalid  [NUM_SLAVES],
    input  logic                  m_axi_wready  [NUM_SLAVES],
    input  logic [ID_WIDTH-1:0]   m_axi_bid     [NUM_SLAVES],
    input  logic [1:0]            m_axi_bresp   [NUM_SLAVES],
    input  logic                  m_axi_bvalid  [NUM_SLAVES],
    output logic                  m_axi_bready  [NUM_SLAVES],
    output logic [ADDR_WIDTH-1:0] m_axi_araddr  [NUM_SLAVES],
    output logic [ID_WIDTH-1:0]   m_axi_arid    [NUM_SLAVES],
    output logic [7:0]            m_axi_arlen   [NUM_SLAVES],
    output logic [2:0]            m_axi_arsize  [NUM_SLAVES],
    output logic [1:0]            m_axi_arburst [NUM_SLAVES],
    output logic                  m_axi_arlock  [NUM_SLAVES],
    output logic [3:0]            m_axi_arcache [NUM_SLAVES],
    output logic [2:0]            m_axi_arprot  [NUM_SLAVES],
    output logic                  m_axi_arvalid [NUM_SLAVES],
    input  logic                  m_axi_arready [NUM_SLAVES],
    input  logic [DATA_WIDTH-1:0] m_axi_rdata   [NUM_SLAVES],
    input  logic [ID_WIDTH-1:0]   m_axi_rid     [NUM_SLAVES],
    input  logic [1:0]            m_axi_rresp   [NUM_SLAVES],
    input  logic                  m_axi_rlast   [NUM_SLAVES],
    input  logic                  m_axi_rvalid  [NUM_SLAVES],
    output logic                  m_axi_rready  [NUM_SLAVES]
);

// ==============================================================================
// Module: bridge_axi4_flat_2x2
// Project: Bridge - AXI4 Full Crossbar Generator
// ==============================================================================
// Description: AXI4 2×2 Full Crossbar
// 
// Bridge: Connecting masters and slaves across the divide
// 
// Generated by: bridge_generator.py (framework version)
// Configuration:
//   - Masters: 2
//   - Slaves: 2
//   - Data Width: 32 bits
//   - Address Width: 32 bits
//   - ID Width: 4 bits
// 
// Architecture:
//   - AMBA axi4_slave_wr/rd components on master-side interfaces
//   - Internal crossbar routing with standard arbitration
//   - AMBA axi4_master_wr/rd components on slave-side interfaces
// 
// Features:
//   - Full 5-channel AXI4 protocol (AW, W, B, AR, R)
//   - Out-of-order transaction support (ID-based routing)
//   - Separate read/write arbitration (no head-of-line blocking)
//   - Burst transfer optimization (grant locking until xlast)
//   - Configurable skid buffers (AW=2, W=4, B=2, AR=2, R=4)
// 
// ==============================================================================

// ==========================================================================
// Internal Crossbar Signals
// ==========================================================================
// Master-side AMBA components (axi4_slave_wr/rd) output to xbar_s_axi_*
// Crossbar routes xbar_s_axi_* to xbar_m_axi_*
// Slave-side AMBA components (axi4_master_wr/rd) input from xbar_m_axi_*
// ==========================================================================

// Signals from axi4_slave_wr/rd to crossbar (NUM_MASTERS sets)
// Write address channel
logic [ADDR_WIDTH-1:0]   xbar_s_axi_awaddr  [NUM_MASTERS];
logic [ID_WIDTH-1:0]     xbar_s_axi_awid    [NUM_MASTERS];
logic [7:0]              xbar_s_axi_awlen   [NUM_MASTERS];
logic [2:0]              xbar_s_axi_awsize  [NUM_MASTERS];
logic [1:0]              xbar_s_axi_awburst [NUM_MASTERS];
logic                    xbar_s_axi_awlock  [NUM_MASTERS];
logic [3:0]              xbar_s_axi_awcache [NUM_MASTERS];
logic [2:0]              xbar_s_axi_awprot  [NUM_MASTERS];
logic [3:0]              xbar_s_axi_awqos   [NUM_MASTERS];
logic [3:0]              xbar_s_axi_awregion [NUM_MASTERS];
logic                    xbar_s_axi_awvalid [NUM_MASTERS];
logic                    xbar_s_axi_awready [NUM_MASTERS];

// Write data channel
logic [DATA_WIDTH-1:0]   xbar_s_axi_wdata  [NUM_MASTERS];
logic [STRB_WIDTH-1:0]   xbar_s_axi_wstrb  [NUM_MASTERS];
logic                    xbar_s_axi_wlast  [NUM_MASTERS];
logic                    xbar_s_axi_wvalid [NUM_MASTERS];
logic                    xbar_s_axi_wready [NUM_MASTERS];

// Write response channel
logic [ID_WIDTH-1:0]     xbar_s_axi_bid    [NUM_MASTERS];
logic [1:0]              xbar_s_axi_bresp  [NUM_MASTERS];
logic                    xbar_s_axi_bvalid [NUM_MASTERS];
logic                    xbar_s_axi_bready [NUM_MASTERS];

// Read address channel
logic [ADDR_WIDTH-1:0]   xbar_s_axi_araddr  [NUM_MASTERS];
logic [ID_WIDTH-1:0]     xbar_s_axi_arid    [NUM_MASTERS];
logic [7:0]              xbar_s_axi_arlen   [NUM_MASTERS];
logic [2:0]              xbar_s_axi_arsize  [NUM_MASTERS];
logic [1:0]              xbar_s_axi_arburst [NUM_MASTERS];
logic                    xbar_s_axi_arlock  [NUM_MASTERS];
logic [3:0]              xbar_s_axi_arcache [NUM_MASTERS];
logic [2:0]              xbar_s_axi_arprot  [NUM_MASTERS];
logic [3:0]              xbar_s_axi_arqos   [NUM_MASTERS];
logic [3:0]              xbar_s_axi_arregion [NUM_MASTERS];
logic                    xbar_s_axi_arvalid [NUM_MASTERS];
logic                    xbar_s_axi_arready [NUM_MASTERS];

// Read data channel
logic [DATA_WIDTH-1:0]   xbar_s_axi_rdata  [NUM_MASTERS];
logic [ID_WIDTH-1:0]     xbar_s_axi_rid    [NUM_MASTERS];
logic [1:0]              xbar_s_axi_rresp  [NUM_MASTERS];
logic                    xbar_s_axi_rlast  [NUM_MASTERS];
logic                    xbar_s_axi_rvalid [NUM_MASTERS];
logic                    xbar_s_axi_rready [NUM_MASTERS];

// Signals from crossbar to axi4_master_wr/rd (NUM_SLAVES sets)
// Write address channel
logic [ADDR_WIDTH-1:0]   xbar_m_axi_awaddr  [NUM_SLAVES];
logic [ID_WIDTH-1:0]     xbar_m_axi_awid    [NUM_SLAVES];
logic [7:0]              xbar_m_axi_awlen   [NUM_SLAVES];
logic [2:0]              xbar_m_axi_awsize  [NUM_SLAVES];
logic [1:0]              xbar_m_axi_awburst [NUM_SLAVES];
logic                    xbar_m_axi_awlock  [NUM_SLAVES];
logic [3:0]              xbar_m_axi_awcache [NUM_SLAVES];
logic [2:0]              xbar_m_axi_awprot  [NUM_SLAVES];
logic [3:0]              xbar_m_axi_awqos   [NUM_SLAVES];
logic [3:0]              xbar_m_axi_awregion [NUM_SLAVES];
logic                    xbar_m_axi_awvalid [NUM_SLAVES];
logic                    xbar_m_axi_awready [NUM_SLAVES];

// Write data channel
logic [DATA_WIDTH-1:0]   xbar_m_axi_wdata  [NUM_SLAVES];
logic [STRB_WIDTH-1:0]   xbar_m_axi_wstrb  [NUM_SLAVES];
logic                    xbar_m_axi_wlast  [NUM_SLAVES];
logic                    xbar_m_axi_wvalid [NUM_SLAVES];
logic                    xbar_m_axi_wready [NUM_SLAVES];

// Write response channel
logic [ID_WIDTH-1:0]     xbar_m_axi_bid    [NUM_SLAVES];
logic [1:0]              xbar_m_axi_bresp  [NUM_SLAVES];
logic                    xbar_m_axi_bvalid [NUM_SLAVES];
logic                    xbar_m_axi_bready [NUM_SLAVES];

// Read address channel
logic [ADDR_WIDTH-1:0]   xbar_m_axi_araddr  [NUM_SLAVES];
logic [ID_WIDTH-1:0]     xbar_m_axi_arid    [NUM_SLAVES];
logic [7:0]              xbar_m_axi_arlen   [NUM_SLAVES];
logic [2:0]              xbar_m_axi_arsize  [NUM_SLAVES];
logic [1:0]              xbar_m_axi_arburst [NUM_SLAVES];
logic                    xbar_m_axi_arlock  [NUM_SLAVES];
logic [3:0]              xbar_m_axi_arcache [NUM_SLAVES];
logic [2:0]              xbar_m_axi_arprot  [NUM_SLAVES];
logic [3:0]              xbar_m_axi_arqos   [NUM_SLAVES];
logic [3:0]              xbar_m_axi_arregion [NUM_SLAVES];
logic                    xbar_m_axi_arvalid [NUM_SLAVES];
logic                    xbar_m_axi_arready [NUM_SLAVES];

// Read data channel
logic [DATA_WIDTH-1:0]   xbar_m_axi_rdata  [NUM_SLAVES];
logic [ID_WIDTH-1:0]     xbar_m_axi_rid    [NUM_SLAVES];
logic [1:0]              xbar_m_axi_rresp  [NUM_SLAVES];
logic                    xbar_m_axi_rlast  [NUM_SLAVES];
logic                    xbar_m_axi_rvalid [NUM_SLAVES];
logic                    xbar_m_axi_rready [NUM_SLAVES];

// ==========================================================================
// Master-Side AMBA Components (axi4_slave_wr and axi4_slave_rd)
// ==========================================================================
// Accept connections from external masters with skid buffers and flow control
// Configuration: SKID_DEPTH_AW=2, W=4, B=2, AR=2, R=4
// ==========================================================================

generate
    for (genvar m = 0; m < NUM_MASTERS; m++) begin : gen_master_side_amba

//         Write path: axi4_slave_wr for AW, W, B channels
        axi4_slave_wr #(
            .AXI_ID_WIDTH(ID_WIDTH),
            .AXI_ADDR_WIDTH(ADDR_WIDTH),
            .AXI_DATA_WIDTH(DATA_WIDTH),
            .SKID_DEPTH_AW(2),
            .SKID_DEPTH_W(4),
            .SKID_DEPTH_B(2)
        ) u_master_wr (
            .aclk(aclk),
            .aresetn(aresetn),

//             External master interface (s_axi_* from outside)
            .s_axi_awid(s_axi_awid[m]),
            .s_axi_awaddr(s_axi_awaddr[m]),
            .s_axi_awlen(s_axi_awlen[m]),
            .s_axi_awsize(s_axi_awsize[m]),
            .s_axi_awburst(s_axi_awburst[m]),
            .s_axi_awlock(s_axi_awlock[m]),
            .s_axi_awcache(s_axi_awcache[m]),
            .s_axi_awprot(s_axi_awprot[m]),
            .s_axi_awvalid(s_axi_awvalid[m]),
            .s_axi_awready(s_axi_awready[m]),

            .s_axi_wdata(s_axi_wdata[m]),
            .s_axi_wstrb(s_axi_wstrb[m]),
            .s_axi_wlast(s_axi_wlast[m]),
            .s_axi_wvalid(s_axi_wvalid[m]),
            .s_axi_wready(s_axi_wready[m]),

            .s_axi_bid(s_axi_bid[m]),
            .s_axi_bresp(s_axi_bresp[m]),
            .s_axi_bvalid(s_axi_bvalid[m]),
            .s_axi_bready(s_axi_bready[m]),

//             Crossbar interface (xbar_s_axi_* to internal routing)
            .fub_axi_awid(xbar_s_axi_awid[m]),
            .fub_axi_awaddr(xbar_s_axi_awaddr[m]),
            .fub_axi_awlen(xbar_s_axi_awlen[m]),
            .fub_axi_awsize(xbar_s_axi_awsize[m]),
            .fub_axi_awburst(xbar_s_axi_awburst[m]),
            .fub_axi_awlock(xbar_s_axi_awlock[m]),
            .fub_axi_awcache(xbar_s_axi_awcache[m]),
            .fub_axi_awprot(xbar_s_axi_awprot[m]),
            .fub_axi_awvalid(xbar_s_axi_awvalid[m]),
            .fub_axi_awready(xbar_s_axi_awready[m]),

            .fub_axi_wdata(xbar_s_axi_wdata[m]),
            .fub_axi_wstrb(xbar_s_axi_wstrb[m]),
            .fub_axi_wlast(xbar_s_axi_wlast[m]),
            .fub_axi_wvalid(xbar_s_axi_wvalid[m]),
            .fub_axi_wready(xbar_s_axi_wready[m]),

            .fub_axi_bid(xbar_s_axi_bid[m]),
            .fub_axi_bresp(xbar_s_axi_bresp[m]),
            .fub_axi_bvalid(xbar_s_axi_bvalid[m]),
            .fub_axi_bready(xbar_s_axi_bready[m]),

//             Extended AXI4 signals (QoS, Region, User) - tied to defaults
            .s_axi_awqos(4'b0000),      // QoS: lowest priority
            .s_axi_awregion(4'b0000),   // Region: unused
            .s_axi_awuser(1'b0),        // User: default
            .s_axi_wuser(1'b0),         // User: default
            .s_axi_buser(),             // User: unconnected output
            .fub_axi_awqos(),           // QoS: unconnected output
            .fub_axi_awregion(),        // Region: unconnected output
            .fub_axi_awuser(),          // User: unconnected output
            .fub_axi_wuser(),           // User: unconnected output
            .fub_axi_buser(1'b0),       // User: tie to default
            .busy()                     // Status: unconnected (FPGA, no clock gating)
        );

//         Read path: axi4_slave_rd for AR, R channels
        axi4_slave_rd #(
            .AXI_ID_WIDTH(ID_WIDTH),
            .AXI_ADDR_WIDTH(ADDR_WIDTH),
            .AXI_DATA_WIDTH(DATA_WIDTH),
            .SKID_DEPTH_AR(2),
            .SKID_DEPTH_R(4)
        ) u_master_rd (
            .aclk(aclk),
            .aresetn(aresetn),

//             External master interface (s_axi_* from outside)
            .s_axi_arid(s_axi_arid[m]),
            .s_axi_araddr(s_axi_araddr[m]),
            .s_axi_arlen(s_axi_arlen[m]),
            .s_axi_arsize(s_axi_arsize[m]),
            .s_axi_arburst(s_axi_arburst[m]),
            .s_axi_arlock(s_axi_arlock[m]),
            .s_axi_arcache(s_axi_arcache[m]),
            .s_axi_arprot(s_axi_arprot[m]),
            .s_axi_arvalid(s_axi_arvalid[m]),
            .s_axi_arready(s_axi_arready[m]),

            .s_axi_rid(s_axi_rid[m]),
            .s_axi_rdata(s_axi_rdata[m]),
            .s_axi_rresp(s_axi_rresp[m]),
            .s_axi_rlast(s_axi_rlast[m]),
            .s_axi_rvalid(s_axi_rvalid[m]),
            .s_axi_rready(s_axi_rready[m]),

//             Crossbar interface (xbar_s_axi_* to internal routing)
            .fub_axi_arid(xbar_s_axi_arid[m]),
            .fub_axi_araddr(xbar_s_axi_araddr[m]),
            .fub_axi_arlen(xbar_s_axi_arlen[m]),
            .fub_axi_arsize(xbar_s_axi_arsize[m]),
            .fub_axi_arburst(xbar_s_axi_arburst[m]),
            .fub_axi_arlock(xbar_s_axi_arlock[m]),
            .fub_axi_arcache(xbar_s_axi_arcache[m]),
            .fub_axi_arprot(xbar_s_axi_arprot[m]),
            .fub_axi_arvalid(xbar_s_axi_arvalid[m]),
            .fub_axi_arready(xbar_s_axi_arready[m]),

            .fub_axi_rid(xbar_s_axi_rid[m]),
            .fub_axi_rdata(xbar_s_axi_rdata[m]),
            .fub_axi_rresp(xbar_s_axi_rresp[m]),
            .fub_axi_rlast(xbar_s_axi_rlast[m]),
            .fub_axi_rvalid(xbar_s_axi_rvalid[m]),
            .fub_axi_rready(xbar_s_axi_rready[m]),

//             Extended AXI4 signals (QoS, Region, User) - tied to defaults
            .s_axi_arqos(4'b0000),      // QoS: lowest priority
            .s_axi_arregion(4'b0000),   // Region: unused
            .s_axi_aruser(1'b0),        // User: default
            .s_axi_ruser(),             // User: unconnected output
            .fub_axi_arqos(),           // QoS: unconnected output
            .fub_axi_arregion(),        // Region: unconnected output
            .fub_axi_aruser(),          // User: unconnected output
            .fub_axi_ruser(1'b0),       // User: tie to default
            .busy()                     // Status: unconnected (FPGA, no clock gating)
        );

    end
endgenerate

// ==========================================================================
// Address Decode (AW and AR channels)
// ==========================================================================
// Decode master addresses to determine target slave(s)
// Generates request signals for per-slave arbitration
// ==========================================================================

// AW channel requests: array of packed vectors per slave
logic [NUM_MASTERS-1:0] aw_request_matrix [NUM_SLAVES-1:0];

// AR channel requests: array of packed vectors per slave
logic [NUM_MASTERS-1:0] ar_request_matrix [NUM_SLAVES-1:0];

generate
    for (genvar m = 0; m < NUM_MASTERS; m++) begin : gen_addr_decode
        always_comb begin
            // Initialize all requests to 0
            for (int s = 0; s < NUM_SLAVES; s++) begin
                aw_request_matrix[s][m] = 1'b0;
                ar_request_matrix[s][m] = 1'b0;
            end

            // Decode AW address to slave
            if (xbar_s_axi_awvalid[m]) begin
                case (xbar_s_axi_awaddr[m][ADDR_WIDTH-1:ADDR_WIDTH-4])
                    4'h0: aw_request_matrix[0][m] = 1'b1;
                    4'h1: aw_request_matrix[1][m] = 1'b1;
                    default: aw_request_matrix[0][m] = 1'b1;  // Default to slave 0
                endcase
            end

            // Decode AR address to slave
            if (xbar_s_axi_arvalid[m]) begin
                case (xbar_s_axi_araddr[m][ADDR_WIDTH-1:ADDR_WIDTH-4])
                    4'h0: ar_request_matrix[0][m] = 1'b1;
                    4'h1: ar_request_matrix[1][m] = 1'b1;
                    default: ar_request_matrix[0][m] = 1'b1;  // Default to slave 0
                endcase
            end
        end
    end
endgenerate

// ==========================================================================
// AW Channel Arbitration - Using Standard arbiter_round_robin
// ==========================================================================
// Per-slave round-robin arbitration with grant locking (WAIT_GNT_ACK=1)
// Grant persists until AW handshake completes
// ==========================================================================

// AW grant matrix: array of packed vectors per slave
logic [NUM_MASTERS-1:0] aw_grant_matrix [NUM_SLAVES-1:0];
logic aw_grant_active [NUM_SLAVES-1:0];  // Valid grant exists

// Grant acknowledgment: AW handshake completion
logic [NUM_MASTERS-1:0] aw_grant_ack [NUM_SLAVES-1:0];

generate
    for (genvar s = 0; s < NUM_SLAVES; s++) begin : gen_aw_grant_ack
        always_comb begin
            aw_grant_ack[s] = '0;
            for (int m = 0; m < NUM_MASTERS; m++) begin
                if (aw_grant_matrix[s][m] && xbar_m_axi_awvalid[s] && xbar_m_axi_awready[s]) begin
                    aw_grant_ack[s][m] = 1'b1;
                end
            end
        end
    end
endgenerate

// Arbiter instances per slave
generate
    for (genvar s = 0; s < NUM_SLAVES; s++) begin : gen_aw_arbiter

        arbiter_round_robin #(
            .CLIENTS(NUM_MASTERS),
            .WAIT_GNT_ACK(1)  // Hold grant until handshake
        ) u_aw_arbiter (
            .clk         (aclk),
            .rst_n       (aresetn),
            .block_arb   (1'b0),
            .request     (aw_request_matrix[s]),
            .grant_ack   (aw_grant_ack[s]),
            .grant_valid (aw_grant_active[s]),
            .grant       (aw_grant_matrix[s]),
            .grant_id    (),  // Optional: can use for debug
            .last_grant  ()   // Optional: debug visibility
        );

    end
endgenerate

// ==========================================================================
// AR Channel Arbitration - Using Standard arbiter_round_robin
// ==========================================================================
// Per-slave round-robin arbitration with grant locking (WAIT_GNT_ACK=1)
// Grant persists until AR handshake completes
// Independent from AW arbitration (separate read/write paths)
// ==========================================================================

// AR grant matrix: array of packed vectors per slave
logic [NUM_MASTERS-1:0] ar_grant_matrix [NUM_SLAVES-1:0];
logic ar_grant_active [NUM_SLAVES-1:0];  // Valid grant exists

// Grant acknowledgment: AR handshake completion
logic [NUM_MASTERS-1:0] ar_grant_ack [NUM_SLAVES-1:0];

generate
    for (genvar s = 0; s < NUM_SLAVES; s++) begin : gen_ar_grant_ack
        always_comb begin
            ar_grant_ack[s] = '0;
            for (int m = 0; m < NUM_MASTERS; m++) begin
                if (ar_grant_matrix[s][m] && xbar_m_axi_arvalid[s] && xbar_m_axi_arready[s]) begin
                    ar_grant_ack[s][m] = 1'b1;
                end
            end
        end
    end
endgenerate

// Arbiter instances per slave
generate
    for (genvar s = 0; s < NUM_SLAVES; s++) begin : gen_ar_arbiter

        arbiter_round_robin #(
            .CLIENTS(NUM_MASTERS),
            .WAIT_GNT_ACK(1)  // Hold grant until handshake
        ) u_ar_arbiter (
            .clk         (aclk),
            .rst_n       (aresetn),
            .block_arb   (1'b0),
            .request     (ar_request_matrix[s]),
            .grant_ack   (ar_grant_ack[s]),
            .grant_valid (ar_grant_active[s]),
            .grant       (ar_grant_matrix[s]),
            .grant_id    (),  // Optional: can use for debug
            .last_grant  ()   // Optional: debug visibility
        );

    end
endgenerate

// ==========================================================================
// AW Channel Multiplexing
// ==========================================================================
// Mux granted master's write address signals to slave
// Grant-based routing ensures only one master per slave at a time
// ==========================================================================

generate
    for (genvar s = 0; s < NUM_SLAVES; s++) begin : gen_aw_mux
        always_comb begin
            // Default: all zeros
            xbar_m_axi_awaddr[s]  = '0;
            xbar_m_axi_awid[s]    = '0;
            xbar_m_axi_awlen[s]   = '0;
            xbar_m_axi_awsize[s]  = '0;
            xbar_m_axi_awburst[s] = '0;
            xbar_m_axi_awlock[s]  = '0;
            xbar_m_axi_awcache[s] = '0;
            xbar_m_axi_awprot[s]  = '0;
            xbar_m_axi_awvalid[s] = 1'b0;

            // Multiplex granted master to this slave
            for (int m = 0; m < NUM_MASTERS; m++) begin
                if (aw_grant_matrix[s][m]) begin
                    xbar_m_axi_awaddr[s]  = xbar_s_axi_awaddr[m];
                    xbar_m_axi_awid[s]    = xbar_s_axi_awid[m];
                    xbar_m_axi_awlen[s]   = xbar_s_axi_awlen[m];
                    xbar_m_axi_awsize[s]  = xbar_s_axi_awsize[m];
                    xbar_m_axi_awburst[s] = xbar_s_axi_awburst[m];
                    xbar_m_axi_awlock[s]  = xbar_s_axi_awlock[m];
                    xbar_m_axi_awcache[s] = xbar_s_axi_awcache[m];
                    xbar_m_axi_awprot[s]  = xbar_s_axi_awprot[m];
                    xbar_m_axi_awvalid[s] = xbar_s_axi_awvalid[m];
                end
            end
        end
    end
endgenerate

// AWREADY backpressure routing
generate
    for (genvar m = 0; m < NUM_MASTERS; m++) begin : gen_awready
        always_comb begin
            xbar_s_axi_awready[m] = 1'b0;
            for (int s = 0; s < NUM_SLAVES; s++) begin
                if (aw_grant_matrix[s][m]) begin
                    xbar_s_axi_awready[m] = xbar_m_axi_awready[s];
                end
            end
        end
    end
endgenerate

// ==========================================================================
// W Channel Multiplexing (Write Data)
// ==========================================================================
// W channel follows AW grant (burst-aware)
// Grant tracking: W grant locked from AWVALID until WLAST
// ==========================================================================

// W grant tracking: which master currently owns W channel for each slave
logic [NUM_MASTERS-1:0] w_grant_matrix [NUM_SLAVES];

generate
    for (genvar s = 0; s < NUM_SLAVES; s++) begin : gen_w_grant_track
        always_ff @(posedge aclk or negedge aresetn) begin
            if (!aresetn) begin
                w_grant_matrix[s] <= '0;
            end else begin
                // Capture AW grant when AW handshake completes
                if (xbar_m_axi_awvalid[s] && xbar_m_axi_awready[s]) begin
                    w_grant_matrix[s] <= aw_grant_matrix[s];
                end
                // Clear grant when W burst completes (WLAST)
                else if (xbar_m_axi_wvalid[s] && xbar_m_axi_wready[s] && xbar_m_axi_wlast[s]) begin
                    w_grant_matrix[s] <= '0;
                end
            end
        end
    end
endgenerate

generate
    for (genvar s = 0; s < NUM_SLAVES; s++) begin : gen_w_mux
        always_comb begin
            // Default: all zeros
            xbar_m_axi_wdata[s]  = '0;
            xbar_m_axi_wstrb[s]  = '0;
            xbar_m_axi_wlast[s]  = 1'b0;
            xbar_m_axi_wvalid[s] = 1'b0;

            // Multiplex W data from granted master
            for (int m = 0; m < NUM_MASTERS; m++) begin
                if (w_grant_matrix[s][m]) begin
                    xbar_m_axi_wdata[s]  = xbar_s_axi_wdata[m];
                    xbar_m_axi_wstrb[s]  = xbar_s_axi_wstrb[m];
                    xbar_m_axi_wlast[s]  = xbar_s_axi_wlast[m];
                    xbar_m_axi_wvalid[s] = xbar_s_axi_wvalid[m];
                end
            end
        end
    end
endgenerate

// WREADY backpressure routing
generate
    for (genvar m = 0; m < NUM_MASTERS; m++) begin : gen_wready
        always_comb begin
            xbar_s_axi_wready[m] = 1'b0;
            for (int s = 0; s < NUM_SLAVES; s++) begin
                if (w_grant_matrix[s][m]) begin
                    xbar_s_axi_wready[m] = xbar_m_axi_wready[s];
                end
            end
        end
    end
endgenerate

// ==========================================================================
// AR Channel Multiplexing
// ==========================================================================
// Mux granted master's read address signals to slave
// Independent from AW channel (separate read/write paths)
// ==========================================================================

generate
    for (genvar s = 0; s < NUM_SLAVES; s++) begin : gen_ar_mux
        always_comb begin
            // Default: all zeros
            xbar_m_axi_araddr[s]  = '0;
            xbar_m_axi_arid[s]    = '0;
            xbar_m_axi_arlen[s]   = '0;
            xbar_m_axi_arsize[s]  = '0;
            xbar_m_axi_arburst[s] = '0;
            xbar_m_axi_arlock[s]  = '0;
            xbar_m_axi_arcache[s] = '0;
            xbar_m_axi_arprot[s]  = '0;
            xbar_m_axi_arvalid[s] = 1'b0;

            // Multiplex granted master to this slave
            for (int m = 0; m < NUM_MASTERS; m++) begin
                if (ar_grant_matrix[s][m]) begin
                    xbar_m_axi_araddr[s]  = xbar_s_axi_araddr[m];
                    xbar_m_axi_arid[s]    = xbar_s_axi_arid[m];
                    xbar_m_axi_arlen[s]   = xbar_s_axi_arlen[m];
                    xbar_m_axi_arsize[s]  = xbar_s_axi_arsize[m];
                    xbar_m_axi_arburst[s] = xbar_s_axi_arburst[m];
                    xbar_m_axi_arlock[s]  = xbar_s_axi_arlock[m];
                    xbar_m_axi_arcache[s] = xbar_s_axi_arcache[m];
                    xbar_m_axi_arprot[s]  = xbar_s_axi_arprot[m];
                    xbar_m_axi_arvalid[s] = xbar_s_axi_arvalid[m];
                end
            end
        end
    end
endgenerate

// ARREADY backpressure routing
generate
    for (genvar m = 0; m < NUM_MASTERS; m++) begin : gen_arready
        always_comb begin
            xbar_s_axi_arready[m] = 1'b0;
            for (int s = 0; s < NUM_SLAVES; s++) begin
                if (ar_grant_matrix[s][m]) begin
                    xbar_s_axi_arready[m] = xbar_m_axi_arready[s];
                end
            end
        end
    end
endgenerate

// ==========================================================================
// Transaction ID Tracking Tables
// ==========================================================================
// Purpose: Enable ID-based response routing (out-of-order support)
// 
// Structure: Distributed RAM
//   - 2 slaves × 2 tables (write, read)
//   - 2^4 = 16 entries per table
//   - Each entry: $clog2(2) = 1 bits (master index)
// 
// Write ID Table: Stores master index for AW transactions → B routing
// Read ID Table:  Stores master index for AR transactions → R routing
// 
// ENHANCEMENT OPPORTUNITY: Replace with CAM for better out-of-order performance:
//   - Track outstanding transaction counts
//   - Detect ID exhaustion and provide backpressure
//   - Enable performance monitoring (latency, throughput)
//   - See cam_tag.sv or cam_tag_perf.sv for CAM implementation
// ==========================================================================

// Transaction ID tables: [slave][transaction_id] → master_index
logic [$clog2(NUM_MASTERS):0] write_id_table [NUM_SLAVES][2**ID_WIDTH];
logic [$clog2(NUM_MASTERS):0] read_id_table [NUM_SLAVES][2**ID_WIDTH];

// ID Table Write Logic
// Store master index when AW/AR handshakes complete
generate
    for (genvar s = 0; s < NUM_SLAVES; s++) begin : gen_id_table_write
        always_ff @(posedge aclk or negedge aresetn) begin
            if (!aresetn) begin
                // Tables don't need explicit reset (overwritten on use)
            end else begin
                // Write ID table: Record master for completed AW transactions
                if (xbar_m_axi_awvalid[s] && xbar_m_axi_awready[s]) begin
                    for (int m = 0; m < NUM_MASTERS; m++) begin
                        if (aw_grant_matrix[s][m]) begin
                            write_id_table[s][xbar_m_axi_awid[s]] <= m[$clog2(NUM_MASTERS):0];
                        end
                    end
                end

                // Read ID table: Record master for completed AR transactions
                if (xbar_m_axi_arvalid[s] && xbar_m_axi_arready[s]) begin
                    for (int m = 0; m < NUM_MASTERS; m++) begin
                        if (ar_grant_matrix[s][m]) begin
                            read_id_table[s][xbar_m_axi_arid[s]] <= m[$clog2(NUM_MASTERS):0];
                        end
                    end
                end
            end
        end
    end
endgenerate

// ==========================================================================
// B Channel Demux (Write Response)
// ==========================================================================
// ID-based routing: Lookup master from write_id_table[slave][bid]
// Single-beat response (no burst, unlike R channel)
// ==========================================================================

// B channel response routing to masters
logic [ID_WIDTH-1:0]     b_routed_id    [NUM_MASTERS];
logic [1:0]              b_routed_resp  [NUM_MASTERS];
logic                    b_routed_valid [NUM_MASTERS];

always_comb begin
    // Initialize all master B channels to idle
    for (int m = 0; m < NUM_MASTERS; m++) begin
        b_routed_id[m]    = '0;
        b_routed_resp[m]  = 2'b00;
        b_routed_valid[m] = 1'b0;
    end

    // Route B responses from each slave to target master
    for (int s = 0; s < NUM_SLAVES; s++) begin
        int target_master;  // Master index for this B response
        if (xbar_m_axi_bvalid[s]) begin
            // Lookup which master this transaction belongs to
            target_master = int'(write_id_table[s][xbar_m_axi_bid[s]]);

            // Route to target master (ID-based)
            b_routed_id[target_master]    = xbar_m_axi_bid[s];
            b_routed_resp[target_master]  = xbar_m_axi_bresp[s];
            b_routed_valid[target_master] = 1'b1;
        end else begin
            target_master = 0;  // Default when no valid
        end
    end
end

// Assign routed B signals to master output ports
generate
    for (genvar m = 0; m < NUM_MASTERS; m++) begin : gen_b_output
        assign xbar_s_axi_bid[m]    = b_routed_id[m];
        assign xbar_s_axi_bresp[m]  = b_routed_resp[m];
        assign xbar_s_axi_bvalid[m] = b_routed_valid[m];
    end
endgenerate

// B channel backpressure: Route master's BREADY to slave
generate
    for (genvar s = 0; s < NUM_SLAVES; s++) begin : gen_b_ready
        always_comb begin
            int target_master;
            xbar_m_axi_bready[s] = 1'b0;
            if (xbar_m_axi_bvalid[s]) begin
                // Find which master this B response goes to
                target_master = int'(write_id_table[s][xbar_m_axi_bid[s]]);
                xbar_m_axi_bready[s] = xbar_s_axi_bready[target_master];
            end else begin
                target_master = 0;  // Default when no valid
            end
        end
    end
endgenerate

// ==========================================================================
// R Channel Demux (Read Data/Response)
// ==========================================================================
// ID-based routing: Lookup master from read_id_table[slave][rid]
// Burst support: Multiple R beats (RLAST indicates last beat)
// Similar to B channel but with DATA_WIDTH data payload
// ==========================================================================

// R channel response routing to masters
logic [DATA_WIDTH-1:0]   r_routed_data  [NUM_MASTERS];
logic [ID_WIDTH-1:0]     r_routed_id    [NUM_MASTERS];
logic [1:0]              r_routed_resp  [NUM_MASTERS];
logic                    r_routed_last  [NUM_MASTERS];
logic                    r_routed_valid [NUM_MASTERS];

always_comb begin
    // Initialize all master R channels to idle
    for (int m = 0; m < NUM_MASTERS; m++) begin
        r_routed_data[m]  = '0;
        r_routed_id[m]    = '0;
        r_routed_resp[m]  = 2'b00;
        r_routed_last[m]  = 1'b0;
        r_routed_valid[m] = 1'b0;
    end

    // Route R responses from each slave to target master
    for (int s = 0; s < NUM_SLAVES; s++) begin
        int target_master;  // Master index for this R response
        if (xbar_m_axi_rvalid[s]) begin
            // Lookup which master this transaction belongs to
            target_master = int'(read_id_table[s][xbar_m_axi_rid[s]]);

            // Route to target master (ID-based, burst-aware)
            r_routed_data[target_master]  = xbar_m_axi_rdata[s];
            r_routed_id[target_master]    = xbar_m_axi_rid[s];
            r_routed_resp[target_master]  = xbar_m_axi_rresp[s];
            r_routed_last[target_master]  = xbar_m_axi_rlast[s];
            r_routed_valid[target_master] = 1'b1;
        end else begin
            target_master = 0;  // Default when no valid
        end
    end
end

// Assign routed R signals to master output ports
generate
    for (genvar m = 0; m < NUM_MASTERS; m++) begin : gen_r_output
        assign xbar_s_axi_rdata[m]  = r_routed_data[m];
        assign xbar_s_axi_rid[m]    = r_routed_id[m];
        assign xbar_s_axi_rresp[m]  = r_routed_resp[m];
        assign xbar_s_axi_rlast[m]  = r_routed_last[m];
        assign xbar_s_axi_rvalid[m] = r_routed_valid[m];
    end
endgenerate

// R channel backpressure: Route master's RREADY to slave
generate
    for (genvar s = 0; s < NUM_SLAVES; s++) begin : gen_r_ready
        always_comb begin
            int target_master;
            xbar_m_axi_rready[s] = 1'b0;
            if (xbar_m_axi_rvalid[s]) begin
                // Find which master this R response goes to
                target_master = int'(read_id_table[s][xbar_m_axi_rid[s]]);
                xbar_m_axi_rready[s] = xbar_s_axi_rready[target_master];
            end else begin
                target_master = 0;  // Default when no valid
            end
        end
    end
endgenerate

// ==========================================================================
// Slave-Side AMBA Components (axi4_master_wr and axi4_master_rd)
// ==========================================================================
// Connect to external slaves with skid buffers and flow control
// Configuration: SKID_DEPTH_AW=2, W=4, B=2, AR=2, R=4
// ==========================================================================

generate
    for (genvar s = 0; s < NUM_SLAVES; s++) begin : gen_slave_side_amba

//         Write path: axi4_master_wr for AW, W, B channels
        axi4_master_wr #(
            .AXI_ID_WIDTH(ID_WIDTH),
            .AXI_ADDR_WIDTH(ADDR_WIDTH),
            .AXI_DATA_WIDTH(DATA_WIDTH),
            .SKID_DEPTH_AW(2),
            .SKID_DEPTH_W(4),
            .SKID_DEPTH_B(2)
        ) u_slave_wr (
            .aclk(aclk),
            .aresetn(aresetn),

//             Crossbar interface (xbar_m_axi_* from internal routing)
            .fub_axi_awid(xbar_m_axi_awid[s]),
            .fub_axi_awaddr(xbar_m_axi_awaddr[s]),
            .fub_axi_awlen(xbar_m_axi_awlen[s]),
            .fub_axi_awsize(xbar_m_axi_awsize[s]),
            .fub_axi_awburst(xbar_m_axi_awburst[s]),
            .fub_axi_awlock(xbar_m_axi_awlock[s]),
            .fub_axi_awcache(xbar_m_axi_awcache[s]),
            .fub_axi_awprot(xbar_m_axi_awprot[s]),
            .fub_axi_awvalid(xbar_m_axi_awvalid[s]),
            .fub_axi_awready(xbar_m_axi_awready[s]),

            .fub_axi_wdata(xbar_m_axi_wdata[s]),
            .fub_axi_wstrb(xbar_m_axi_wstrb[s]),
            .fub_axi_wlast(xbar_m_axi_wlast[s]),
            .fub_axi_wvalid(xbar_m_axi_wvalid[s]),
            .fub_axi_wready(xbar_m_axi_wready[s]),

            .fub_axi_bid(xbar_m_axi_bid[s]),
            .fub_axi_bresp(xbar_m_axi_bresp[s]),
            .fub_axi_bvalid(xbar_m_axi_bvalid[s]),
            .fub_axi_bready(xbar_m_axi_bready[s]),

//             External slave interface (m_axi_* to outside)
            .m_axi_awid(m_axi_awid[s]),
            .m_axi_awaddr(m_axi_awaddr[s]),
            .m_axi_awlen(m_axi_awlen[s]),
            .m_axi_awsize(m_axi_awsize[s]),
            .m_axi_awburst(m_axi_awburst[s]),
            .m_axi_awlock(m_axi_awlock[s]),
            .m_axi_awcache(m_axi_awcache[s]),
            .m_axi_awprot(m_axi_awprot[s]),
            .m_axi_awvalid(m_axi_awvalid[s]),
            .m_axi_awready(m_axi_awready[s]),

            .m_axi_wdata(m_axi_wdata[s]),
            .m_axi_wstrb(m_axi_wstrb[s]),
            .m_axi_wlast(m_axi_wlast[s]),
            .m_axi_wvalid(m_axi_wvalid[s]),
            .m_axi_wready(m_axi_wready[s]),

            .m_axi_bid(m_axi_bid[s]),
            .m_axi_bresp(m_axi_bresp[s]),
            .m_axi_bvalid(m_axi_bvalid[s]),
            .m_axi_bready(m_axi_bready[s]),

//             Extended AXI4 signals (QoS, Region, User) - tied to defaults
            .fub_axi_awqos(4'b0000),    // QoS: tie to default
            .fub_axi_awregion(4'b0000), // Region: tie to default
            .fub_axi_awuser(1'b0),      // User: tie to default
            .fub_axi_wuser(1'b0),       // User: tie to default
            .fub_axi_buser(),           // User: unconnected input
            .m_axi_awqos(),             // QoS: unconnected output
            .m_axi_awregion(),          // Region: unconnected output
            .m_axi_awuser(),            // User: unconnected output
            .m_axi_wuser(),             // User: unconnected output
            .m_axi_buser(1'b0),         // User: tie input to default
            .busy()                     // Status: unconnected (FPGA, no clock gating)
        );

//         Read path: axi4_master_rd for AR, R channels
        axi4_master_rd #(
            .AXI_ID_WIDTH(ID_WIDTH),
            .AXI_ADDR_WIDTH(ADDR_WIDTH),
            .AXI_DATA_WIDTH(DATA_WIDTH),
            .SKID_DEPTH_AR(2),
            .SKID_DEPTH_R(4)
        ) u_slave_rd (
            .aclk(aclk),
            .aresetn(aresetn),

//             Crossbar interface (xbar_m_axi_* from internal routing)
            .fub_axi_arid(xbar_m_axi_arid[s]),
            .fub_axi_araddr(xbar_m_axi_araddr[s]),
            .fub_axi_arlen(xbar_m_axi_arlen[s]),
            .fub_axi_arsize(xbar_m_axi_arsize[s]),
            .fub_axi_arburst(xbar_m_axi_arburst[s]),
            .fub_axi_arlock(xbar_m_axi_arlock[s]),
            .fub_axi_arcache(xbar_m_axi_arcache[s]),
            .fub_axi_arprot(xbar_m_axi_arprot[s]),
            .fub_axi_arvalid(xbar_m_axi_arvalid[s]),
            .fub_axi_arready(xbar_m_axi_arready[s]),

            .fub_axi_rid(xbar_m_axi_rid[s]),
            .fub_axi_rdata(xbar_m_axi_rdata[s]),
            .fub_axi_rresp(xbar_m_axi_rresp[s]),
            .fub_axi_rlast(xbar_m_axi_rlast[s]),
            .fub_axi_rvalid(xbar_m_axi_rvalid[s]),
            .fub_axi_rready(xbar_m_axi_rready[s]),

//             External slave interface (m_axi_* to outside)
            .m_axi_arid(m_axi_arid[s]),
            .m_axi_araddr(m_axi_araddr[s]),
            .m_axi_arlen(m_axi_arlen[s]),
            .m_axi_arsize(m_axi_arsize[s]),
            .m_axi_arburst(m_axi_arburst[s]),
            .m_axi_arlock(m_axi_arlock[s]),
            .m_axi_arcache(m_axi_arcache[s]),
            .m_axi_arprot(m_axi_arprot[s]),
            .m_axi_arvalid(m_axi_arvalid[s]),
            .m_axi_arready(m_axi_arready[s]),

            .m_axi_rid(m_axi_rid[s]),
            .m_axi_rdata(m_axi_rdata[s]),
            .m_axi_rresp(m_axi_rresp[s]),
            .m_axi_rlast(m_axi_rlast[s]),
            .m_axi_rvalid(m_axi_rvalid[s]),
            .m_axi_rready(m_axi_rready[s]),

//             Extended AXI4 signals (QoS, Region, User) - tied to defaults
            .fub_axi_arqos(4'b0000),    // QoS: tie to default
            .fub_axi_arregion(4'b0000), // Region: tie to default
            .fub_axi_aruser(1'b0),      // User: tie to default
            .fub_axi_ruser(),           // User: unconnected input
            .m_axi_arqos(),             // QoS: unconnected output
            .m_axi_arregion(),          // Region: unconnected output
            .m_axi_aruser(),            // User: unconnected output
            .m_axi_ruser(1'b0),         // User: tie input to default
            .busy()                     // Status: unconnected (FPGA, no clock gating)
        );

    end
endgenerate

endmodule
