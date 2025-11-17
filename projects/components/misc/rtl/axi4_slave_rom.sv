`timescale 1ns / 1ps

//==============================================================================
// Module: axi4_slave_rom
//==============================================================================
// Description:
//   AXI4 read-only memory slave wrapper. Combines axi4_slave_rd protocol
//   handler with simple_rom storage backend to provide AXI4-compliant ROM
//   interface. Useful for boot code, configuration data, lookup tables, etc.
//
// Parameters:
//   SKID_DEPTH_AR  - AR channel skid buffer depth (default: 2)
//   SKID_DEPTH_R   - R channel skid buffer depth (default: 4)
//   AXI_ID_WIDTH   - AXI ID width (default: 8)
//   AXI_ADDR_WIDTH - AXI address width (default: 32)
//   AXI_DATA_WIDTH - AXI data width (default: 64)
//   AXI_USER_WIDTH - AXI user signal width (default: 1)
//   ROM_INIT_FILE  - ROM initialization file path (default: "none")
//
// Interfaces:
//   aclk, aresetn     - Clock and reset
//   s_axi_ar*         - AXI4 read address channel (slave)
//   s_axi_r*          - AXI4 read data channel (slave)
//   busy              - Status output (active transactions)
//
// Notes:
//   - Read-only interface (no write channels)
//   - Single-cycle ROM access latency
//   - FPGA block RAM inference for ROM storage
//   - Supports bursts via AXI4 slave read handler
//   - ROM address is byte-aligned AXI address shifted by data width
//
//==============================================================================

module axi4_slave_rom
#(
    parameter int SKID_DEPTH_AR     = 2,                    // AR channel buffer depth
    parameter int SKID_DEPTH_R      = 4,                    // R channel buffer depth
    parameter int AXI_ID_WIDTH      = 8,                    // AXI ID width
    parameter int AXI_ADDR_WIDTH    = 32,                   // AXI address width
    parameter int AXI_DATA_WIDTH    = 64,                   // AXI data width
    parameter int AXI_USER_WIDTH    = 1,                    // AXI user width
    parameter string ROM_INIT_FILE  = "none"                // ROM initialization file
)
(
    // Global Clock and Reset
    input  logic                        aclk,               // AXI clock
    input  logic                        aresetn,            // AXI reset (active-low)

    // AXI4 Slave Interface (Read-Only)
    // Read address channel (AR)
    input  logic [AXI_ID_WIDTH-1:0]     s_axi_arid,         // Read address ID
    input  logic [AXI_ADDR_WIDTH-1:0]   s_axi_araddr,       // Read address
    input  logic [7:0]                  s_axi_arlen,        // Burst length
    input  logic [2:0]                  s_axi_arsize,       // Burst size
    input  logic [1:0]                  s_axi_arburst,      // Burst type
    input  logic                        s_axi_arlock,       // Lock type
    input  logic [3:0]                  s_axi_arcache,      // Cache type
    input  logic [2:0]                  s_axi_arprot,       // Protection type
    input  logic [3:0]                  s_axi_arqos,        // QoS identifier
    input  logic [3:0]                  s_axi_arregion,     // Region identifier
    input  logic [AXI_USER_WIDTH-1:0]   s_axi_aruser,       // User signal
    input  logic                        s_axi_arvalid,      // Read address valid
    output logic                        s_axi_arready,      // Read address ready

    // Read data channel (R)
    output logic [AXI_ID_WIDTH-1:0]     s_axi_rid,          // Read data ID
    output logic [AXI_DATA_WIDTH-1:0]   s_axi_rdata,        // Read data
    output logic [1:0]                  s_axi_rresp,        // Read response
    output logic                        s_axi_rlast,        // Read last
    output logic [AXI_USER_WIDTH-1:0]   s_axi_ruser,        // User signal
    output logic                        s_axi_rvalid,       // Read data valid
    input  logic                        s_axi_rready,       // Read data ready

    // Status Output
    output logic                        busy                // Busy indicator
);

    //==========================================================================
    // Local Parameters
    //==========================================================================

    localparam int BYTES_PER_WORD = AXI_DATA_WIDTH / 8;
    localparam int ROM_ADDR_WIDTH = AXI_ADDR_WIDTH - $clog2(BYTES_PER_WORD);

    //==========================================================================
    // Internal Signals - FUB (Functional Unit Backend) Interface
    //==========================================================================

    // Internal interface between axi4_slave_rd and ROM
    logic [AXI_ID_WIDTH-1:0]     fub_axi_arid;
    logic [AXI_ADDR_WIDTH-1:0]   fub_axi_araddr;
    logic [7:0]                  fub_axi_arlen;
    logic [2:0]                  fub_axi_arsize;
    logic [1:0]                  fub_axi_arburst;
    logic                        fub_axi_arlock;
    logic [3:0]                  fub_axi_arcache;
    logic [2:0]                  fub_axi_arprot;
    logic [3:0]                  fub_axi_arqos;
    logic [3:0]                  fub_axi_arregion;
    logic [AXI_USER_WIDTH-1:0]   fub_axi_aruser;
    logic                        fub_axi_arvalid;
    logic                        fub_axi_arready;

    logic [AXI_ID_WIDTH-1:0]     fub_axi_rid;
    logic [AXI_DATA_WIDTH-1:0]   fub_axi_rdata;
    logic [1:0]                  fub_axi_rresp;
    logic                        fub_axi_rlast;
    logic [AXI_USER_WIDTH-1:0]   fub_axi_ruser;
    logic                        fub_axi_rvalid;
    logic                        fub_axi_rready;

    //==========================================================================
    // Glue Logic - ROM Interface Conversion
    //==========================================================================

    // Convert byte-aligned AXI address to word-aligned ROM address
    logic [ROM_ADDR_WIDTH-1:0] rom_addr;
    assign rom_addr = fub_axi_araddr[AXI_ADDR_WIDTH-1:$clog2(BYTES_PER_WORD)];

    // ROM enable: active when valid address transaction
    logic rom_en;
    assign rom_en = fub_axi_arvalid;

    // ROM read data
    logic [AXI_DATA_WIDTH-1:0] rom_data;

    // FUB AR channel ready (ROM always ready for single-cycle access)
    assign fub_axi_arready = 1'b1;

    // FUB R channel - ROM read data and control
    assign fub_axi_rid     = fub_axi_arid;      // Pass through ID
    assign fub_axi_rdata   = rom_data;          // ROM data
    assign fub_axi_rresp   = 2'b00;             // OKAY response (no errors in ROM)
    assign fub_axi_rlast   = 1'b1;              // Single-beat response (burst handled by slave_rd)
    assign fub_axi_ruser   = '0;                // User signal unused
    assign fub_axi_rvalid  = fub_axi_arvalid;   // Valid when AR valid (single-cycle)
    assign fub_axi_rready  = 1'b1;              // Always ready (no backpressure from ROM)

    //==========================================================================
    // AXI4 Slave Read Protocol Handler
    //==========================================================================

    axi4_slave_rd #(
        .SKID_DEPTH_AR      (SKID_DEPTH_AR),
        .SKID_DEPTH_R       (SKID_DEPTH_R),
        .AXI_ID_WIDTH       (AXI_ID_WIDTH),
        .AXI_ADDR_WIDTH     (AXI_ADDR_WIDTH),
        .AXI_DATA_WIDTH     (AXI_DATA_WIDTH),
        .AXI_USER_WIDTH     (AXI_USER_WIDTH)
    ) u_axi4_slave_rd (
        // Clock and Reset
        .aclk               (aclk),
        .aresetn            (aresetn),

        // Slave AXI Interface (External)
        .s_axi_arid         (s_axi_arid),
        .s_axi_araddr       (s_axi_araddr),
        .s_axi_arlen        (s_axi_arlen),
        .s_axi_arsize       (s_axi_arsize),
        .s_axi_arburst      (s_axi_arburst),
        .s_axi_arlock       (s_axi_arlock),
        .s_axi_arcache      (s_axi_arcache),
        .s_axi_arprot       (s_axi_arprot),
        .s_axi_arqos        (s_axi_arqos),
        .s_axi_arregion     (s_axi_arregion),
        .s_axi_aruser       (s_axi_aruser),
        .s_axi_arvalid      (s_axi_arvalid),
        .s_axi_arready      (s_axi_arready),

        .s_axi_rid          (s_axi_rid),
        .s_axi_rdata        (s_axi_rdata),
        .s_axi_rresp        (s_axi_rresp),
        .s_axi_rlast        (s_axi_rlast),
        .s_axi_ruser        (s_axi_ruser),
        .s_axi_rvalid       (s_axi_rvalid),
        .s_axi_rready       (s_axi_rready),

        // Master AXI Interface (Internal to ROM)
        .fub_axi_arid       (fub_axi_arid),
        .fub_axi_araddr     (fub_axi_araddr),
        .fub_axi_arlen      (fub_axi_arlen),
        .fub_axi_arsize     (fub_axi_arsize),
        .fub_axi_arburst    (fub_axi_arburst),
        .fub_axi_arlock     (fub_axi_arlock),
        .fub_axi_arcache    (fub_axi_arcache),
        .fub_axi_arprot     (fub_axi_arprot),
        .fub_axi_arqos      (fub_axi_arqos),
        .fub_axi_arregion   (fub_axi_arregion),
        .fub_axi_aruser     (fub_axi_aruser),
        .fub_axi_arvalid    (fub_axi_arvalid),
        .fub_axi_arready    (fub_axi_arready),

        .fub_axi_rid        (fub_axi_rid),
        .fub_axi_rdata      (fub_axi_rdata),
        .fub_axi_rresp      (fub_axi_rresp),
        .fub_axi_rlast      (fub_axi_rlast),
        .fub_axi_ruser      (fub_axi_ruser),
        .fub_axi_rvalid     (fub_axi_rvalid),
        .fub_axi_rready     (fub_axi_rready),

        // Status Output
        .busy               (busy)
    );

    //==========================================================================
    // Simple ROM Storage Backend
    //==========================================================================

    simple_rom #(
        .ADDR_WIDTH         (ROM_ADDR_WIDTH),
        .DATA_WIDTH         (AXI_DATA_WIDTH),
        .INIT_FILE          (ROM_INIT_FILE)
    ) u_simple_rom (
        .clk                (aclk),
        .en                 (rom_en),
        .addr               (rom_addr),
        .data               (rom_data)
    );

endmodule : axi4_slave_rom
