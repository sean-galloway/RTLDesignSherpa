`timescale 1ns / 1ps

//==============================================================================
// Module: axi4_slave_wr_crc_check
//==============================================================================
// Description:
//   AXI4 write-only slave that computes CRC-32 on received data for DMA
//   validation. Combines axi4_slave_wr protocol handler with CRC checker.
//
// Purpose:
//   DMA characterization and data integrity validation. Companion to
//   axi4_slave_rd_pattern_gen - receives DMA writes and computes CRC-32
//   for comparison with read pattern generator CRC.
//
// Parameters:
//   SKID_DEPTH_AW  - AW channel skid buffer depth (default: 2)
//   SKID_DEPTH_W   - W channel skid buffer depth (default: 4)
//   SKID_DEPTH_B   - B channel skid buffer depth (default: 2)
//   AXI_ID_WIDTH   - AXI ID width (default: 8)
//   AXI_ADDR_WIDTH - AXI address width (default: 32)
//   AXI_DATA_WIDTH - AXI data width (default: 64, can be wider)
//   AXI_USER_WIDTH - AXI user signal width (default: 1)
//   CRC_SLICE_OFFSET - Which 32-bit slice to CRC (0 = [31:0], 1 = [63:32], etc.)
//
// Architecture:
//   AXI AW/W → axi4_slave_wr → Extract 32-bit slice → CRC-32 → write_crc_value
//
// Interfaces:
//   aclk, aresetn          - Clock and reset
//   crc_reset              - Synchronous reset for test control (from UART)
//   write_crc_value[31:0]  - CRC-32 output for validation
//   write_crc_valid        - CRC value is valid (after first update)
//   write_beat_count[31:0] - Number of AXI write beats received
//   s_axi_aw*              - AXI4 write address channel (slave)
//   s_axi_w*               - AXI4 write data channel (slave)
//   s_axi_b*               - AXI4 write response channel (slave)
//   busy                   - Status output (active transactions)
//
// Notes:
//   - Extracts 32-bit slice from AXI_DATA_WIDTH (default [31:0])
//   - CRC processes 32-bit data only
//   - CRC-32 Ethernet standard (POLY=0x04C11DB7, INIT/XOR=0xFFFFFFFF)
//   - CRC accumulates over all write beats
//   - crc_reset resets CRC for new test sequence
//   - Companion module: axi4_slave_rd_pattern_gen.sv (must use matching CRC params)
//   - Written data is discarded (no storage backend)
//
// Example Usage (Python via UART):
//   uart.write("RESET_CRC")
//   dma.read_burst(addr=pattern_gen_addr, length=10000)
//   dma.write_burst(addr=crc_check_addr, length=10000)
//   read_crc = uart.read("READ_CRC_VALUE")
//   write_crc = uart.read("WRITE_CRC_VALUE")
//   assert read_crc == write_crc, "DMA data integrity failure!"
//
//==============================================================================

`include "reset_defs.svh"

module axi4_slave_wr_crc_check #(
    // AXI parameters
    parameter int SKID_DEPTH_AW  = 2,
    parameter int SKID_DEPTH_W   = 4,
    parameter int SKID_DEPTH_B   = 2,
    parameter int AXI_ID_WIDTH   = 8,
    parameter int AXI_ADDR_WIDTH = 32,
    parameter int AXI_DATA_WIDTH = 64,
    parameter int AXI_USER_WIDTH = 1,

    // CRC parameters (MUST MATCH axi4_slave_rd_pattern_gen!)
    parameter int CRC_WIDTH      = 32,
    parameter int CRC_DATA_WIDTH = 32,  // Process 32-bit slice only
    parameter logic [31:0] CRC_POLY    = 32'h04C11DB7,  // CRC-32 Ethernet
    parameter logic [31:0] CRC_INIT    = 32'hFFFFFFFF,
    parameter logic [31:0] CRC_XOROUT  = 32'hFFFFFFFF,
    parameter int CRC_REFIN  = 1,
    parameter int CRC_REFOUT = 1,

    // Which 32-bit slice to CRC from AXI_DATA_WIDTH
    // 0 = [31:0], 1 = [63:32], 2 = [95:64], etc.
    parameter int CRC_SLICE_OFFSET = 0
) (
    // Global Clock and Reset
    input  logic                        aclk,
    input  logic                        aresetn,

    // Test Control (from UART controller or test logic)
    input  logic                        crc_reset,  // Pulse to reset CRC

    // CRC and Status Outputs (to UART controller)
    output logic [31:0]                 write_crc_value,   // Current CRC-32 value
    output logic                        write_crc_valid,   // CRC valid after first update
    output logic [31:0]                 write_beat_count,  // Number of write beats received

    // AXI4 Slave Interface (Write-Only)
    // Write address channel (AW)
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

    // Write data channel (W)
    input  logic [AXI_DATA_WIDTH-1:0]   s_axi_wdata,
    input  logic [AXI_DATA_WIDTH/8-1:0] s_axi_wstrb,
    input  logic                        s_axi_wlast,
    input  logic [AXI_USER_WIDTH-1:0]   s_axi_wuser,
    input  logic                        s_axi_wvalid,
    output logic                        s_axi_wready,

    // Write response channel (B)
    output logic [AXI_ID_WIDTH-1:0]     s_axi_bid,
    output logic [1:0]                  s_axi_bresp,
    output logic [AXI_USER_WIDTH-1:0]   s_axi_buser,
    output logic                        s_axi_bvalid,
    input  logic                        s_axi_bready,

    // Status Output
    output logic                        busy
);

    //==========================================================================
    // Internal Signals - FUB (Functional Unit Backend) Interface
    //==========================================================================

    // Internal interface between axi4_slave_wr and CRC checker
    logic [AXI_ID_WIDTH-1:0]     fub_axi_awid;
    logic [AXI_ADDR_WIDTH-1:0]   fub_axi_awaddr;
    logic [7:0]                  fub_axi_awlen;
    logic [2:0]                  fub_axi_awsize;
    logic [1:0]                  fub_axi_awburst;
    logic                        fub_axi_awlock;
    logic [3:0]                  fub_axi_awcache;
    logic [2:0]                  fub_axi_awprot;
    logic [3:0]                  fub_axi_awqos;
    logic [3:0]                  fub_axi_awregion;
    logic [AXI_USER_WIDTH-1:0]   fub_axi_awuser;
    logic                        fub_axi_awvalid;
    logic                        fub_axi_awready;

    logic [AXI_DATA_WIDTH-1:0]   fub_axi_wdata;
    logic [AXI_DATA_WIDTH/8-1:0] fub_axi_wstrb;
    logic                        fub_axi_wlast;
    logic [AXI_USER_WIDTH-1:0]   fub_axi_wuser;
    logic                        fub_axi_wvalid;
    logic                        fub_axi_wready;

    logic [AXI_ID_WIDTH-1:0]     fub_axi_bid;
    logic [1:0]                  fub_axi_bresp;
    logic [AXI_USER_WIDTH-1:0]   fub_axi_buser;
    logic                        fub_axi_bvalid;
    logic                        fub_axi_bready;

    //==========================================================================
    // Extract 32-bit Slice from AXI Data
    //==========================================================================

    logic [31:0] data_slice;

    generate
        if (AXI_DATA_WIDTH == 32) begin : gen_no_slice
            // Direct connection for 32-bit AXI data
            assign data_slice = fub_axi_wdata;
        end else begin : gen_slice
            // Extract 32-bit slice based on CRC_SLICE_OFFSET
            localparam int SLICE_LSB = CRC_SLICE_OFFSET * 32;
            localparam int SLICE_MSB = SLICE_LSB + 31;

            // Bounds checking at compile time
            initial begin
                if (SLICE_MSB >= AXI_DATA_WIDTH) begin
                    $error("CRC_SLICE_OFFSET=%0d out of range for AXI_DATA_WIDTH=%0d",
                           CRC_SLICE_OFFSET, AXI_DATA_WIDTH);
                end
            end

            assign data_slice = fub_axi_wdata[SLICE_MSB:SLICE_LSB];
        end
    endgenerate

    //==========================================================================
    // CRC-32 Calculator
    //==========================================================================

    logic        crc_load_start;
    logic        crc_load_from_cascade;
    logic [3:0]  crc_cascade_sel;
    logic [31:0] crc_out;
    logic        crc_update;

    // CRC resets on crc_reset pulse
    assign crc_load_start = crc_reset;

    // CRC updates on each write beat
    assign crc_update = fub_axi_wvalid && fub_axi_wready;
    assign crc_load_from_cascade = crc_update;

    // Process all 4 bytes of 32-bit slice (cascade_sel = one-hot for byte 3)
    assign crc_cascade_sel = 4'b1000;

    dataint_crc #(
        .ALGO_NAME("CRC32_WRITE_CHECK"),
        .DATA_WIDTH(CRC_DATA_WIDTH),  // 32-bit input
        .CRC_WIDTH(CRC_WIDTH),        // 32-bit output
        .REFIN(CRC_REFIN),
        .REFOUT(CRC_REFOUT)
    ) u_crc (
        .POLY(CRC_POLY),
        .POLY_INIT(CRC_INIT),
        .XOROUT(CRC_XOROUT),
        .clk(aclk),
        .rst_n(aresetn),
        .load_crc_start(crc_load_start),
        .load_from_cascade(crc_load_from_cascade),
        .cascade_sel(crc_cascade_sel),
        .data(data_slice),  // CRC on 32-bit slice
        .crc(crc_out)
    );

    //==========================================================================
    // CRC Valid and Beat Counter
    //==========================================================================

    logic r_crc_valid;
    logic [31:0] r_beat_count;

    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_crc_valid <= 1'b0;
            r_beat_count <= '0;
        end else begin
            // CRC valid after first update
            if (crc_reset) begin
                r_crc_valid <= 1'b0;
            end else if (crc_update) begin
                r_crc_valid <= 1'b1;
            end

            // Beat counter
            if (crc_reset) begin
                r_beat_count <= '0;
            end else if (crc_update) begin
                r_beat_count <= r_beat_count + 1'b1;
            end
        end
    )

    // Output assignments
    assign write_crc_value  = crc_out;
    assign write_crc_valid  = r_crc_valid;
    assign write_beat_count = r_beat_count;

    //==========================================================================
    // FUB Interface - Accept Writes (Data Discarded)
    //==========================================================================

    // FUB AW channel ready (always ready)
    assign fub_axi_awready = 1'b1;

    // FUB W channel ready (always ready, data discarded)
    assign fub_axi_wready = 1'b1;

    // FUB B channel - Write response (always OKAY)
    assign fub_axi_bid    = fub_axi_awid;   // Pass through ID
    assign fub_axi_bresp  = 2'b00;          // OKAY response
    assign fub_axi_buser  = '0;             // User signal unused
    assign fub_axi_bvalid = fub_axi_wvalid && fub_axi_wlast;  // Response when last beat
    assign fub_axi_bready = 1'b1;           // Always ready

    //==========================================================================
    // AXI4 Slave Write Protocol Handler
    //==========================================================================

    axi4_slave_wr #(
        .SKID_DEPTH_AW      (SKID_DEPTH_AW),
        .SKID_DEPTH_W       (SKID_DEPTH_W),
        .SKID_DEPTH_B       (SKID_DEPTH_B),
        .AXI_ID_WIDTH       (AXI_ID_WIDTH),
        .AXI_ADDR_WIDTH     (AXI_ADDR_WIDTH),
        .AXI_DATA_WIDTH     (AXI_DATA_WIDTH),
        .AXI_USER_WIDTH     (AXI_USER_WIDTH)
    ) u_axi4_slave_wr (
        // Clock and Reset
        .aclk               (aclk),
        .aresetn            (aresetn),

        // Slave AXI Interface (External)
        .s_axi_awid         (s_axi_awid),
        .s_axi_awaddr       (s_axi_awaddr),
        .s_axi_awlen        (s_axi_awlen),
        .s_axi_awsize       (s_axi_awsize),
        .s_axi_awburst      (s_axi_awburst),
        .s_axi_awlock       (s_axi_awlock),
        .s_axi_awcache      (s_axi_awcache),
        .s_axi_awprot       (s_axi_awprot),
        .s_axi_awqos        (s_axi_awqos),
        .s_axi_awregion     (s_axi_awregion),
        .s_axi_awuser       (s_axi_awuser),
        .s_axi_awvalid      (s_axi_awvalid),
        .s_axi_awready      (s_axi_awready),

        .s_axi_wdata        (s_axi_wdata),
        .s_axi_wstrb        (s_axi_wstrb),
        .s_axi_wlast        (s_axi_wlast),
        .s_axi_wuser        (s_axi_wuser),
        .s_axi_wvalid       (s_axi_wvalid),
        .s_axi_wready       (s_axi_wready),

        .s_axi_bid          (s_axi_bid),
        .s_axi_bresp        (s_axi_bresp),
        .s_axi_buser        (s_axi_buser),
        .s_axi_bvalid       (s_axi_bvalid),
        .s_axi_bready       (s_axi_bready),

        // Master AXI Interface (Internal to CRC checker)
        .fub_axi_awid       (fub_axi_awid),
        .fub_axi_awaddr     (fub_axi_awaddr),
        .fub_axi_awlen      (fub_axi_awlen),
        .fub_axi_awsize     (fub_axi_awsize),
        .fub_axi_awburst    (fub_axi_awburst),
        .fub_axi_awlock     (fub_axi_awlock),
        .fub_axi_awcache    (fub_axi_awcache),
        .fub_axi_awprot     (fub_axi_awprot),
        .fub_axi_awqos      (fub_axi_awqos),
        .fub_axi_awregion   (fub_axi_awregion),
        .fub_axi_awuser     (fub_axi_awuser),
        .fub_axi_awvalid    (fub_axi_awvalid),
        .fub_axi_awready    (fub_axi_awready),

        .fub_axi_wdata      (fub_axi_wdata),
        .fub_axi_wstrb      (fub_axi_wstrb),
        .fub_axi_wlast      (fub_axi_wlast),
        .fub_axi_wuser      (fub_axi_wuser),
        .fub_axi_wvalid     (fub_axi_wvalid),
        .fub_axi_wready     (fub_axi_wready),

        .fub_axi_bid        (fub_axi_bid),
        .fub_axi_bresp      (fub_axi_bresp),
        .fub_axi_buser      (fub_axi_buser),
        .fub_axi_bvalid     (fub_axi_bvalid),
        .fub_axi_bready     (fub_axi_bready),

        // Status Output
        .busy               (busy)
    );

endmodule : axi4_slave_wr_crc_check
