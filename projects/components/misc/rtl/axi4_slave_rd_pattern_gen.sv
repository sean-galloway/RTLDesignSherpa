`timescale 1ns / 1ps

//==============================================================================
// Module: axi4_slave_rd_pattern_gen
//==============================================================================
// Description:
//   AXI4 read-only slave that generates pseudo-random patterns using LFSR
//   and computes CRC-32 for DMA validation. Combines axi4_slave_rd protocol
//   handler with LFSR pattern generator and CRC checker.
//
// Purpose:
//   DMA characterization and data integrity validation. Read pattern data
//   via DMA, write to companion axi4_slave_wr_crc_check module, then compare
//   CRC values to verify data integrity across entire transfer.
//
// Parameters:
//   SKID_DEPTH_AR  - AR channel skid buffer depth (default: 2)
//   SKID_DEPTH_R   - R channel skid buffer depth (default: 4)
//   AXI_ID_WIDTH   - AXI ID width (default: 8)
//   AXI_ADDR_WIDTH - AXI address width (default: 32)
//   AXI_DATA_WIDTH - AXI data width (default: 64, can be wider)
//   AXI_USER_WIDTH - AXI user signal width (default: 1)
//   LFSR_SEED      - LFSR initial seed value (default: 0xDEADBEEF)
//   LFSR_TAPS      - LFSR tap positions for maximal length (default: [32,22,2,1])
//
// Architecture:
//   AXI AR → axi4_slave_rd → LFSR (32-bit) → Replicate → AXI R data
//                                    ↓
//                                  CRC-32 → read_crc_value output
//
// Interfaces:
//   aclk, aresetn         - Clock and reset
//   crc_lfsr_reset        - Synchronous reset for test control (from UART)
//   read_crc_value[31:0]  - CRC-32 output for validation
//   read_crc_valid        - CRC value is valid (after first update)
//   read_beat_count[31:0] - Number of AXI read beats served
//   s_axi_ar*             - AXI4 read address channel (slave)
//   s_axi_r*              - AXI4 read data channel (slave)
//   busy                  - Status output (active transactions)
//
// Notes:
//   - LFSR is 32-bit, replicated to fill AXI_DATA_WIDTH
//   - CRC processes 32-bit LFSR output (before replication)
//   - CRC-32 Ethernet standard (POLY=0x04C11DB7, INIT/XOR=0xFFFFFFFF)
//   - LFSR advances on each AXI read beat
//   - crc_lfsr_reset resets both LFSR and CRC for new test sequence
//   - Companion module: axi4_slave_wr_crc_check.sv (must use matching CRC params)
//
// Example Usage (Python via UART):
//   uart.write("RESET_CRC_LFSR")
//   dma.read_burst(addr=pattern_gen_addr, length=10000)
//   dma.write_burst(addr=crc_check_addr, length=10000)
//   read_crc = uart.read("READ_CRC_VALUE")
//   write_crc = uart.read("WRITE_CRC_VALUE")
//   assert read_crc == write_crc, "DMA data integrity failure!"
//
//==============================================================================

`include "reset_defs.svh"

module axi4_slave_rd_pattern_gen #(
    // AXI parameters
    parameter int SKID_DEPTH_AR  = 2,
    parameter int SKID_DEPTH_R   = 4,
    parameter int AXI_ID_WIDTH   = 8,
    parameter int AXI_ADDR_WIDTH = 32,
    parameter int AXI_DATA_WIDTH = 64,
    parameter int AXI_USER_WIDTH = 1,

    // LFSR parameters (32-bit fixed for simplicity and timing)
    parameter int LFSR_WIDTH = 32,
    parameter logic [31:0] LFSR_SEED = 32'hDEADBEEF,
    parameter logic [47:0] LFSR_TAPS = {12'd32, 12'd22, 12'd2, 12'd1},  // Maximal length

    // CRC parameters (fixed, MUST MATCH axi4_slave_wr_crc_check!)
    parameter int CRC_WIDTH      = 32,
    parameter int CRC_DATA_WIDTH = 32,  // Process 32-bit LFSR output only
    parameter logic [31:0] CRC_POLY    = 32'h04C11DB7,  // CRC-32 Ethernet
    parameter logic [31:0] CRC_INIT    = 32'hFFFFFFFF,
    parameter logic [31:0] CRC_XOROUT  = 32'hFFFFFFFF,
    parameter int CRC_REFIN  = 1,
    parameter int CRC_REFOUT = 1,

    // Derived parameters
    parameter int REPLICATION_FACTOR = (AXI_DATA_WIDTH + 31) / 32
) (
    // Global Clock and Reset
    input  logic                        aclk,
    input  logic                        aresetn,

    // Test Control (from UART controller or test logic)
    input  logic                        crc_lfsr_reset,  // Pulse to reset LFSR and CRC

    // CRC and Status Outputs (to UART controller)
    output logic [31:0]                 read_crc_value,   // Current CRC-32 value
    output logic                        read_crc_valid,   // CRC valid after first update
    output logic [31:0]                 read_beat_count,  // Number of read beats served

    // AXI4 Slave Interface (Read-Only)
    // Read address channel (AR)
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

    // Read data channel (R)
    output logic [AXI_ID_WIDTH-1:0]     s_axi_rid,
    output logic [AXI_DATA_WIDTH-1:0]   s_axi_rdata,
    output logic [1:0]                  s_axi_rresp,
    output logic                        s_axi_rlast,
    output logic [AXI_USER_WIDTH-1:0]   s_axi_ruser,
    output logic                        s_axi_rvalid,
    input  logic                        s_axi_rready,

    // Status Output
    output logic                        busy
);

    //==========================================================================
    // Local Parameters
    //==========================================================================

    localparam int LFSR_TAP_INDEX_WIDTH = 12;
    localparam int LFSR_TAP_COUNT = 4;

    //==========================================================================
    // Internal Signals - FUB (Functional Unit Backend) Interface
    //==========================================================================

    // Internal interface between axi4_slave_rd and pattern generator
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
    // LFSR Pattern Generator
    //==========================================================================

    logic [31:0] lfsr_out;
    logic        lfsr_enable;
    logic        lfsr_seed_load;

    // LFSR advances on each read beat
    assign lfsr_enable = fub_axi_arvalid && fub_axi_arready;
    assign lfsr_seed_load = crc_lfsr_reset;

    shifter_lfsr_fibonacci #(
        .WIDTH(LFSR_WIDTH),
        .TAP_INDEX_WIDTH(LFSR_TAP_INDEX_WIDTH),
        .TAP_COUNT(LFSR_TAP_COUNT)
    ) u_lfsr (
        .clk(aclk),
        .rst_n(aresetn),
        .enable(lfsr_enable),
        .seed_load(lfsr_seed_load),
        .seed_data(LFSR_SEED),
        .taps(LFSR_TAPS),
        .lfsr_out(lfsr_out),
        .lfsr_done()  // Not used
    );

    //==========================================================================
    // Pattern Data Replication
    //==========================================================================

    logic [AXI_DATA_WIDTH-1:0] pattern_data;

    // Replicate 32-bit LFSR output to fill AXI data width
    generate
        if (AXI_DATA_WIDTH == 32) begin : gen_no_replication
            assign pattern_data = lfsr_out;
        end else if (AXI_DATA_WIDTH % 32 == 0) begin : gen_aligned_replication
            // Clean multiple of 32 bits
            assign pattern_data = {REPLICATION_FACTOR{lfsr_out}};
        end else begin : gen_unaligned_replication
            // Partial replication for non-multiple widths
            logic [(REPLICATION_FACTOR*32)-1:0] temp_pattern;
            assign temp_pattern = {REPLICATION_FACTOR{lfsr_out}};
            assign pattern_data = temp_pattern[AXI_DATA_WIDTH-1:0];
        end
    endgenerate

    //==========================================================================
    // CRC-32 Calculator
    //==========================================================================

    logic        crc_load_start;
    logic        crc_load_from_cascade;
    logic [3:0]  crc_cascade_sel;
    logic [31:0] crc_out;

    // CRC resets on crc_lfsr_reset pulse
    assign crc_load_start = crc_lfsr_reset;

    // CRC updates on each read beat (processes 32-bit LFSR output)
    assign crc_load_from_cascade = lfsr_enable;

    // Process all 4 bytes of 32-bit LFSR output (cascade_sel = one-hot for byte 3)
    assign crc_cascade_sel = 4'b1000;

    dataint_crc #(
        .ALGO_NAME("CRC32_READ_PATTERN"),
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
        .data(lfsr_out),  // CRC on 32-bit LFSR output (before replication)
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
            if (crc_lfsr_reset) begin
                r_crc_valid <= 1'b0;
            end else if (lfsr_enable) begin
                r_crc_valid <= 1'b1;
            end

            // Beat counter
            if (crc_lfsr_reset) begin
                r_beat_count <= '0;
            end else if (lfsr_enable) begin
                r_beat_count <= r_beat_count + 1'b1;
            end
        end
    )

    // Output assignments
    assign read_crc_value  = crc_out;
    assign read_crc_valid  = r_crc_valid;
    assign read_beat_count = r_beat_count;

    //==========================================================================
    // FUB Interface - Connect Pattern Data to AXI
    //==========================================================================

    // FUB AR channel ready (always ready for single-cycle access)
    assign fub_axi_arready = 1'b1;

    // FUB R channel - Pattern data and control
    assign fub_axi_rid     = fub_axi_arid;      // Pass through ID
    assign fub_axi_rdata   = pattern_data;      // LFSR pattern (replicated)
    assign fub_axi_rresp   = 2'b00;             // OKAY response
    assign fub_axi_rlast   = 1'b1;              // Single-beat response (burst handled by slave_rd)
    assign fub_axi_ruser   = '0;                // User signal unused
    assign fub_axi_rvalid  = fub_axi_arvalid;   // Valid when AR valid (single-cycle)
    assign fub_axi_rready  = 1'b1;              // Always ready (no backpressure)

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

        // Master AXI Interface (Internal to pattern generator)
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

endmodule : axi4_slave_rd_pattern_gen
