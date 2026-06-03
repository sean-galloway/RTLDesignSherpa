`timescale 1ns / 1ps

//==============================================================================
// Module: axi4_slave_wr_crc_check
//==============================================================================
//
// TODO -- ARCHITECTURAL RULE: every AXI/AXIL agent must use the standard
// protocol modules under rtl/amba/. The AW/W/B protocol logic in this
// module is hand-rolled and therefore NON-COMPLIANT. Refactor to wrap
// `axi4_slave_wr_mon` (which already bundles `axi4_slave_wr` + filtered
// monitor) and drive the CRC accumulator from its fub_axi_aw* / fub_axi_w*
// / fub_axi_b* user interface. Tracked as task #79.
//
// Description:
//   AXI4 write-only slave that computes CRC-32 on received data for DMA
//   validation. Combines axi4_slave_wr protocol handler with CRC checker.
//
//   Per-channel mode (NUM_CHANNELS > 1): the slave maintains independent
//   CRC state per channel, demuxed off the low bits of the W-side wuser
//   (which the STREAM master drives with the burst's channel index). The
//   AW FSM accepts one burst at a time and W beats are in-order with AW,
//   so r_wr_id[CIW-1:0] is the active channel during W; we use that as
//   the demux selector.
//
// Per-channel outputs:
//   write_crc_value [NUM_CHANNELS][31:0] - per-channel CRC values
//   write_crc_valid [NUM_CHANNELS]       - per-channel valid flags
//   write_beat_count[NUM_CHANNELS][31:0] - per-channel beat counts
//
// Aggregate output (for harness timer):
//   write_beat_count_total [31:0]        - sum of per-channel beat counts
//
//==============================================================================

`include "reset_defs.svh"

module axi4_slave_wr_crc_check #(
    // AXI parameters
    parameter int NUM_CHANNELS  = 1,
    parameter int SKID_DEPTH_AW = 2,
    parameter int SKID_DEPTH_W  = 4,
    parameter int SKID_DEPTH_B  = 2,
    parameter int AXI_ID_WIDTH  = 8,
    parameter int AXI_ADDR_WIDTH = 32,
    parameter int AXI_DATA_WIDTH = 64,
    parameter int AXI_USER_WIDTH = 1,

    // CRC parameters (MUST MATCH axi4_slave_rd_pattern_gen!)
    parameter int CRC_WIDTH      = 32,
    parameter int CRC_DATA_WIDTH = 32,
    parameter logic [31:0] CRC_POLY    = 32'h04C11DB7,
    parameter logic [31:0] CRC_INIT    = 32'hFFFFFFFF,
    parameter logic [31:0] CRC_XOROUT  = 32'hFFFFFFFF,
    parameter int CRC_REFIN  = 1,
    parameter int CRC_REFOUT = 1,

    // Which 32-bit slice to CRC from AXI_DATA_WIDTH
    parameter int CRC_SLICE_OFFSET = 0,

    // Derived
    parameter int CIW = (NUM_CHANNELS > 1) ? $clog2(NUM_CHANNELS) : 1
) (
    // Global Clock and Reset
    input  logic                        aclk,
    input  logic                        aresetn,

    // Test Control
    input  logic                        crc_reset,

    // Per-channel CRC and Status Outputs
    output logic [NUM_CHANNELS-1:0][31:0] write_crc_value,
    output logic [NUM_CHANNELS-1:0]       write_crc_valid,
    output logic [NUM_CHANNELS-1:0][31:0] write_beat_count,
    // Aggregate beat count (sum across channels) for the harness stop trigger.
    output logic [31:0]                   write_beat_count_total,

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
            assign data_slice = fub_axi_wdata;
        end else begin : gen_slice
            localparam int SLICE_LSB = CRC_SLICE_OFFSET * 32;
            localparam int SLICE_MSB = SLICE_LSB + 31;

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
    // FUB burst state (declared early — used by per-channel CRC gating)
    //==========================================================================

    logic                      r_b_pending;
    logic [AXI_ID_WIDTH-1:0]   r_wr_id;
    logic [AXI_USER_WIDTH-1:0] r_wr_user;
    logic                      r_wr_active;

    // Active channel index for the in-flight burst (low bits of captured AW ID).
    logic [CIW-1:0] w_active_ch;
    assign w_active_ch = (NUM_CHANNELS == 1) ? '0 : r_wr_id[CIW-1:0];

    // Single accepted-W-beat strobe; per-channel CRC instances gate on this.
    wire w_w_beat = fub_axi_wvalid && fub_axi_wready && r_wr_active;

    //==========================================================================
    // Per-channel CRC-32 Calculators + beat counters
    //==========================================================================

    logic [31:0] crc_out_per_ch [NUM_CHANNELS];

    genvar gch;
    generate
        for (gch = 0; gch < NUM_CHANNELS; gch++) begin : gen_crc
            logic ch_load_from_cascade;
            logic r_ch_crc_valid;
            logic [31:0] r_ch_beat_count;

            // CRC accumulates only when the active burst belongs to this channel
            assign ch_load_from_cascade = w_w_beat
                                       && (w_active_ch == gch[CIW-1:0]);

            dataint_crc #(
                .DATA_WIDTH(CRC_DATA_WIDTH),
                .CRC_WIDTH (CRC_WIDTH),
                .REFIN     (CRC_REFIN),
                .REFOUT    (CRC_REFOUT)
            ) u_crc (
                .POLY             (CRC_POLY),
                .POLY_INIT        (CRC_INIT),
                .XOROUT           (CRC_XOROUT),
                .clk              (aclk),
                .rst_n            (aresetn),
                .load_crc_start   (crc_reset),
                .load_from_cascade(ch_load_from_cascade),
                .cascade_sel      (4'b1000),
                .data             (data_slice),
                .crc              (crc_out_per_ch[gch])
            );

            `ALWAYS_FF_RST(aclk, aresetn,
                if (`RST_ASSERTED(aresetn)) begin
                    r_ch_crc_valid  <= 1'b0;
                    r_ch_beat_count <= '0;
                end else begin
                    if (crc_reset) begin
                        r_ch_crc_valid  <= 1'b0;
                        r_ch_beat_count <= '0;
                    end else if (ch_load_from_cascade) begin
                        r_ch_crc_valid  <= 1'b1;
                        r_ch_beat_count <= r_ch_beat_count + 1'b1;
                    end
                end
            )

            assign write_crc_value [gch] = crc_out_per_ch[gch];
            assign write_crc_valid [gch] = r_ch_crc_valid;
            assign write_beat_count[gch] = r_ch_beat_count;
        end
    endgenerate

    //==========================================================================
    // Aggregate beat count (sum across all channels) for the harness timer
    //==========================================================================

    always_comb begin
        write_beat_count_total = '0;
        for (int ch = 0; ch < NUM_CHANNELS; ch++) begin
            write_beat_count_total = write_beat_count_total + write_beat_count[ch];
        end
    end

    //==========================================================================
    // FUB Interface - Burst FSM for Write Acceptance
    //==========================================================================

    assign fub_axi_awready = !r_wr_active;
    assign fub_axi_wready  = r_wr_active;
    assign fub_axi_bid     = r_wr_id;
    assign fub_axi_bresp   = 2'b00;  // OKAY
    assign fub_axi_buser   = r_wr_user;
    assign fub_axi_bvalid  = r_b_pending;

    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_wr_active <= 1'b0;
            r_b_pending <= 1'b0;
            r_wr_id <= '0;
            r_wr_user <= '0;
        end else begin
            // AW acceptance — start a new burst
            if (fub_axi_awvalid && fub_axi_awready) begin
                r_wr_active <= 1'b1;
                r_wr_id <= fub_axi_awid;
                r_wr_user <= fub_axi_awuser;
            end

            // W last beat — end burst, assert B
            if (r_wr_active && fub_axi_wvalid && fub_axi_wready && fub_axi_wlast) begin
                r_wr_active <= 1'b0;
                r_b_pending <= 1'b1;
            end

            // B consumed by skid buffer
            if (r_b_pending && fub_axi_bready) begin
                r_b_pending <= 1'b0;
            end
        end
    )

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
        .aclk               (aclk),
        .aresetn            (aresetn),

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

        .busy               (busy)
    );

endmodule : axi4_slave_wr_crc_check
