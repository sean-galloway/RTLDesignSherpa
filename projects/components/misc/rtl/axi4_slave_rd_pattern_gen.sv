`timescale 1ns / 1ps

//==============================================================================
// Module: axi4_slave_rd_pattern_gen
//==============================================================================
//
// TODO -- ARCHITECTURAL RULE: every AXI/AXIL agent must use the standard
// protocol modules under rtl/amba/. The AR/R protocol logic in this module
// is hand-rolled and therefore NON-COMPLIANT. Refactor to wrap
// `axi4_slave_rd_mon` (which already bundles `axi4_slave_rd` + filtered
// monitor) and drive the LFSR pattern generator + CRC accumulator from
// its fub_axi_ar* / fub_axi_r* user interface. Tracked as task #78.
//
// Description:
//   AXI4 read-only slave that generates pseudo-random patterns using LFSR
//   and computes CRC-32 for DMA validation. Combines axi4_slave_rd protocol
//   handler with LFSR pattern generator and CRC checker.
//
//   Per-channel mode (NUM_CHANNELS > 1): the slave maintains independent
//   LFSR + CRC state per channel, demuxed off the low bits of s_axi_arid.
//   This makes the data each channel reads back independent of any other
//   channel's traffic, so a multi-channel test can verify integrity per
//   channel without ordering interleave at the shared AXI port corrupting
//   the running CRC.
//
// Parameters:
//   NUM_CHANNELS   - Number of independent LFSR/CRC contexts (default: 1)
//   SKID_DEPTH_AR  - AR channel skid buffer depth (default: 2)
//   SKID_DEPTH_R   - R channel skid buffer depth (default: 4)
//   AXI_ID_WIDTH   - AXI ID width (default: 8). Channel index is extracted
//                    from arid[CIW-1:0] where CIW = $clog2(NUM_CHANNELS).
//   AXI_ADDR_WIDTH - AXI address width (default: 32)
//   AXI_DATA_WIDTH - AXI data width (default: 64, can be wider)
//   AXI_USER_WIDTH - AXI user signal width (default: 1)
//   LFSR_SEED      - Base LFSR seed; channel N uses (LFSR_SEED ^ N) so
//                    each channel generates a distinct pseudo-random stream
//
// Per-channel outputs:
//   read_crc_value [NUM_CHANNELS][31:0]  - per-channel CRC values
//   read_crc_valid [NUM_CHANNELS]        - per-channel valid flags
//   read_beat_count[NUM_CHANNELS][31:0]  - per-channel beat counts
//
// Aggregate output (for harness timer):
//   read_beat_count_total [31:0]         - sum of per-channel beat counts
//
//==============================================================================

`include "reset_defs.svh"

module axi4_slave_rd_pattern_gen #(
    // AXI parameters
    parameter int NUM_CHANNELS  = 1,
    parameter int SKID_DEPTH_AR = 2,
    parameter int SKID_DEPTH_R  = 4,
    parameter int AXI_ID_WIDTH  = 8,
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
    parameter int REPLICATION_FACTOR = (AXI_DATA_WIDTH + 31) / 32,
    parameter int CIW = (NUM_CHANNELS > 1) ? $clog2(NUM_CHANNELS) : 1
) (
    // Global Clock and Reset
    input  logic                        aclk,
    input  logic                        aresetn,

    // Test Control (from UART controller or test logic)
    input  logic                        crc_lfsr_reset,  // Pulse to reset LFSR and CRC

    // Per-channel CRC and Status Outputs
    output logic [NUM_CHANNELS-1:0][31:0] read_crc_value,
    output logic [NUM_CHANNELS-1:0]       read_crc_valid,
    output logic [NUM_CHANNELS-1:0][31:0] read_beat_count,
    // Aggregate beat count (sum across channels) for the harness stop trigger.
    output logic [31:0]                   read_beat_count_total,

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
    // FUB Burst FSM — early forward-declarations (used by the per-channel
    // LFSR/CRC generate block below before the FSM body that drives them)
    //==========================================================================

    typedef enum logic [1:0] {
        RD_IDLE   = 2'b00,
        RD_BURST  = 2'b01
    } rd_state_t;

    rd_state_t r_rd_state;
    logic [AXI_ID_WIDTH-1:0]   r_rd_id;
    logic [AXI_USER_WIDTH-1:0] r_rd_user;
    logic [7:0]                r_rd_beats_remaining;

    // Active channel index for the in-flight burst (low bits of the captured AR ID)
    logic [CIW-1:0] w_active_ch;
    assign w_active_ch = (NUM_CHANNELS == 1) ? '0 : r_rd_id[CIW-1:0];

    // R-beat handshake (one beat consumed per channel per cycle)
    wire w_r_beat = fub_axi_rvalid && fub_axi_rready;

    //==========================================================================
    // Per-channel LFSR Pattern Generators
    //==========================================================================
    // Each channel has its own LFSR seeded uniquely (LFSR_SEED ^ ch_index)
    // so its data stream is independent of other channels'. Only the channel
    // currently being served advances on each R beat; the others hold state.

    logic [31:0] lfsr_out_per_ch [NUM_CHANNELS];

    genvar gch;
    generate
        for (gch = 0; gch < NUM_CHANNELS; gch++) begin : gen_lfsr
            logic ch_enable;
            // LFSR advances on this channel's R beat, OR loads its seed on
            // the global crc_lfsr_reset pulse (the LFSR module accepts the
            // seed only when enable is also high during seed_load).
            assign ch_enable = (w_r_beat && (w_active_ch == gch[CIW-1:0]))
                            || crc_lfsr_reset;

            shifter_lfsr_fibonacci #(
                .WIDTH(LFSR_WIDTH),
                .TAP_INDEX_WIDTH(LFSR_TAP_INDEX_WIDTH),
                .TAP_COUNT(LFSR_TAP_COUNT)
            ) u_lfsr (
                .clk      (aclk),
                .rst_n    (aresetn),
                .enable   (ch_enable),
                .seed_load(crc_lfsr_reset),
                .seed_data(LFSR_SEED ^ 32'(gch)),  // unique seed per channel
                .taps     (LFSR_TAPS),
                .lfsr_out (lfsr_out_per_ch[gch]),
                .lfsr_done()
            );
        end
    endgenerate

    // Active channel's LFSR output drives the R data
    logic [31:0] lfsr_out;
    assign lfsr_out = lfsr_out_per_ch[w_active_ch];

    //==========================================================================
    // Pattern Data Replication (active channel feeds the AXI R bus)
    //==========================================================================

    logic [AXI_DATA_WIDTH-1:0] pattern_data;

    generate
        if (AXI_DATA_WIDTH == 32) begin : gen_no_replication
            assign pattern_data = lfsr_out;
        end else if (AXI_DATA_WIDTH % 32 == 0) begin : gen_aligned_replication
            assign pattern_data = {REPLICATION_FACTOR{lfsr_out}};
        end else begin : gen_unaligned_replication
            logic [(REPLICATION_FACTOR*32)-1:0] temp_pattern;
            assign temp_pattern = {REPLICATION_FACTOR{lfsr_out}};
            assign pattern_data = temp_pattern[AXI_DATA_WIDTH-1:0];
        end
    endgenerate

    //==========================================================================
    // Per-channel CRC-32 Calculators + beat counters
    //==========================================================================
    // Each channel has its own dataint_crc instance and beat counter.
    // The CRC for channel N updates only when the active R beat is for ch N.

    logic [31:0] crc_out_per_ch [NUM_CHANNELS];

    generate
        for (gch = 0; gch < NUM_CHANNELS; gch++) begin : gen_crc
            logic ch_load_from_cascade;
            logic r_ch_crc_valid;
            logic [31:0] r_ch_beat_count;

            // CRC accumulates only for this channel's beats
            assign ch_load_from_cascade = w_r_beat
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
                .load_crc_start   (crc_lfsr_reset),
                .load_from_cascade(ch_load_from_cascade),
                .cascade_sel      (4'b1000),  // process all 4 bytes of 32-bit slice
                .data             (lfsr_out_per_ch[gch]),
                .crc              (crc_out_per_ch[gch])
            );

            // Per-channel CRC-valid + beat counter
            `ALWAYS_FF_RST(aclk, aresetn,
                if (`RST_ASSERTED(aresetn)) begin
                    r_ch_crc_valid  <= 1'b0;
                    r_ch_beat_count <= '0;
                end else begin
                    if (crc_lfsr_reset) begin
                        r_ch_crc_valid  <= 1'b0;
                        r_ch_beat_count <= '0;
                    end else if (ch_load_from_cascade) begin
                        r_ch_crc_valid  <= 1'b1;
                        r_ch_beat_count <= r_ch_beat_count + 1'b1;
                    end
                end
            )

            assign read_crc_value [gch] = crc_out_per_ch[gch];
            assign read_crc_valid [gch] = r_ch_crc_valid;
            assign read_beat_count[gch] = r_ch_beat_count;
        end
    endgenerate

    //==========================================================================
    // Aggregate beat count (sum across all channels) for the harness timer
    //==========================================================================

    always_comb begin
        read_beat_count_total = '0;
        for (int ch = 0; ch < NUM_CHANNELS; ch++) begin
            read_beat_count_total = read_beat_count_total + read_beat_count[ch];
        end
    end

    //==========================================================================
    // FUB Interface - Burst FSM
    //==========================================================================
    // Accepts AR requests, tracks burst beat count, generates R beats with
    // LFSR pattern data. Asserts rlast on final beat of each burst.

    // Accept AR only when idle
    assign fub_axi_arready = (r_rd_state == RD_IDLE);

    // R channel outputs
    assign fub_axi_rid   = r_rd_id;
    assign fub_axi_rdata = pattern_data;
    assign fub_axi_rresp = 2'b00;  // OKAY
    assign fub_axi_ruser = r_rd_user;
    assign fub_axi_rlast = (r_rd_state == RD_BURST) && (r_rd_beats_remaining == 8'd0);
    assign fub_axi_rvalid = (r_rd_state == RD_BURST);

    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_rd_state <= RD_IDLE;
            r_rd_id <= '0;
            r_rd_user <= '0;
            r_rd_beats_remaining <= '0;
        end else begin
            case (r_rd_state)
                RD_IDLE: begin
                    if (fub_axi_arvalid && fub_axi_arready) begin
                        r_rd_state <= RD_BURST;
                        r_rd_id <= fub_axi_arid;
                        r_rd_user <= fub_axi_aruser;
                        r_rd_beats_remaining <= fub_axi_arlen;  // arlen = beats - 1
                    end
                end

                RD_BURST: begin
                    if (fub_axi_rvalid && fub_axi_rready) begin
                        if (r_rd_beats_remaining == 8'd0) begin
                            r_rd_state <= RD_IDLE;
                        end else begin
                            r_rd_beats_remaining <= r_rd_beats_remaining - 8'd1;
                        end
                    end
                end

                default: r_rd_state <= RD_IDLE;
            endcase
        end
    )

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
        .aclk               (aclk),
        .aresetn            (aresetn),

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

        .busy               (busy)
    );

endmodule : axi4_slave_rd_pattern_gen
